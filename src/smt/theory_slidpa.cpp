#include "ast/expr_abstract.h"
#include "smt/smt_context.h"
#include "theory_slidpa.h"

#include <string>
#include <queue>

namespace smt {

namespace slidpa {

inductive_definition_manager::inductive_definition_manager(ast_manager& om)
    : o_manager(om),
      util(om),
      name2decl(),
      inductive_definitions(),
      def2abs(),
      aux_rpl(om),
      x(util.mk_loc("x")),
      y(util.mk_loc("y")) {}

void inductive_definition_manager::register_defs(recfun::decl::plugin* recfun_plugin) {
    if (recfun_plugin == nullptr) {
        o_manager.raise_exception(" no recfun plugin?");
        return;
    }
    SLIDPA_MSG("Handle inductive definitions");
    for (auto recf : recfun_plugin->get_rec_funs()) {
        recfun::def& def = recfun_plugin->get_def(recf);
        func_decl* fd = def.get_decl();

        // replace args to x and y
        aux_rpl.insert(def.get_vars()[0], x);
        aux_rpl.insert(def.get_vars()[1], y);
        
        expr_ref renamed_rule = aux_rpl(def.get_rhs());
        expr* br = to_app(renamed_rule.get())->get_arg(0);
        expr* ir = to_app(renamed_rule.get())->get_arg(1);
        register_def(fd, br ,ir);
    }
    display(std::cout);
}

void inductive_definition_manager::register_def(func_decl* fd, expr* br, expr* ir) {
    inductive_definition def;
    def.fd = fd;
    SLIDPA_MSG("check inductive definition\n" << mk_pp(br, o_manager) << "\n" << mk_pp(ir, o_manager));
    if (!check_base_rule(br) || !check_inductive_rule(ir)) {
        o_manager.raise_exception(" wrong definition ");
        return;
    }
    to_normal_form(br, ir, def);
    std::string name(fd->get_name().bare_str());
    if (name2decl.find(name) != name2decl.end()) return;
    name2decl[name] = fd;
    inductive_definitions.insert(fd, def);
    compute_abs_of(def);
}

func_decl* inductive_definition_manager::get_func_decl(symbol name) {
    return name2decl[std::string(name.bare_str())];
}

inductive_definition& inductive_definition_manager::get_inductive_def(symbol name) {
    return get_inductive_def(name2decl[std::string(name.bare_str())]);
}

inductive_definition& inductive_definition_manager::get_inductive_def(func_decl* fd) {
    SASSERT(fd != nullptr);
    return inductive_definitions.find(fd);
}

expr* inductive_definition_manager::get_abs_of(func_decl* fd) {
    SASSERT(def2abs.contains(fd));
    return def2abs.find(fd);
}

void inductive_definition_manager::display(std::ostream& out) {
    for (auto def : inductive_definitions) {
        out << def.get_key().get_name() << '\n'
            << "Base rule : " << mk_pp(def.get_value().base_rule, o_manager) << '\n'
            << "Inductive rule : " << mk_pp(def.get_value().inductive_rule, o_manager) << '\n'
            << "Abstraction : " << mk_pp(def2abs.find(def.get_value().fd), o_manager) << '\n';
    }
}

void inductive_definition_manager::compute_abs_of(inductive_definition& def) {
    SLIDPA_MSG("compute abstraction of " << def.fd->get_name());
    if (def.size_var == nullptr || def2abs.contains(def.fd)) {
        o_manager.raise_exception(" no size field? has fd?");
        return;
    }
    Bound base;
    if (def.fd->get_name() != "blk")
        base = def.var2bound.find(def.size_var);
    else
        base = std::make_pair(0, -1);
    base.first += def.k;
    if (base.second != -1) base.second += def.k;
    svector<Bound> bounds;
    bounds.push_back(base);
    if (def.is_continuous && base.second != -1) {
        while(true) {
            Bound n_bound = std::make_pair(
                bounds.back().first + base.first,
                bounds.back().second + base.second);
            if (n_bound.first <= bounds.back().second + 1) {
                bounds.back().second = -1; break;
            }
            bounds.push_back(n_bound);
        }
    }
    expr* sz_var = util.mk_loc("sz");
    expr* abs = nullptr;
    for (auto bound : bounds) {
        app* res = nullptr;
        app* glb = util.mk_ge(sz_var, bound.first);
        if (bound.second != -1) {
            app* lub = util.mk_le(sz_var, bound.second);
            res = o_manager.mk_and(glb, lub);
        } else res = glb;
        if (abs == nullptr) abs = res;
        else abs = o_manager.mk_or(abs, res);
    }
    def2abs.insert(def.fd, abs);
}

bool inductive_definition_manager::check_base_rule(expr* n) {
    SLIDPA_MSG("check base rule\n" << mk_pp(n, o_manager));
    if (!is_app(n) || !o_manager.is_and(n)) return false;
    if (to_app(n)->get_num_args() != 2) return false;
    expr* p = to_app(n)->get_arg(0);
    if (!o_manager.is_eq(p)) return false;
    if (to_app(to_app(p)->get_arg(0))->get_name() != "x" ||
        to_app(to_app(p)->get_arg(1))->get_name() != "y")
        return false;
    expr* s = to_app(n)->get_arg(1);
    if (!util.plugin()->is_emp(s)) return false;
    return true;
}

bool inductive_definition_manager::check_inductive_rule(expr* n) {
    SLIDPA_MSG("check inductive rule\n" << mk_pp(n, o_manager));
    if (!is_quantifier(n)) return false;
    expr* body = static_cast<quantifier*>(n)->get_expr();
    expr* p = o_manager.mk_true();
    expr* h;
    if (o_manager.is_and(body) && to_app(body)->get_num_args() == 2) {
        p = to_app(body)->get_arg(0);
        h = to_app(body)->get_arg(1);
    } else if (util.plugin()->is_op_sep(body)) {
        h = body;
    } else return false;
    if (!check_inductive_pure(p)) return false;
    return check_inductive_heap(h);
}

bool inductive_definition_manager::check_inductive_pure(expr* n) {
    if (o_manager.is_true(n)) return true;
    if (o_manager.is_or(n)) return false;
    if (o_manager.is_and(n)) {
        for (auto arg : *to_app(n))
            if (!check_inductive_pure(arg))
                return false;
    } else {
        if (is_app_of(to_app(n)->get_arg(1), arith_family_id, OP_NUM)) {
            if (!is_var(to_app(n)->get_arg(0)))
                return false;
        } else if (is_app_of(to_app(n)->get_arg(0), arith_family_id, OP_NUM)) {
            if (!is_var(to_app(n)->get_arg(0)))
                return false;
        } else return false;

    }
    return true;
}

bool inductive_definition_manager::check_inductive_heap(expr* n) {
    SLIDPA_MSG("check inductive heap\n" << mk_pp(n, o_manager));
    if (!util.plugin()->is_op_sep(n)) return false;
    unsigned int k = 0;
    app* h = to_app(n);
    for (unsigned int i = 0; i < h->get_num_args(); i++)
        if (!util.plugin()->is_op_pto(h->get_arg(i))) {
            k = i; break;
        }
    if (k == 0) return false;
    // TODO if lseg is defined, change the format
    for (unsigned int i = 0; i <= k; i++) {
        app* sh = to_app(h->get_arg(i));
        symbol v;
        unsigned int theta = 0;
        if (i == 0) {
            v = to_app(sh->get_arg(0))->get_name();
            theta = 0;
        } else {
            app* l = to_app(sh->get_arg(0));
            if (!util.plugin()->is_op_add(l)) return false;
            if (!is_app_of(l->get_arg(1), arith_family_id, OP_NUM))
                return false;
            v = to_app(l->get_arg(0))->get_name();
            theta = to_app(l->get_arg(1))
                ->get_parameter(0).get_rational().get_int32();
        }
        if (v != "x" || theta != i) return false;
        if (i == k && sh->get_name() != "blk") return false;
    }
    for (unsigned int i = 0; i < k; i++) {
        app* sh = to_app(h->get_arg(i));
        if (!is_var(sh->get_arg(1))) return false;
        for (unsigned int j = i + 1; j < k; j++)
            if (sh->get_arg(1) == to_app(h->get_arg(j))->get_arg(1))
                return false;
    }
    if (k + 1 == h->get_num_args()) return true;
    app* blk = to_app(h->get_arg(k));
    app* ip = to_app(h->get_arg(k + 1));
    return blk->get_arg(1) == ip->get_arg(0) ||
           ip->get_arg(0) == to_app(h->get_arg(0))->get_arg(1);
}


void inductive_definition_manager::to_normal_form(expr* br, expr* ir, inductive_definition& def) {
    def.base_rule = br;
    quantifier* q_ir = static_cast<quantifier*>(ir);
    expr* body = q_ir->get_expr();
    app* p;
    app* h;
    if (util.plugin()->is_op_sep(body)) {
        p = o_manager.mk_true();
        h = to_app(body);
    } else {
        p = to_app(to_app(body)->get_arg(0));
        h = to_app(to_app(body)->get_arg(1));
    }
    for (unsigned int i = 0; i < h->get_num_args(); i++)
        if (!util.plugin()->is_op_pto(h->get_arg(i))) {
            def.k = i; break;
        }
    SASSERT(def.k > 0);
    unsigned int n = def.k;
    sort** decl_sorts = new sort* [n];
    symbol* decl_names = new symbol [n];
    Replace rpl;
    for (unsigned int i = 0; i < n; i++) {
        app* sh = to_app(to_app(h)->get_arg(i));
        SASSERT(util.plugin()->is_op_pto(sh));
        app* v = util.mk_loc(("z" + std::to_string(i + 1)).c_str());
        rpl.insert(sh->get_arg(1), v);
        decl_sorts[i] = v->get_sort();
        decl_names[i] = v->get_name();
        if (i == n - 1) def.size_var = v;
        def.var2bound.insert(v, std::make_pair(0, -1));
    }
    expr* replaced_pure = aux_replace(p, rpl);
    expr* replaced_heap = aux_replace(h, rpl);
    def.inductive_rule = o_manager.mk_exists(
        n, decl_sorts, decl_names,
        o_manager.mk_and(replaced_pure, replaced_heap)
    );
    compute_bounds(replaced_pure, def.var2bound);
}

expr* inductive_definition_manager::aux_replace(expr* n, Replace& rpl) {
    if (rpl.contains(n)) return rpl.find(n);
    SASSERT(!is_var(n));
    app* e = to_app(n);
    if (e->get_num_args() == 0) return e;
    ptr_vector<expr> n_args;
    for (auto arg : *e)
        n_args.push_back(aux_replace(arg, rpl));
    if (o_manager.is_and(n))
        return o_manager.mk_and(n_args);
    if (o_manager.is_or(n))
        return o_manager.mk_or(n_args);
    if (o_manager.is_eq(n))
        return o_manager.mk_eq(n_args[0], n_args[1]);
    if (util.plugin()->is_inductive_heap(e))
        return util.mk_inductive_atom(e->get_decl(), n_args[0], n_args[1]);
    switch (e->get_decl_kind()) {
        case ::slidpa::OP_ADD: return util.mk_add(n_args[0], n_args[1]);
        case ::slidpa::OP_SUB: return util.mk_sub(n_args[0], n_args[1]);
        case ::slidpa::OP_GE: return util.mk_ge(n_args[0], n_args[1]);
        case ::slidpa::OP_GT: return util.mk_gt(n_args[0], n_args[1]);
        case ::slidpa::OP_LE: return util.mk_le(n_args[0], n_args[1]);
        case ::slidpa::OP_LT: return util.mk_lt(n_args[0], n_args[1]);
        case ::slidpa::OP_EMP: return util.mk_emp();
        case ::slidpa::OP_PTO: return util.mk_pto(n_args[0], n_args[1]);
        case ::slidpa::OP_SEP: return util.mk_sep(n_args.size(), n_args.data());
        default: break;
    }
    SASSERT(false);
    return nullptr;
}

void inductive_definition_manager::compute_bounds(expr* p, obj_map<expr, Bound>& var2bound) {
    if (o_manager.is_true(p)) return;
    app* e = to_app(p);
    if (o_manager.is_and(e)) {
        for (auto arg : *e)
            compute_bounds(arg, var2bound);
        return;
    }
    unsigned int vid, nid;
    if (is_app_of(e->get_arg(1), arith_family_id, OP_NUM)) {
        vid = 0; nid = 1;
    } else {
        vid = 1; nid = 0;
    }
    expr* v = e->get_arg(vid);
    int num = to_app(e->get_arg(nid))
                ->get_parameter(0).get_rational().get_int32();
    int lb = 0, rb = -1;
    switch (e->get_decl()->get_decl_kind()){
        case ::slidpa::slidpa_op_kind::OP_GE: lb = num; break;
        case ::slidpa::slidpa_op_kind::OP_LE: rb = num; break;
        default: SASSERT(false);
    }
    SASSERT (var2bound.contains(v));
    Bound& b = var2bound.find(v);
    if (b.second != -1 && b.second < lb) return;
    b.first = std::max(b.first, lb);
    if (b.second == -1) b.second = rb;
    else if (rb != -1) b.second = std::min(b.second, rb);
}

lia_formula::lia_formula(ast_manager& m)
    : n_manager(&m),
      lvars(),
      bvars(),
      pure(m.mk_true()),
      spatial_atoms() {}

void lia_formula::add_pure(expr* n) {
    SASSERT(n_manager->contains(n));
    if (n_manager->is_true(pure))
        pure = n;
    else if (!n_manager->is_true(n))
        pure = n_manager->mk_and(pure, n);
    n_manager->inc_ref(pure);
}

expr* lia_formula::get_pure(bool with_vars_c) {
    if (!with_vars_c) return pure;
    return n_manager->mk_and(vars_c, pure);
}

void lia_formula::display(std::ostream& out) {
    out << "    Location variables : ";
    for (auto v : lvars) out << to_app(v)->get_name() << " ";
    out << "\n";
    out << "    Pure : ";
    if (n_manager->contains(pure))
        out << mk_pp(pure, *n_manager);
    else out << "erased?";
    out << '\n';
    out << "    Spatial atoms : ";
    for (auto atom : spatial_atoms)
        out << "("<< atom.fd->get_name() << " "
            << to_app(atom.h)->get_name() << " "
            << to_app(atom.t)->get_name() << ") ";
    out << '\n';
}

formula_translator::formula_translator(ast_manager& om, ast_manager& nm)
    : o_manager(om),
      n_manager(nm),
      o_s_util(om),
      o_a_util(om),
      n_a_util(nm),
      loc_vars_count(0),
      slidpa_var_to_lia_var() {}

bool formula_translator::check_slidpa_formula(expr* n) {
    SLIDPA_MSG("check format " << mk_pp(n, o_manager));
    SASSERT(o_manager.contains(n));
    expr* pure = nullptr;
    expr* heap = nullptr;
    if (o_manager.is_or(n)) pure = n;
    else if (o_s_util.plugin()->is_heap(n)) heap = n;
    else if (o_manager.is_and(n)) {
        for (auto arg : *to_app(n))
            if (o_s_util.plugin()->is_heap(arg)) {
                SASSERT(heap == nullptr);
                heap = arg;
            } else {
                if (pure == nullptr) pure = arg;
                else
                    pure = o_manager.mk_and(pure, arg);
            }
        if (heap == nullptr) pure = n;
    } else pure = n;
    if (pure == nullptr) pure = o_manager.mk_true();
    if (heap == nullptr) heap = o_s_util.mk_emp();
    return aux_check_pure(pure) && aux_check_heap(heap);
}

lia_formula formula_translator::to_lia(expr* n) {
    SLIDPA_MSG("slidpa to lia");
    lia_formula f(n_manager);
    if (!check_slidpa_formula(n)) return f;
    expr* normal_form = to_normal_form(n, f);
    if (normal_form != nullptr) f.add_pure(normal_form);
    expr* zero = n_a_util.mk_int(0);
    expr* vars_c = n_manager.mk_true();
    for (auto v : f.get_lvars()) {
        vars_c = n_manager.mk_and(vars_c, n_a_util.mk_ge(v, zero));
        n_manager.inc_ref(vars_c);
    }
    f.add_vars_constraints(vars_c);
    return f;
}

expr* formula_translator::to_lia(expr* n, Replace& rpl) {
    SASSERT(is_app(n) && !o_s_util.plugin()->is_heap(n));
    app* e = to_app(n);
    if (e->get_num_args() == 0) {
        if (o_a_util.is_numeral(n)) {
            int value = e->get_parameter(0).get_rational().get_int32();
            return n_a_util.mk_int(value);
        }
        SASSERT(rpl.contains(n));
        return rpl.find(n);
    }
    ptr_vector<expr> n_args;
    for (auto arg : *e)
        n_args.push_back(to_lia(arg, rpl));
    if (o_manager.is_and(n))
        return n_manager.mk_and(n_args);
    if (o_manager.is_or(n))
        return n_manager.mk_or(n_args);
    if (o_manager.is_eq(n))
        return n_manager.mk_eq(n_args[0], n_args[1]);
    if (o_s_util.plugin()->is_op_arith(n)) {
        SASSERT(n_args.size() == 2);
        switch (e->get_decl_kind()) {
            case ::slidpa::OP_ADD: return n_a_util.mk_add(n_args[0], n_args[1]);
            case ::slidpa::OP_SUB: return n_a_util.mk_sub(n_args[0], n_args[1]);
            case ::slidpa::OP_GE: return n_a_util.mk_ge(n_args[0], n_args[1]);
            case ::slidpa::OP_GT: return n_a_util.mk_gt(n_args[0], n_args[1]);
            case ::slidpa::OP_LE: return n_a_util.mk_le(n_args[0], n_args[1]);
            case ::slidpa::OP_LT: return n_a_util.mk_lt(n_args[0], n_args[1]);
            default: break;
        }
    }
    SASSERT(false);
    return nullptr;
}

expr* formula_translator::mk_new_loc_var() {
    std::string name = "l" + std::to_string(loc_vars_count++);
    return n_manager.mk_const(name.c_str(), n_a_util.mk_int());
}

expr* formula_translator::to_normal_form(expr* n, lia_formula& f) {
    SASSERT(is_app(n));
    SLIDPA_MSG("to normal form " << mk_pp(n, o_manager));
    app* e = to_app(n);
    if (e->get_num_args() == 0) {
        if (o_s_util.plugin()->is_emp(e)) return nullptr;
        // find variable
        expr* v = nullptr;
        if (o_s_util.plugin()->is_loc(e->get_sort())) {
            v = mk_loc_var(e); f.add_loc_var(v);
        } else if (o_a_util.is_numeral(e)) {
            v = n_a_util.mk_int(e->get_parameter(0).get_rational().get_int32());
        } else {
            n_manager.raise_exception("wrong sort");
            return nullptr;
        }
        return v;
    }
    ptr_vector<expr> n_args;
    for (auto arg : *e) {
        expr* n_arg = to_normal_form(arg, f);
        if (n_arg != nullptr) n_args.push_back(n_arg);
    }
    if (o_s_util.plugin()->is_heap(e)) {
        if (o_s_util.plugin()->is_atomic_heap(e) &&
            !o_s_util.plugin()->is_emp(e)) {
            SASSERT(n_args.size() == 2);
            func_decl* fd = e->get_decl();
            app* h = to_app(n_args[0]);
            app* t = to_app(n_args[1]);
            if (h->get_num_args() != 0) {
                expr* v = mk_loc_var(h);
                f.add_pure(n_manager.mk_eq(v, h));
                h = to_app(v);
            }
            if (t->get_num_args() != 0) {
                expr* v;
                SASSERT(o_s_util.plugin()->is_loc(e->get_arg(1)->get_sort()));
                v = mk_new_loc_var();
                f.add_pure(n_manager.mk_eq(v, t));
                t = to_app(v);
            }
            f.add_spatial_atom(spatial_atom { fd, h, t });
        }
        return nullptr;
    }
    if (o_manager.is_and(n))
        return n_manager.mk_and(n_args);
    if (o_manager.is_or(n))
        return n_manager.mk_or(n_args);
    if (o_manager.is_eq(n))
        return n_manager.mk_eq(n_args[0], n_args[1]);
    if (o_s_util.plugin()->is_op_arith(n)) {
        SASSERT(n_args.size() == 2);
        switch (e->get_decl_kind()) {
            case ::slidpa::OP_ADD: return n_a_util.mk_add(n_args[0], n_args[1]);
            case ::slidpa::OP_SUB: return n_a_util.mk_sub(n_args[0], n_args[1]);
            case ::slidpa::OP_GE: return n_a_util.mk_ge(n_args[0], n_args[1]);
            case ::slidpa::OP_GT: return n_a_util.mk_gt(n_args[0], n_args[1]);
            case ::slidpa::OP_LE: return n_a_util.mk_le(n_args[0], n_args[1]);
            case ::slidpa::OP_LT: return n_a_util.mk_lt(n_args[0], n_args[1]);
            default: break;
        }
    }
    n_manager.raise_exception("unrecognized sub formula");
    return nullptr;
}

bool formula_translator::aux_check_pure(expr* n) {
    SLIDPA_MSG("check format pure " << mk_pp(n, o_manager));
    if (o_manager.is_true(n)) return true;
    if (!is_app(n)) return true;
    SLIDPA_MSG("check " << mk_pp(n, o_manager));
    if (o_s_util.plugin()->is_heap(n)) return false;
    for (auto arg : *to_app(n))
        if(!aux_check_pure(arg))
            return false;
    return true;
}

bool formula_translator::aux_check_heap(expr* n) {
    SLIDPA_MSG("check format heap " << mk_pp(n, o_manager));
    if (!o_s_util.plugin()->is_heap(n)) return false;
    if (o_s_util.plugin()->is_atomic_heap(n))
        return true;
    for (auto arg : *to_app(n))
        if (!aux_check_heap(arg))
            return false;
    return true;
}

expr* formula_translator::mk_loc_var(expr* n) {
    SASSERT(n);
    if (slidpa_var_to_lia_var.contains(n))
        return slidpa_var_to_lia_var.find(n);
    expr* v = mk_new_loc_var();
    n_manager.inc_ref(v);
    slidpa_var_to_lia_var.insert(n, v);
    return v;
}

expr* formula_translator::mk_isemp_var(expr* n) {
    SASSERT(n);
    if (loc_to_isemp.contains(n))
        return loc_to_isemp.find(n);
    std::string name = "isEmp_" +
        std::string(to_app(n)->get_name().bare_str());
    expr* v = n_manager.mk_const(name.c_str(), n_manager.mk_bool_sort());
    n_manager.inc_ref(v);
    loc_to_isemp.insert(n, v);
    return v;
}

expr* formula_translator::mk_bool_var() {
    std::string name = "isEmp_" + std::to_string(bool_vars_count++);
    return n_manager.mk_const(name.c_str(), n_manager.mk_bool_sort());
}

expr* equivalence_class_manager::find(expr* n) {
    if (!eq.contains(n)) eq.insert(n, n);
    if (eq.find(n) == n) return n;
    eq.insert(n, find(eq.find(n)));
    return eq.find(n);
}

expr* equivalence_class_manager::merge(expr* n1, expr* n2) {
    expr* r1 = find(n1);
    expr* r2 = find(n2);
    eq.insert(r2, r1);
    return r1;
}

auxiliary_solver::auxiliary_solver(ast_manager& o_manager)
    : n_cmd_ctx(false),
      n_smt_params(),
      o_manager(o_manager),
      n_manager(n_cmd_ctx.get_ast_manager()),
      n_smt_ctx(n_manager, n_smt_params),
      n_a_util(n_manager),
      o_s_util(o_manager),
      id_manager(o_manager),
      translator(o_manager, n_manager),
      p(nullptr) {
    lia_solver = mk_smt_solver(
        n_manager, n_smt_ctx.get_params(), symbol("QF_LIA"));
    recfun::decl::plugin* recfuc_plugin = 
        static_cast<recfun::decl::plugin*>(
            o_manager.get_plugin(o_manager.get_family_id("recfun")));
    id_manager.register_defs(recfuc_plugin);
    p = new problem(o_manager);
}

lbool auxiliary_solver::check() {
    if (p->type == problem::SAT)
        return check_sat();
    else
        return check_entail();
}

void auxiliary_solver::register_prolbem(expr* n) {
    SLIDPA_MSG("register problem " << mk_pp(n, o_manager));
    app* p = to_app(n);
    if (o_s_util.plugin()->is_op_entail(n)) 
        register_entailment(p->get_arg(0), p->get_arg(1));
    else
        register_satisfiability(p);
    SLIDPA_MSG("register problem done");
}

void auxiliary_solver::display(std::ostream& out) {
    out << " =========================== chenking =========================\n";
    id_manager.display(out);
    out << "Problem : ";
    if (p->type == problem::SAT) {
        out << "satisfiability\n";
        out << "  Phi :\n";
        p->phi.display(out);
    } else {
        out << "entailment\n";
        out << "  Phi :\n";
        p->phi.display(out);
        out << "  Psi :\n";
        p->psi.display(out);
    }
}

void auxiliary_solver::register_satisfiability(expr* phi) {
    p->type = problem::SAT;
    p->phi = translator.to_lia(phi);
}

void auxiliary_solver::register_entailment(expr* phi, expr* psi) {
    p->type = problem::ENTAIL;
    p->phi = translator.to_lia(phi);
    p->psi = translator.to_lia(psi);
}

lbool auxiliary_solver::check_sat() {
    SLIDPA_MSG("check satisfiability");
    expr* abs = mk_abs(p->phi, false);
    SLIDPA_MSG("abs : " << mk_pp(abs, n_manager));
    lia_solver->assert_expr(abs);
    lia_solver->display(std::cout);
    lbool res = lia_solver->check_sat();
    if (res == l_true) {
        model_ref m;
        lia_solver->get_model(m);
        SLIDPA_MSG(*m.get());
    }
    return res;
}

lbool auxiliary_solver::check_entail() {
    expr* abs_phi = mk_abs(p->phi, false);
    n_manager.inc_ref(abs_phi);
    expr* abs_psi = mk_abs(p->psi, true);
    n_manager.inc_ref(abs_psi);
    expr* qabs_psi = mk_abs_exists(abs_psi);
    lia_solver->assert_expr(abs_phi);
    lbool res;
    res = lia_solver->check_sat();
    if (res != l_true) return res;
    lia_solver->push();
    res = aux_check_entail(qabs_psi);
    if (res != l_true) return res;
    lia_solver->pop(1);
    eliminate_emp();
    display(std::cout);
    return l_true;
}

lbool auxiliary_solver::aux_check_sat(expr* n) {
    SLIDPA_MSG(mk_pp(n, n_manager));
    lbool res;
    lia_solver->push();
    lia_solver->assert_expr(n);
    lia_solver->display(std::cout);
    res = lia_solver->check_sat();
    lia_solver->pop(1);
    return res;
}

lbool auxiliary_solver::aux_check_entail(expr* n) {
    lbool res = aux_check_sat(n_manager.mk_not(n));
    return res == l_false ? l_true : 
            (res == l_true ? l_false : l_undef);
}

expr* auxiliary_solver::mk_abs(lia_formula& f, bool is_psi) {
    SLIDPA_MSG("orig " << mk_pp(f.get_pure(), n_manager));
    expr* res = f.get_pure(!is_psi);
    expr* one = n_a_util.mk_int(1);
    svector<reg> regs;
    for (auto atom : f.get_spatial_atoms()) {
        expr* h = atom.h;
        expr* t = nullptr;
        expr* abs = nullptr;
        expr* isEmp = nullptr;
        if (atom.fd->get_name() == "pto") {
            t = translator.mk_new_loc_var();
            abs = n_manager.mk_eq(t, n_a_util.mk_add(h, one));
        } else {
            inductive_definition& def = id_manager.get_inductive_def(atom.fd);
            if (def.is_continuous) t = atom.t;
            else t = translator.mk_new_loc_var();
            isEmp = translator.mk_bool_var();
            f.add_bool_var(isEmp);
            Replace rpl;
            rpl.insert(o_s_util.mk_loc("sz"), n_a_util.mk_sub(t, h));
            expr* slidpa_abs = id_manager.get_abs_of(def.fd);
            expr* ufld_ge1 = translator.to_lia(slidpa_abs, rpl);
            abs = mk_abs_inductive(triple(isEmp, h, t), atom.t, ufld_ge1, def.is_continuous);
            SLIDPA_MSG(atom.fd->get_name() << " " << mk_pp(abs, n_manager));
        }
        regs.push_back(triple(isEmp, h, t));
        res = n_manager.mk_and(res, abs);
    }
    if (!regs.empty())
        res = n_manager.mk_and(res, mk_abs_disjoint(regs));
    SLIDPA_MSG("done");
    return res;
}

expr* auxiliary_solver::mk_abs_inductive(reg r, expr* t, expr* ufld_ge1, bool is_continuous) {
    expr* emp_c = n_manager.mk_and(r.first, n_manager.mk_eq(r.second, r.third));
    expr* not_emp_c = n_manager.mk_and(n_manager.mk_not(r.first), ufld_ge1);
    return n_manager.mk_or(emp_c, not_emp_c);
}

expr* auxiliary_solver::mk_abs_disjoint(svector<reg>& regs) {
    expr* disjoint_c = n_manager.mk_true();
    for (unsigned int i = 0; i < regs.size(); i++)
        for (unsigned int j = i + 1; j < regs.size(); j++) {
            expr* cond = n_manager.mk_true();
            if (regs[i].first != nullptr)
                cond = n_manager.mk_and(cond, n_manager.mk_not(regs[i].first));
            if (regs[j].first != nullptr)
                cond = n_manager.mk_and(cond, n_manager.mk_not(regs[j].first));
            expr* conc = n_manager.mk_or(
                n_a_util.mk_le(regs[i].third, regs[j].second),
                n_a_util.mk_le(regs[j].third, regs[i].second)  
            );
            expr* disjoint;
            if (n_manager.is_true(cond))
                disjoint = conc;
            else
                disjoint = n_manager.mk_implies(cond, conc);
            if (!n_manager.is_true(disjoint_c))
                disjoint_c = n_manager.mk_and(disjoint_c, disjoint);
            else
                disjoint_c = disjoint;
        }
    return disjoint_c;
}

expr* auxiliary_solver::mk_abs_exists(expr* abs) {
    app_ref_vector bound(n_manager);
    for (auto v : p->psi.get_bvars())
        bound.push_back(to_app(v));
    if (bound.size() == 0) return abs;
    unsigned int n = bound.size();
    sort** decl_sorts = new sort* [n];
    symbol* decl_names = new symbol [n];
    for (unsigned int i = 0; i < n; i++) {
        decl_sorts[i] = bound[i]->get_sort();
        decl_names[i] = bound[i]->get_name();
    }
    expr_ref abs_body = expr_abstract(bound, abs);
    return n_manager.mk_exists(n, decl_sorts, decl_names, abs_body.get());
}

void auxiliary_solver::eliminate_emp() {
    equivalence_class_manager eq_manager;
    ptr_vector<expr> lvars;
    for (auto atom : p->phi.get_spatial_atoms()) {
        if (!lvars.contains(atom.h)) lvars.push_back(atom.h);
        if (atom.fd->get_name() != "pto" &&
            !lvars.contains(atom.t))
            lvars.push_back(atom.t);
    }
    for (unsigned int i = 0; i < lvars.size(); i++)
        for (unsigned int j = i + 1; j < lvars.size(); j++) {
            expr* eq = n_manager.mk_eq(lvars[i], lvars[j]);
            SLIDPA_MSG("check eq " << mk_pp(eq, n_manager));
            if (aux_check_entail(eq) == l_true)
                eq_manager.merge(lvars[i], lvars[j]);
        }
    reset_locs(p->phi, eq_manager);
    reset_locs(p->psi, eq_manager);
}


void auxiliary_solver::reset_locs(lia_formula& f, equivalence_class_manager& eq_manager) {
    svector<spatial_atom> deleted_atoms;
    for (auto atom : f.get_spatial_atoms()) {
        if (atom.fd->get_name() == "pto") continue;
        if (eq_manager.find(atom.h) == eq_manager.find(atom.t))
            deleted_atoms.push_back(atom);
    }
    for (auto atom : deleted_atoms) {
        SLIDPA_MSG("delete " << atom.fd->get_name());
        f.remove(atom);
    }
    for (auto& atom : p->phi.get_spatial_atoms()) {
        atom.h = eq_manager.find(atom.h);
        if (atom.fd->get_name() == "pto") continue;
        atom.t = eq_manager.find(atom.t);
    }
}


} // namespace smtslidpa

theory_slidpa::theory_slidpa(context& ctx)
    : theory(ctx, ctx.get_manager().get_family_id("slidpa")) {
    m_decl_plug =
        static_cast<::slidpa::slidpa_decl_plugin*>(m.get_plugin(m_id));
    m_aux_solver = new slidpa::auxiliary_solver(m);
}

bool theory_slidpa::internalize_atom(app * atom, bool gate_ctx) {
    SLIDPA_MSG("theroy slidpa internalize atom " << mk_ismt2_pp(atom, m));
    if (!m_decl_plug->is_heap(atom) &&
        !m_decl_plug->is_op_cmp(atom)) return false;
    if (ctx.e_internalized(atom)) return false;
    mk_var(ctx.mk_enode(atom, true, false, true));
    if (!ctx.b_internalized(atom)) {
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
    }
    return true;
}

bool theory_slidpa::internalize_term(app * term) {
    SLIDPA_MSG("theroy slidpa internalize term " << mk_ismt2_pp(term, m));
    if (!m_decl_plug->is_op_arith(term))
        return false;
    return internalize_term_core(term);
}

bool theory_slidpa::internalize_term_core(app* term) {
    // for (expr* arg : *term)
    //     ctx.internalize(arg, false);
    if (ctx.e_internalized(term)) return false;
    mk_var(ctx.mk_enode(term, true, false, true));
    if (m.is_bool(term) && !ctx.b_internalized(term)) {
        bool_var bv = ctx.mk_bool_var(term);
        ctx.set_var_theory(bv, get_id());
    }
    return true;
}

void theory_slidpa::display(std::ostream & out) const {
    SLIDPA_MSG("theroy slidpa display");
    out << "Theory slidpa\n";
}

theory * theory_slidpa::mk_fresh(context * new_ctx) {
    SLIDPA_MSG("theroy slidpa make fresh");
    return alloc(theory_slidpa, *new_ctx);
}

final_check_status theory_slidpa::final_check_eh() {
    lbool r = final_check();
    switch (r)
    {
    case l_true : return FC_DONE;
    case l_false :
        set_conflict();
        return FC_CONTINUE;
    default: return FC_GIVEUP;
    }
}

void theory_slidpa::set_conflict() {
    ctx.set_conflict(
        ctx.mk_justification(
            ext_theory_conflict_justification(get_id(), ctx, 0, nullptr, 0, nullptr)
        )
    );
}

lbool theory_slidpa::final_check() {
    SLIDPA_MSG("final check ===> to aux solver");

    expr* slidpa_formula = nullptr;
    ptr_vector<expr> assertions;
    ctx.get_assertions(assertions);
    for (auto e : assertions) {
        if (slidpa_formula == nullptr)
            slidpa_formula = e;
        else
            slidpa_formula = m.mk_and(slidpa_formula, e);
    }
    m_aux_solver->register_prolbem(slidpa_formula);
    m_aux_solver->display(std::cout);
    return m_aux_solver->check();
}

}