
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
        this->register_def(fd, br ,ir);
    }
    this->display(std::cout);
}

void inductive_definition_manager::register_def(func_decl* fd, expr* br, expr* ir) {
    inductive_definition def;
    def.fd = fd;
    def.base_rule = br;
    def.inductive_rule = ir;
    SLIDPA_MSG("check inductive definition\n" << mk_pp(br, o_manager) << "\n" << mk_pp(ir, o_manager));
    if (!check_base_rule(br) ||
        !check_inductive_rule(ir, def)) {
        o_manager.raise_exception(" wrong definition ");
        return;
    }
    std::string name(fd->get_name().bare_str());
    if (name2decl.find(name) != name2decl.end()) {
        return;
    }
    name2decl[name] = fd;
    inductive_definitions.insert(fd, def);
    this->compute_abs_of(def);
}

func_decl* inductive_definition_manager::get_func_decl(symbol name) {
    return name2decl[std::string(name.bare_str())];
}

inductive_definition& inductive_definition_manager::get_inductive_def(symbol name) {
    return this->get_inductive_def(name2decl[std::string(name.bare_str())]);
}

inductive_definition& inductive_definition_manager::get_inductive_def(func_decl* fd) {
    SASSERT(fd != nullptr);
    return inductive_definitions.find(fd);
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
    if (def.size_var == nullptr ||
        !def.var2bound.contains(def.size_var) ||
        def2abs.contains(def.fd)) {
        o_manager.raise_exception(" no size field? has fd?");
        return;
    }
    app* diff = nullptr;
    if (def.is_continuous) diff = util.mk_sub(y, x);
    else {
        // x' - x
        diff = util.mk_sub(util.mk_loc("xp"), x);
    }
    Bound base = def.var2bound.find(def.size_var);
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
    expr* abs = nullptr;
    for (auto bound : bounds) {
        app* res = nullptr;
        app* glb = util.mk_ge(diff, bound.first);
        if (bound.second != -1) {
            app* lub = util.mk_le(diff, bound.second);
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

bool inductive_definition_manager::check_inductive_rule(
    expr* n, inductive_definition& def) {
    if (!is_quantifier(n)) return false;
    quantifier* qf = static_cast<quantifier*>(n);
    for (unsigned int i = 0; i < qf->get_num_decls(); i++) {
        var * v = o_manager.mk_var(i, qf->get_decl_sort(i));
        def.var2bound.insert(v, std::make_pair(0, -1));
    }
    expr* body = static_cast<quantifier*>(n)->get_expr();
    expr* p = nullptr;
    expr* h = nullptr;
    if (o_manager.is_and(body) && to_app(body)->get_num_args() == 2) {
        p = to_app(body)->get_arg(0);
        h = to_app(body)->get_arg(1);
    } else if (util.plugin()->is_op_sep(body)) {
        h = body;
    } else return false;
    if (!check_inductive_pure(p, def)) return false;
    return check_inductive_heap(h, def);
}

bool inductive_definition_manager::check_inductive_pure(
    expr* n, inductive_definition& def) {
    SLIDPA_MSG("check inductive pure\n" << mk_pp(n, o_manager));
    if (!n) return true;
    if (o_manager.is_or(n)) return false;
    if (o_manager.is_and(n)) {
        for (auto arg : *to_app(n))
            if (!check_inductive_pure(arg, def))
                return false;
    } else {
        expr* v;
        int num, lb = 0, rb = -1;
        if (is_app_of(to_app(n)->get_arg(1), arith_family_id, OP_NUM)) {
            v = to_app(n)->get_arg(0);
            num = to_app(to_app(n)->get_arg(1))
                ->get_parameter(0).get_rational().get_int32();
        } else if (is_app_of(to_app(n)->get_arg(0), arith_family_id, OP_NUM)) {
            v = to_app(n)->get_arg(1);
            num = to_app(to_app(n)->get_arg(0))
                ->get_parameter(0).get_rational().get_int32();
        } else return false;
        if (!def.var2bound.contains(v)) return false;
        switch (to_app(n)->get_decl()->get_decl_kind()){
            case ::slidpa::slidpa_op_kind::OP_GE: lb = num; break;
            case ::slidpa::slidpa_op_kind::OP_LE: rb = num; break;
            default: return false;
        }
        Bound& b = def.var2bound.find(v);
        if (b.second != -1 && b.second < lb)
            return false;
        b.first = std::max(b.first, lb);
        if (b.second == -1) b.second = rb;
        else if (rb != -1)
            b.second = std::min(b.second, rb);
    }
    return true;
}

bool inductive_definition_manager::check_inductive_heap(
    expr* n, inductive_definition& def) {
    SLIDPA_MSG("check inductive heap\n" << mk_pp(n, o_manager));
    if (!util.plugin()->is_op_sep(n)) return false;
    unsigned int k = 0;
    app* h = to_app(n);
    for (unsigned int i = 0; i < h->get_num_args(); i++)
        if (!util.plugin()->is_op_pto(h->get_arg(i))) {
            k = i; break;
        }
    if (k == 0) return false;
    def.k = k;
    // TODO if lseg is defined, change the format
    for (unsigned int i = 0; i <= k; i++) {
        app* sh = to_app(h->get_arg(i));
        symbol v;
        unsigned int theta = 0;
        if (i == 0) {
            v = to_app(sh->get_arg(0))->get_name();
            theta = 0;
            if (util.plugin()->is_data(sh->get_arg(1)->get_sort()))
                def.is_continuous = true;
            else def.is_continuous = false;
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
        if (i == k - 1) def.size_var = sh->get_arg(1);
    }
    if (k + 1 == h->get_num_args()) return true;
    app* blk = to_app(h->get_arg(k));
    app* ip = to_app(h->get_arg(k + 1));
    if (def.is_continuous) {
        return blk->get_arg(1) == ip->get_arg(0);
    } else {
        return is_var(ip->get_arg(0)) &&
            util.plugin()->is_loc(ip->get_arg(0)->get_sort());
    }
}

lia_formula::lia_formula(ast_manager& m)
    : n_manager(&m),
      lvars(),
      dvars(),
      pure(nullptr),
      spatial_atoms() {
    pure = m.mk_true();
}

void lia_formula::add_loc_var(expr* v) {
    if (lvars.contains(v)) return;
    lvars.push_back(v);
}

void lia_formula::add_data_var(expr* v) {
    if (dvars.contains(v)) return;
    dvars.push_back(v);
}

void lia_formula::add_pure(expr* n) {
    if (!n_manager->contains(n)) {
        n_manager->raise_exception(" use the right manager");
        return;
    }
    pure = n_manager->mk_and(pure, n);
}

void lia_formula::add_spatial_atom(spatial_atom atom) {
    spatial_atoms.push_back(atom);
}

expr* lia_formula::get_pure() {
    return pure;
}

unsigned int lia_formula::get_num_atoms() {
    return spatial_atoms.size();
}

spatial_atom& lia_formula::get_spatial_atom(unsigned int i) {
    SASSERT(i < this->get_num_atoms());
    return spatial_atoms.get(i);
}

svector<spatial_atom>& lia_formula::get_spatial_atoms() {
    return spatial_atoms;
}
void lia_formula::display(std::ostream& out) {
    out << "    Location variables : ";
    for (auto v : lvars) out << to_app(v)->get_name() << " ";
    out << "\n";
    out << "    Data variables : ";
    for (auto v : dvars) out << to_app(v)->get_name() << " ";
    out << "\n";
    out << "    Pure : " << mk_pp(pure, *n_manager) << '\n';
    out << "    Spatial atoms : ";
    for (auto atom : spatial_atoms)
        out << atom.fd->get_name() << " "
            << to_app(atom.s)->get_name() << " "
            << to_app(atom.t)->get_name() << '\n';
    if (spatial_atoms.size() == 0) out << '\n';
}

formula_translator::formula_translator(ast_manager& om, ast_manager& nm)
    : o_manager(om),
      n_manager(nm),
      o_s_util(om),
      o_a_util(om),
      n_a_util(nm),
      loc_vars_count(0),
      data_vars_count(0),
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
    SLIDPA_MSG("slidpa to lia + transform to nomal form");
    expr* normal_form = to_nomal_form(n, f);
    if (normal_form) f.add_pure(normal_form);
    SLIDPA_MSG("slidpa to lia done");
    return f;
}

expr* formula_translator::to_nomal_form(expr* n, lia_formula& f) {
    SASSERT(is_app(n));
    SLIDPA_MSG("to normal form " << mk_pp(n, o_manager));
    app* e = to_app(n);
    if (e->get_num_args() == 0) {
        if (o_s_util.plugin()->is_emp(e)) return nullptr;
        // find variable
        expr* v = nullptr;
        if (o_s_util.plugin()->is_loc(e->get_sort())) {
            v = mk_loc_var(e);
            f.add_loc_var(v);
        } else if (o_s_util.plugin()->is_data(e->get_sort())) {
            v = mk_data_var(e);
            f.add_data_var(v);
        } else if (o_a_util.is_numeral(e)) {
            v = n_a_util.mk_int(e->get_parameter(0).get_rational().get_int32());
        } else {
            n_manager.raise_exception("wrong sort");
            return nullptr;
        }
        if (!n_a_util.is_int(v)) {
            app* var_constraint = n_a_util.mk_ge(v, n_a_util.mk_int(0));
            f.add_pure(var_constraint);
        }
        SLIDPA_MSG("to normal form done for var " << mk_pp(n, o_manager));
        return v;
    }
    ptr_vector<expr> n_args;
    for (auto arg : *e) {
        expr* n_arg = to_nomal_form(arg, f);
        if (n_arg != nullptr) n_args.push_back(n_arg);
    }
    if (o_s_util.plugin()->is_heap(e)) {
        if (o_s_util.plugin()->is_atomic_heap(e) &&
            o_s_util.plugin()->is_emp(e)) {
            SASSERT(n_args.size() == 2);
            func_decl* fd = e->get_decl();
            app* s = to_app(n_args[0]);
            app* t = to_app(n_args[1]);
            if (s->get_num_args() != 0) {
                expr* v = mk_loc_var(nullptr);
                f.add_pure(n_manager.mk_eq(v, s));
                s = to_app(v);
            }
            if (t->get_num_args() != 0) {
                expr* v;
                if (o_s_util.plugin()->is_loc(e->get_arg(1)->get_sort())) {
                    v = mk_loc_var(nullptr);
                } else {
                    v = mk_data_var(nullptr);
                }
                f.add_pure(n_manager.mk_eq(v, t));
                t = to_app(v);
            }
            f.add_spatial_atom(spatial_atom { fd, s, t });
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
    SLIDPA_MSG("check done " << mk_pp(n, o_manager));
    return true;
}

bool formula_translator::aux_check_heap(expr* n) {
    SLIDPA_MSG("check format heap " << mk_pp(n, o_manager));
    if (!o_s_util.plugin()->is_heap(n)) return false;
    if (o_s_util.plugin()->is_atomic_heap(n)) {
        SLIDPA_MSG("check done for atomic");
        return true;
    }
    for (auto arg : *to_app(n))
        if (!aux_check_heap(arg))
            return false;
    SLIDPA_MSG("check done for disjoint " << mk_pp(n, o_manager))
    return true;
}

expr* formula_translator::mk_loc_var(expr* n) {
    if (slidpa_var_to_lia_var.contains(n))
        return slidpa_var_to_lia_var.find(n);
    std::string name = "l" + std::to_string(loc_vars_count++);
    return n_manager.mk_const(name.c_str(), n_a_util.mk_int());
}

expr* formula_translator::mk_data_var(expr* n) {
    if (slidpa_var_to_lia_var.contains(n))
        return slidpa_var_to_lia_var.find(n);
    std::string name = "d" + std::to_string(data_vars_count++);
    return n_manager.mk_const(name.c_str(), n_a_util.mk_int());
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
    // TODO
    return l_true;
}

void auxiliary_solver::register_prolbem(expr* n) {
    SLIDPA_MSG("register begin");
    app* p = to_app(n);
    SLIDPA_MSG("register problem " << mk_pp(n, o_manager));
    if (o_s_util.plugin()->is_op_entail(n)) 
        register_entailment(p->get_arg(0), p->get_arg(1));
    else
        register_satisfiability(p);
    SLIDPA_MSG("register problem done");
}

void auxiliary_solver::display(std::ostream& out) {
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

void auxiliary_solver::register_entailment(expr* phi, expr* psi) {
    SLIDPA_MSG("register entailment");
    p->type = problem::ENTAIL;
    p->phi = translator.to_lia(phi);
    SLIDPA_MSG("register phi done");
    p->psi = translator.to_lia(psi);
    SLIDPA_MSG("register psi done");
    SLIDPA_MSG("register entailment done");
}

void auxiliary_solver::register_satisfiability(expr* phi) {
    SLIDPA_MSG("register satisfiability");
    p->type = problem::SAT;
    p->phi = translator.to_lia(phi);
    SLIDPA_MSG("register satisfiability done");
}

}

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
    return final_check() ? FC_DONE : FC_GIVEUP;
}

bool theory_slidpa::final_check() {
    SLIDPA_MSG("final check");

    ptr_vector<expr> assertion;
    ctx.get_assertions(assertion);
    SLIDPA_MSG("assertions");
    for (auto e : assertion) {
        SLIDPA_MSG(mk_pp(e, m));
    }
    m_aux_solver->register_prolbem(assertion[0]);
    m_aux_solver->display(std::cout);

    return true;
}

}