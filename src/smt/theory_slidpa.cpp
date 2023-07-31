
#include "smt/smt_context.h"
#include "theory_slidpa.h"

#include <string>
#include <queue>

namespace smt {

namespace slidpa {

inductive_definition_manager::inductive_definition_manager(ast_manager& o_manager)
    : o_manager(o_manager),
      name2decl(),
      inductive_definitions(),
      def2abs(),
      aux_rpl(o_manager) {}

void inductive_definition_manager::register_defs(recfun::decl::plugin* recfun_plugin) {
    if (recfun_plugin == nullptr) {
        o_manager.raise_exception(" no recfun plugin?");
        return;
    }
    SLIDPA_MSG("Handle inductive definitions");
    ::slidpa::slidpa_decl_plugin* slidpa_plug =
        static_cast<::slidpa::slidpa_decl_plugin*>
            (o_manager.get_plugin(o_manager.get_family_id("slidpa")));
    sort* loc_sort = 
        slidpa_plug->mk_sort(::slidpa::LOC_SORT, 0, nullptr);
    expr* x = o_manager.mk_const("x", loc_sort);
    expr* y = o_manager.mk_const("y", loc_sort);
    
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
    def.base_rule = br;
    def.inductive_rule = ir;
    SLIDPA_MSG("check inductive definition\n" << mk_pp(br, o_manager) << "\n" << mk_pp(ir, o_manager));
    if (!check_base_rule(br) ||
        !check_inductive_rule(ir, def)) {
        o_manager.raise_exception(" wrong definition ");
        return;
    }
    std::string name(fd->get_name().bare_str());
    SLIDPA_MSG(name << " " << (name2decl.find(name) != name2decl.end()));
    if (name2decl.find(name) != name2decl.end()) {
        return;
    }
    name2decl[name] = fd;
    inductive_definitions.insert(fd, def);
    SLIDPA_MSG("ok");
    this->register_abs_of(def);
}

void inductive_definition_manager::register_abs_of(inductive_definition& def) {
    svector<std::pair<int, int>> bounds;
    bounds.push_back(std::make_pair(0, 0));
    expr* rule = ((quantifier*)def.inductive_rule)->get_expr();
    expr* heap = to_app(rule)->get_arg(1);
    ::slidpa::slidpa_decl_plugin* slidpa_plug =
        static_cast<::slidpa::slidpa_decl_plugin*>
            (o_manager.get_plugin(o_manager.get_family_id("slidpa")));
    // TODO
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
    if (!is_app_of(s,
        o_manager.get_family_id("slidpa"),
            ::slidpa::slidpa_op_kind::OP_EMP))
        return false;
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
    } else if (to_app(body)->get_name() == "sep") {
        h = body;
    } else return false;
    if (!check_inductive_pure(p, def)) return false;
    
    SLIDPA_MSG("here berfor check heap");
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
        if (!merge_bound(std::make_pair(lb, rb), b))
            return false;
    }
    return true;
}

bool inductive_definition_manager::check_inductive_heap(
    expr* n, inductive_definition& def) {
    SLIDPA_MSG("check inductive heap\n" << mk_pp(n, o_manager));
    ::slidpa::slidpa_decl_plugin* slidpa_plug =
        static_cast<::slidpa::slidpa_decl_plugin*>
            (o_manager.get_plugin(o_manager.get_family_id("slidpa")));
    if (!slidpa_plug->is_op_sep(n)) return false;
    unsigned int k = 0;
    app* h = to_app(n);
    for (unsigned int i = 0; i < h->get_num_args(); i++)
        if (!slidpa_plug->is_op_pto(h->get_arg(i))) {
            k = i; break;
        }
    
    // TODO if lseg is defined, change the format
    for (unsigned int i = 0; i <= k; i++) {
        app* sh = to_app(h->get_arg(i));
        symbol v;
        unsigned int theta = 0;
        if (i == 0) {
            v = to_app(sh->get_arg(0))->get_name();
            theta = 0;
            if (slidpa_plug->is_data(sh->get_arg(1)->get_sort()))
                def.is_continuous = true;
            else def.is_continuous = false;
        } else {
            app* l = to_app(sh->get_arg(0));
            if (!slidpa_plug->is_op_add(l)) return false;
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
            slidpa_plug->is_loc(ip->get_arg(0)->get_sort());
    }
}

inline bool inductive_definition_manager::merge_bound(Bound nb, Bound& b) {
    b.first = std::max(b.first, nb.first);
    if (b.second == -1) b.second = nb.second;
    else if (nb.second != -1)
        b.second = std::min(b.second, nb.second);
    if (b.second != -1 && b.first > b.second)
        return false;
    return true;
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
            << mk_pp(def.get_value().base_rule, o_manager) << '\n'
            << mk_pp(def.get_value().inductive_rule, o_manager) << '\n';
    }
}

Translator::Translator(ast_manager& om, ast_manager& nm)
    : o_manager(om), n_manager(nm) {}

auxiliary_solver::auxiliary_solver(ast_manager& o_manager)
    : _ctx(false),
      _params(),
      n_manager(_ctx.get_ast_manager()),
      aux_ctx(n_manager, _params),
      aux_arith_util(n_manager),
      id_manager(o_manager) {
    lia_solver = mk_smt_solver(
        n_manager, aux_ctx.get_params(), symbol("QF_LIA"));
}

arith_util const& auxiliary_solver::util() {
    return aux_arith_util;
}

void auxiliary_solver::add(expr* n) {
    lia_solver->assert_expr(n);
}

void auxiliary_solver::push() {
    lia_solver->push();
}

void auxiliary_solver::pop(unsigned int n) {
    SASSERT(n <= lia_solver->get_scope_level());
    lia_solver->pop(n);
}

lbool auxiliary_solver::check_sat() {
    for (auto e : lia_solver->get_assertions()) {
        SLIDPA_MSG(mk_pp(e, n_manager));
    }

    return lia_solver->check_sat();
}

inductive_definition_manager& auxiliary_solver::get_id_manager() {
    return id_manager;
}

}

theory_slidpa::theory_slidpa(context& ctx)
    : theory(ctx, ctx.get_manager().get_family_id("slidpa")) {
    m_decl_plug =
        static_cast<::slidpa::slidpa_decl_plugin*>(m.get_plugin(m_id));
    aux_solver = new slidpa::auxiliary_solver(m);
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

    ptr_vector<expr> afs;
    ctx.get_assertions(afs);
    SLIDPA_MSG("assertions");
    for (auto e : afs) {
        SLIDPA_MSG(mk_pp(e, m));
    }

    aux_solver->get_id_manager()
        .register_defs(
        static_cast<recfun::decl::plugin*>(
            m.get_plugin(m.get_family_id("recfun"))));
    // aux_solver->get_id_manager().display(std::cout);

    return true;
}

}