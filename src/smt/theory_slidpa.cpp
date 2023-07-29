
#include "smt/smt_context.h"
#include "theory_slidpa.h"

#include <string>

namespace smt {

namespace slidpa {


inductive_def::inductive_def(ast_manager& ast_m)
    : m(ast_m),
      m_func_decl(nullptr),
      m_base_rule(nullptr),
      m_inductive_rule(nullptr) {
    m_args.reset();
}

inductive_def::inductive_def(ast_manager& ast_m,
    func_decl* fd, svector<expr*> args, expr* br, expr* ir)
    : m(ast_m), m_func_decl(fd), m_base_rule(br), m_inductive_rule(ir) {
    SASSERT(args.size() == 2);
    m_args = args;
}

func_decl* inductive_def::get_func_decl() {
    return m_func_decl;
}

svector<expr*> const& inductive_def::get_args() {
    return m_args;
}

expr* inductive_def::get_base_rule() {
    return m_base_rule;
}

expr* inductive_def::get_inductive_rule() {
    return m_inductive_rule;
}

void inductive_def::display(std::ostream& out) {
    out << m_func_decl->get_name();
    out << " (" << to_app(m_args[0])->get_name()
        << " " << m_args[0]->get_sort()->get_name() << ")";
    out << " (" << to_app(m_args[1])->get_name()
        << " " << m_args[1]->get_sort()->get_name() << ")\n";
    out << "  base: " << mk_pp(m_base_rule, m) << "\n";
    out << "  inductive: " << mk_pp(m_inductive_rule, m) << "\n";
}

}

theory_slidpa::theory_slidpa(context& ctx)
    : theory(ctx, ctx.get_manager().get_family_id("slidpa")),
      m_rpl(ctx.get_manager()) {
    m_decl_plug =
        static_cast<::slidpa::slidpa_decl_plugin*>(m.get_plugin(m_id));
    m_i_defs.reset();
    init_inductive_predicates();
}

void theory_slidpa::init_inductive_predicates() {
    recfun::decl::plugin* recfun_plugin =
        static_cast<recfun::decl::plugin*>
            (m.get_plugin(m.get_family_id(symbol("recfun"))));
    if (recfun_plugin == nullptr) {
        m.raise_exception(" no recfun plugin?");
        return;
    }
    SLIDPA_MSG("Handle inductive definitions");
    sort* loc_sort =
        m_decl_plug->mk_sort(::slidpa::LOC_SORT, 0, nullptr);
    expr* x = m.mk_const("x", loc_sort);
    expr* y = m.mk_const("y", loc_sort);

    for (auto recf : recfun_plugin->get_rec_funs()) {
        recfun::def& def = recfun_plugin->get_def(recf);
        func_decl* fd = def.get_decl();

        // replace args to x and y
        m_rpl.insert(def.get_vars()[0], x);
        m_rpl.insert(def.get_vars()[1], y);
        
        expr_ref renamed_rule = m_rpl(def.get_rhs());
        svector<expr*> args;
        expr* br = to_app(renamed_rule.get())->get_arg(0);
        expr* ir = to_app(renamed_rule.get())->get_arg(1);
        args.push_back(x);
        args.push_back(y);
        m_i_defs.insert(fd,
            new slidpa::inductive_def(m, fd, args, br, ir));
    }

    for (auto recf : recfun_plugin->get_rec_funs())
        SLIDPA_MSG(*m_i_defs[recf]);
}

bool theory_slidpa::is_arith(expr const* e) {
    return m_decl_plug->is_op_add(e) ||
           m_decl_plug->is_op_sub(e) ||
           m_decl_plug->is_op_le(e) ||
           m_decl_plug->is_op_lt(e) ||
           m_decl_plug->is_op_ge(e) ||
           m_decl_plug->is_op_gt(e);
}

bool theory_slidpa::is_arith_assertion(expr const* e) {
    return m_decl_plug->is_op_le(e) ||
           m_decl_plug->is_op_lt(e) ||
           m_decl_plug->is_op_ge(e) ||
           m_decl_plug->is_op_gt(e);
}

bool theory_slidpa::is_heap(expr const* e) {
    return m_decl_plug->is_heap(e);
}

bool theory_slidpa::is_disjoin(expr const* e) {
    return m_decl_plug->is_op_sep(e);
}

bool theory_slidpa::is_atomic_heap(expr const* e) {
    return is_heap(e) && !is_disjoin(e);
}

bool theory_slidpa::internalize_atom(app * atom, bool gate_ctx) {
    SLIDPA_MSG("theroy slidpa internalize atom " << mk_ismt2_pp(atom, m));
    if (!is_heap(atom) && !is_arith_assertion(atom)) return false;
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
    if (!is_arith(term) || is_arith_assertion(term))
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

    return true;
}

}