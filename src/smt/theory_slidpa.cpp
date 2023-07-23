
#include "smt/smt_context.h"
#include "theory_slidpa.h"

namespace smt {

theory_slidpa::theory_slidpa(context& ctx)
    : theory(ctx, ctx.get_manager().get_family_id("slidpa")) {}

bool theory_slidpa::internalize_atom(app * atom, bool gate_ctx) {
    SLIDPA_MSG("theroy slidpa internalize atom " << mk_ismt2_pp(atom, m));
    if (!is_app_of(atom, m_id, OP_POINTS_TO) &&
        !is_app_of(atom, m_id, OP_SEPARATING_CONJUNCTION))
        return false;
    if (ctx.e_internalized(atom)) return false;
    for (expr* arg : *atom) {
        ctx.internalize(arg, false);
    }
    enode* e = ctx.mk_enode(atom, false, false, true);
    if (m.is_bool(atom)) {
        bool_var bv = ctx.mk_bool_var(atom);
        ctx.set_var_theory(bv, get_id());
        ctx.set_enode_flag(bv, true);
    }
    return true;
}

bool theory_slidpa::internalize_term(app * term) {
    SLIDPA_MSG("theroy slidpa internalize term " << mk_ismt2_pp(term, m));
    for (expr* arg : *term) {
        ctx.internalize(arg, false);
    }
    
    if (ctx.e_internalized(term)) return false;
    enode* e = ctx.mk_enode(term, false, false, true);
    // if (m.is_bool(term)) {
    //     bool_var bv = ctx.mk_bool_var(term);
    //     ctx.set_var_theory(bv, get_id());
    //     ctx.set_enode_flag(bv, true);
    // }
    return true;
}

void theory_slidpa::new_eq_eh(theory_var v1, theory_var v2) {
    SLIDPA_MSG("theroy slidpa new_eq_eh");
}

void theory_slidpa::new_diseq_eh(theory_var v1, theory_var v2) {
    SLIDPA_MSG("theroy slidpa new_diseq_eh");
}

void theory_slidpa::display(std::ostream & out) const {
    SLIDPA_MSG("theroy slidpa display");
}

theory * theory_slidpa::mk_fresh(context * new_ctx) {
    SLIDPA_MSG("theroy slidpa make fresh");
    return alloc(theory_slidpa, *new_ctx);
}

final_check_status theory_slidpa::final_check_eh() {
    return final_check() ? FC_DONE : FC_CONTINUE;
}

bool theory_slidpa::final_check() {
    SLIDPA_MSG("final check");

    expr_ref_vector assignments(m);
    ctx.get_assignments(assignments);

    for(auto e : assignments) {
        SLIDPA_MSG(mk_ismt2_pp(e, m));
    }

    for(auto en : ctx.enodes()) {
        SLIDPA_MSG(en->get_decl()->get_range()->get_name());
    }

    return true;
}

}