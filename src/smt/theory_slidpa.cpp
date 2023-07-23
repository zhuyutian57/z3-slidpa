
#include "smt/smt_context.h"
#include "theory_slidpa.h"

namespace smt {

theory_slidpa::theory_slidpa(context& ctx)
    : theory(ctx, ctx.get_manager().get_family_id("slidpa")) {}

bool theory_slidpa::internalize_atom(app * atom, bool gate_ctx) {
    SLIDPA_MSG("theroy slidpa internalize atom");
    SLIDPA_MSG(atom->get_name() << " " << gate_ctx);
    return false;
}

bool theory_slidpa::internalize_term(app * term) {
    SLIDPA_MSG("theroy slidpa internalize term");
    SLIDPA_MSG(term->get_name() << " " << term->get_sort());
    return false;
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

    return true;
}

}