#pragma once

#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/recfun_replace.h"
#include "ast/slidpa_decl_plugin.h"
#include "smt/smt_theory.h"
#include "smt/smt_solver.h"

namespace smt {

    namespace slidpa {
        class inductive_def {
            ast_manager& m;
            func_decl* m_func_decl;
            svector<expr*> m_args;
            expr* m_base_rule;
            expr* m_inductive_rule;
        
        public:
            inductive_def(ast_manager& ast_m);
            inductive_def(
                ast_manager& ast_m,
                func_decl* fd, svector<expr*> args, expr* br, expr* ir);

            func_decl* get_func_decl();
            svector<expr*> const& get_args();
            expr* get_base_rule();
            expr* get_inductive_rule();

            void display(std::ostream& out);
        };
        inline std::ostream& operator<<(std::ostream & out, inductive_def& i_def) {
            i_def.display(out);
            return out;
        }
    }

    class theory_slidpa : public theory {

        ::slidpa::slidpa_decl_plugin* m_decl_plug;

        recfun_replace m_rpl;
        obj_map<func_decl, slidpa::inductive_def*> m_i_defs;

        void init_inductive_predicates();

        bool is_arith(expr const *e);
        bool is_arith_assertion(expr const* e);
        bool is_heap(expr const* e);
        bool is_disjoin(expr const* e);
        bool is_atomic_heap(expr const* e);

        bool final_check();
    public:
        theory_slidpa(context& ctx);
        ~theory_slidpa() {}

        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        bool internalize_term_core(app* term);

        void new_eq_eh(theory_var v1, theory_var v2) override {} ;
        void new_diseq_eh(theory_var v1, theory_var v2) override {};


        void display(std::ostream & out) const override;
        char const * get_name() const override { return "slidpa"; }

        theory * mk_fresh(context * new_ctx) override;

        final_check_status final_check_eh() override;
    };

    class auxiliary_solver {
        context aux_ctx;
        solver * aux_solver;
    
    public:
        auxiliary_solver();
        ~auxiliary_solver() {}
        
    };



} // namespace smt