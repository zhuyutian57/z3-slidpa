#pragma once

#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/recfun_replace.h"
#include "ast/slidpa_decl_plugin.h"
#include "smt/smt_theory.h"

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

        recfun_replace m_rpl;
        obj_map<func_decl, slidpa::inductive_def*> m_i_defs;

        void init_inductive_predicates();

        bool final_check();
    public:
        theory_slidpa(context& ctx);
        ~theory_slidpa() {}

        bool internalize_atom(app * atom, bool gate_ctx) override;
        bool internalize_term(app * term) override;
        void new_eq_eh(theory_var v1, theory_var v2) override;
        void new_diseq_eh(theory_var v1, theory_var v2) override;
        void display(std::ostream & out) const override;
        char const * get_name() const override { return "slidpa"; }

        theory * mk_fresh(context * new_ctx) override;

        final_check_status final_check_eh() override;
    };



} // namespace smt