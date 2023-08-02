#pragma once

#include <map>
#include <string>

#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/recfun_replace.h"
#include "ast/slidpa_decl_plugin.h"
#include "cmd_context/cmd_context.h"
#include "smt/smt_context.h"
#include "smt/smt_theory.h"
#include "smt/smt_solver.h"

namespace smt {

    namespace slidpa {
        
        typedef std::pair<int, int> Bound;
        struct inductive_definition {
            func_decl* fd;
            expr * base_rule;
            expr * inductive_rule;
            bool is_continuous;
            unsigned int k;
            expr * size_var;
            obj_map<expr, Bound> var2bound;
        };

        class inductive_definition_manager {
            ast_manager& o_manager;
            ::slidpa::slidpa_decl_util util;
            std::map<std::string, func_decl*> name2decl;
            obj_map<func_decl, inductive_definition> inductive_definitions;
            obj_map<func_decl, expr*> def2abs;

            recfun_replace aux_rpl;
        
        public:
            inductive_definition_manager(ast_manager& om);
            ~inductive_definition_manager() {}

            void register_defs(recfun::decl::plugin* recfun_plugin);
            void register_def(func_decl* fd, expr* br, expr* ir);

            func_decl* get_func_decl(symbol name);
            inductive_definition& get_inductive_def(symbol name);
            inductive_definition& get_inductive_def(func_decl* fd);

            void display(std::ostream& out);
        
        private:
            expr * const x;
            expr * const y;

            void compute_abs_of(inductive_definition& def);
            bool check_base_rule(expr* n);
            bool check_inductive_rule(expr* n, inductive_definition& def);
            bool check_inductive_pure(expr* n, inductive_definition& def);
            bool check_inductive_heap(expr* n, inductive_definition& def);
        };

        class slidpa_formula {
            ast_manager& n_manager;
            expr_ref pure;
            expr_ref_vector spatial_atoms;
            
        public:
            slidpa_formula(ast_manager& m);
            ~slidpa_formula() {}

            void set_pure(expr* p);
            void add_spatial_atom(expr* atom);

            expr_ref& get_pure();
            unsigned int get_num_atoms();
            expr* get_spatial_atom(unsigned int i);
            expr_ref_vector& get_spatial_atoms();
        };

        // used for translating formulas to builtin qf_lia
        class Translator {
            ast_manager& o_manager;
            ast_manager& n_manager;

            int loc_vars_count;
            int data_vars_count;

        public:
            Translator(ast_manager& om, ast_manager& nm);
            ~Translator() {}

        };

        class auxiliary_solver {
            cmd_context _ctx;
            smt_params _params;
            ast_manager& n_manager;
            context aux_ctx;
            arith_util aux_arith_util;
            solver * lia_solver;

            // inductive definitions manager use ast manager from slidpa theory
            // the new context here only handle the formulas being checked.
            inductive_definition_manager id_manager;
        
        public:
            auxiliary_solver(ast_manager& o_manager);
            ~auxiliary_solver() {}

            arith_util const& util();
            
            void add(expr* n);
            void push();
            void pop(unsigned int n);

            lbool check_sat();
        
            inductive_definition_manager& get_id_manager();
        };

    } // namespace slidpa

    class theory_slidpa : public theory {

        ::slidpa::slidpa_decl_plugin* m_decl_plug;

        slidpa::auxiliary_solver * aux_solver;

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

} // namespace smt