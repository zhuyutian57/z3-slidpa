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
            ::slidpa::slidpa_util util;
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
            expr* get_abs_of(func_decl* fd);

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

        struct spatial_atom {
            func_decl* fd;
            expr* h; // head
            expr* t; // tail or target
        };

        class lia_formula {
            ast_manager * n_manager;
            ptr_vector<expr> lvars;
            ptr_vector<expr> dvars;
            expr* pure;
            svector<spatial_atom> spatial_atoms;
            
        public:
            lia_formula(ast_manager& m);
            ~lia_formula() {}

            void add_loc_var(expr* v) { if (lvars.contains(v)) return; lvars.push_back(v); }
            void add_data_var(expr* v) { if (dvars.contains(v)) return; dvars.push_back(v); }
            void add_pure(expr* n);
            void add_spatial_atom(spatial_atom atom) { spatial_atoms.push_back(atom); }

            ptr_vector<expr>& get_lvars() { return lvars; }
            ptr_vector<expr>& get_dvars() { return dvars; }
            expr* get_pure() { return pure; }
            unsigned int get_num_atoms() { return spatial_atoms.size(); }
            spatial_atom& get_spatial_atom(unsigned int i) { SASSERT(i < this->get_num_atoms()); return spatial_atoms.get(i); }
            svector<spatial_atom>& get_spatial_atoms() { return spatial_atoms; }

            void display(std::ostream& out);
        };

        // used for translating formulas to builtin qf_lia
        typedef obj_map<expr, expr*> Replace;
        class formula_translator {
            ast_manager& o_manager;
            ast_manager& n_manager;

            ::slidpa::slidpa_util o_s_util;
            arith_util o_a_util;
            arith_util n_a_util;

            int loc_vars_count;
            int data_vars_count;
            int bool_vars_count;
            obj_map<expr, expr*> slidpa_var_to_lia_var;

        public:
            formula_translator(ast_manager& om, ast_manager& nm);
            ~formula_translator() {}

            bool check_slidpa_formula(expr* n);

            lia_formula to_lia(expr* n);
            expr* replace_pure_to_lia(expr* n, Replace& rpl);

            expr* mk_new_loc_var();
            expr* mk_new_data_var();
            expr* mk_new_bool_var();
        
        private:
            expr* to_normal_form(expr* n, lia_formula& f);
            bool aux_check_pure(expr* n);
            bool aux_check_heap(expr* n);
            expr* mk_loc_var(expr* n);
            expr* mk_data_var(expr* n);
        };

        struct problem {
            enum Type { SAT, ENTAIL };
            Type type;
            lia_formula phi;
            lia_formula psi;

            problem(ast_manager& m) : phi(m), psi(m) {}
        };

        class auxiliary_solver {
            cmd_context n_cmd_ctx;
            smt_params n_smt_params;
            ast_manager& o_manager;
            ast_manager& n_manager;
            context n_smt_ctx;
            arith_util n_a_util;
            ::slidpa::slidpa_util o_s_util;
            solver * lia_solver;

            // inductive definitions manager use ast manager from slidpa theory
            // the new context here only handle the formulas being checked.
            inductive_definition_manager id_manager;
            formula_translator translator;

            problem * p;
        
        public:
            auxiliary_solver(ast_manager& o_manager);
            ~auxiliary_solver() {}
            
            lbool check();
            void register_prolbem(expr * n);

            void display(std::ostream& out);
        
        private:
            void register_satisfiability(expr* phi);
            void register_entailment(expr* phi, expr* psi);
            
            lbool check_sat();
            lbool check_entail();
            expr* compute_abs_of(lia_formula& f);
        };

    } // namespace slidpa

    class theory_slidpa : public theory {

        ::slidpa::slidpa_decl_plugin* m_decl_plug;

        slidpa::auxiliary_solver * m_aux_solver;

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
    private:

        void set_conflict();

        lbool final_check();
    };

} // namespace smt