
#include <queue>

#include "ast/arith_decl_plugin.h"
#include "ast/slidpa_decl_plugin.h"
#include "tactic/tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/solve_eqs_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/smtlogics/slidpa_tactic.h"

// class slidpa2arith_tactic : public tactic {
//     class imp {
//         ast_manager & m_manager;
//         arith_util m_arith;

//     public:
//         imp(ast_manager & m, params_ref const& p)
//             : m_manager(m), m_arith(m) {}
    
//         ~imp() {}

//         ast_manager& m() { return m_manager; }

//         void updt_params(params_ref const& p) {}

//         void operator()(goal & g) {
//         }

//     private:
//         class collect_t {
//             imp& m_imp;
//             slidpa_decl_plugin * slidpa_plugin;
//             ptr_vector<app> m_vars;
//             ptr_vector<app> m_heaps;
//         public:
//             collect_t(imp& s) : m_imp(s) {
//                 m_vars.reset();
//                 m_heaps.reset();
//                 slidpa_plugin =
//                     static_cast<slidpa_decl_plugin*>
//                         (s.m().get_plugin(s.m().get_family_id("slidpa")));
//             }

//             ast_manager& m() {
//                 return m_imp.m();
//             }
            
//             ptr_vector<app> get_vars() { return m_vars; }
//             ptr_vector<app> get_heaps() { return m_heaps; }

//             void operator()(app* n) {
//                 if (slidpa_plugin->is_loc(n->get_sort())) {
                    
//                     return;
//                 } else  {
//                     for (auto e : *n)
//                         this->operator()(to_app(e));
                    
//                     return;
//                 }
//             }

//             void collect_vars(app* n) {
                
//             }

//             void collect_heaps(app* n) {

//             }

//         };
    

//     };

//     params_ref m_params;
//     imp * m_imp;

// public:
//     slidpa2arith_tactic(params_ref const & p):
//         m_params(p),
//         m_imp(nullptr) {
//     }

//     tactic * translate(ast_manager& m) override {
//         return alloc(slidpa2arith_tactic, m_params);
//     }

//     char const* name() const override { return "slidpa2arith"; }

//     void operator()(goal_ref const & g, goal_ref_buffer& result) override {
//         result.reset();
//         // SLIDPA_MSG("use slidpa to arith tactic");
//         // for (unsigned i = 0; i < g.get()->size(); i++)
//         //     SLIDPA_MSG(mk_pp(g->form(i), g->m()));
//         result.push_back(g.get());
        
//     }

//     void cleanup() override {}

// };

// tactic * mk_slidpa2arith_tactic(ast_manager & m, params_ref const & p = params_ref()) {
//     return alloc(slidpa2arith_tactic, p);
// }

tactic * mk_slidpa_tactic(ast_manager & m, params_ref const & p) {
    return using_params(
            and_then(mk_simplify_tactic(m),
            and_then(mk_solve_eqs_tactic(m),
                mk_smt_tactic(m)))
            ,p);
}