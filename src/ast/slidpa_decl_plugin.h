#pragma once

#include "ast/ast.h"

enum slidpa_sort_kind {
    LOC_SORT,
    DATA_SORT
};

enum slidpa_op_kind {
    OP_POINTS_TO,
    OP_SEPARATING_CONJUNCTION,
    OP_EMP,

    OP_SL_ADD,
    OP_SL_SUB,

    OP_SL_LE,
    OP_SL_LT,
    OP_SL_GE,
    OP_SL_GT
};

class slidpa_decl_plugin : public decl_plugin {
    symbol m_pt_sym;
    symbol m_sep_con_sym;
    symbol m_emp_sym;

    sort* m_loc_decl;
    sort* m_data_decl;
    sort* m_heap_decl;

    // func_decl* m_l_add_decl;
    // func_decl* m_l_sub_decl;
    // func_decl* m_d_add_decl;
    // func_decl* m_d_sub_decl;

    // func_decl* m_l_le_decl;
    // func_decl* m_l_lt_decl;
    // func_decl* m_l_ge_decl;
    // func_decl* m_l_gt_decl;
    // func_decl* m_d_le_decl;
    // func_decl* m_d_lt_decl;
    // func_decl* m_d_ge_decl;
    // func_decl* m_d_gt_decl;

    app* m_emp;

public:

    slidpa_decl_plugin();

    decl_plugin* mk_fresh() override;
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
    void set_manager(ast_manager * m, family_id id) override;
    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    func_decl* mk_points_to(unsigned arity, sort * const * domain);
    func_decl* mk_separating_conjunction(unsigned arity, sort * const * domain);
    func_decl* mk_const_emp(unsigned arity, sort * const * domain);

    func_decl* mk_func(char const* s, unsigned arity, sort* const * domain);
    func_decl* mk_pred(char const* s, unsigned arity, sort* const * domain);
    

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                        unsigned arity, sort * const * domain, sort * range) override;

private:
    void check_sorts(sort* const * domain, bool is_func);

};