#pragma once

#include "ast/ast.h"

namespace slidpa {

enum slidpa_sort_kind {
    LOC_SORT,
    DATA_SORT
};

enum slidpa_op_kind {
    OP_PTO,
    OP_SEP,
    OP_EMP,
    OP_ENTAIL,

    OP_ADD,
    OP_SUB,

    OP_LE,
    OP_LT,
    OP_GE,
    OP_GT
};

class slidpa_decl_plugin : public decl_plugin {

    sort* m_loc_decl;
    sort* m_data_decl;
    sort* m_heap_decl;

    func_decl* m_entail_decl;

    app* m_emp;

public:

    slidpa_decl_plugin();

    bool is_loc(sort const * s);
    bool is_data(sort const * s);
    bool is_heap(expr const * e);
    bool is_op_pto(expr const * e);
    bool is_op_sep(expr const * e);
    bool is_op_entail(expr const * e);
    bool is_op_add(expr const * e);
    bool is_op_sub(expr const * e);
    bool is_op_le(expr const * e);
    bool is_op_lt(expr const * e);
    bool is_op_ge(expr const * e);
    bool is_op_gt(expr const * e);

    decl_plugin* mk_fresh() override;
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
    void set_manager(ast_manager * m, family_id id) override;
    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    func_decl* mk_points_to(unsigned arity, sort * const * domain);
    func_decl* mk_separating_conjunction(unsigned arity, sort * const * domain);
    func_decl* mk_const_emp(unsigned arity, sort * const * domain);

    func_decl* mk_func(decl_kind k, unsigned arity, sort* const * domain);
    func_decl* mk_pred(decl_kind k, unsigned arity, sort* const * domain);
    

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                        unsigned arity, sort * const * domain, sort * range) override;

private:
    void check_sorts(sort* const * domain, bool is_func);
    void set_propertie(func_decl* fd);

};

}