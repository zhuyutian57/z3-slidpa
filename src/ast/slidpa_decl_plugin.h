#pragma once

#include "ast/ast.h"

namespace slidpa {

typedef unsigned int value_c;

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
    bool is_op_pto(expr const * e);
    bool is_op_sep(expr const * e);
    bool is_op_entail(expr const * e);
    bool is_op_add(expr const * e);
    bool is_op_sub(expr const * e);
    bool is_op_le(expr const * e);
    bool is_op_lt(expr const * e);
    bool is_op_ge(expr const * e);
    bool is_op_gt(expr const * e);

    bool is_op_arith(expr const * e);
    bool is_op_cmp(expr const * e);

    bool is_emp(expr const * e);
    bool is_heap(expr const * e);
    bool is_disjoint_heap(expr const* e);
    bool is_atomic_heap(expr const * e);
    bool is_inductive_heap(expr const * e);

    decl_plugin* mk_fresh() override;
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
    void set_manager(ast_manager * m, family_id id) override;
    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    app* mk_emp();
    func_decl* mk_pto(unsigned arity, sort * const * domain);
    func_decl* mk_sep(unsigned arity, sort * const * domain);

    func_decl* mk_func(decl_kind k, unsigned arity, sort* const * domain);
    func_decl* mk_pred(decl_kind k, unsigned arity, sort* const * domain);
    

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                        unsigned arity, sort * const * domain, sort * range) override;

private:
    void check_sorts(sort* const * domain, bool is_func);

};

class slidpa_util {
    ast_manager& m;
    slidpa_decl_plugin* plug;
    arith_util int_util;

public:
    slidpa_util(ast_manager& m);
    ~slidpa_util() {}

    slidpa_decl_plugin * plugin();
    arith_util& get_arith_util();

    sort* mk_loc_sort();
    sort* mk_data_sort();

    app* mk_loc(char const * name);
    app* mk_data(char const * name);

    app* mk_add(expr* arg1, expr* arg2);
    app* mk_add(expr* arg1, value_c arg2);
    app* mk_sub(expr* arg1, expr* arg2);
    app* mk_sub(expr* arg1, value_c arg2);
    app* mk_ge(expr* arg1, expr* arg2);
    app* mk_ge(expr* arg1, value_c arg2);
    app* mk_gt(expr* arg1, expr* arg2);
    app* mk_gt(expr* arg1, value_c arg2);
    app* mk_le(expr* arg1, expr* arg2);
    app* mk_le(expr* arg1, value_c arg2);
    app* mk_lt(expr* arg1, expr* arg2);
    app* mk_lt(expr* arg1, value_c arg2);
    
    app* mk_emp();
    app* mk_pto(expr* arg1, expr* arg2);
    app* mk_sep(unsigned int num_args, expr * const * args);
};

}