#pragma once

#include "ast/ast.h"

namespace slidpa {

typedef unsigned int value_c;

enum slidpa_sort_kind { LOC_SORT };

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

    bool is_loc(sort const * s) { return s == m_loc_decl; }
    bool is_op_pto(expr const * e) { return is_app_of(e, m_family_id, OP_PTO); }
    bool is_op_sep(expr const * e) { return is_app_of(e, m_family_id, OP_SEP); }
    bool is_op_entail(expr const * e) { return is_app_of(e, m_family_id, OP_ENTAIL); }
    bool is_op_add(expr const * e) { return is_app_of(e, m_family_id, OP_ADD); }
    bool is_op_sub(expr const * e) { return is_app_of(e, m_family_id, OP_SUB); }
    bool is_op_le(expr const * e) { return is_app_of(e, m_family_id, OP_LE); }
    bool is_op_lt(expr const * e) { return is_app_of(e, m_family_id, OP_LT); }
    bool is_op_ge(expr const * e) { return is_app_of(e, m_family_id, OP_GE); }
    bool is_op_gt(expr const * e) { return is_app_of(e, m_family_id, OP_GT); }
    bool is_op_arith(expr const *e) { return is_op_add(e) || is_op_sub(e) || is_op_cmp(e); }
    bool is_op_cmp(expr const * e) { return is_op_ge(e) || is_op_gt(e) || is_op_le(e) || is_op_lt(e); }
    bool is_emp(expr const * e) { return e == m_emp; }
    bool is_heap(expr const * e) { return is_atomic_heap(e) || is_disjoint_heap(e); }
    bool is_atomic_heap(expr const * e) { return is_emp(e) || is_op_pto(e) || is_inductive_heap(e); }
    bool is_inductive_heap(expr const * e);
    bool is_disjoint_heap(expr const * e) { return is_op_sep(e); }

    decl_plugin* mk_fresh() override { return alloc(slidpa_decl_plugin); }
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
    void set_manager(ast_manager * m, family_id id) override;
    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;
    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    app* mk_emp() { SLIDPA_MSG("make emp"); return m_emp; }
    func_decl* mk_pto(unsigned arity, sort * const * domain);
    func_decl* mk_sep(unsigned arity, sort * const * domain);

    func_decl* mk_func(decl_kind k, unsigned arity, sort* const * domain);
    func_decl* mk_pred(decl_kind k, unsigned arity, sort* const * domain);
    

    func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                        unsigned arity, sort * const * domain, sort * range) override;
};

class slidpa_util {
    ast_manager& m;
    slidpa_decl_plugin* plug;
    arith_util int_util;

public:
    slidpa_util(ast_manager& m)
        : m(m), plug(nullptr), int_util(m) {
        plug =
            static_cast<slidpa_decl_plugin*>
                (m.get_plugin(m.get_family_id("slidpa")));
    }
    ~slidpa_util() {}

    slidpa_decl_plugin* plugin() { return plug; }
    arith_util& get_arith_util() { return int_util; }
    sort* mk_loc_sort() { return plug->mk_sort(LOC_SORT, 0, nullptr); }
    app* mk_loc(char const * name) { return m.mk_const(name, this->mk_loc_sort()); }
    app* mk_add(expr* arg1, expr* arg2) { return m.mk_app(plug->get_family_id(), OP_ADD, arg1, arg2); }
    app* mk_add(expr* arg1, value_c arg2) { return m.mk_app(plug->get_family_id(), OP_ADD, arg1, int_util.mk_int(arg2)); }
    app* mk_sub(expr* arg1, expr* arg2) { return m.mk_app(plug->get_family_id(), OP_SUB, arg1, arg2); }
    app* mk_sub(expr* arg1, value_c arg2) { return m.mk_app(plug->get_family_id(), OP_SUB, arg1, int_util.mk_int(arg2)); }
    app* mk_ge(expr* arg1, expr* arg2) { return m.mk_app(plug->get_family_id(), OP_GE, arg1, arg2); }
    app* mk_ge(expr* arg1, value_c arg2) { return m.mk_app(plug->get_family_id(), OP_GE, arg1, int_util.mk_int(arg2)); }
    app* mk_gt(expr* arg1, expr* arg2) { return m.mk_app(plug->get_family_id(), OP_GT, arg1, arg2); }
    app* mk_gt(expr* arg1, value_c arg2) { return m.mk_app(plug->get_family_id(), OP_GT, arg1, int_util.mk_int(arg2)); }
    app* mk_le(expr* arg1, expr* arg2) { return m.mk_app(plug->get_family_id(), OP_LE, arg1, arg2); }
    app* mk_le(expr* arg1, value_c arg2) { return m.mk_app(plug->get_family_id(), OP_LE, arg1, int_util.mk_int(arg2)); }
    app* mk_lt(expr* arg1, expr* arg2) { return m.mk_app(plug->get_family_id(), OP_LT, arg1, arg2); }
    app* mk_lt(expr* arg1, value_c arg2) { return m.mk_app(plug->get_family_id(), OP_LT, arg1, int_util.mk_int(arg2)); }
    app* mk_emp() { return plug->mk_emp(); }
    app* mk_pto(expr* arg1, expr* arg2) { return m.mk_app(plug->get_family_id(), OP_PTO, arg1, arg2); }
    app* mk_sep(unsigned int num_args, expr * const * args) { return m.mk_app(plug->get_family_id(), OP_SEP, num_args, args); }
};

}