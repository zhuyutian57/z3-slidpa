#include "recfun_decl_plugin.h"
#include "slidpa_decl_plugin.h"

namespace slidpa {

slidpa_decl_plugin::slidpa_decl_plugin()
    : m_loc_decl(nullptr),
      m_data_decl(nullptr),
      m_emp(nullptr) {}

void slidpa_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    SLIDPA_MSG("initial manager for slidpa");

    m_loc_decl = m->mk_sort(symbol("Loc"),
        sort_info(id, LOC_SORT));
    m->inc_ref(m_loc_decl);

    m_data_decl = m->mk_sort(symbol("Data"),
        sort_info(id, DATA_SORT));
    m->inc_ref(m_data_decl);

    sort * b_sort = m->mk_bool_sort();
    
    m_heap_decl = b_sort;

    m_entail_decl =
        m->mk_func_decl(symbol("entail"),
            b_sort, b_sort, b_sort,
                func_decl_info(m_family_id, OP_ENTAIL));
    m->inc_ref(m_entail_decl);

    m_emp = m->mk_const(
        m->mk_const_decl(symbol("emp"),
            m_heap_decl, func_decl_info(id, OP_EMP)));
    m->inc_ref(m_emp);
}

bool slidpa_decl_plugin::is_loc(sort const * s) {
    return s == m_loc_decl;
}

bool slidpa_decl_plugin::is_data(sort const * s) {
    return s == m_data_decl;
}

bool slidpa_decl_plugin::is_op_pto(expr const * e) {
    return is_app_of(e, m_family_id, OP_PTO);
}

bool slidpa_decl_plugin::is_op_sep(expr const * e) {
    return is_app_of(e, m_family_id, OP_SEP);
}

bool slidpa_decl_plugin::is_op_entail(expr const * e) {
    return is_app_of(e, m_family_id, OP_ENTAIL);
}

bool slidpa_decl_plugin::is_op_add(expr const * e) {
    return is_app_of(e, m_family_id, OP_ADD);
}

bool slidpa_decl_plugin::is_op_sub(expr const * e) {
    return is_app_of(e, m_family_id, OP_SUB);
}

bool slidpa_decl_plugin::is_op_le(expr const * e) {
    return is_app_of(e, m_family_id, OP_LE);
}

bool slidpa_decl_plugin::is_op_lt(expr const * e) {
    return is_app_of(e, m_family_id, OP_LT);
}

bool slidpa_decl_plugin::is_op_ge(expr const * e) {
    return is_app_of(e, m_family_id, OP_GE);
}

bool slidpa_decl_plugin::is_op_gt(expr const * e) {
    return is_app_of(e, m_family_id, OP_GT);
}

bool slidpa_decl_plugin::is_op_arith(expr const *e) {
    return is_op_add(e) ||
           is_op_sub(e) ||
           is_op_cmp(e);
}

bool slidpa_decl_plugin::is_op_cmp(expr const * e) {
    return is_op_ge(e) ||
           is_op_gt(e) ||
           is_op_le(e) ||
           is_op_lt(e);
}

bool slidpa_decl_plugin::is_emp(expr const * e) {
    return e == m_emp;
}

bool slidpa_decl_plugin::is_heap(expr const * e) {
    return is_atomic_heap(e) ||is_disjoint_heap(e);
}

bool slidpa_decl_plugin::is_disjoint_heap(expr const * e) {
    return is_op_sep(e);
}

bool slidpa_decl_plugin::is_atomic_heap(expr const * e) {
    return is_op_pto(e) ||
           is_inductive_heap(e);
}

bool slidpa_decl_plugin::is_inductive_heap(expr const * e) {
    recfun::decl::plugin * rec_plug =
        static_cast<recfun::decl::plugin*>
            (m_manager->get_plugin(m_manager->get_family_id("recfun")));
    return rec_plug->has_def(to_app(e)->get_decl());
}

decl_plugin* slidpa_decl_plugin::mk_fresh() {
    return alloc(slidpa_decl_plugin);
}

sort* slidpa_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    SLIDPA_MSG("slidpa make sort -- " << (k == LOC_SORT ? "Loc" : "Data"));
    
    switch (k)
    {
        case LOC_SORT:
            return m_loc_decl;
        case DATA_SORT:
            return m_data_decl;
        default:
            m_manager->raise_exception("no such sort in SLIDPA!");
            return nullptr;
    }
}

void slidpa_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    op_names.push_back(builtin_name("sep", OP_SEP));
    op_names.push_back(builtin_name("pto", OP_PTO));
    op_names.push_back(builtin_name("emp", OP_EMP));
    op_names.push_back(builtin_name("entail", OP_ENTAIL));
    op_names.push_back(builtin_name("+",  OP_ADD));
    op_names.push_back(builtin_name("-",  OP_SUB));
    op_names.push_back(builtin_name("<=",  OP_LE));
    op_names.push_back(builtin_name("<",  OP_LT));
    op_names.push_back(builtin_name(">=",  OP_GE));
    op_names.push_back(builtin_name(">",  OP_GT));
}

void slidpa_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    sort_names.push_back(builtin_name("Loc", LOC_SORT));
    sort_names.push_back(builtin_name("Data", DATA_SORT));
}

func_decl* slidpa_decl_plugin::mk_pto(unsigned arity, sort * const * domain) {
    SLIDPA_MSG("make points-to");
    if (arity != 2) {
        m_manager->raise_exception("points-to must contain two operands");
        return nullptr;
    }
    if (!is_loc(domain[0])) {
        m_manager->raise_exception("source's sort must be loc");
        return nullptr;
    }
    if (!is_loc(domain[1]) && !is_data(domain[1])) {
        m_manager->raise_exception("target's sort must be loc or data");
        return nullptr;
    }
    return m_manager->mk_func_decl(symbol("pto"), arity, domain, m_heap_decl,
            func_decl_info(m_family_id, OP_PTO));
}

func_decl* slidpa_decl_plugin::mk_sep(unsigned arity, sort * const * domain) {
    SLIDPA_MSG("make separating conjunction");
    if (arity < 2) {
        m_manager->raise_exception("separating conjunction must contain at least two sub-heaps");
        return nullptr;
    }
    for (unsigned i = 0; i < arity; i++)
        if (domain[i] != m_heap_decl) {
            m_manager->raise_exception("every atom must be a (sub-)heap");
            return nullptr;
        }
    return m_manager->mk_func_decl(symbol("sep"), arity, domain, m_heap_decl,
            func_decl_info(m_family_id, OP_SEP));
}

func_decl* slidpa_decl_plugin::mk_func(decl_kind k, unsigned arity, sort* const * domain) {
    SLIDPA_MSG("make function ");
    if (arity != 2) {
        m_manager->raise_exception("that is a binary function");
        return nullptr;
    }
    this->check_sorts(domain, true);
    symbol s(k == OP_ADD ? "+" : "-");
    sort* range;
    if (domain[0]->get_name() == "Loc" ||
        domain[1]->get_name() == "Loc")
        range = m_loc_decl;
    else range = m_data_decl;
    return m_manager->mk_func_decl(s, domain[0], domain[1], range,
        func_decl_info(m_family_id, k));
}

func_decl* slidpa_decl_plugin::mk_pred(decl_kind k, unsigned arity, sort* const * domain) {
    SLIDPA_MSG("make predicate ");
    if (arity != 2) {
        m_manager->raise_exception("that is a binary predicate");
        return nullptr;
    }
    this->check_sorts(domain, false);
    symbol s;
    switch (k) {
        case OP_LE: s = "<="; break;
        case OP_LT: s = "<"; break;
        case OP_GE: s = ">="; break;
        case OP_GT: s = ">"; break;
        default:
            m_manager->raise_exception(" wrong predicate symbol");
            break;
    }
    return m_manager->mk_func_decl(s, domain[0], domain[1], m_manager->mk_bool_sort(),
        func_decl_info(m_family_id, k));
}

func_decl* slidpa_decl_plugin::mk_emp(unsigned arity, sort * const * domain) {
    SLIDPA_MSG("make emp");
    if (arity != 0) {
        m_manager->raise_exception("emp is a unary operator");
        return nullptr;
    }
    return m_emp->get_decl();
}

func_decl* slidpa_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    switch (k) {
        case OP_PTO: return mk_pto(arity, domain);
        case OP_SEP: return mk_sep(arity, domain);
        case OP_ADD: return mk_func(k, arity, domain);
        case OP_SUB: return mk_func(k, arity, domain);
        case OP_GE: return mk_pred(k, arity, domain);
        case OP_GT: return mk_pred(k, arity, domain);
        case OP_LE: return mk_pred(k, arity, domain);
        case OP_LT: return mk_pred(k, arity, domain);
        case OP_EMP: return mk_emp(arity, domain);
        case OP_ENTAIL: return m_entail_decl;
        default:
            m_manager->raise_exception("wrong operator");
            return nullptr;
    }
}

void slidpa_decl_plugin::check_sorts(sort* const * domain, bool is_func) {
    bool res = true;
    for (int i = 0; i < 2; i++) {
        symbol name = domain[i]->get_name();
        if (name != "Loc" && name != "Data" && name != "Int")
            res = false;
    }
    if (is_func) return;
    if ((domain[0] == m_loc_decl && domain[1] == m_data_decl) ||
        (domain[0] == m_data_decl && domain[1] == m_loc_decl))
        res = false;
    if (!res) {
        m_manager->raise_exception("Wrong arguments");
        return;
    }
}

slidpa_decl_util::slidpa_decl_util(ast_manager& m)
    : m(m), plug(nullptr), int_util(m) {
    plug =
        static_cast<slidpa_decl_plugin*>
            (m.get_plugin(m.get_family_id("slidpa")));
}

slidpa_decl_plugin* slidpa_decl_util::plugin() {
    return plug;
}

arith_util& slidpa_decl_util::get_arith_util() {
    return int_util;
}

sort* slidpa_decl_util::mk_loc_sort() {
    return plug->mk_sort(LOC_SORT, 0, nullptr);
}

sort* slidpa_decl_util::mk_data_sort() {
    return plug->mk_sort(DATA_SORT, 0, nullptr);
}

app* slidpa_decl_util::mk_loc(char const * name) {
    return m.mk_const(name, this->mk_loc_sort());
}

app* slidpa_decl_util::mk_data(char const * name) {
    return m.mk_const(name, this->mk_data_sort());
}

app* slidpa_decl_util::mk_add(expr* arg1, expr* arg2) {
    return m.mk_app(plug->get_family_id(), OP_ADD, arg1, arg2);
}

app* slidpa_decl_util::mk_add(expr* arg1, value_c arg2) {
    expr* _arg2 = int_util.mk_int(arg2);
    return m.mk_app(plug->get_family_id(), OP_ADD, arg1, _arg2);
}

app* slidpa_decl_util::mk_sub(expr* arg1, expr* arg2) {
    return m.mk_app(plug->get_family_id(), OP_SUB, arg1, arg2);
}

app* slidpa_decl_util::mk_sub(expr* arg1, value_c arg2) {
    expr* _arg2 = int_util.mk_int(arg2);
    return m.mk_app(plug->get_family_id(), OP_SUB, arg1, _arg2);
}

app* slidpa_decl_util::mk_ge(expr* arg1, expr* arg2) {
    return m.mk_app(plug->get_family_id(), OP_GE, arg1, arg2);
}

app* slidpa_decl_util::mk_ge(expr* arg1, value_c arg2) {
    expr* _arg2 = int_util.mk_int(arg2);
    return m.mk_app(plug->get_family_id(), OP_GE, arg1, _arg2);
}

app* slidpa_decl_util::mk_gt(expr* arg1, expr* arg2) {
    return m.mk_app(plug->get_family_id(), OP_GT, arg1, arg2);
}

app* slidpa_decl_util::mk_gt(expr* arg1, value_c arg2) {
    expr* _arg2 = int_util.mk_int(arg2);
    return m.mk_app(plug->get_family_id(), OP_GT, arg1, _arg2);
}

app* slidpa_decl_util::mk_le(expr* arg1, expr* arg2) {
    return m.mk_app(plug->get_family_id(), OP_LE, arg1, arg2);
}

app* slidpa_decl_util::mk_le(expr* arg1, value_c arg2) {
    expr* _arg2 = int_util.mk_int(arg2);
    return m.mk_app(plug->get_family_id(), OP_LE, arg1, _arg2);
}

app* slidpa_decl_util::mk_lt(expr* arg1, expr* arg2) {
    return m.mk_app(plug->get_family_id(), OP_LT, arg1, arg2);
}

app* slidpa_decl_util::mk_lt(expr* arg1, value_c arg2) {
    expr* _arg2 = int_util.mk_int(arg2);
    return m.mk_app(plug->get_family_id(), OP_LT, arg1, _arg2);
}

app* slidpa_decl_util::mk_pto(expr* arg1, expr* arg2) {
    return m.mk_app(plug->get_family_id(), OP_PTO, arg1, arg2);
}

app* slidpa_decl_util::mk_sep(unsigned int num_args, expr * const * args) {
    return m.mk_app(plug->get_family_id(), OP_SEP, num_args, args);
}


} // namespace slidpa