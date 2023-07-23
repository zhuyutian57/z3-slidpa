
#include "arith_decl_plugin.h"
#include "slidpa_decl_plugin.h"

slidpa_decl_plugin::slidpa_decl_plugin()
    : m_pt_sym("pt"),
      m_sep_con_sym("sepc"),
      m_emp_sym("emp"),
      m_loc_decl(nullptr),
      m_data_decl(nullptr),
      
    //   m_l_add_decl(nullptr),
    //   m_l_sub_decl(nullptr),
    //   m_d_add_decl(nullptr),
    //   m_d_sub_decl(nullptr),
    //   m_l_le_decl(nullptr),
    //   m_l_ge_decl(nullptr),
    //   m_l_lt_decl(nullptr),
    //   m_l_gt_decl(nullptr),
    //   m_d_le_decl(nullptr),
    //   m_d_ge_decl(nullptr),
    //   m_d_lt_decl(nullptr),
    //   m_d_gt_decl(nullptr),
      m_emp(nullptr) { }

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

void slidpa_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    SLIDPA_MSG("initial manager for slidpa");

    m_loc_decl = m->mk_sort(symbol("Loc"),
        sort_info(id, LOC_SORT));
    m->inc_ref(m_loc_decl);

    m_data_decl = m->mk_sort(symbol("Data"),
        sort_info(id, DATA_SORT));
    m->inc_ref(m_data_decl);

    m_heap_decl = m->mk_bool_sort();

    func_decl * emp_decl =
        m->mk_const_decl(symbol("emp"), m_heap_decl, func_decl_info(id, OP_EMP));
    m_emp = m->mk_const(emp_decl);
    m->inc_ref(m_emp);
}

void slidpa_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic != "SLIDPA") m_manager->raise_exception(" wrong logic ");
    op_names.push_back(builtin_name("sepc", OP_SEPARATING_CONJUNCTION));
    op_names.push_back(builtin_name("pt", OP_POINTS_TO));
    op_names.push_back(builtin_name("emp", OP_EMP));
    op_names.push_back(builtin_name("+",  OP_SL_ADD));
    op_names.push_back(builtin_name("-",  OP_SL_SUB));
    op_names.push_back(builtin_name("<=",  OP_SL_LE));
    op_names.push_back(builtin_name("<",  OP_SL_LT));
    op_names.push_back(builtin_name(">=",  OP_SL_GE));
    op_names.push_back(builtin_name(">",  OP_SL_GT));
}

void slidpa_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    if (logic != "SLIDPA") m_manager->raise_exception(" wrong logic ");
    sort_names.push_back(builtin_name("Loc", LOC_SORT));
    sort_names.push_back(builtin_name("Data", DATA_SORT));
}

func_decl* slidpa_decl_plugin::mk_points_to(unsigned arity, sort * const * domain) {
    SLIDPA_MSG("make points-to");
    if (arity != 2) {
        m_manager->raise_exception("points-to must contain two operands");
        return nullptr;
    }
    sort* loc_sort = domain[0];
    sort* target_sort = domain[1];
    func_decl* res_decl =
        m_manager->mk_func_decl(m_pt_sym, arity, domain, m_heap_decl,
            func_decl_info(m_family_id, OP_POINTS_TO));
    return res_decl;
}

func_decl* slidpa_decl_plugin::mk_separating_conjunction(unsigned arity, sort * const * domain) {
    SLIDPA_MSG("make separating conjunction");
    if (arity < 2) {
        m_manager->raise_exception("separating conjunction must contain no less than two operands");
        return nullptr;
    }
    for (int i = 0; i < arity; i++)
        if (domain[i] != m_heap_decl) {
            m_manager->raise_exception("every atom must be a (sub-)heap");
            return nullptr;
        }
    func_decl* res_decl =
        m_manager->mk_func_decl(m_sep_con_sym, arity, domain, m_heap_decl,
            func_decl_info(m_family_id, OP_SEPARATING_CONJUNCTION));
    return res_decl;
}

func_decl* slidpa_decl_plugin::mk_func(decl_kind k, unsigned arity, sort* const * domain) {
    SLIDPA_MSG("make function ");
    if (arity != 2) {
        m_manager->raise_exception("that is a binary function");
        return nullptr;
    }
    this->check_sorts(domain, true);
    symbol s(k == OP_SL_ADD ? "+" : "-");
    sort* range;
    if (domain[0]->get_name() == "Loc" || domain[1]->get_name() == "Loc")
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
    switch (k)
    {
    case OP_SL_LE: s = "<="; break;
    case OP_SL_LT: s = "<"; break;
    case OP_SL_GE: s = ">="; break;
    case OP_SL_GT: s = ">"; break;
    default:
        m_manager->raise_exception(" wrong predicate symbol");
        break;
    }
    return m_manager->mk_func_decl(s, domain[0], domain[1], m_manager->mk_bool_sort(),
        func_decl_info(m_family_id, k));
}

func_decl* slidpa_decl_plugin::mk_const_emp(unsigned arity, sort * const * domain) {
    SLIDPA_MSG("make const emp");
    if (arity != 0) {
        m_manager->raise_exception("emp is a unary operator");
        return nullptr;
    }
    return m_emp->get_decl();
}

func_decl* slidpa_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
    switch (k) {
        case OP_POINTS_TO: return mk_points_to(arity, domain);
        case OP_SEPARATING_CONJUNCTION: return mk_separating_conjunction(arity, domain);
        case OP_SL_ADD: return mk_func(k, arity, domain);
        case OP_SL_SUB: return mk_func(k, arity, domain);
        case OP_SL_GE: return mk_pred(k, arity, domain);
        case OP_SL_GT: return mk_pred(k, arity, domain);
        case OP_SL_LE: return mk_pred(k, arity, domain);
        case OP_SL_LT: return mk_pred(k, arity, domain);
        case OP_EMP: return mk_const_emp(arity, domain);
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
    if (!res) {
        m_manager->raise_exception("Wrong arguments");
        return;
    }
    if (is_func) return;
    if (domain[0]->get_name() == "Loc" || domain[1]->get_name() == "Loc")
        res = domain[0]->get_name() != "Data" && domain[1]->get_name() != "Data";
    else if (domain[0]->get_name() == "Data" || domain[1]->get_name() == "Data")
        res = domain[0]->get_name() != "Loc" && domain[1]->get_name() != "Loc";
    if (!res) m_manager->raise_exception("Wrong arguments");
}