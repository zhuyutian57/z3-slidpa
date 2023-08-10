#include "recfun_decl_plugin.h"
#include "slidpa_decl_plugin.h"

namespace slidpa {

slidpa_decl_plugin::slidpa_decl_plugin()
    : m_loc_decl(nullptr),
      m_emp(nullptr) {}

void slidpa_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
    SLIDPA_MSG("initial manager for slidpa");

    m_loc_decl = m->mk_sort(symbol("Loc"),
        sort_info(id, LOC_SORT));
    m->inc_ref(m_loc_decl);

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

bool slidpa_decl_plugin::is_inductive_heap(expr const * e) {
    recfun::decl::plugin * rec_plug =
        static_cast<recfun::decl::plugin*>
            (m_manager->get_plugin(m_manager->get_family_id("recfun")));
    return rec_plug->has_def(to_app(e)->get_decl());
}

sort* slidpa_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    SLIDPA_MSG("slidpa make sort -- " );
    switch (k)
    {
        case LOC_SORT:
            return m_loc_decl;
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
    symbol s(k == OP_ADD ? "+" : "-");
    return m_manager->mk_func_decl(s, domain[0], domain[1], m_loc_decl,
        func_decl_info(m_family_id, k));
}

func_decl* slidpa_decl_plugin::mk_pred(decl_kind k, unsigned arity, sort* const * domain) {
    SLIDPA_MSG("make predicate ");
    if (arity != 2) {
        m_manager->raise_exception("that is a binary predicate");
        return nullptr;
    }
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
        case OP_EMP: return m_emp->get_decl();
        case OP_ENTAIL: return m_entail_decl;
        default:
            m_manager->raise_exception("wrong operator");
            return nullptr;
    }
}

} // namespace slidpa