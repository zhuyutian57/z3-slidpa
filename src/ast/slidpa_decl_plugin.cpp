
#include "arith_decl_plugin.h"
#include "slidpa_decl_plugin.h"

slidpa_decl_plugin::slidpa_decl_plugin()
  : m_var_decl(nullptr),
    m_ptl_sym("ptl"),
    m_ptd_sym("ptd"),
    m_sep_con_sym("sepc"),
    m_emp_sym("emp"),
    m_emp_decl(nullptr) {}

decl_plugin* slidpa_decl_plugin::mk_fresh() {
  return alloc(slidpa_decl_plugin);
}

sort* slidpa_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
  SLIDPA_MSG("slidpa make sort");
  switch (k)
  {
  case LOC_SORT:
    return m_var_decl;
  case DATA_SORT:
    return m_var_decl;
  default:
    m_manager->raise_exception("no such sort in SLIDPA!");
    return nullptr;
  }
}

void slidpa_decl_plugin::set_manager(ast_manager * m, family_id id) {
  decl_plugin::set_manager(m, id);
  SLIDPA_MSG("initial manager for slidpa");

  sort_info info = sort_info(arith_family_id, arith_sort_kind::INT_SORT);

  m_var_decl = m->mk_sort(symbol("Int"), info);
  m->inc_ref(m_var_decl);

  m_heap_decl = m->mk_bool_sort();
}

void slidpa_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
  SASSERT(logic == "QF_SLIDPA");
  op_names.push_back(builtin_name("sepc", OP_SEPARATING_CONJUNCTION));
  op_names.push_back(builtin_name("ptl", OP_POINTS_TO_LOC));
  op_names.push_back(builtin_name("ptd", OP_POINTS_TO_DATA));
  op_names.push_back(builtin_name("emp", OP_EMP));
}

void slidpa_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
  SASSERT(logic == "QF_SLIDPA");
  sort_names.push_back(builtin_name("Loc", arith_sort_kind::INT_SORT));
  sort_names.push_back(builtin_name("Data", arith_sort_kind::INT_SORT));
}

func_decl* slidpa_decl_plugin::mk_points_to(unsigned arity, sort * const * domain) {
  SLIDPA_MSG("make points-to");
  if(arity != 2) {
    m_manager->raise_exception("points-to must contain two operands");
    return nullptr;
  }
  sort* loc_sort = domain[0];
  sort* target_sort = domain[1];
  symbol m_pt_sym;
  decl_kind target_sort_kind = target_sort->get_decl_kind();
  if(target_sort_kind == slidpa_sort_kind::LOC_SORT)
    m_pt_sym = m_ptl_sym;
  else
    m_pt_sym = m_ptd_sym;
  func_decl* res_decl =
    m_manager->mk_func_decl(m_pt_sym, arity, domain, m_heap_decl,
      func_decl_info(m_family_id, target_sort_kind));
  SLIDPA_MSG("points to res : " << res_decl->get_name());
  return res_decl;
}

func_decl* slidpa_decl_plugin::mk_separating_conjunction(unsigned arity, sort * const * domain) {
  SLIDPA_MSG("make separating conjunction");
  if(arity < 2) {
    m_manager->raise_exception("separating conjunction must contain no less than two operands");
    return nullptr;
  }
  for(int i = 0; i < arity; i++)
    SASSERT(domain[i]->get_decl_kind() == m_heap_decl);
  func_decl* res_decl =
    m_manager->mk_func_decl(m_sep_con_sym, arity, domain, m_heap_decl,
      func_decl_info(m_family_id, OP_SEPARATING_CONJUNCTION));
  SLIDPA_MSG(res_decl->get_name() << " " << res_decl->get_range()->get_name());
  return res_decl;
}

func_decl* slidpa_decl_plugin::mk_const_emp(unsigned arity, sort * const * domain) {
  SLIDPA_MSG("make const emp");
  if(arity != 0) {
    m_manager->raise_exception("emp is a unary operator");
    return nullptr;
  }
  if(m_emp_decl != nullptr)
    return m_emp_decl->get_decl();
  func_decl* res_decl =
    m_manager->mk_const_decl(m_emp_sym, m_manager->mk_bool_sort(),
      func_decl_info(m_family_id, OP_EMP));
  expr* const* res_expr = nullptr;
  m_emp_decl = m_manager->mk_app(res_decl, res_expr);
  return res_decl;
}

func_decl* slidpa_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) {
  switch (k) {
    case OP_POINTS_TO_LOC:
      return mk_points_to(arity, domain);
    case OP_POINTS_TO_DATA:
      return mk_points_to(arity, domain);
    case OP_SEPARATING_CONJUNCTION:
      return mk_separating_conjunction(arity, domain);
    case OP_EMP:
      return mk_const_emp(arity, domain);
    default:
      return nullptr;
  }
}