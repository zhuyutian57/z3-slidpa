#pragma once

#include "ast/ast.h"

enum slidpa_sort_kind {
  LOC_SORT,
  DATA_SORT,
};

enum slidpa_op_kind {
  OP_POINTS_TO_LOC,
  OP_POINTS_TO_DATA,
  OP_SEPARATING_CONJUNCTION,
  OP_EMP
};

class slidpa_decl_plugin : public decl_plugin {
  symbol m_ptl_sym;
  symbol m_ptd_sym;
  symbol m_sep_con_sym;
  symbol m_emp_sym;

  // sort* m_loc_decl;
  // sort* m_data_decl;
  sort* m_var_decl;
  sort* m_heap_decl;

  app* m_emp_decl;

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

  func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) override;
};