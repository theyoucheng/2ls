/*******************************************************************\

Module: Automatic Invariants Generation

Author: Youcheng Sun

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include "2ls_parse_options.h"

/*******************************************************************\

Function: twols_parse_optionst::generate_invariants

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void twols_parse_optionst::generate_invariants(
  goto_modelt &goto_model)
{
  const symbol_tablet &symbol_table=goto_model.symbol_table;
  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(f_it->first=="main" ||
       has_prefix(f_it->first.c_str(), CPROVER_PREFIX))
      continue;
    goto_programt &program=f_it->second.body;
    instrument_candidate_invariants(symbol_table, program);
  }
}

/*******************************************************************\

Function: twols_parse_optionst::instrument_candidate_invariants

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void twols_parse_optionst::instrument_candidate_invariants(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program)
{
  namespacet ns(symbol_table);
  std::set<exprt> invars;
  Forall_goto_program_instructions(i_it, goto_program)
  {
    if(!i_it->is_assign()) continue;
    if(to_code_assign(i_it->code).lhs().has_operands()) continue;
    const symbol_exprt &sym=to_symbol_expr(
      to_code_assign(i_it->code).lhs());

    // is it a __CPROVER_* variable?
    if(has_prefix(id2string(sym.get_identifier()), CPROVER_PREFIX))
      continue;

    // static lifetime?
    if(!ns.lookup(sym.get_identifier()).is_static_lifetime)
      continue;

    // constant?
    if(sym.type().get_bool(ID_C_constant))
      continue;

    generate_candidate_invariants(to_code_assign(i_it->code), invars);
  }

  // instrument these candidate invariants in the end of a function
  auto it_last=goto_program.instructions.end();
  it_last--;
  for(auto &invar : invars)
  {
    goto_program.insert_before_swap(it_last);
    it_last->make_assertion(invar);
    std::string p_string=from_expr(ns, "", invar);
    std::string comment="Candidate Invariant: "+p_string;
    it_last->source_location.set_comment(comment);
  }
}

/*******************************************************************\

Function: twols_parse_optionst::generate_candidate_invariants

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void twols_parse_optionst::generate_candidate_invariants(
  const exprt &src,
  std::set<exprt> &results)
{
  assert(src.operands().size()==2);
  // candidate 1: lhs>=rhs
  exprt expr_ge(src);
  expr_ge.type().id(ID_bool);
  expr_ge.id(ID_ge);
  results.insert(expr_ge);
  // candidate 2: lhs<=rhs
  exprt expr_le(src);
  expr_le.type().id(ID_bool);
  expr_le.id(ID_le);
  results.insert(expr_le);
  //// candidate 3: lhs==rhs
  // exprt expr_eq(src);
  // expr_eq.type().id(ID_bool);
  // expr_eq.id(ID_equal);
  // results.insert(expr_eq);
}
