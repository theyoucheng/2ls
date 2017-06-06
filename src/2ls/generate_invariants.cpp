/*******************************************************************\

Module: Automatic Invariants Generation

Author: Youcheng Sun

\*******************************************************************/

#include <util/cprover_prefix.h>
#include <util/prefix.h>
#include "2ls_parse_options.h"
#include "../../cbmc/src/cbmc/cbmc_solvers.h"
#include "../../cbmc/src/cbmc/bmc.h"
#include "../../cbmc/src/cbmc/all_properties_class.h"
#include <iostream>

/*******************************************************************\

Function: twols_parse_optionst::generate_invariants

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void twols_parse_optionst::generate_invariants(
  const optionst &options,
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
  filter_candidate_invariants(options, goto_model);
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
    std::string comment="__CPROVER_Candidate Invariant: "+p_string;
    it_last->source_location.set_comment(comment);
    it_last->source_location.set_property_id(comment);
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

/*******************************************************************\

Function: twols_parse_optionst::filter_candidate_invariants

Inputs:

Outputs:

Purpose:

\*******************************************************************/

void twols_parse_optionst::filter_candidate_invariants(
  const optionst &options,
  goto_modelt &goto_model)
{
  const symbol_tablet &symbol_table=goto_model.symbol_table;
  optionst opts(options);
  opts.set_option("unwind", 10); // let's say 10 unwindings

  Forall_goto_functions(f_it, goto_model.goto_functions)
  {
    if(f_it->first=="main" ||
       has_prefix(f_it->first.c_str(), CPROVER_PREFIX))
      continue;
    // If f_it->first is never called ==> ignore it
    goto_programt::instructionst::iterator fcall_it;
    bool f_called=false;
    Forall_goto_functions(e_it, goto_model.goto_functions)
    {
      if(f_it==e_it) continue;
      Forall_goto_program_instructions(i_it, e_it->second.body)
      {
        if(!i_it->is_function_call()) continue;
        const code_function_callt &code=
          to_code_function_call(i_it->code);
        const symbol_exprt &sym=to_symbol_expr(code.function());
        if(sym.get_identifier()==f_it->first) 
        {
          std::cout << "\n\n symbol: " << from_expr(sym) << "\n\n";
          fcall_it=i_it;
          f_called=true;
          break;
        }
      }
      if(f_called) break;
    }
    if(!f_called) continue;
    // To perform method local analysis, we replace the entry of
    // main in ID__start with function call to f_it->first
    std::cout << "\n\n ---> " << f_it->first << " <---\n\n"; 
    goto_programt::instructiont main_inst;
    auto &goto_instructions=
      goto_model.goto_functions.function_map[ID__start].body;
    Forall_goto_program_instructions(i_it, goto_instructions)
    {
      if(!i_it->is_function_call()) continue;
      const code_function_callt &code=
        to_code_function_call(i_it->code);
      const symbol_exprt &sym=to_symbol_expr(code.function());
      if(sym.get_identifier()=="main")
      {
        main_inst=*i_it;
        i_it->make_function_call(fcall_it->code);
      }
    }

    // Some method local analysis
    cbmc_solverst cbmc_solvers(opts, symbol_table, ui_message_handler);
    std::unique_ptr<cbmc_solverst::solvert> cbmc_solver;
    try
    {
      cbmc_solver=cbmc_solvers.get_solver();
    }

    catch(const char *error_msg)
    {
      error() << error_msg << eom;
      return;
    }

    prop_convt &prop_conv=cbmc_solver->prop_conv();
    bmct bmc(opts, symbol_table, ui_message_handler, prop_conv);
    bmc.run(goto_model.goto_functions);

    const auto &valid_properties=bmc.valid_properties;
    Forall_goto_program_instructions(i_it, f_it->second.body)
    {
      if(!i_it->is_assert()) continue;
      irep_idt comment=i_it->source_location.get_comment();
      if(!has_prefix(comment.c_str(), CPROVER_PREFIX))
        continue;
      if(valid_properties.find(comment)!=valid_properties.end())
      {
        i_it->make_assumption(exprt(i_it->guard));
      }
      else i_it->make_skip();
    }

    // Do not forget to reset the main entry
    Forall_goto_program_instructions(i_it, goto_instructions)
    {
      if(!i_it->is_function_call()) continue;
      const code_function_callt &code=
        to_code_function_call(i_it->code);
      const symbol_exprt &sym=to_symbol_expr(code.function());
      if(sym.get_identifier()==f_it->first)
        *i_it=main_inst;
    }
  }
}
