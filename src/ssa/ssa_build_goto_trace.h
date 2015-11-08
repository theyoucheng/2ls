/*******************************************************************\

Module: Traces of GOTO Programs for SSA Models

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SSA_BUILD_GOTO_TRACE_H
#define CPROVER_SSA_BUILD_GOTO_TRACE_H

#include <goto-programs/goto_trace.h>
#include <solvers/prop/prop_conv.h>

#include "local_ssa.h"
#include "unwindable_local_ssa.h"

class ssa_build_goto_tracet {
public:
  ssa_build_goto_tracet(
    unwindable_local_SSAt &_unwindable_local_SSA,
    const prop_convt &_prop_conv) 
  : 
  unwindable_local_SSA(_unwindable_local_SSA),  
  prop_conv(_prop_conv)
  {}

  void operator()(goto_tracet &);

protected:
  unwindable_local_SSAt &unwindable_local_SSA;
  const prop_convt &prop_conv;
  goto_programt::const_targett current_pc;

  exprt finalize_lhs(const exprt &src);

  bool record_step(
    goto_tracet &goto_trace,
    unsigned &step_nr);
};

#endif
