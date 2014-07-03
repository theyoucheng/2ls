/*******************************************************************\

Module: Summarizer

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/simplify_expr.h>


#include "summarizer.h"
#include "summary_db.h"

#include "../domains/ssa_analyzer.h"

#include "../ssa/local_ssa.h"
#include "../ssa/simplify_ssa.h"


/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summaryt summarizert::summarize(functiont &function, 
				const preconditiont &precondition)
{
  functions.clear();
  preconditions.clear();
  functions[function.first] = function.second;
  preconditions[function.first] = precondition; 
  run();
  return summary_db.get(function.first);
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

summaryt summarizert::summarize(functiont &function)
{ 
  return summarize(function,true_exprt()); 
} 

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(functionst &_functions)
{
  preconditionst _preconditions;
  for(functionst::const_iterator it = _functions.begin(); 
      it!=_functions.end(); it++)
  {
    _preconditions[it->first] = true_exprt();
  }
  summarize(_functions,_preconditions);
}

/*******************************************************************\

Function: summarizert::summarize()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::summarize(functionst &_functions,const preconditionst &_preconditions)
{
  functions = _functions;
  preconditions = _preconditions;
  run();
}

/*******************************************************************\

Function: summarizert::run()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::run()
{
  //TODO: make context sensitive (currently, only globally given preconditions are used),
  //      compute fixed point (if any descendents in the call graph are updated)
  //TODO: replace simple iterator by something following the call graph
  for(functionst::const_iterator it = functions.begin(); 
      it!=functions.end(); it++)
  {
    status() << "\nSummarizing function " << it->first << eom;
    if(!summary_db.exists(it->first)) compute_summary_rec(it->first);
    else status() << "Summary for function " << it->first << 
           " exists already" << eom;
  }
}

/*******************************************************************\

Function: summarizert::compute_summary_rec()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::compute_summary_rec(const function_namet &function_name)
{
  local_SSAt &SSA = *functions[function_name]; 
  inline_summaries(function_name,SSA,true); 

  {
    std::ostringstream out;
    out << "Function body for " << function_name << 
      " to be analyzed: " << std::endl;
    for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
        n!=SSA.nodes.end(); n++)
    {
      if(!n->second.empty()) n->second.output(out,SSA.ns);
    }
    debug() << out.str() << eom;
  }

  //analyze
  ssa_analyzert analyzer(SSA.ns, options);
  analyzer.set_message_handler(get_message_handler());

  analyzer(SSA);

  summaryt summary;
  summary.params =SSA.params;
  summary.globals_in =SSA.globals_in;
  summary.globals_out =SSA.globals_out;
  summary.precondition = preconditions.at(function_name);
  analyzer.get_summary(summary.transformer);
  simplify_expr(summary.transformer, SSA.ns);

  {
    std::ostringstream out;
    out << std::endl << "Summary for function " << function_name << std::endl;
    summary.output(out,SSA.ns);   
    status() << out.str() << eom;
  }

  summary_db.put(function_name,summary);

  // Add loop invariants as constraints back into SSA.
  // We simply use the last CFG node. It would be prettier to put
  // these close to the loops.
  goto_programt::const_targett loc=
    SSA.goto_function.body.instructions.end();
  loc--;
  local_SSAt::nodet &node=SSA.nodes[loc];
  exprt inv;
  analyzer.get_loop_invariants(inv);
  node.constraints.push_back(inv);

  status() << "Adding loop invariant: " << from_expr(SSA.ns, "", inv) << eom;
}

/*******************************************************************\

Function: summarizert::inline_summaries()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizert::inline_summaries(const function_namet &function_name, 
  local_SSAt &SSA, bool recursive)
{
  ssa_inlinert inliner;
  inliner.set_message_handler(get_message_handler());

  // replace calls with summaries
  // TODO: functions with pointers passed as parameters
  for(local_SSAt::nodest::iterator n = SSA.nodes.begin(); 
      n!=SSA.nodes.end(); n++)
  {
    for(local_SSAt::nodet::function_callst::iterator 
        f_it = n->second.function_calls.begin();
        f_it != n->second.function_calls.end(); f_it++)
    {
      assert(f_it->function().id()==ID_symbol); //no function pointers
      irep_idt fname = to_symbol_expr(f_it->function()).get_identifier();

      summaryt summary; 
      bool recompute = false;
      // replace call with summary if it exists 
      if(summary_db.exists(fname)) 
      {
        status() << "Using existing summary for function " << fname << eom;
	summary = summary_db.get(fname);
	  //TODO: check whether summary applies (as soon as context-sensitive)
	  //      (requires retrieving the local context from the current analysis), 
	  //      otherwise compute new one: recompute = true;
      }
      // compute summary if function_name in functions
      else if(functions.find(fname)!=functions.end() && recursive) 
        recompute = true;
      else // havoc function call by default
      {
        status() << "Function " << fname << " not found" << eom;
        inliner.havoc(n->second,f_it);
        continue;
      }
      if(recompute) 
      {
        status() << "Recursively summarizing function " << fname << eom;
        compute_summary_rec(fname);
        summary = summary_db.get(fname);
      }

      status() << "Replacing function " << fname << eom;
      //getting globals at call site
      local_SSAt::var_sett cs_globals_in, cs_globals_out; 
      goto_programt::const_targett loc = n->first;
      SSA.get_globals(loc,cs_globals_in);
      assert(loc!=SSA.goto_function.body.instructions.end());
      SSA.get_globals(++loc,cs_globals_out);

      /*      for(summaryt::var_sett::const_iterator it = summary.globals_in.begin();
          it != summary.globals_in.end(); it++)
	  std::cout << "global " << SSA.read_rhs(*it,loc) << std::endl; */
    
#if 0
      std::cout << "globals at call site: ";
      for(summaryt::var_sett::const_iterator it = cs_globals_out.begin();
          it != cs_globals_out.end(); it++)
         std::cout << from_expr(functions[function_name]->ns,"",*it) << " ";
      std::cout << std::endl;
#endif

      //replace
      inliner.replace(SSA.nodes,n,f_it,cs_globals_in,cs_globals_out,summary);
    }
    inliner.commit_node(n);
  }
  inliner.commit_nodes(SSA.nodes);
}
