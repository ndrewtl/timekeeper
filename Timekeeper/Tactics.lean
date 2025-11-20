import Lean
import Lean.Parser.Tactic
import Timekeeper.Notation.Logic
import Timekeeper.Language.Expression.NumericExpression
import Timekeeper.Language.Expression.NumericExpressionList
import Timekeeper.Language.Expression.BooleanExpression
import Timekeeper.Language.Command
import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Logic.Assertion.GeneralAssertion

namespace Timekeeper.Tactics
open Lean Elab Tactic Elab.Tactic Parser.Tactic

syntax "simp_replacement" (ppSpace ("at " locationHyp))? : tactic
macro_rules
  | `(tactic|simp_replacement) => do
    `(tactic|simp [
      NumericExpression.replaceNumericExpression,
      NumericExpression.evaluate,
      NumericExpression.add,
      NumericExpression.sub,
      NumericExpression.mod,
      NumericExpression.index,
      NumericExpression.arrayAssign,
      NumericExpressionList.replaceNumericExpression,
      NumericExpressionList.evaluate,
      BooleanExpression.replaceNumericExpression,
      BooleanExpression.evaluate,
      TraceAssertion.replaceNumericExpression,
      GeneralAssertion.replaceNumericExpression
    ])
macro_rules
  | `(tactic|simp_replacement at $id) => do
    `(tactic|simp [
      NumericExpression.replaceNumericExpression,
      NumericExpression.evaluate,
      NumericExpression.add,
      NumericExpression.sub,
      NumericExpression.mod,
      NumericExpression.index,
      NumericExpression.arrayAssign,
      NumericExpressionList.replaceNumericExpression,
      NumericExpressionList.evaluate,
      BooleanExpression.replaceNumericExpression,
      BooleanExpression.evaluate,
      TraceAssertion.replaceNumericExpression,
      GeneralAssertion.replaceNumericExpression
    ] at $id)

syntax "fold_all" (ppSpace ("at " locationHyp))? : tactic
elab_rules : tactic
| `(tactic|fold_all) => do
    evalTactic (<- `(tactic|repeat rw [<-Store.replacement]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.add]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.sub]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.mod]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.index]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.arrayAssign]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.variable_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.numeric_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.eval]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.variable_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.numeric_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.evaluate]))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.eval]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.negation_boolean_expression]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.disjunction_boolean_expression]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.conjunction_boolean_expression]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.equalTo]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.notEqualTo]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.lessThan]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.eval]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.variable_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.numeric_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.negation_trace_assertion]))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.disjunction_trace_assertion]))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.conjunction_trace_assertion]))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.once]))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.eventually]))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.variable_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.numeric_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.negation_general_assertion]))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.disjunction_general_assertion]))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.conjunction_general_assertion]))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.implication_general_assertion]))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.variable_replacement]))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.numeric_replacement]))
elab_rules : tactic
| `(tactic|fold_all at $id) => do
    evalTactic (<- `(tactic|repeat rw [<-Store.replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.add] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.sub] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.mod] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.index] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.arrayAssign] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.variable_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.numeric_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpression.eval] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.variable_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.numeric_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.evaluate] at $id))
    evalTactic (<- `(tactic|repeat rw [<-NumericExpressionList.eval] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.negation_boolean_expression] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.disjunction_boolean_expression] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.conjunction_boolean_expression] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.equalTo] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.notEqualTo] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.lessThan] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.eval] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.variable_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-BooleanExpression.numeric_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.negation_trace_assertion] at $id))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.disjunction_trace_assertion] at $id))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.conjunction_trace_assertion] at $id))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.once] at $id))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.eventually] at $id))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.variable_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-TraceAssertion.numeric_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.negation_general_assertion] at $id))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.disjunction_general_assertion] at $id))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.conjunction_general_assertion] at $id))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.implication_general_assertion] at $id))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.variable_replacement] at $id))
    evalTactic (<- `(tactic|repeat rw [<-GeneralAssertion.numeric_replacement] at $id))

syntax "normalize" (ppSpace ("at " locationHyp))? : tactic
elab_rules : tactic
| `(tactic|normalize) => do
  evalTactic  (<- `(tactic|try simp_replacement))
  evalTactic  (<- `(tactic|try fold_all))
elab_rules : tactic
| `(tactic|normalize at $id) => do
  evalTactic  (<- `(tactic|try simp_replacement at $id))
  evalTactic  (<- `(tactic|try fold_all at $id))

syntax "auto_wf" : tactic
elab_rules : tactic
| `(tactic|auto_wf) => do
  evalTactic (<- `(tactic|simp [
    Command.wellFormed,
    Command.numericExpressionPredicate,
    -- Well-formedness definitions
    GeneralAssertion.wellFormed,
    TraceAssertion.wellFormed,
    -- containsExpression
    NumericExpressionList.containsExpression,
    NumericExpression.containsExpression,
    NumericExpression.predicateHoldsSubtree,
    NumericExpression.containsLogicalVariables,
    NumericExpression.isLogicalVariable,
    -- replaceNumericExpression
    NumericExpression.replaceNumericExpression,
    NumericExpressionList.replaceNumericExpression,
    NumericExpressionList.numericExpressionPredicate,
    BooleanExpression.numericExpressionPredicate,
    TraceAssertion.replaceNumericExpression,
    TraceAssertion.numericExpressionPredicate,
    GeneralAssertion.replaceNumericExpression,
    GeneralAssertion.numericExpressionPredicate,
    -- top and bot
    GeneralAssertion.top,
    GeneralAssertion.bot
    ]))

syntax "auto_contains" : tactic
elab_rules : tactic
| `(tactic|auto_contains) => do
  evalTactic (<- `(tactic|simp [
    NumericExpressionList.containsExpression,
    NumericExpression.containsExpression,
    NumericExpression.predicateHoldsSubtree,
    NumericExpression.replaceNumericExpression,
    NumericExpressionList.containsExpression,
    NumericExpressionList.replaceNumericExpression,
    BooleanExpression.containsNumericExpression,
    BooleanExpression.replaceNumericExpression,
    TraceAssertion.containsNumericExpression,
    TraceAssertion.replaceNumericExpression,
    GeneralAssertion.containsNumericExpression,
    GeneralAssertion.replaceNumericExpression,
    GeneralAssertion.top,
    GeneralAssertion.bot
  ]))
