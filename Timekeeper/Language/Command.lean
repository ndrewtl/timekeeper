import Timekeeper.Types
import Timekeeper.Language.Expression.NumericExpression
import Timekeeper.Language.Expression.BooleanExpression
import Timekeeper.Logic.Assertion.GeneralAssertion

namespace Timekeeper

inductive Command where
| skip : Command
| assign : VariableName -> NumericExpression -> Command
| emit : List NumericExpression -> Command
| resolve : GeneralAssertion -> Command
| seq : Command -> Command -> Command
| cond : BooleanExpression -> Command -> Command -> Command
| while : BooleanExpression -> Command -> Command

namespace Command

def numericExpressionPredicate (P : NumericExpression -> Bool) (C : Command) : Prop :=
  match C with
  | skip => false
  | assign _ E => P E
  | emit Es => Es.any P
  | resolve ω => ω.numericExpressionPredicate P
  | seq C₁ C₂ => numericExpressionPredicate P C₁ ∨ numericExpressionPredicate P C₂
  | Command.cond B C₁ C₂ =>
    BooleanExpression.numericExpressionPredicate P B ∨
    numericExpressionPredicate P C₁ ∨
    numericExpressionPredicate P C₂
  | Command.while B C =>
    BooleanExpression.numericExpressionPredicate P B ∨
    numericExpressionPredicate P C

def wellFormed (C : Command) : Prop :=
  ¬(C.numericExpressionPredicate NumericExpression.containsLogicalVariables)

notation:251 "set " "⋆$" x " ⋆:= " E:390 => assign x E
infixr:250 " ⋆; " => seq
notation:251 "if: " b:250 " then: " c₁:250 " else: " c₂:250 " end" => Command.cond b c₁ c₂
notation:252 "while: " b:250 " do: " c:250 " end" => Command.while b c
