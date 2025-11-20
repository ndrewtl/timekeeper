import Timekeeper.Language.Expression.BooleanExpression
import Timekeeper.Language.Expression.NumericExpressionList
import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Logic.Specification
import Timekeeper.Notation.TermReplacement

namespace Timekeeper

inductive GeneralAssertion where
  | expression : BooleanExpression -> GeneralAssertion
  | negation : GeneralAssertion -> GeneralAssertion
  | disjunction : GeneralAssertion -> GeneralAssertion -> GeneralAssertion
  | trace : TraceAssertion -> NumericExpression -> GeneralAssertion
  | universal_quantification : VariableName -> GeneralAssertion -> GeneralAssertion

namespace GeneralAssertion
open Notation

instance : Negation GeneralAssertion where
  not := GeneralAssertion.negation

@[simp]
lemma negation_general_assertion : Negation.not φ = GeneralAssertion.negation φ := by
  dsimp [Negation.not]

instance : Disjunction GeneralAssertion where
  or := GeneralAssertion.disjunction

@[simp]
lemma disjunction_general_assertion : Disjunction.or l r = GeneralAssertion.disjunction l r := by
  simp [Disjunction.or]

instance : Conjunction GeneralAssertion where
  and left right := ⋆¬(⋆¬left ⋆∨ ⋆¬right)

@[simp]
lemma conjunction_general_assertion {l r : GeneralAssertion} : Conjunction.and l r = ⋆¬(⋆¬l ⋆∨ ⋆¬r) := by
  simp [Conjunction.and]

instance : Implication GeneralAssertion where
  implies left right := ⋆¬left ⋆∨ right

@[simp]
lemma implication_general_assertion {l r : GeneralAssertion} : Implication.implies l r = ⋆¬l ⋆∨ r := by
  simp [Implication.implies]

prefix:max "~" => expression
infixl:290  " ⋆@ " => trace
notation:269 "⋆∀ " x:269 " : " A:269 => universal_quantification x A

def top : GeneralAssertion := ~(♯0 ⋆≤ ♯0)
notation:max "⋆⊤" => top

def bot : GeneralAssertion := ⋆¬(⋆⊤)
notation:max "⋆⊥" => bot


def wellFormed : GeneralAssertion -> Prop
| expression _ => True
| negation φ => wellFormed φ
| disjunction φ ψ => wellFormed φ ∧ wellFormed ψ
| trace T _ => T.wellFormed
| universal_quantification _ φ => wellFormed φ

def replaceNumericExpression : GeneralAssertion -> NumericExpression -> NumericExpression -> GeneralAssertion
  | assertion, oldExpr, newExpr =>
    match assertion with
    | expression B => expression $ B[oldExpr ↦ newExpr]
    | negation φ => ⋆¬(φ.replaceNumericExpression oldExpr newExpr)
    | disjunction φ ψ => φ.replaceNumericExpression oldExpr newExpr ⋆∨ ψ.replaceNumericExpression oldExpr newExpr
    | trace φ E => φ[oldExpr ↦ newExpr] ⋆@ E[oldExpr ↦ newExpr]
    | universal_quantification x φ => ⋆∀ x : φ.replaceNumericExpression oldExpr newExpr

def numericExpressionPredicate (P : NumericExpression -> Bool) (A : GeneralAssertion) : Prop :=
  match A with
  | expression B => B.numericExpressionPredicate P
  | negation A' => A'.numericExpressionPredicate P
  | disjunction φ ψ => φ.numericExpressionPredicate P ∨ ψ.numericExpressionPredicate P
  | trace T E => T.numericExpressionPredicate P ∨ E.predicateHoldsSubtree P
  | universal_quantification _ A' => A'.numericExpressionPredicate P

def containsNumericExpression (A : GeneralAssertion) (E : NumericExpression) : Prop :=
  match A with
  | expression B => B.containsNumericExpression E
  | negation A' => A'.containsNumericExpression E
  | disjunction A₁ A₂ => A₁.containsNumericExpression E ∨ A₂.containsNumericExpression E
  | trace T Eₜ => T.containsNumericExpression E ∨ Eₜ.containsExpression E
  | universal_quantification _ A' => A'.containsNumericExpression E

def containsVariables (A : GeneralAssertion) : Prop :=
  A.numericExpressionPredicate NumericExpression.isVariable

instance : TermReplacement GeneralAssertion NumericExpression where
  γ := NumericExpression
  replace := replaceNumericExpression

instance : TermReplacement GeneralAssertion Variable where
  γ := NumericExpression
  replace σ x := replaceNumericExpression σ (NumericExpression.var x)

@[simp]
lemma numeric_replacement :
  TermReplacement.replace A old new = replaceNumericExpression A old new := by
  dsimp [TermReplacement.replace]

@[simp]
lemma variable_replacement :
  TermReplacement.replace A x new = replaceNumericExpression A (NumericExpression.var x) new := by
  dsimp [TermReplacement.replace]

instance : Coe BooleanExpression GeneralAssertion where
  coe := expression
