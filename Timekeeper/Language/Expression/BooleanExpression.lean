import Mathlib.Tactic.Lemma
import Timekeeper.Notation.Logic
import Timekeeper.Notation.Evaluation
import Timekeeper.Language.Expression.NumericExpression

namespace Timekeeper

inductive BooleanExpression where
  | negation          : BooleanExpression -> BooleanExpression
  | disjunction       : BooleanExpression -> BooleanExpression -> BooleanExpression
  | lessThanOrEqualTo : NumericExpression -> NumericExpression -> BooleanExpression
deriving Repr, BEq

namespace BooleanExpression
open Notation

instance : Negation BooleanExpression where
  not := BooleanExpression.negation

@[simp]
lemma negation_boolean_expression : Negation.not φ = BooleanExpression.negation φ := by
  dsimp [Negation.not]

instance : Disjunction BooleanExpression where
  or := BooleanExpression.disjunction

@[simp]
lemma disjunction_boolean_expression : Disjunction.or l r = BooleanExpression.disjunction l r := by
  simp [Disjunction.or]

instance : Conjunction BooleanExpression where
  and B₁ B₂ := ⋆¬(⋆¬B₁ ⋆∨ ⋆¬B₂)

@[simp]
lemma conjunction_boolean_expression {l r : BooleanExpression} : Conjunction.and l r = ⋆¬(⋆¬l ⋆∨ ⋆¬r) := by
  simp [Conjunction.and]

infixl:350  " ⋆≤ " => lessThanOrEqualTo

@[simp]
def equalTo (E₁ E₂ : NumericExpression) : BooleanExpression :=
  E₁ ⋆≤ E₂ ⋆∧ E₂ ⋆≤ E₁

infixl:351 " ⋆= " => equalTo

@[simp]
def notEqualTo (E₁ E₂ : NumericExpression) : BooleanExpression :=
  ⋆¬(E₁ ⋆= E₂)

infixl:352 " ⋆≠ " => notEqualTo

@[simp]
def lessThan (E₁ E₂ : NumericExpression) : BooleanExpression :=
  E₁ ⋆≤ E₂ ⋆∧ E₁ ⋆≠ E₂

infixl:353 " ⋆< " => lessThan

noncomputable def evaluate (B : BooleanExpression) (σ : Store) (τ : Trace) : Bool :=
  match B with
  | BooleanExpression.negation B' => not $ evaluate B' σ τ
  | BooleanExpression.disjunction B₁ B₂ =>
    (evaluate B₁ σ τ) ∨ (evaluate B₂ σ τ)
  | BooleanExpression.lessThanOrEqualTo E₁ E₂ =>
    NumericExpression.evaluate E₁ σ τ ≤ NumericExpression.evaluate E₂ σ τ

noncomputable instance : Evaluation BooleanExpression where
  β := Bool
  eval := evaluate

def numericExpressionPredicate (P : NumericExpression -> Bool) (B : BooleanExpression) : Bool :=
  match B with
  | negation B' => numericExpressionPredicate P B'
  | disjunction B₁ B₂ => numericExpressionPredicate P B₁ ∨ numericExpressionPredicate P B₂
  | lessThanOrEqualTo E₁ E₂ => NumericExpression.predicateHoldsSubtree P E₁ ∨ NumericExpression.predicateHoldsSubtree P E₂

def containsVariables (B : BooleanExpression) : Bool :=
  B.numericExpressionPredicate NumericExpression.isVariable

def replaceNumericExpression : BooleanExpression -> NumericExpression -> NumericExpression -> BooleanExpression
  | B, oldExpr, newExpr =>
    match B with
    | BooleanExpression.negation B' => ⋆¬(replaceNumericExpression B' oldExpr newExpr)
    | BooleanExpression.disjunction l r => (replaceNumericExpression l oldExpr newExpr) ⋆∨ (replaceNumericExpression r oldExpr newExpr)
    | BooleanExpression.lessThanOrEqualTo l r =>
        NumericExpression.replaceNumericExpression l oldExpr newExpr ⋆≤
        NumericExpression.replaceNumericExpression r oldExpr newExpr

instance : TermReplacement BooleanExpression NumericExpression where
  γ := NumericExpression
  replace := replaceNumericExpression

instance : TermReplacement BooleanExpression Variable where
  γ := NumericExpression
  replace := fun σ x => replaceNumericExpression σ (NumericExpression.var x)

@[simp]
lemma eval:
  Evaluation.eval b σ τ = evaluate b σ τ := by
  dsimp [Evaluation.eval]

@[simp]
lemma numeric_replacement :
  TermReplacement.replace term old new = replaceNumericExpression term old new := by
  dsimp [TermReplacement.replace]

@[simp]
lemma variable_replacement {x : Variable}:
  TermReplacement.replace term x new = replaceNumericExpression term (NumericExpression.var x) new := by
  dsimp [TermReplacement.replace]

def containsNumericExpression (B : BooleanExpression) (E : NumericExpression) : Bool :=
  match B with
  | negation B' => B'.containsNumericExpression E
  | disjunction B₁ B₂  => B₁.containsNumericExpression E || B₂.containsNumericExpression E
  | lessThanOrEqualTo E₁ E₂ => E₁.containsExpression E || E₂.containsExpression E

noncomputable def literalize (B : BooleanExpression) (σ : Store) (τ : Trace) : BooleanExpression :=
  match B with
  | .negation B' => ⋆¬(B'.literalize σ τ)
  | .disjunction B₁ B₂ => B₁.literalize σ τ ⋆∨ B₂.literalize σ τ
  | .lessThanOrEqualTo E₁ E₂ => E₁.literalize σ τ ⋆≤ E₂.literalize σ τ
