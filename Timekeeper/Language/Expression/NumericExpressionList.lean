import Timekeeper.Language.Expression.NumericExpression

namespace Timekeeper
open Notation
open Variable
open NumericExpression

abbrev NumericExpressionList := List NumericExpression

namespace NumericExpressionList

noncomputable def evaluate (Es : NumericExpressionList) (σ : Store) (τ : Trace) : List Val :=
  Es.map (fun E => E.evaluate σ τ)

noncomputable instance : Evaluation (NumericExpressionList) where
  β := Event
  eval := evaluate

def replaceNumericExpression (Es : NumericExpressionList) (E : NumericExpression) (E' : NumericExpression) : NumericExpressionList :=
  match Es with
  | List.nil => List.nil
  | List.cons E₀ tail => List.cons (E₀[E ↦ E']) (replaceNumericExpression tail E E')

instance : TermReplacement NumericExpressionList NumericExpression where
  γ := NumericExpression
  replace := replaceNumericExpression

instance : TermReplacement NumericExpressionList Variable where
  γ := NumericExpression
  replace σ x := replaceNumericExpression σ (var x)

@[simp]
lemma eval {Es : NumericExpressionList} : Evaluation.eval Es σ τ = Es.evaluate σ τ := by
  dsimp [Evaluation.eval]

@[simp]
lemma numeric_replacement :
  TermReplacement.replace term old new = replaceNumericExpression term old new := by
  dsimp [TermReplacement.replace]

@[simp]
lemma variable_replacement {x : Variable}:
  TermReplacement.replace term x new = replaceNumericExpression term (var x) new := by
  dsimp [TermReplacement.replace]

def numericExpressionPredicate (P : NumericExpression -> Bool) (Es : NumericExpressionList) : Bool :=
  Es.any (fun E => E.predicateHoldsSubtree P)

def containsExpression (haystack : NumericExpressionList) (needle : NumericExpression) : Bool
  := haystack.any (fun E => E.containsExpression needle)

def containsTraceLength (Es : NumericExpressionList) : Bool :=
  Es.containsExpression ℓ

def containsVariables (Es : NumericExpressionList) : Bool :=
  Es.numericExpressionPredicate NumericExpression.isVariable

noncomputable def literalize (Es : NumericExpressionList) (σ : Store) (τ : Trace) : NumericExpressionList :=
  match Es with
  | [] => []
  | head :: tail => head.literalize σ τ :: (literalize tail σ τ)
