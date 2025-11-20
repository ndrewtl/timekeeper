import Mathlib.Tactic.Ring
import Timekeeper.Language.Expression.NumericExpressionList
import Timekeeper.Lemma.NumericExpression
import Timekeeper.Lemma.Store

namespace Timekeeper.NumericExpressionList

lemma evaluation_remapping {Es : NumericExpressionList} {E : NumericExpression} {x : Variable} :
  ⟦ Es[x ↦ E] ⟧(σ, τ) = ⟦ Es ⟧(σ[x ↦ ⟦ E ⟧(σ, τ)], τ) := by
  induction Es with
  | nil =>
    simp [replaceNumericExpression, eval, evaluate]
  | cons head tail ih =>
    normalize
    normalize at ih
    rw [ih]
    normalize
    repeat rw [NumericExpression.evaluation_remapping]

lemma nonexistent_term_replacement {Es : NumericExpressionList} {E₀ E₁ : NumericExpression} :
  Es.containsExpression E₀ = false ->
  Es[E₀ ↦ E₁] = Es := by
  intros hEs
  induction Es with
  | nil => simp [replaceNumericExpression]
  | cons head tail ih =>
    simp [replaceNumericExpression]
    simp [containsExpression] at hEs
    rcases hEs with ⟨hhead, hrest⟩
    repeat rw [<-NumericExpression.numeric_replacement]
    constructor
    . rw [NumericExpression.nonexistent_term_replacement]
      exact hhead
    . normalize at ih
      apply ih
      auto_contains
      exact fun x a => hrest x a

lemma equivalent_replacement {Es : NumericExpressionList} {E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⟧(σ, τ) = ⟦ E₂ ⟧(σ, τ) ->
  ⟦ Es[E₁ ↦ E₂] ⟧(σ, τ) = ⟦ Es ⟧(σ, τ) := by
  intros hE₁E₂
  induction Es with
  | nil => normalize
  | cons head tail ih =>
    normalize
    rw [NumericExpression.equivalent_replacement] ; rotate_left
    . exact hE₁E₂
    rw [ih]

lemma store_independence {Es : NumericExpressionList} :
  Es.containsVariables = false ->
  ⟦ Es ⟧(σ₁, τ) = ⟦ Es ⟧(σ₂, τ) := by
  induction Es with
  | nil => normalize
  | cons head tail ih =>
    intros hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hconthead, hconttail⟩
    normalize
    rw [NumericExpression.store_independence (σ₁ := σ₁) (σ₂ := σ₂), ih] ; rotate_left
    . simp [NumericExpression.containsVariables] ; exact hconthead
    . simp [containsVariables, numericExpressionPredicate] ; exact fun x a => hconttail x a

lemma nonexistent_variable_replacement {Es : NumericExpressionList} {x : Variable} {E : NumericExpression} :
  Es.containsExpression (NumericExpression.var x) = false ->
  Es[x ↦ E] = Es := by
  intros h
  rw [variable_replacement, <-numeric_replacement]
  exact nonexistent_term_replacement h

lemma trace_subtraction_replacement {Es : NumericExpressionList} :
  ⟦ Es[ℓ ↦ (ℓ ⋆- ♯p)][ℓ ↦ (ℓ ⋆- ♯q)] ⟧(σ, τ) =
  ⟦ Es[ℓ ↦ (ℓ ⋆- ♯(p + q))] ⟧(σ, τ) := by
  induction Es with
  | nil => simp [replaceNumericExpression, eval, evaluate]
  | cons head tail ih =>
    normalize
    normalize at ih
    rw [ih]
    rw [NumericExpression.trace_subtraction_replacement]

lemma evaluation_remapping_trace_extension_minus {Es : NumericExpressionList} {E : NumericExpression} :
  ⟦ Es[⋆$x ↦ E][ℓ ↦ ℓ ⋆- ♯τext.length] ⟧(σ, τ ++ τext) =
  ⟦ Es[ℓ ↦ ℓ ⋆- ♯τext.length] ⟧(σ[⋆$x ↦ ⟦ E ⟧(σ, τ)], τ ++ τext) := by
  induction Es with
  | nil => simp [replaceNumericExpression, eval, evaluate]
  | cons head tail ih =>
    normalize
    normalize at ih
    rw [ih]
    rw [NumericExpression.evaluation_remapping_trace_extension_minus]

lemma trace_length_substitution_preserves_trace_length_presence {Es : NumericExpressionList} :
  Es[ℓ ↦ NumericExpression.binaryOperation op ℓ ♯n].containsTraceLength = Es.containsTraceLength := by
  induction Es with
  | nil => simp [replaceNumericExpression]
  | cons head tail ih =>
    normalize
    normalize at ih
    simp [containsTraceLength, containsExpression]
    simp [containsTraceLength, containsExpression] at ih
    rw [ih]

    set hhead := NumericExpression.trace_length_substitution_preserves_trace_length_presence (E := head) (n := n) (op := op)
    simp [NumericExpression.containsTraceLength, NumericExpression.containsExpression] at hhead
    simp [NumericExpression.containsExpression]
    rw [hhead]

lemma trace_independence {Es : NumericExpressionList} :
  Es.containsTraceLength = false ->
  ⟦ Es ⟧(σ, τ ++ τ') = ⟦ Es ⟧(σ, τ) := by
  intros hEs
  induction Es with
  | nil => simp [eval, evaluate]
  | cons head tail ih =>
    simp [containsTraceLength, containsExpression] at hEs
    rcases hEs with ⟨hhead, htail⟩
    simp [eval, evaluate] at ih
    simp [eval, evaluate]
    repeat rw [<-NumericExpression.eval]
    rw [NumericExpression.trace_independence]
    rw [ih]
    . simp [containsTraceLength, containsExpression]
      exact fun x a => htail x a
    . simp [NumericExpression.containsTraceLength]
      exact hhead

lemma trace_extension_plus_one {Es : NumericExpressionList} :
  ⟦ Es ⟧(σ, τ ++ [e]) = ⟦ Es[ℓ ↦ ℓ ⋆+ ♯1] ⟧(σ, τ) := by
  induction Es with
  | nil =>
    simp [eval, evaluate, replaceNumericExpression]
  | cons head tail ih =>
    normalize
    normalize at ih
    rw [ih]
    normalize
    rw [NumericExpression.trace_extension_plus_one]

lemma trace_extension_minus {Es : NumericExpressionList} :
  ⟦ Es[ℓ ↦ ℓ ⋆- ♯τ'.length] ⟧(σ, τ ++ τ') = ⟦ Es ⟧(σ, τ) := by
  induction Es with
  | nil =>
    simp [eval, evaluate, replaceNumericExpression]
  | cons head tail ih =>
    normalize
    normalize at ih
    rw [ih]
    normalize
    rw [NumericExpression.trace_extension_minus]

lemma trace_extension_minus_one {Es : NumericExpressionList} :
  ⟦ Es[ℓ ↦ ℓ ⋆- ♯1] ⟧(σ, τ ++ [e]) = ⟦ Es ⟧(σ, τ) := by
  have helen : 1 = [e].length := by exact rfl
  rw [helen]
  apply trace_extension_minus

lemma trace_sub_add_cancel {Es : NumericExpressionList} :
  ⟦ Es[ℓ ↦ ℓ ⋆- ♯k][ℓ ↦ ℓ ⋆+ ♯k] ⟧(σ, τ) = ⟦ Es ⟧(σ, τ) := by
  induction Es with
  | nil => simp [replaceNumericExpression]
  | cons head tail ih =>
    normalize
    normalize at ih
    rw [ih]
    normalize
    rw [NumericExpression.trace_sub_add_cancel]

lemma replacement_preserves_does_not_contain_trace_length {Es : NumericExpressionList} {E E' : NumericExpression} :
  Es.containsExpression ℓ = false ->
  E'.containsExpression ℓ = false ->
  Es[E ↦ E'].containsExpression ℓ = false := by
  intros hEs hE'
  induction Es with
  | nil =>
    simp [containsExpression, replaceNumericExpression]
  | cons head tail ih =>
    simp [containsExpression, replaceNumericExpression]
    normalize
    simp [containsExpression] at hEs
    rcases hEs with ⟨hhead, htail⟩
    constructor
    . rw [NumericExpression.replacement_preserves_does_not_contain_trace_length] ; rotate_left
      . exact hE'
      exact hhead
    . normalize at ih
      simp [containsExpression] at ih
      apply ih
      exact fun x a => htail x a

lemma eq_literalize {Es : NumericExpressionList} :
  ⟦ Es ⟧(σ, τ) = ⟦ Es.literalize σ τ ⟧(σ', τ') := by
  induction Es with
  | nil => simp [literalize] ; normalize
  | cons head tail ih =>
    simp [literalize]
    normalize
    rw [NumericExpression.eq_literalize, ih]

lemma double_trace_replace {Es : NumericExpressionList} {E₁ E₂ E₁' : NumericExpression} :
   ⟦ E₁[ℓ ↦ E₂] ⟧(σ, τ) = ⟦ E₁' ⟧(σ, τ) ->
  (⟦ Es[ℓ ↦ E₁][ℓ ↦ E₂] ⟧(σ, τ) =
  ⟦ Es[ℓ ↦ E₁'] ⟧(σ, τ)) := by
  intros hE₁'
  induction Es with
  | nil => normalize
  | cons head tail ih =>
    normalize
    rw [NumericExpression.double_trace_replace] ; rotate_left
    . exact hE₁'
    rw [ih]
