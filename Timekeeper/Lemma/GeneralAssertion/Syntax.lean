import Timekeeper.Lemma.BooleanExpression
import Timekeeper.Lemma.TraceAssertion
import Timekeeper.Lemma.GeneralAssertion.Inversion

namespace Timekeeper.GeneralAssertion

lemma nonexistent_term_replacement {A : GeneralAssertion} :
  ¬A.containsNumericExpression E -> A[E ↦ E'] = A := by
  intros hcont
  induction A with
  | expression B =>
    simp [containsNumericExpression] at hcont
    normalize
    rw [BooleanExpression.nonexistent_term_replacement]
    . exact hcont
  | negation A₁ ihA₁ =>
    simp [containsNumericExpression] at hcont
    specialize ihA₁ hcont
    normalize
    exact ihA₁
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hA₁cont, hA₂cont⟩
    apply ihA₁ at hA₁cont
    apply ihA₂ at hA₂cont
    normalize
    rw [hA₁cont, hA₂cont]
    trivial
  | trace T Eₜ =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hTcont, hEₜcont⟩
    normalize
    constructor
    . rw [TraceAssertion.nonexistent_term_replacement]
      . exact hTcont
    . rw [NumericExpression.nonexistent_term_replacement]
      exact hEₜcont
  | universal_quantification x A' ihA' =>
    simp [containsNumericExpression] at hcont
    apply ihA' at hcont
    normalize
    rw [hcont]

lemma nonexistent_variable_replacement {A : GeneralAssertion} {x : Variable} :
  ¬A.containsNumericExpression (NumericExpression.var x) ->
  A[x ↦ E'] = A := by
  intros h
  rw [variable_replacement, <-numeric_replacement]
  exact nonexistent_term_replacement h

lemma trace_length_substitution_preserves_well_formedness {A : GeneralAssertion} :
  A[ℓ ↦ NumericExpression.binaryOperation op ℓ ♯n].wellFormed = A.wellFormed := by
  induction A with
  | expression B =>
    simp [wellFormed, replaceNumericExpression]
  | negation A' ihA' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    rw [ihA']
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    rw [ihA₁, ihA₂]
  | trace T E =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    rw [TraceAssertion.trace_length_substitution_preserves_well_formedness]
  | universal_quantification _ A' ihA' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    rw [ihA']

lemma trace_length_addition_preserves_well_formedness {A : GeneralAssertion} :
  A[ℓ ↦ ℓ ⋆+ ♯n].wellFormed = A.wellFormed := by
  have hop : ℓ ⋆+ ♯n = NumericExpression.binaryOperation BinOp.plus ℓ ♯n := by
    exact rfl
  rw [hop]
  exact trace_length_substitution_preserves_well_formedness

lemma trace_length_subtraction_preserves_well_formedness {A : GeneralAssertion} :
  A[ℓ ↦ ℓ ⋆- ♯n].wellFormed = A.wellFormed := by
  have hop : ℓ ⋆- ♯n = NumericExpression.binaryOperation BinOp.minus ℓ ♯n := by
    exact rfl
  rw [hop]
  exact trace_length_substitution_preserves_well_formedness
