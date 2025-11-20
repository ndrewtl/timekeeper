import Timekeeper.Lemma.BooleanExpression
import Timekeeper.Lemma.NumericExpressionList
import Timekeeper.Lemma.TraceAssertion
import Timekeeper.Lemma.GeneralAssertion.Inversion
import Timekeeper.Lemma.GeneralAssertion.TraceExtension

namespace Timekeeper.GeneralAssertion
open Models

lemma trace_subtraction_replacement :
  A.wellFormed ->
  (⋆ σ, τ ⊧[ b ] A[ℓ ↦ (ℓ ⋆- ♯p)][ℓ ↦ (ℓ ⋆- ♯q)] <->
  ⋆ σ, τ ⊧[ b ] A[ℓ ↦ (ℓ ⋆- ♯(p + q))]) := by
  intros hAwf
  revert b σ τ
  induction A with
  | expression B =>
    intros σ τ b
    constructor <;>
    intros hA <;>
    apply expression_inversion at hA <;>
    apply expression_intro
    . rw [BooleanExpression.trace_subtraction_replacement] at hA
      exact hA
    . rw [BooleanExpression.trace_subtraction_replacement]
      exact hA
  | negation A' ihA' =>
    intros σ τ b
    constructor <;>
    intros hA <;>
    apply negation_inversion at hA <;>
    simp [wellFormed] at hAwf <;>
    specialize ihA' (σ := σ) (τ := τ) (b := !b) hAwf <;>
    apply negation_intro <;>
    normalize at hA <;>
    normalize
    . rw [ihA'] at hA
      exact hA
    . rw [ihA']
      exact hA
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    intros σ τ b
    constructor <;>
    intros hA <;>
    simp [GeneralAssertion.wellFormed] at hAwf <;>
    rcases hAwf with ⟨hA₁wf, hA₂wf⟩ <;>
    specialize ihA₁ hA₁wf (σ := σ) (τ := τ) (b := b) <;>
    specialize ihA₂ hA₂wf (σ := σ) (τ := τ) (b := b) <;>
    apply disjunction_inversion_bool at hA <;>
    normalize at hA <;>
    rcases hA with (⟨rfl, hA₁, hA₂⟩ | ⟨rfl, (hA₁ | hA₂)⟩) <;>
    (try apply disjunction_intro_false) <;>
    (try rw [ihA₁] at hA₁) <;>
    (try rw [ihA₂] at hA₂) <;>
    normalize <;>
    (try rw [ihA₁]) <;>
    (try rw [ihA₂]) <;>
    (try exact hA₁) <;>
    (try exact hA₂)
    . apply disjunction_intro_left
      exact hA₁
    . apply disjunction_intro_right
      exact hA₂
    . apply disjunction_intro_left
      rw [ihA₁]
      exact hA₁
    . apply disjunction_intro_right
      rw [ihA₂]
      exact hA₂
  | trace T E =>
    intros σ τ b
    constructor <;>
    intros hA <;>
    apply trace_inversion at hA <;>
    apply trace_intro
    . rw [TraceAssertion.trace_subtraction_replacement, NumericExpression.trace_subtraction_replacement] at hA
      exact hA
    . rw [TraceAssertion.trace_subtraction_replacement, NumericExpression.trace_subtraction_replacement]
      exact hA
  | universal_quantification x A' ihA' =>
    intros σ τ b
    constructor <;>
    intros hA <;>
    apply universal_quantification_inversion at hA <;>
    apply universal_quantification_intro <;>
    simp [GeneralAssertion.wellFormed] at hAwf <;>
    intros v' <;>
    specialize hA v' <;>
    specialize ihA' hAwf (σ := σ[⋆^x ↦ v']) (τ := τ) (b := b) <;>
    normalize at hA <;>
    normalize
    . rw [ihA'] at hA
      exact hA
    . rw [ihA']
      exact hA

lemma evaluation_remapping_trace_extension_minus_bool {E : NumericExpression} :
  E.containsLogicalVariables = false ->
  (⋆ σ, τ ++ τext ⊧[ b ] A[⋆$x ↦ E][ℓ ↦ ℓ ⋆- ♯τext.length] <->
  ⋆ σ[⋆$x ↦ ⟦ E ⟧(σ, τ)], τ ++ τext ⊧[ b ] A[ℓ ↦ ℓ ⋆- ♯τext.length]) := by
  intros hEwf
  revert σ b
  induction A with
  | expression B =>
    intros σ b
    constructor <;> intros h
    . apply expression_inversion at h
      rw [BooleanExpression.numeric_replacement, BooleanExpression.numeric_replacement, <-BooleanExpression.variable_replacement, <-BooleanExpression.numeric_replacement] at h
      rw [BooleanExpression.evaluation_remapping_trace_extension_minus] at h
      apply expression_intro
      exact h
    . apply expression_inversion at h
      rw [<-BooleanExpression.evaluation_remapping_trace_extension_minus] at h
      apply expression_intro
      exact h
  | negation A' ihA' =>
    intros σ b
    constructor <;> intros h <;>
    apply negation_inversion at h
    . rw [<-variable_replacement] at h
      rw [<-numeric_replacement] at h
      rw [ihA'] at h
      apply negation_intro
      exact h
    . rw [<-numeric_replacement] at h
      rw [<-ihA'] at h
      apply negation_intro
      exact h
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    intros σ b
    constructor <;> intros h <;>
    apply disjunction_inversion_bool at h <;>
    normalize at h <;>
    rcases h with (⟨rfl, hA₁, hA₂⟩ | ⟨rfl, (hA₁ | hA₂)⟩) <;>
    (try rw [ihA₁] at hA₁) <;>
    (try rw [ihA₂] at hA₂) <;>
    normalize
    . exact disjunction_intro_false hA₁ hA₂
    . exact disjunction_intro_left hA₁
    . exact disjunction_intro_right hA₂
    . apply disjunction_intro_false
      . rw [ihA₁] ; exact hA₁
      . rw [ihA₂] ; exact hA₂
    . apply disjunction_intro_left
      rw [ihA₁] ; exact hA₁
    . apply disjunction_intro_right
      rw [ihA₂] ; exact hA₂
  | trace T E' =>
    intros σ b
    constructor <;> intros h <;>
    apply trace_inversion at h <;>
    apply trace_intro <;>
    normalize at h <;>
    normalize
    . rw [TraceAssertion.evaluation_remapping_trace_extension_minus, NumericExpression.evaluation_remapping_trace_extension_minus] at h ; rotate_left
      . exact hEwf
      exact h
    . rw [TraceAssertion.evaluation_remapping_trace_extension_minus, NumericExpression.evaluation_remapping_trace_extension_minus] ; rotate_left
      . exact hEwf
      exact h
  | universal_quantification x' A' ihA' =>
    intros σ b
    constructor <;> intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihA'] at h
      rw [Store.replacement_different_variables_reordering] at h
      . rw [NumericExpression.logical_state_independence] at h
        . exact h
        . exact hEwf
      . simp
    . rw [ihA']
      rw [Store.replacement_different_variables_reordering]
      . rw [NumericExpression.logical_state_independence]
        . exact h
        . exact hEwf
      . simp

lemma evaluation_remapping_trace_extension_minus {E : NumericExpression} :
  E.containsLogicalVariables = false ->
  (⋆ σ, τ ++ τext ⊧ A[⋆$x ↦ E][ℓ ↦ ℓ ⋆- ♯τext.length] <->
  ⋆ σ[⋆$x ↦ ⟦ E ⟧(σ, τ)], τ ++ τext ⊧ A[ℓ ↦ ℓ ⋆- ♯τext.length]) := by
  intros hE
  exact evaluation_remapping_trace_extension_minus_bool hE

lemma trace_sub_add_cancel :
  ⋆ σ, τ ⊧[ b ] A[ℓ ↦ ℓ ⋆- ♯1][ℓ ↦ ℓ ⋆+ ♯1] <->
  ⋆ σ, τ ⊧[ b ] A := by
  revert σ b
  induction A with
  | expression B =>
    intros σ b
    constructor <;> intros h <;>
    apply expression_inversion at h <;>
    apply expression_intro
    . rw [BooleanExpression.trace_sub_add_cancel] at h
      exact h
    . rw [BooleanExpression.trace_sub_add_cancel]
      exact h
  | negation A' ihA' =>
    intros σ b
    constructor <;> intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . normalize at h
      rw [ihA'] at h
      exact h
    . normalize
      rw [ihA']
      exact h
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    intros σ b
    constructor <;> intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hA₁, hA₂⟩ | ⟨rfl, (hA₁ | hA₂)⟩) <;>
    normalize at hA₁ <;>
    normalize at hA₂ <;>
    (try rw [ihA₁] at hA₁) <;>
    (try rw [ihA₂] at hA₂) <;>
    (try apply disjunction_intro_false) <;>
    normalize <;>
    (try rw [ihA₁]) <;>
    (try rw [ihA₂]) <;>
    (try exact hA₁) <;>
    (try exact hA₂) <;>
    (try exact disjunction_intro_left hA₁)
    (try exact disjunction_intro_right hA₂)
    . apply disjunction_intro_left
      rw [ihA₁]
      exact hA₁
    . apply disjunction_intro_right
      rw [ihA₂]
      exact hA₂
  | universal_quantification x A' ihA' =>
    intros σ b
    constructor <;> intros h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    apply universal_quantification_inversion at h <;>
    specialize h v'
    . normalize at h
      rw [ihA'] at h
      exact h
    . normalize
      rw [ihA']
      exact h
  | trace T E =>
    intros σ b
    constructor <;> intros h <;>
    apply trace_intro <;>
    apply trace_inversion at h
    . rw [TraceAssertion.trace_sub_add_cancel, NumericExpression.trace_sub_add_cancel] at h
      exact h
    . rw [TraceAssertion.trace_sub_add_cancel, NumericExpression.trace_sub_add_cancel]
      exact h

lemma equivalent_replacement {A : GeneralAssertion} {E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⟧(σ, τ) = ⟦ E₂ ⟧(σ, τ) ->
  E₁.containsLogicalVariables = false ->
  E₂.containsLogicalVariables = false ->
  (⋆ σ, τ ⊧[ b ] A[E₁ ↦ E₂] <-> ⋆ σ, τ ⊧[ b ] A) := by
  intros hE₁E₂ hE₁ hE₂
  revert σ b
  induction A with
  | expression B =>
    intros σ b hE₁E₂
    constructor <;>
    intros h <;>
    apply expression_inversion at h <;>
    apply expression_intro
    . rw [BooleanExpression.equivalent_replacement] at h ; rotate_left
      . exact hE₁E₂
      exact h
    . rw [BooleanExpression.equivalent_replacement] ; rotate_left
      . exact hE₁E₂
      exact h
  | negation B' ihB' =>
    intros σ b hE₁E₂
    constructor <;>
    intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . normalize at h
      rw [ihB'] at h ; rotate_left
      . exact hE₁E₂
      exact h
    . normalize
      rw [ihB'] ; rotate_left
      . exact hE₁E₂
      exact h
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    intros σ b hE₁E₂
    constructor <;>
    intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hA₁, hA₂⟩ | ⟨rfl, (hA₁ | hA₂)⟩) <;>
    (try normalize at hA₁) <;>
    (try normalize at hA₂) <;>
    (try rw [ihA₁] at hA₁ ; rotate_left ; exact hE₁E₂) <;>
    (try rw [ihA₂] at hA₂ ; rotate_left ; exact hE₁E₂) <;>
    (try apply disjunction_intro_false) <;>
    normalize <;>
    (try rw [ihA₁] ; rotate_left ; exact hE₁E₂) <;>
    (try rw [ihA₂] ; rotate_left ; exact hE₁E₂) <;>
    (try exact hA₁) <;>
    (try exact hA₂)
    . apply disjunction_intro_left
      exact hA₁
    . apply disjunction_intro_right
      exact hA₂
    . apply disjunction_intro_left
      rw [ihA₁] ; rotate_left
      . exact hE₁E₂
      exact hA₁
    . apply disjunction_intro_right
      rw [ihA₂] ; rotate_left
      . exact hE₁E₂
      exact hA₂
  | trace T E =>
    intros σ b hE₁E₂
    normalize
    constructor <;>
    intros h <;>
    apply trace_inversion at h <;>
    apply trace_intro
    . rw [NumericExpression.equivalent_replacement, TraceAssertion.equivalent_replacement] at h ; rotate_left
      . exact hE₁E₂
      . exact hE₁
      . exact hE₂
      . exact hE₁E₂
      exact h
    . rw [NumericExpression.equivalent_replacement, TraceAssertion.equivalent_replacement] ; rotate_left
      . exact hE₁E₂
      . exact hE₁
      . exact hE₂
      . exact hE₁E₂
      exact h
  | universal_quantification x A' ihA' =>
    intros σ b hE₁E₂
    constructor <;>
    intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihA'] at h ; rotate_left
      . rw [NumericExpression.logical_variable_independence, NumericExpression.logical_variable_independence] ; rotate_left
        . exact hE₂
        . exact hE₁
        exact hE₁E₂
      exact h
    . rw [ihA'] ; rotate_left
      . rw [NumericExpression.logical_variable_independence, NumericExpression.logical_variable_independence] ; rotate_left
        . exact hE₂
        . exact hE₁
        exact hE₁E₂
      exact h

lemma double_trace_replace {A : GeneralAssertion} {E₁ E₂ E₁' : NumericExpression} :
  ⟦ E₁[ℓ ↦ E₂] ⟧(σ, τ) = ⟦ E₁' ⟧(σ, τ) ->
  E₁.containsLogicalVariables = false ->
  E₂.containsLogicalVariables = false ->
  E₁'.containsLogicalVariables = false ->
  (⋆ σ, τ ⊧[ b ] A[ℓ ↦ E₁][ℓ ↦ E₂] <->
  ⋆ σ, τ ⊧[ b ] A[ℓ ↦ E₁']) := by
  intros hE₁' hE₁lv hE₂lv hE₁'lv
  revert σ b
  induction A with
  | expression B =>
    intros σ b hE₁'
    constructor <;>
    intros h <;>
    apply expression_inversion at h <;>
    apply expression_intro
    . rw [BooleanExpression.double_trace_replace] at h ; rotate_left
      . exact hE₁'
      exact h
    . rw [BooleanExpression.double_trace_replace] ; rotate_left
      . exact hE₁'
      exact h
  | negation A' ihA' =>
    intros σ b hE₁'
    constructor <;>
    intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro <;>
    normalize at h <;>
    specialize ihA' (σ := σ) (b := !b) hE₁' <;>
    normalize
    . rw [ihA'] at h
      exact h
    . rw [ihA']
      exact h
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    intros σ b hE₁'
    constructor <;>
    intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hA₁, hA₂⟩ | ⟨rfl, (hA₁ | hA₂)⟩) <;>
    (try normalize at hA₁) <;>
    (try normalize at hA₂) <;>
    (try rw [ihA₁] at hA₁ ; rotate_left ; exact hE₁') <;>
    (try rw [ihA₂] at hA₂ ; rotate_left ; exact hE₁') <;>
    (try normalize at hA₂) <;>
    (try apply disjunction_intro_false) <;>
    normalize <;>
    (try rw [ihA₁] ; rotate_left ; exact hE₁') <;>
    (try rw [ihA₂] ; rotate_left ; exact hE₁') <;>
    (try exact hA₁) <;>
    (try exact hA₂)
    . apply disjunction_intro_left
      exact hA₁
    . apply disjunction_intro_right
      exact hA₂
    . apply disjunction_intro_left
      rw [ihA₁] ; rotate_left
      . exact hE₁'
      exact hA₁
    . apply disjunction_intro_right
      rw [ihA₂] ; rotate_left
      . exact hE₁'
      exact hA₂
  | trace T E =>
    intros σ b hE₁'
    constructor <;>
    intros h <;>
    apply trace_inversion at h <;>
    apply trace_intro
    . rw [NumericExpression.double_trace_replace (E₁' := E₁'), TraceAssertion.double_trace_replace (E₁' := E₁')] at h ; rotate_left
      . exact hE₁'
      . exact hE₁lv
      . exact hE₂lv
      . exact hE₁'lv
      . exact hE₁'
      exact h
    . rw [NumericExpression.double_trace_replace (E₁' := E₁'), TraceAssertion.double_trace_replace (E₁' := E₁')] ; rotate_left
      . exact hE₁'
      . exact hE₁lv
      . exact hE₂lv
      . exact hE₁'lv
      . exact hE₁'
      exact h
  | universal_quantification x A' ihA' =>
    intros σ b hE₁'
    constructor <;>
    intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihA'] at h ; rotate_left
      . rw [NumericExpression.logical_state_independence, NumericExpression.logical_state_independence] ; rotate_left
        . exact hE₁'lv
        . apply NumericExpression.term_replacement_preserves_logical_variable_absence
          . exact hE₁lv
          . exact hE₂lv
        exact hE₁'
      exact h
    . rw [ihA'] ; rotate_left
      . rw [NumericExpression.logical_state_independence, NumericExpression.logical_state_independence] ; rotate_left
        . exact hE₁'lv
        . apply NumericExpression.term_replacement_preserves_logical_variable_absence
          . exact hE₁lv
          . exact hE₂lv
        exact hE₁'
      exact h
