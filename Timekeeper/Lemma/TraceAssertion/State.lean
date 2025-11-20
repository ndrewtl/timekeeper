import Timekeeper.Lemma.TraceAssertion.Introduction
import Timekeeper.Lemma.TraceAssertion.Inversion

namespace Timekeeper.TraceAssertion
open Models

lemma evaluation_remapping
  {E : NumericExpression} {x : VariableName} {T : TraceAssertion}:
  E.containsLogicalVariables = false ->
  (⋆ σ, τ, k ⊧ₜ[ b ] T[⋆$x ↦ E] <-> ⋆ σ[⋆$x ↦ ⟦ E ⟧(σ, τ)], τ, k ⊧ₜ[ b ] T) := by
  intros hE
  revert σ k b
  induction T with
  | top =>
    intros σ k b
    constructor <;>
    intros h <;>
    normalize at h <;>
    normalize <;>
    apply top_inversion at h <;>
    rcases h with rfl <;>
    exact top_intro
  | atomic Es =>
    intros σ k b
    . constructor <;> intros h
      . apply atomic_inversion_bool at h
        rcases h with ⟨hkbound, h⟩
        simp at h
        rw [<-NumericExpressionList.variable_replacement] at h
        apply atomic_intro
        normalize at h
        rw [NumericExpressionList.evaluation_remapping] at h
        exact h
      . apply atomic_inversion_bool at h
        rcases h with ⟨hkbound, h⟩
        simp at h
        rw [<-NumericExpression.eval] at h
        rw [<-Store.replacement] at h
        apply atomic_intro
        normalize
        normalize at h
        rw [NumericExpressionList.evaluation_remapping]
        exact h
  | negation T' ihT' =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . rw [<-variable_replacement] at h
      rw [ihT'] at h
      exact h
    . rw [<-variable_replacement]
      rw [ihT']
      exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b₃
    -- rcases (any_or (b₃ := b₃)) with ⟨b₁, b₂, rfl⟩
    constructor <;> intros h <;>
    apply disjunction_inversion_bool at h <;>

    rcases h with (⟨rfl, h₁, h₂⟩ | ⟨rfl, (h₁ | h₂)⟩)
    . rw [<-variable_replacement, ihT₁] at h₁
      rw [<-variable_replacement, ihT₂] at h₂
      exact disjunction_intro_false h₁ h₂
    . rw [<-variable_replacement, models_true, ihT₁] at h₁
      exact disjunction_intro_left h₁
    . rw [<-variable_replacement, models_true, ihT₂] at h₂
      exact disjunction_intro_right h₂
    . simp [replaceNumericExpression]
      repeat rw [<-variable_replacement]
      apply disjunction_intro_false
      . rw [ihT₁] ; exact h₁
      . rw [ihT₂] ; exact h₂
    . apply disjunction_intro_left
      rw [<-variable_replacement, ihT₁]
      exact h₁
    . apply disjunction_intro_right
      rw [<-variable_replacement, ihT₂]
      exact h₂
  | previous T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply previous_inversion_bool at h <;>
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩)
    . exact previous_intro_zero
    . rw [<-variable_replacement] at h
      rw [ihT'] at h
      exact previous_intro_succ h
    . simp [replaceNumericExpression]
      exact previous_intro_zero
    . apply previous_intro_succ
      rw [<-variable_replacement]
      rw [ihT']
      exact h
  | next T' ihT' =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply next_inversion_bool at h <;>
    apply next_intro
    . rw [<-variable_replacement] at h
      rw [ihT'] at h
      exact h
    . rw [<-variable_replacement]
      rw [ihT']
      exact h
  | since φ ψ ihφ ihψ =>
    intros σ k b
    revert b
    induction k with
    | zero =>
      intros b
      constructor <;> intros h
      . apply since_inversion_bool at h
        apply since_intro
        rcases b
        . repeat rw [<-variable_replacement] at h
          apply disjunction_inversion_false at h
          rcases h with ⟨hψ, hφφSψ⟩
          rw [ihψ] at hψ
          apply conjunction_inversion_false at hφφSψ

          apply disjunction_intro_false hψ
          . apply conjunction_intro_false
            rcases hφφSψ with (hφ | hφSψ)
            . left
              rw [ihφ] at hφ ; exact hφ
            . right ; exact previous_intro_zero
        . apply disjunction_inversion at h
          repeat rw [<-variable_replacement] at h

          rcases h with (hψ | hφφSψ)
          . rw [models_true, ihψ] at hψ
            exact disjunction_intro_left hψ
          . apply conjunction_inversion at hφφSψ
            rcases hφφSψ with ⟨hφ, hφSψ⟩
            apply previous_inversion at hφSψ
            rcases hφSψ with ⟨k', contr, _⟩
            contradiction
      . apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩)
        . simp [replaceNumericExpression]
          repeat rw [<-variable_replacement]
          apply since_intro
          apply disjunction_intro_false
          . rw [ihψ] ; exact hψ
          . apply conjunction_intro_false
            right ; exact previous_intro_zero
        . simp [replaceNumericExpression]
          repeat rw [<-variable_replacement]
          apply since_intro
          apply disjunction_intro_left
          rw [ihψ] ; exact hψ
        . simp [replaceNumericExpression]
          repeat rw [<-variable_replacement]
          apply since_intro
          apply disjunction_intro_right
          apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply conjunction_intro
          . rw [models_true, ihφ] ; exact hφ
          . apply previous_inversion_zero at hφSψ
            contradiction
    | succ k' ihk' =>
      intros b
      constructor <;> intros h <;>
      apply since_inversion_bool at h <;>
      apply since_intro
      . repeat rw [<-variable_replacement] at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩)
        . apply conjunction_inversion_false at hφφSψ
          rcases hφφSψ with (hφ | hφSψ)
          . apply disjunction_intro_false
            . rw [ihψ] at hψ
              exact hψ
            . apply conjunction_intro_false
              rw [ihφ] at hφ
              left ; exact hφ
          . -- Prepare hψ
            rw [ihψ] at hψ

            -- Prepare hφSψ
            apply previous_inversion_succ_bool at hφSψ
            specialize ihk' (b := false)
            simp [replaceNumericExpression] at ihk'
            repeat rw [<-variable_replacement] at ihk'
            rw [ihk'] at hφSψ
            rw [<-Store.replacement, <-NumericExpression.eval] at hφSψ

            apply disjunction_intro_false hψ
            apply conjunction_intro_false ; right
            apply previous_intro_succ
            exact hφSψ
        . rw [models_true, ihψ] at hψ
          apply disjunction_intro_left
          exact hψ
        . apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          rw [models_true, ihφ] at hφ

          specialize ihk' (b := true)
          simp [replaceNumericExpression] at ihk'
          repeat rw [<-variable_replacement] at ihk'

          apply previous_inversion_succ_bool at hφSψ
          rw [ihk'] at hφSψ
          rw [<-Store.replacement, <-NumericExpression.eval] at hφSψ

          apply disjunction_intro_right
          apply conjunction_intro hφ
          apply previous_intro_succ
          exact hφSψ
      . repeat rw [<-variable_replacement]
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩)
        . apply conjunction_inversion_false at hφφSψ
          rcases hφφSψ with (hφ | hφSψ)
          . apply disjunction_intro_false
            . rw [ihψ] ; exact hψ
            . apply conjunction_intro_false
              left
              rw [ihφ] ; exact hφ
          . apply disjunction_intro_false
            . rw [ihψ] ; exact hψ
            . apply conjunction_intro_false
              right
              apply previous_intro_succ

              specialize ihk' (b := false)
              simp [replaceNumericExpression] at ihk'
              repeat rw [<-variable_replacement] at ihk'
              rw [ihk']

              apply previous_inversion_succ_bool at hφSψ
              exact hφSψ

        . apply disjunction_intro_left
          rw [ihψ] ; exact hψ
        . apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihφ] ; exact hφ
          . apply previous_intro_succ
            specialize ihk' (b := true)
            simp [replaceNumericExpression] at ihk'
            repeat rw [<-variable_replacement] at ihk'
            rw [ihk']
            apply previous_inversion_succ_bool at hφSψ
            exact hφSψ
  | «until» φ ψ n ihφ ihψ =>
    induction n with
    | zero =>
      intros σ k b
      constructor <;> intros h
      . apply until_inversion_zero_bool at h
        repeat rw [<-variable_replacement] at h
        rw [ihψ] at h
        exact until_intro_zero h
      . apply until_inversion_zero_bool at h
        simp [replaceNumericExpression]
        repeat rw [<-variable_replacement]
        apply until_intro_zero
        rw [ihψ]
        exact h
    | succ n' ihn' =>
      intros σ k b
      constructor <;> intros h
      . apply until_inversion_succ_bool at h
        repeat rw [<-variable_replacement] at h
        apply disjunction_inversion_bool at h

        rcases h with (⟨rfl, hψ, hφφUψ⟩ | ⟨rfl, (hψ | hφφUψ)⟩)
        . rw [ihψ] at hψ
          apply until_intro_succ
          apply disjunction_intro_false hψ
          apply conjunction_intro_false
          apply conjunction_inversion_false at hφφUψ
          rcases hφφUψ with (hφ | hφUψ)
          . left ; rw [ihφ] at hφ ; exact hφ
          . right
            apply next_inversion_bool at hφUψ
            specialize ihn' (b := false) (k := k + 1) (σ := σ)
            normalize at ihn'
            rw [ihn'] at hφUψ
            apply next_intro
            exact hφUψ
        . apply until_intro_succ
          apply disjunction_intro_left
          rw [models_true, ihψ] at hψ
          exact hψ
        . apply conjunction_inversion at hφφUψ
          rcases hφφUψ with ⟨hφ, hφUψ⟩
          rw [models_true, ihφ] at hφ
          apply next_inversion at hφUψ
          rw [models_true] at hφUψ

          specialize ihn' (b := true) (k := k + 1) (σ := σ)
          simp [replaceNumericExpression] at ihn'
          repeat rw [<-variable_replacement] at ihn'
          rw [ihn'] at hφUψ

          apply until_intro_succ
          apply disjunction_intro_right
          apply conjunction_intro hφ
          apply next_intro
          exact hφUψ
      . simp [replaceNumericExpression]
        repeat rw [<-variable_replacement]
        apply until_intro_succ
        apply until_inversion_succ_bool at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφUψ⟩ | ⟨rfl, (hψ | hφφUψ)⟩)
        . apply conjunction_inversion_false at hφφUψ
          rcases  hφφUψ with (hφ | hφUψ)
          . apply disjunction_intro_false
            . rw [ihψ] ; exact hψ
            . apply conjunction_intro_false
              left ; rw [ihφ] ; exact hφ
          . apply disjunction_intro_false
            . rw [ihψ] ; exact hψ
            . apply conjunction_intro_false
              right
              apply next_intro
              specialize ihn' (b := false) (k := k + 1) (σ := σ)
              simp [replaceNumericExpression] at ihn'
              repeat rw [<-variable_replacement] at ihn'
              rw [ihn']
              exact next_inversion_bool hφUψ
        . apply disjunction_intro_left
          rw [ihψ] ; exact hψ
        . apply disjunction_intro_right
          apply conjunction_inversion at hφφUψ
          rcases hφφUψ with ⟨hφ, hφUψ⟩
          apply conjunction_intro
          . rw [models_true, ihφ] ; exact hφ
          . specialize ihn' (b := true) (k := k + 1) (σ := σ)
            simp [replaceNumericExpression] at ihn'
            repeat rw [<-variable_replacement] at ihn'
            apply next_intro
            rw [ihn']
            exact next_inversion_bool hφUψ
  | function F Es ihF =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply function_inversion_bool at h <;>
    normalize at h <;>
    apply function_intro <;>
    normalize
    . rw [NumericExpressionList.evaluation_remapping] at h
      rw [ihF] at h
      exact h
    . rw [NumericExpressionList.evaluation_remapping]
      rw [ihF]
      exact h
  | universal_quantification x' T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihT'] at h
      rw [NumericExpression.logical_variable_independence] at h ; rotate_left
      . exact hE
      rw [Store.replacement_different_variables_reordering] ; rotate_left
      . simp
      exact h
    . rw [ihT']
      rw [NumericExpression.logical_variable_independence] ; rotate_left
      . exact hE
      rw [Store.replacement_different_variables_reordering] at h ; rotate_left
      . simp
      exact h

lemma store_independence {T : TraceAssertion} :
  ¬(T.containsVariables) ->
  (⋆ σ₁, τ, k ⊧ₜ[ b ] T <-> ⋆ σ₂, τ, k ⊧ₜ[ b ] T) := by
  revert σ₁ σ₂ k b
  induction T with
  | top =>
    intros σ₁ σ₂ k b hcont
    constructor <;>
    intros h <;>
    normalize at h <;>
    apply top_inversion at h <;>
    rcases h with rfl <;>
    exact top_intro
  | atomic Es =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    . constructor <;> intros h
      . apply atomic_inversion_bool at h
        rcases h with ⟨hkbound, h⟩
        simp at h
        normalize at h
        rw [NumericExpressionList.store_independence (σ₁ := σ₁) (σ₂ := σ₂)] at h ; rotate_left
        . simp [NumericExpressionList.containsVariables] ; exact hcont
        apply atomic_intro
        . exact h
      . apply atomic_inversion_bool at h
        rcases h with ⟨hkbound, h⟩
        simp at h
        normalize at h
        apply atomic_intro
        . rw [NumericExpressionList.store_independence (σ₁ := σ₁) (σ₂ := σ₂)] ; rotate_left
          . simp [NumericExpressionList.containsVariables] ; exact hcont
          exact h
  | negation T' ihT' =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    constructor <;>
    intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . rw [ihT' (σ₁ := σ₁) (σ₂ := σ₂)] at h ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
    . rw [ihT' (σ₁ := σ₁) (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hcont₁, hcont₂⟩
    constructor <;> intros h <;>
    apply disjunction_inversion_bool at h <;>

    rcases h with (⟨rfl, h₁, h₂⟩ | ⟨rfl, (h₁ | h₂)⟩)
    . rw [ihT₁ (σ₁ := σ₁) (σ₂ := σ₂)] at h₁ ; rotate_left
      . simp [containsVariables] ; exact hcont₁
      rw [ihT₂ (σ₁ := σ₁) (σ₂ := σ₂)] at h₂ ; rotate_left
      . simp [containsVariables] ; exact hcont₂
      exact disjunction_intro_false h₁ h₂
    . rw [models_true, ihT₁ (σ₁ := σ₁) (σ₂ := σ₂)] at h₁ ; rotate_left
      . simp [containsVariables] ; exact hcont₁
      exact disjunction_intro_left h₁
    . rw [models_true, ihT₂ (σ₁ := σ₁) (σ₂ := σ₂)] at h₂ ; rotate_left
      . simp [containsVariables] ; exact hcont₂
      exact disjunction_intro_right h₂
    . apply disjunction_intro_false
      . rw [ihT₁ (σ₁ := σ₁) (σ₂ := σ₂)] ; rotate_left
        . simp [containsVariables] ; exact hcont₁
        exact h₁
      . rw [ihT₂ (σ₁ := σ₁) (σ₂ := σ₂)] ; rotate_left
        . simp [containsVariables] ; exact hcont₂
        exact h₂
    . apply disjunction_intro_left
      rw [ihT₁ (σ₁ := σ₁) (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont₁
      exact h₁
    . apply disjunction_intro_right
      rw [ihT₂ (σ₁ := σ₁) (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont₂
      exact h₂
  | previous T' ihT' =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    constructor <;> intros h <;>
    apply previous_inversion_bool at h <;>
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩)
    . exact previous_intro_zero
    . rw [ihT' (σ₁ := σ₁) (σ₂ := σ₂)] at h ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact previous_intro_succ h
    . exact previous_intro_zero
    . apply previous_intro_succ
      rw [ihT' (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
  | next T' ihT' =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    constructor <;>
    intros h <;>
    apply next_inversion_bool at h <;>
    apply next_intro
    . rw [ihT' (σ₂ := σ₂)] at h ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
    . rw [ihT' (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
  | since T₁ T₂ ihT₁ ihT₂ =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hcont₁, hcont₂⟩
    constructor <;>
    intros h <;>
    apply since_inversion_bool at h <;>
    apply since_intro
    . normalize at h
      induction k with
      | zero =>
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩)
        . apply conjunction_inversion_false at hT₁ST₂
          rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
          . rw [ihT₂ (σ₂ := σ₂)] at hT₂ ; rotate_left
            . simp [containsVariables] ; exact hcont₂
            apply disjunction_intro_false
            . exact hT₂
            . apply conjunction_intro_false ; left
              rw [ihT₁ (σ₂ := σ₂)] at hT₁ ; rotate_left
              . simp [containsVariables] ; exact hcont₁
              exact hT₁
          . apply disjunction_intro_false
            . rw [ihT₂ (σ₂ := σ₂)] at hT₂ ; rotate_left
              . simp [containsVariables] ; exact hcont₂
              exact hT₂
            . apply conjunction_intro_false ; right
              exact previous_intro_zero
        . rw [models_true, ihT₂ (σ₂ := σ₂)] at hT₂ ; rotate_left
          . simp [containsVariables] ; exact hcont₂
          apply disjunction_intro_left
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply previous_inversion_zero at hT₁ST₂
          contradiction
      | succ k' ihk' =>
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂ (σ₂ := σ₂)] at hT₂ ; rotate_left
            . simp [containsVariables] ; exact hcont₂
            exact hT₂
          . apply conjunction_intro_false
            apply conjunction_inversion_false at hT₁ST₂
            rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
            . rw [ihT₁ (σ₂ := σ₂)] at hT₁ ; rotate_left
              . simp [containsVariables] ; exact hcont₁
              left ; exact hT₁
            . right
              apply previous_intro_succ
              apply since_intro
              apply ihk'
              apply previous_inversion_succ_bool at hT₁ST₂
              apply since_inversion_bool at hT₁ST₂
              exact hT₁ST₂
        . rw [models_true, ihT₂ (σ₂ := σ₂)] at hT₂ ; rotate_left
          . simp [containsVariables] ; exact hcont₂
          apply disjunction_intro_left
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply previous_inversion_succ at hT₁ST₂
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁ (σ₂ := σ₂)] at hT₁ ; rotate_left
            . simp [containsVariables] ; exact hcont₁
            exact hT₁
          . apply previous_intro_succ
            apply since_intro
            apply ihk'
            apply since_inversion at hT₁ST₂
            apply disjunction_inversion at hT₁ST₂
            rcases hT₁ST₂ with (hT₂ | hT₁ST₂)
            . apply disjunction_intro_left
              exact hT₂
            . apply disjunction_intro_right
              exact hT₁ST₂
    . normalize at h
      induction k with
      | zero =>
        normalize
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩)
        . apply conjunction_inversion_false at hT₁ST₂
          rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
          . apply disjunction_intro_false
            . rw [ihT₂ (σ₂ := σ₂)] ; rotate_left
              . simp [containsVariables] ; exact hcont₂
              exact hT₂
            . apply conjunction_intro_false ; left
              rw [ihT₁ (σ₂ := σ₂)] ; rotate_left
              . simp [containsVariables] ; exact hcont₁
              exact hT₁
          . apply disjunction_intro_false
            . rw [ihT₂ (σ₂ := σ₂)] ; rotate_left
              . simp [containsVariables] ; exact hcont₂
              exact hT₂
            . apply conjunction_intro_false ; right
              exact previous_intro_zero
        . apply disjunction_intro_left
          rw [ihT₂ (σ₂ := σ₂)] ; rotate_left
          . simp [containsVariables] ; exact hcont₂
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply previous_inversion_zero at hT₁ST₂
          contradiction
      | succ k' ihk' =>
        apply disjunction_inversion_bool at h
        normalize
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂ (σ₂ := σ₂)] ; rotate_left
            . simp [containsVariables] ; exact hcont₂
            exact hT₂
          . apply conjunction_intro_false
            apply conjunction_inversion_false at hT₁ST₂
            rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
            . rw [ihT₁ (σ₂ := σ₂)] ; rotate_left
              . simp [containsVariables] ; exact hcont₁
              left ; exact hT₁
            . right
              apply previous_intro_succ
              apply since_intro
              apply ihk'
              apply previous_inversion_succ_bool at hT₁ST₂
              apply since_inversion_bool at hT₁ST₂
              exact hT₁ST₂
        . apply disjunction_intro_left
          rw [ihT₂ (σ₂ := σ₂)] ; rotate_left
          . simp [containsVariables] ; exact hcont₂
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply previous_inversion_succ at hT₁ST₂
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁ (σ₂ := σ₂)] ; rotate_left
            . simp [containsVariables] ; exact hcont₁
            exact hT₁
          . apply previous_intro_succ
            apply since_intro
            apply ihk'
            apply since_inversion at hT₁ST₂
            apply disjunction_inversion at hT₁ST₂
            rcases hT₁ST₂ with (hT₂ | hT₁ST₂)
            . apply disjunction_intro_left
              exact hT₂
            . apply disjunction_intro_right
              exact hT₁ST₂
  | «until» T₁ T₂ n ihT₁ ihT₂ =>
    induction n with
    | zero =>
      intros σ₁ k b σ₂ hcont
      simp [containsVariables, numericExpressionPredicate] at hcont
      rcases hcont with ⟨hcont₁, hcont₂⟩
      constructor <;>
      intros h
      . normalize at h
        apply until_inversion_zero_bool at h
        apply until_intro_zero
        rw [ihT₂ (σ₂ := σ₂)] at h ; rotate_left
        . simp [containsVariables] ; exact hcont₂
        exact h
      . apply until_inversion_zero_bool at h
        apply until_intro_zero
        rw [ihT₂ (σ₂ := σ₂)] ; rotate_left
        . simp [containsVariables] ; exact hcont₂
        exact h
    | succ n' ihn' =>
      intros σ₁ k b σ₂ hcont
      simp [containsVariables, numericExpressionPredicate] at hcont
      rcases hcont with ⟨hcont₁, hcont₂⟩
      constructor <;>
      intros h
      . normalize at h
        apply until_inversion_succ_bool at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂ (σ₂ := σ₂)] at hT₂ ; rotate_left
            . simp [containsVariables] ; exact hcont₂
            exact hT₂
          . apply conjunction_inversion_false at hT₁UT₂
            apply conjunction_intro_false
            rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
            . left
              rw [ihT₁ (σ₂ := σ₂)] at hT₁ ; rotate_left
              . simp [containsVariables] ; exact hcont₁
              exact hT₁
            . apply next_inversion_bool at hT₁UT₂
              specialize ihn' (σ₁ := σ₁) (σ₂ := σ₂) (k := k + 1) (b := false) _
              . simp [containsVariables, numericExpressionPredicate]
                exact ⟨hcont₁, hcont₂⟩
              rw [ihn'] at hT₁UT₂
              right
              apply next_intro
              exact hT₁UT₂
        . apply disjunction_intro_left
          rw [models_true, ihT₂ (σ₂ := σ₂)] at hT₂ ; rotate_left
          . simp [containsVariables] ; exact hcont₂
          exact hT₂
        . apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁ (σ₂ := σ₂)] at hT₁ ; rotate_left
            . simp [containsVariables] ; exact hcont₁
            exact hT₁
          . apply next_inversion at hT₁UT₂
            specialize ihn' (σ₁ := σ₁) (σ₂:= σ₂) (k := k + 1) (b := true) _
            . simp [containsVariables, numericExpressionPredicate]
              exact ⟨hcont₁, hcont₂⟩
            rw [models_true, ihn'] at hT₁UT₂
            apply next_intro
            exact hT₁UT₂
      . apply until_inversion_succ_bool at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂ (σ₂:= σ₂)] ; rotate_left
            . simp [containsVariables] ; exact hcont₂
            exact hT₂
          . apply conjunction_inversion_false at hT₁UT₂
            apply conjunction_intro_false
            rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
            . left
              rw [ihT₁ (σ₂:= σ₂)] ; rotate_left
              . simp [containsVariables] ; exact hcont₁
              exact hT₁
            . apply next_inversion_bool at hT₁UT₂
              specialize ihn' (σ₁ := σ₁) (σ₂ := σ₂) (k := k + 1) (b := false) _
              . simp [containsVariables, numericExpressionPredicate]
                exact ⟨hcont₁, hcont₂⟩
              right
              apply next_intro
              rw [ihn']
              exact hT₁UT₂
        . apply disjunction_intro_left
          rw [ihT₂ (σ₂ := σ₂)] ; rotate_left
          . simp [containsVariables] ; exact hcont₂
          exact hT₂
        . apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁ (σ₂ := σ₂)] ; rotate_left
            . simp [containsVariables] ; exact hcont₁
            exact hT₁
          . apply next_inversion at hT₁UT₂
            specialize ihn' (σ₁ := σ₁) (σ₂ := σ₂) (k := k + 1) (b := true) _
            . simp [containsVariables, numericExpressionPredicate]
              exact ⟨hcont₁, hcont₂⟩
            apply next_intro
            rw [ihn']
            exact hT₁UT₂
  | function F Es ihF =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hcontEs, hcontF⟩
    constructor <;>
    intros h <;>
    apply function_inversion_bool at h <;>
    normalize at h <;>
    apply function_intro <;>
    normalize
    . rw [NumericExpressionList.store_independence (σ₂ := σ₂), ihF (σ₂ := σ₂)] at h ; rotate_left
      . simp [containsVariables] ; exact hcontF σ₂ τ
      . simp [NumericExpressionList.containsVariables] ; exact hcontEs
      exact h
    . rw [NumericExpressionList.store_independence (σ₂ := σ₂), ihF (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcontF σ₂ τ
      . simp [NumericExpressionList.containsVariables] ; exact hcontEs
      exact h
  | universal_quantification x' T' ihT' =>
    intros σ₁ k b σ₂ hcont
    simp [containsVariables] at hcont
    constructor <;> intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihT' (σ₂ := σ₂[⋆^x' ↦ v'])] at h ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
    . rw [ihT' (σ₂ := σ₂[⋆^x' ↦ v'])] ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
