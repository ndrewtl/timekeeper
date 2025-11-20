import Timekeeper.Tactics
import Timekeeper.Lemma.TraceAssertion.Inversion
import Timekeeper.Lemma.TraceAssertion.Introduction
import Timekeeper.Lemma.TraceAssertion.Definiteness
import Timekeeper.Lemma.TraceAssertion.Syntax

namespace Timekeeper.TraceAssertion
open Models

lemma trace_subtraction_replacement {T : TraceAssertion} :
  ⋆ σ, τ, k ⊧ₜ[ b ] T[ℓ ↦ (ℓ ⋆- ♯p)][ℓ ↦ (ℓ ⋆- ♯q)] <->
  ⋆ σ, τ, k ⊧ₜ[ b ] T[ℓ ↦ ℓ ⋆- ♯(p + q)] := by
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
    constructor <;> intros h <;>
    apply atomic_inversion_bool at h <;>
    rcases h with ⟨hkbound, h⟩ <;>
    simp at h <;>
    apply atomic_intro
    . normalize at h
      rw [NumericExpressionList.trace_subtraction_replacement] at h
      exact h
    . rw [NumericExpressionList.trace_subtraction_replacement]
      exact h
  | negation T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . repeat rw [<-numeric_replacement] at h
      rw [ihT'] at h
      exact h
    . repeat rw [<-numeric_replacement]
      rw [ihT']
      exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b
    simp [replaceNumericExpression]
    repeat rw [<-numeric_replacement]
    constructor <;> intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩) <;>
    (try normalize at hT₁) <;>
    (try normalize at hT₂) <;>
    normalize
    . apply disjunction_intro_false
      . rw [ihT₁] at hT₁ ; exact hT₁
      . rw [ihT₂] at hT₂ ; exact hT₂
    . rw [ihT₁] at hT₁
      apply disjunction_intro_left hT₁
    . rw [ihT₂] at hT₂
      apply disjunction_intro_right hT₂
    . apply disjunction_intro_false
      . rw [ihT₁] ; exact hT₁
      . rw [ihT₂] ; exact hT₂
    . apply disjunction_intro_left
      rw [ihT₁] ; exact hT₁
    . apply disjunction_intro_right
      rw [ihT₂] ; exact hT₂
  | previous T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply previous_inversion_bool at h <;>
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩)
    . exact previous_intro_zero
    . repeat rw [<-numeric_replacement] at h
      apply previous_intro_succ
      rw [<-numeric_replacement]
      rw [ihT'] at h
      exact h
    . exact previous_intro_zero
    . apply previous_intro_succ
      repeat rw [<-numeric_replacement]
      rw [ihT']
      exact h
  | next T' ihT' =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply next_inversion_bool at h <;>
    apply next_intro
    . repeat rw [<-numeric_replacement] at h
      rw [ihT'] at h
      exact h
    . repeat rw [<-numeric_replacement]
      rw [ihT']
      exact h
  | since φ ψ ihφ ihψ =>
    intros σ k
    induction k with
    | zero =>
      intros b
      normalize
      constructor <;> intros h
      . apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩)
        . rw [ihψ] at hψ
          apply since_intro
          apply disjunction_intro_false hψ
          apply conjunction_inversion_false at hφφSψ
          apply conjunction_intro_false
          rcases hφφSψ with (hφ | hφSψ)
          . rw [ihφ] at hφ
            left ; exact hφ
          . right ; exact previous_intro_zero
        . normalize at hψ ; rw [ihψ] at hψ
          apply since_intro
          apply disjunction_intro_left
          exact hψ
        . apply conjunction_inversion at hφφSψ
          normalize at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply previous_inversion_zero at hφSψ
          contradiction
      . apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        apply since_intro
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩)
        . apply disjunction_intro_false
          . rw [ihψ] ; exact hψ
          . apply conjunction_intro_false
            right ; exact previous_intro_zero
        . apply disjunction_intro_left
          rw [ihψ] ; exact hψ
        . apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply previous_inversion_zero at hφSψ
          contradiction
    | succ k' ihk' =>
      intros b
      constructor <;> intros h
      . simp [replaceNumericExpression] at h
        repeat rw [<-numeric_replacement] at h
        apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩) <;>
        (try normalize at hψ) <;>
        (try normalize at hφφSψ)
        . rw [ihψ] at hψ
          simp [replaceNumericExpression]
          repeat rw [<-numeric_replacement]
          apply conjunction_inversion_false at hφφSψ
          apply since_intro
          rcases hφφSψ with (hφ | hφSψ)
          . rw [ihφ] at hφ
            apply disjunction_intro_false hψ
            apply conjunction_intro_false
            left
            exact hφ
          . apply previous_inversion_succ_bool at hφSψ
            specialize ihk' (b := false)
            normalize at ihk'
            rw [ihk'] at hφSψ
            apply disjunction_intro_false
            . exact hψ
            . apply conjunction_intro_false
              right
              exact previous_intro_succ hφSψ
        . rw [ihψ] at hψ
          simp [replaceNumericExpression]
          apply since_intro
          apply disjunction_intro_left
          exact hψ
        . apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          rw [models_true, ihφ] at hφ
          apply previous_inversion at hφSψ
          rcases hφSψ with ⟨k', ⟨⟩, hφSψ⟩
          specialize ihk' (b := true)
          normalize at ihk'
          rw [models_true] at hφSψ
          rw [ihk'] at hφSψ
          simp [replaceNumericExpression]
          repeat rw [<-numeric_replacement]
          apply since_intro
          apply disjunction_intro_right
          apply conjunction_intro
          . exact hφ
          . apply previous_intro_succ
            exact hφSψ
      . normalize at h
        apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        normalize
        apply since_intro
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
              normalize at ihk'
              rw [ihk']
              exact previous_inversion_succ_bool hφSψ
        . apply disjunction_intro_left
          rw [ihψ] ; exact hψ
        . apply disjunction_intro_right
          apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply conjunction_intro
          . normalize ; rw [ihφ] ; exact hφ
          . apply previous_inversion at hφSψ
            rcases hφSψ with ⟨k', ⟨⟩, hφSψ⟩
            apply previous_intro_succ
            specialize ihk' (b := true)
            normalize at ihk'
            rw [ihk']
            exact hφSψ
  | «until» φ ψ n ihφ ihψ =>
    induction n with
    | zero =>
      intros σ k b
      normalize
      constructor <;> intros h <;>
      apply until_inversion_zero_bool at h
      . rw [ihψ] at h
        exact until_intro_zero h
      . apply until_intro_zero
        rw [ihψ] ; exact h
    | succ n' ihn' =>
      intros σ k b
      normalize
      constructor <;> intros h <;>
      apply until_inversion_succ_bool at h <;>
      apply disjunction_inversion_bool at h <;>
      rcases h with (⟨rfl, hψ, hφφUψ⟩ | ⟨rfl, (hψ | hφφUψ)⟩) <;>
      (try apply conjunction_inversion_false at hφφUψ) <;>
      (try apply conjunction_inversion at hφφUψ) <;>
      (try rcases hφφUψ with (hφ | hφUψ)) <;>
      (try rcases hφφUψ with ⟨hφ, hφUψ⟩) <;>
      (try normalize at hφ) <;>
      (try normalize at hψ) <;>
      (try rw [ihφ] at hφ) <;>
      (try rw [ihψ] at hψ) <;>
      (try apply next_inversion_bool at hφUψ) <;>
      apply until_intro_succ <;>
      (try apply disjunction_intro_false) <;>
      (try apply conjunction_intro_false) <;>
      normalize <;>
      (try rw [ihφ]) <;>
      (try rw [ihψ]) <;>
      normalize
      . exact hψ
      . left ; exact hφ
      . exact hψ
      . right
        specialize ihn' (b := false) (k := k + 1) (σ := σ)
        normalize at ihn'
        apply next_intro
        rw [ihn'] at hφUψ
        exact hφUψ
      . exact disjunction_intro_left hψ
      . apply disjunction_intro_right
        specialize ihn' (b := true) (k := k + 1) (σ := σ)
        normalize at ihn'
        rw [ihn'] at hφUψ
        apply conjunction_intro hφ
        exact next_intro hφUψ
      . exact hψ
      . left ; exact hφ
      . exact hψ
      . right
        apply next_intro
        specialize ihn' (b := false) (k := k + 1) (σ := σ)
        normalize at ihn'
        rw [ihn']
        exact hφUψ
      . apply disjunction_intro_left
        rw [ihψ] ; exact hψ
      . apply disjunction_intro_right
        apply conjunction_intro
        . normalize
          rw [ihφ] ; exact hφ
        . apply next_intro
          specialize ihn' (b := true) (k := k + 1) (σ := σ)
          normalize at ihn'
          rw [ihn']
          exact hφUψ
  | function F Es ihF =>
    intros σ k b
    constructor <;> intros h <;>
    apply function_inversion_bool at h <;>
    apply function_intro <;>
    normalize at h <;>
    normalize
    . rw [NumericExpressionList.trace_subtraction_replacement] at h
      rw [ihF] at h
      exact h
    . rw [NumericExpressionList.trace_subtraction_replacement]
      rw [ihF]
      exact h
  | universal_quantification x T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihT'] at h
      exact h
    . rw [ihT']
      exact h

lemma evaluation_remapping_trace_extension_minus {T : TraceAssertion} {E : NumericExpression} :
  E.containsLogicalVariables = false ->
  (⋆ σ, τ ++ τext, k ⊧ₜ[ b ] T[⋆$x ↦ E][ℓ ↦ ℓ ⋆- ♯τext.length] <->
  ⋆ σ[⋆$x ↦ ⟦ E ⟧(σ, τ)] , τ ++ τext, k ⊧ₜ[ b ] T[ℓ ↦ ℓ ⋆- ♯τext.length]) := by
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
    constructor <;> intros h <;>
    apply atomic_inversion_bool at h <;>
    rcases h with ⟨hkbound, h⟩ <;>
    apply atomic_intro
    . rw [NumericExpressionList.numeric_replacement, NumericExpressionList.numeric_replacement, <-NumericExpressionList.variable_replacement, <-NumericExpressionList.numeric_replacement] at h
      rw [NumericExpressionList.evaluation_remapping_trace_extension_minus] at h
      exact h
    . rw [NumericExpressionList.numeric_replacement, NumericExpressionList.numeric_replacement, <-NumericExpressionList.variable_replacement, <-NumericExpressionList.numeric_replacement]
      rw [NumericExpressionList.evaluation_remapping_trace_extension_minus]
      exact h
  | negation T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . normalize at h
      rw [ihT'] at h
      exact h
    . normalize
      rw [ihT']
      exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b
    simp [replaceNumericExpression]
    repeat rw [<-numeric_replacement]
    constructor <;> intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩) <;>
    (try normalize at hT₁) <;>
    (try normalize at hT₂) <;>
    (try rw [ihT₁] at hT₁) <;>
    (try rw [ihT₂] at hT₂) <;>
    normalize
    . apply disjunction_intro_false
      . exact hT₁
      . exact hT₂
    . apply disjunction_intro_left hT₁
    . apply disjunction_intro_right hT₂
    . apply disjunction_intro_false
      . rw [ihT₁] ; exact hT₁
      . rw [ihT₂] ; exact hT₂
    . apply disjunction_intro_left
      rw [ihT₁] ; exact hT₁
    . apply disjunction_intro_right
      rw [ihT₂] ; exact hT₂
  | previous T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply previous_inversion_bool at h <;>
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩) <;>
    normalize at h
    . exact previous_intro_zero
    . apply previous_intro_succ
      normalize
      rw [ihT'] at h
      exact h
    . exact previous_intro_zero
    . apply previous_intro_succ
      normalize
      rw [ihT']
      exact h
  | next T' ihT' =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply next_inversion_bool at h <;>
    apply next_intro
    . normalize at h
      rw [ihT'] at h
      exact h
    . normalize
      rw [ihT']
      exact h
  | since φ ψ ihφ ihψ =>
    intros σ k
    induction k with
    | zero =>
      intros b
      normalize
      constructor <;> intros h
      . apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩)
        . rw [ihψ] at hψ
          apply since_intro
          apply disjunction_intro_false hψ
          apply conjunction_inversion_false at hφφSψ
          apply conjunction_intro_false
          rcases hφφSψ with (hφ | hφSψ)
          . rw [ihφ] at hφ
            left ; exact hφ
          . right ; exact previous_intro_zero
        . normalize at hψ ; rw [ihψ] at hψ
          apply since_intro
          apply disjunction_intro_left
          exact hψ
        . apply conjunction_inversion at hφφSψ
          normalize at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply previous_inversion_zero at hφSψ
          contradiction
      . apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        apply since_intro
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩)
        . apply disjunction_intro_false
          . rw [ihψ] ; exact hψ
          . apply conjunction_intro_false
            right ; exact previous_intro_zero
        . apply disjunction_intro_left
          rw [ihψ] ; exact hψ
        . apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply previous_inversion_zero at hφSψ
          contradiction
    | succ k' ihk' =>
      intros b
      constructor <;> intros h
      . simp [replaceNumericExpression] at h
        repeat rw [<-numeric_replacement] at h
        apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hψ, hφφSψ⟩ | ⟨rfl, (hψ | hφφSψ)⟩) <;>
        (try normalize at hψ)
        . rw [ihψ] at hψ
          simp [replaceNumericExpression]
          repeat rw [<-numeric_replacement]
          apply conjunction_inversion_false at hφφSψ
          apply since_intro
          rcases hφφSψ with (hφ | hφSψ)
          . normalize at hφ
            rw [ihφ] at hφ
            apply disjunction_intro_false hψ
            apply conjunction_intro_false
            left
            exact hφ
          . apply previous_inversion_succ_bool at hφSψ
            specialize ihk' (b := false)
            simp [replaceNumericExpression] at ihk'
            repeat rw [<-numeric_replacement] at ihk'
            rw [ihk'] at hφSψ
            apply disjunction_intro_false
            . exact hψ
            . apply conjunction_intro_false
              right
              exact previous_intro_succ hφSψ
        . rw [ihψ] at hψ
          simp [replaceNumericExpression]
          apply since_intro
          apply disjunction_intro_left
          exact hψ
        . apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          normalize at hφ
          rw [ihφ] at hφ
          apply previous_inversion at hφSψ
          rcases hφSψ with ⟨k', ⟨⟩, hφSψ⟩
          specialize ihk' (b := true)
          simp [replaceNumericExpression] at ihk'
          repeat rw [<-numeric_replacement] at ihk'
          rw [models_true, ihk'] at hφSψ
          simp [replaceNumericExpression]
          repeat rw [<-numeric_replacement]
          apply since_intro
          apply disjunction_intro_right
          apply conjunction_intro
          . exact hφ
          . apply previous_intro_succ
            exact hφSψ
      . normalize at h
        apply since_inversion_bool at h
        apply disjunction_inversion_bool at h
        normalize
        apply since_intro
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
              normalize at ihk'
              rw [ihk']
              exact previous_inversion_succ_bool hφSψ
        . apply disjunction_intro_left
          rw [ihψ] ; exact hψ
        . apply disjunction_intro_right
          apply conjunction_inversion at hφφSψ
          rcases hφφSψ with ⟨hφ, hφSψ⟩
          apply conjunction_intro
          . normalize ; rw [ihφ] ; exact hφ
          . apply previous_inversion at hφSψ
            rcases hφSψ with ⟨k', ⟨⟩, hφSψ⟩
            apply previous_intro_succ
            specialize ihk' (b := true)
            normalize at ihk'
            rw [ihk']
            exact hφSψ
  | «until» φ ψ n ihφ ihψ =>
    induction n with
    | zero =>
      intros σ k b
      normalize
      constructor <;> intros h <;>
      apply until_inversion_zero_bool at h
      . rw [ihψ] at h
        exact until_intro_zero h
      . apply until_intro_zero
        rw [ihψ] ; exact h
    | succ n' ihn' =>
      intros σ k b
      normalize
      constructor <;> intros h <;>
      apply until_inversion_succ_bool at h <;>
      apply disjunction_inversion_bool at h <;>
      rcases h with (⟨rfl, hψ, hφφUψ⟩ | ⟨rfl, (hψ | hφφUψ)⟩) <;>
      (try apply conjunction_inversion_false at hφφUψ) <;>
      (try apply conjunction_inversion at hφφUψ) <;>
      (try rcases hφφUψ with (hφ | hφUψ)) <;>
      (try rcases hφφUψ with ⟨hφ, hφUψ⟩) <;>
      (try normalize at hφ) <;>
      (try normalize at hψ) <;>
      (try rw [ihφ] at hφ) <;>
      (try rw [ihψ] at hψ) <;>
      (try apply next_inversion_bool at hφUψ) <;>
      apply until_intro_succ <;>
      (try apply disjunction_intro_false) <;>
      (try apply conjunction_intro_false) <;>
      normalize <;>
      (try rw [ihφ]) <;>
      (try rw [ihψ]) <;>
      normalize
      . exact hψ
      . left ; exact hφ
      . exact hψ
      . right
        specialize ihn' (b := false) (k := k + 1) (σ := σ)
        normalize at ihn'
        apply next_intro
        rw [ihn'] at hφUψ
        exact hφUψ
      . exact disjunction_intro_left hψ
      . apply disjunction_intro_right
        specialize ihn' (b := true) (k := k + 1) (σ := σ)
        normalize at ihn'
        rw [ihn'] at hφUψ
        apply conjunction_intro hφ
        exact next_intro hφUψ
      . exact hψ
      . left ; exact hφ
      . exact hψ
      . right
        apply next_intro
        specialize ihn' (b := false) (k := k + 1) (σ := σ)
        normalize at ihn'
        rw [ihn']
        exact hφUψ
      . apply disjunction_intro_left
        rw [ihψ] ; exact hψ
      . apply disjunction_intro_right
        apply conjunction_intro
        . normalize
          rw [ihφ] ; exact hφ
        . apply next_intro
          specialize ihn' (b := true) (k := k + 1) (σ := σ)
          normalize at ihn'
          rw [ihn']
          exact hφUψ
  | function F Es ihF =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply function_inversion_bool at h <;>
    normalize at h <;>
    apply function_intro <;>
    normalize
    . rw [NumericExpressionList.evaluation_remapping_trace_extension_minus] at h
      rw [ihF] at h
      exact h
    . rw [NumericExpressionList.evaluation_remapping_trace_extension_minus]
      rw [ihF]
      exact h
  | universal_quantification x' T' ihT' =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihT'] at h
      rw [Store.replacement_different_variables_reordering] at h ; rotate_left
      . simp
      rw [NumericExpression.logical_state_independence] at h ; rotate_left
      . exact hE
      exact h
    . rw [ihT']
      rw [Store.replacement_different_variables_reordering] ; rotate_left
      . simp
      rw [NumericExpression.logical_state_independence] ; rotate_left
      . exact hE
      exact h

lemma trace_sub_add_cancel :
  ⋆ σ, τ, k ⊧ₜ[ b ] T[ℓ ↦ ℓ ⋆- ♯1][ℓ ↦ ℓ ⋆+ ♯1] <->
  ⋆ σ, τ, k ⊧ₜ[ b ] T := by
  revert σ k b
  induction T with
  | top => normalize
  | atomic Es =>
    intros σ k b
    constructor <;> intros h <;>
    apply atomic_inversion_bool at h <;>
    rcases h with ⟨hkbound, h⟩ <;>
    apply atomic_intro
    . rw [NumericExpressionList.trace_sub_add_cancel] at h
      rw [h]
    . rw [NumericExpressionList.trace_sub_add_cancel]
      exact h
  | negation T' ihT' =>
    intros σ k b
    constructor <;> intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . normalize at h
      rw [ihT'] at h
      exact h
    . normalize
      rw [ihT']
      exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b
    constructor <;> intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩) <;>
    normalize at hT₁ <;>
    normalize at hT₂ <;>
    (try rw [ihT₁] at hT₁) <;>
    (try rw [ihT₂] at hT₂) <;>
    (try apply disjunction_intro_false) <;>
    normalize <;>
    (try rw [ihT₁]) <;>
    (try rw [ihT₂]) <;>
    (try exact hT₁) <;>
    (try exact hT₂) <;>
    (try exact disjunction_intro_left hT₁)
    (try exact disjunction_intro_right hT₂)
    . apply disjunction_intro_left
      rw [ihT₁]
      exact hT₁
    . apply disjunction_intro_right
      rw [ihT₂]
      exact hT₂
  | previous T' ihT' =>
    intros σ k b
    constructor <;> intros hT' <;>
    rcases k with (_ | k') <;>
    (try apply previous_inversion_zero_bool at hT' ;
         rcases hT' with rfl ;
         apply previous_intro_zero) <;>
    apply previous_inversion_succ_bool at hT' <;>
    apply previous_intro_succ
    . normalize at hT'
      rw [ihT'] at hT'
      exact hT'
    . normalize
      rw [ihT']
      exact hT'
  | next T' ihT' =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply next_inversion_bool at h <;>
    apply next_intro
    . normalize at h
      rw [ihT'] at h
      exact h
    . normalize
      rw [ihT']
      exact h
  | since T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b
    constructor <;>
    intros h
    . induction k with
      | zero =>
        apply since_intro
        apply since_inversion_bool at h
        normalize at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩) <;>
        (try apply disjunction_intro_false) <;>
        (try apply conjunction_intro_false)
        . rw [ihT₂] at hT₂
          exact hT₂
        . right
          exact previous_intro_zero
        . rw [models_true, ihT₂] at hT₂
          apply disjunction_intro_left
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₂, hT₁ST₂⟩
          apply previous_inversion_zero at hT₁ST₂
          contradiction
      | succ k' ihk' =>
        apply since_intro
        apply since_inversion_bool at h
        normalize at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩) <;>
        (try apply disjunction_intro_false) <;>
        (try apply conjunction_intro_false) <;>
        (try apply conjunction_inversion_false at hT₁ST₂ ; rcases hT₁ST₂ with (hT₁ | hT₁ST₂)) <;>
        (try rw [ihT₁] at hT₁) <;>
        (try rw [ihT₂] at hT₂)
        . exact hT₂
        . exact hT₂
        . left ; exact hT₁
        . right
          apply previous_intro_succ
          apply ihk'
          normalize
          apply previous_inversion_succ_bool at hT₁ST₂
          exact hT₁ST₂
        . apply disjunction_intro_left
          rw [models_true, ihT₂] at hT₂
          exact hT₂
        . apply disjunction_intro_right
          apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply conjunction_intro
          . rw [models_true, ihT₁] at hT₁
            exact hT₁
          . apply previous_intro_succ
            apply ihk'
            normalize
            apply previous_inversion_succ_bool at hT₁ST₂
            exact hT₁ST₂
    . induction k with
      | zero =>
        apply since_intro
        apply since_inversion_bool at h
        normalize at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩) <;>
        (try apply disjunction_intro_false) <;>
        (try apply conjunction_intro_false) <;>
        normalize
        . rw [ihT₂]
          exact hT₂
        . right
          exact previous_intro_zero
        . apply disjunction_intro_left
          rw [ihT₂]
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₂, hT₁ST₂⟩
          apply previous_inversion_zero at hT₁ST₂
          contradiction
      | succ k' ihk' =>
        apply since_intro
        apply since_inversion_bool at h
        normalize at h
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩) <;>
        (try apply disjunction_intro_false) <;>
        (try apply conjunction_intro_false) <;>
        (try apply conjunction_inversion_false at hT₁ST₂ ; rcases hT₁ST₂ with (hT₁ | hT₁ST₂)) <;>
        normalize <;>
        (try rw [ihT₁]) <;>
        (try rw [ihT₂])
        . exact hT₂
        . exact hT₂
        . left ; exact hT₁
        . right
          apply previous_intro_succ
          apply ihk'
          apply previous_inversion_succ_bool at hT₁ST₂
          exact hT₁ST₂
        . apply disjunction_intro_left
          rw [ihT₂]
          exact hT₂
        . apply disjunction_intro_right
          apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply conjunction_intro
          . rw [models_true, ihT₁]
            exact hT₁
          . apply previous_intro_succ
            apply ihk'
            apply previous_inversion_succ_bool at hT₁ST₂
            exact hT₁ST₂
  | «until» T₁ T₂ n ihT₁ ihT₂ =>
    intros σ k b
    constructor <;>
    intros h
    . revert σ k b
      induction n with
      | zero =>
        intros σ k b h
        apply until_inversion_bool at h
        normalize at h
        apply until_intro_zero
        rw [ihT₂] at h
        exact h
      | succ n' ihn' =>
        intros σ k b h
        apply until_inversion_bool at h
        normalize at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩) <;>
        (try apply disjunction_intro_false) <;>
        (try apply conjunction_intro_false)
        . rw [ihT₂] at hT₂
          exact hT₂
        . apply conjunction_inversion_false at hT₁UT₂
          rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
          . left
            rw [ihT₁] at hT₁
            exact hT₁
          . right
            apply next_intro
            apply ihn'
            apply next_inversion_bool at hT₁UT₂
            normalize
            exact hT₁UT₂
        . apply disjunction_intro_left
          rw [models_true, ihT₂] at hT₂
          exact hT₂
        . apply disjunction_intro_right
          apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply conjunction_intro
          . rw [models_true, ihT₁] at hT₁
            exact hT₁
          . apply next_intro
            apply ihn'
            apply next_inversion at hT₁UT₂
            normalize
            exact hT₁UT₂
    . revert σ k b
      induction n with
      | zero =>
        intros σ k b h
        apply until_inversion_bool at h
        normalize at h
        apply until_intro_zero
        normalize
        rw [ihT₂]
        exact h
      | succ n' ihn' =>
        intros σ k b h
        apply until_inversion_bool at h
        normalize at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩) <;>
        (try apply disjunction_intro_false) <;>
        (try apply conjunction_intro_false)
        . normalize
          rw [ihT₂]
          exact hT₂
        . apply conjunction_inversion_false at hT₁UT₂
          rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
          . left
            normalize
            rw [ihT₁]
            exact hT₁
          . right
            apply next_intro
            apply ihn'
            apply next_inversion_bool at hT₁UT₂
            exact hT₁UT₂
        . apply disjunction_intro_left
          normalize
          rw [ihT₂]
          exact hT₂
        . apply disjunction_intro_right
          apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply conjunction_intro
          . normalize
            rw [ihT₁]
            exact hT₁
          . apply next_intro
            apply ihn'
            apply next_inversion at hT₁UT₂
            exact hT₁UT₂
  | function F Es ihF =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply function_inversion_bool at h <;>
    normalize at h <;>
    apply function_intro <;>
    normalize
    . rw [NumericExpressionList.trace_sub_add_cancel] at h
      rw [ihF] at h
      exact h
    . rw [NumericExpressionList.trace_sub_add_cancel]
      rw [ihF]
      exact h
  | universal_quantification x T' ihT' =>
    intros σ k b
    constructor <;>
    intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihT'] at h
      exact h
    . rw [ihT']
      exact h

lemma replacement_preserves_well_formedness {T : TraceAssertion} {E : NumericExpression} :
  T.wellFormed ->
  E'.containsExpression ℓ = false ->
  T[E ↦ E'].wellFormed := by
  intros hwf hE'
  induction T with
  | top =>
    normalize
    exact hwf
  | atomic Es =>
    simp [wellFormed] at hwf
    simp [wellFormed, replaceNumericExpression]
    normalize
    rw [NumericExpressionList.replacement_preserves_does_not_contain_trace_length] ; rotate_left
    . exact hE'
    exact hwf
  | negation T' ihT' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    apply ihT'
    simp [wellFormed] at hwf
    exact hwf
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    simp [wellFormed] at hwf
    rcases hwf with ⟨hT₁wf, hT₂wf⟩
    constructor
    . exact ihT₁ hT₁wf
    . exact ihT₂ hT₂wf
  | previous T' ihT' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    apply ihT'
    simp [wellFormed] at hwf
    exact hwf
  | next T' ihT' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    apply ihT'
    simp [wellFormed] at hwf
    exact hwf
  | since T₁ T₂ ihT₁ ihT₂ =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    simp [wellFormed] at hwf
    rcases hwf with ⟨hT₁wf, hT₂wf⟩
    constructor
    . exact ihT₁ hT₁wf
    . exact ihT₂ hT₂wf
  | «until» T₁ T₂ n ihT₁ ihT₂ =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    simp [wellFormed] at hwf
    rcases hwf with ⟨hT₁wf, hT₂wf⟩
    constructor
    . exact ihT₁ hT₁wf
    . exact ihT₂ hT₂wf
  | function F Es ihF =>
    simp [wellFormed] at hwf
    rcases hwf with ⟨hFwf, hEswf⟩
    simp [wellFormed, replaceNumericExpression]
    constructor
    . intros event
      normalize
      apply ihF
      exact hFwf event
    . normalize
      apply NumericExpressionList.replacement_preserves_does_not_contain_trace_length
      . exact hEswf
      . exact hE'
  | universal_quantification x T' ihT' =>
    simp [wellFormed] at hwf
    simp [wellFormed, replaceNumericExpression]
    normalize
    exact ihT' hwf

lemma equivalent_replacement {T : TraceAssertion} {E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⟧(σ, τ) = ⟦ E₂ ⟧(σ, τ) ->
  E₁.containsLogicalVariables = false ->
  E₂.containsLogicalVariables = false ->
  (⋆ σ, τ, k ⊧ₜ[ b ] T[E₁ ↦ E₂] <-> ⋆ σ, τ, k ⊧ₜ[ b ] T) := by
  intros hE₁E₂ hE₁ hE₂
  revert σ k b
  induction T with
  | top => normalize
  | atomic Es =>
    intros σ k b hE₁E₂
    constructor <;>
    intros h <;>
    apply atomic_inversion_bool at h <;>
    rcases h with ⟨hkbound, h⟩ <;>
    apply atomic_intro
    . rw [NumericExpressionList.equivalent_replacement] at h ; rotate_left
      . exact hE₁E₂
      exact h
    . rw [NumericExpressionList.equivalent_replacement] ; rotate_left
      . exact hE₁E₂
      exact h
  | negation T' ihT' =>
    intros σ k b hE₁E₂
    constructor <;>
    intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro <;>
    normalize at h <;>
    normalize
    . rw [ihT'] at h ; rotate_left
      . exact hE₁E₂
      exact h
    . rw [ihT'] ; rotate_left
      . exact hE₁E₂
      exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b hE₁E₂
    constructor <;>
    intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩) <;>
    (try normalize at hT₁) <;>
    (try normalize at hT₂) <;>
    (try rw [ihT₁] at hT₁ ; rotate_left ; exact hE₁E₂) <;>
    (try rw [ihT₂] at hT₂ ; rotate_left ; exact hE₁E₂) <;>
    (try apply disjunction_intro_false) <;>
    normalize <;>
    (try rw [ihT₁] ; rotate_left ; exact hE₁E₂) <;>
    (try rw [ihT₂] ; rotate_left ; exact hE₁E₂) <;>
    (try exact hT₁) <;>
    (try exact hT₂)
    . apply disjunction_intro_left
      exact hT₁
    . apply disjunction_intro_right
      exact hT₂
    . apply disjunction_intro_left
      rw [ihT₁] ; rotate_left
      . exact hE₁E₂
      exact hT₁
    . apply disjunction_intro_right
      rw [ihT₂] ; rotate_left
      . exact hE₁E₂
      exact hT₂
  | previous T' ihT' =>
    intros σ k b hE₁E₂
    constructor <;>
    intros h <;>
    apply previous_inversion_bool at h <;>
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩) <;>
    normalize at h
    . exact previous_intro_zero
    . apply previous_intro_succ
      rw [ihT'] at h ; rotate_left
      . exact hE₁E₂
      exact h
    . exact previous_intro_zero
    . apply previous_intro_succ
      normalize
      rw [ihT'] ; rotate_left
      . exact hE₁E₂
      exact h
  | next T' ihT' =>
    intros σ k b hE₁E₂
    constructor <;>
    intros h <;>
    apply next_inversion_bool at h <;>
    apply next_intro
    . normalize at h
      rw [ihT'] at h ; rotate_left
      . exact hE₁E₂
      exact h
    . normalize
      rw [ihT'] ; rotate_left
      . exact hE₁E₂
      exact h
  | since T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b hE₁E₂
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
          . rw [ihT₂] at hT₂ ; rotate_left
            . exact hE₁E₂
            apply disjunction_intro_false
            . exact hT₂
            . apply conjunction_intro_false ; left
              rw [ihT₁] at hT₁ ; rotate_left
              . exact hE₁E₂
              exact hT₁
          . apply disjunction_intro_false
            . rw [ihT₂] at hT₂ ; rotate_left
              . exact hE₁E₂
              exact hT₂
            . apply conjunction_intro_false ; right
              exact previous_intro_zero
        . rw [models_true, ihT₂] at hT₂ ; rotate_left
          . exact hE₁E₂
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
          . rw [ihT₂] at hT₂ ; rotate_left
            . exact hE₁E₂
            exact hT₂
          . apply conjunction_intro_false
            apply conjunction_inversion_false at hT₁ST₂
            rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
            . rw [ihT₁] at hT₁ ; rotate_left
              . exact hE₁E₂
              left ; exact hT₁
            . right
              apply previous_intro_succ
              apply since_intro
              apply ihk'
              apply previous_inversion_succ_bool at hT₁ST₂
              apply since_inversion_bool at hT₁ST₂
              exact hT₁ST₂
        . rw [models_true, ihT₂] at hT₂ ; rotate_left
          . exact hE₁E₂
          apply disjunction_intro_left
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply previous_inversion_succ at hT₁ST₂
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁] at hT₁ ; rotate_left
            . exact hE₁E₂
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
            . rw [ihT₂] ; rotate_left
              . exact hE₁E₂
              exact hT₂
            . apply conjunction_intro_false ; left
              rw [ihT₁] ; rotate_left
              . exact hE₁E₂
              exact hT₁
          . apply disjunction_intro_false
            . rw [ihT₂] ; rotate_left
              . exact hE₁E₂
              exact hT₂
            . apply conjunction_intro_false ; right
              exact previous_intro_zero
        . apply disjunction_intro_left
          rw [ihT₂] ; rotate_left
          . exact hE₁E₂
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
          . rw [ihT₂] ; rotate_left
            . exact hE₁E₂
            exact hT₂
          . apply conjunction_intro_false
            apply conjunction_inversion_false at hT₁ST₂
            rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
            . rw [ihT₁] ; rotate_left
              . exact hE₁E₂
              left ; exact hT₁
            . right
              apply previous_intro_succ
              apply since_intro
              apply ihk'
              apply previous_inversion_succ_bool at hT₁ST₂
              apply since_inversion_bool at hT₁ST₂
              exact hT₁ST₂
        . apply disjunction_intro_left
          rw [ihT₂] ; rotate_left
          . exact hE₁E₂
          exact hT₂
        . apply conjunction_inversion at hT₁ST₂
          rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
          apply previous_inversion_succ at hT₁ST₂
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁] ; rotate_left
            . exact hE₁E₂
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
      intros σ k b hE₁E₂
      constructor <;>
      intros h
      . normalize at h
        apply until_inversion_zero_bool at h
        apply until_intro_zero
        rw [ihT₂] at h ; rotate_left
        . exact hE₁E₂
        exact h
      . normalize
        apply until_inversion_zero_bool at h
        apply until_intro_zero
        rw [ihT₂] ; rotate_left
        . exact hE₁E₂
        exact h
    | succ n' ihn' =>
      intros σ k b hE₁E₂
      constructor <;>
      intros h
      . normalize at h
        apply until_inversion_succ_bool at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂] at hT₂ ; rotate_left
            . exact hE₁E₂
            exact hT₂
          . apply conjunction_inversion_false at hT₁UT₂
            apply conjunction_intro_false
            rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
            . left
              rw [ihT₁] at hT₁ ; rotate_left
              . exact hE₁E₂
              exact hT₁
            . apply next_inversion_bool at hT₁UT₂
              specialize ihn' (σ := σ) (k := k + 1) (b := false) hE₁E₂
              normalize at ihn'
              rw [ihn'] at hT₁UT₂
              right
              apply next_intro
              exact hT₁UT₂
        . apply disjunction_intro_left
          rw [models_true, ihT₂] at hT₂ ; rotate_left
          . exact hE₁E₂
          exact hT₂
        . apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁] at hT₁ ; rotate_left
            . exact hE₁E₂
            exact hT₁
          . apply next_inversion at hT₁UT₂
            specialize ihn' (σ := σ) (k := k + 1) (b := true) hE₁E₂
            normalize at ihn'
            rw [models_true, ihn'] at hT₁UT₂
            apply next_intro
            exact hT₁UT₂
      . normalize
        apply until_inversion_succ_bool at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂] ; rotate_left
            . exact hE₁E₂
            exact hT₂
          . apply conjunction_inversion_false at hT₁UT₂
            apply conjunction_intro_false
            rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
            . left
              rw [ihT₁] ; rotate_left
              . exact hE₁E₂
              exact hT₁
            . apply next_inversion_bool at hT₁UT₂
              specialize ihn' (σ := σ) (k := k + 1) (b := false) hE₁E₂
              normalize at ihn'
              right
              apply next_intro
              rw [ihn']
              exact hT₁UT₂
        . apply disjunction_intro_left
          rw [ihT₂] ; rotate_left
          . exact hE₁E₂
          exact hT₂
        . apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁] ; rotate_left
            . exact hE₁E₂
            exact hT₁
          . apply next_inversion at hT₁UT₂
            specialize ihn' (σ := σ) (k := k + 1) (b := true) hE₁E₂
            normalize at ihn'
            apply next_intro
            rw [ihn']
            exact hT₁UT₂
  | function F Es ihF =>
    intros σ k b hE₁E₂
    constructor <;>
    intros h <;>
    apply function_inversion_bool at h <;>
    apply function_intro
    . normalize at h
      rw [NumericExpressionList.equivalent_replacement, ihF] at h ; rotate_left
      . exact hE₁E₂
      . exact hE₁E₂
      exact h
    . normalize
      rw [NumericExpressionList.equivalent_replacement, ihF] ; rotate_left
      . exact hE₁E₂
      . exact hE₁E₂
      exact h
  | universal_quantification x T' ihT' =>
    intros σ k b hE₁E₂
    constructor <;>
    intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihT'] at h ; rotate_left
      . rw [NumericExpression.logical_variable_independence, NumericExpression.logical_variable_independence] ; rotate_left
        . exact hE₂
        . exact hE₁
        exact hE₁E₂
      exact h
    . rw [ihT'] ; rotate_left
      . rw [NumericExpression.logical_variable_independence, NumericExpression.logical_variable_independence] ; rotate_left
        . exact hE₂
        . exact hE₁
        exact hE₁E₂
      exact h

lemma implies_literalize {T : TraceAssertion} :
  ⋆ σ, τ, k ⊧ₜ[ b ] T -> ⋆ σ', τ, k ⊧ₜ[ b ] T.literalize σ τ := by
  revert σ σ' k b
  induction T with
  | top =>
    intros σ k b σ'
    simp [literalize]
    intros h
    rcases b
    . apply top_inversion at h
      contradiction
    . exact top_intro
  | atomic Es =>
    intros σ k b σ'
    simp [literalize]
    intros h
    apply atomic_inversion_bool at h
    rcases h with ⟨hkbound, h⟩
    apply atomic_intro
    . rw [NumericExpressionList.eq_literalize (σ' := σ')] at h
      exact h
  | negation T' ihT' =>
    intros σ k b σ'
    intros h
    apply negation_inversion at h
    apply negation_intro
    apply ihT' (σ' := σ') at h
    . exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b σ'
    intros h
    apply disjunction_inversion_bool at h
    rcases h with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩) <;>
    (try normalize at hT₁) <;>
    (try normalize at hT₂) <;>
    (try apply ihT₁ (σ' := σ') at hT₁) <;>
    (try apply ihT₂ (σ' := σ') at hT₂) <;>
    (try apply disjunction_intro_false) <;>
    (try exact hT₁) <;>
    (try exact hT₂)
    . apply disjunction_intro_left
      exact hT₁
    . apply disjunction_intro_right
      exact hT₂
  | previous T' ihT' =>
    intros σ k b σ'
    intros h
    apply previous_inversion_bool at h
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩)
    . exact previous_intro_zero
    . apply previous_intro_succ
      apply ihT' (σ' := σ') at h
      exact h
  | next T' ihT' =>
    intros σ k b σ'
    intros h
    apply next_inversion_bool at h
    apply next_intro
    . apply ihT' (σ' := σ') at h
      exact h
  | since T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b σ'
    intros h
    apply since_inversion_bool at h
    apply since_intro
    normalize at h
    induction k with
    | zero =>
      apply disjunction_inversion_bool at h
      rcases h with (⟨rfl, hT₂, hT₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁ST₂)⟩)
      . apply conjunction_inversion_false at hT₁ST₂
        rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
        . apply ihT₂ (σ' := σ') at hT₂
          apply disjunction_intro_false
          . exact hT₂
          . apply conjunction_intro_false ; left
            apply ihT₁ (σ' := σ') at hT₁
            exact hT₁
        . apply disjunction_intro_false
          . apply ihT₂ (σ' := σ') at hT₂
            exact hT₂
          . apply conjunction_intro_false ; right
            exact previous_intro_zero
      . apply ihT₂ (σ' := σ') at hT₂
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
        . apply ihT₂ (σ' := σ') at hT₂
          exact hT₂
        . apply conjunction_intro_false
          apply conjunction_inversion_false at hT₁ST₂
          rcases hT₁ST₂ with (hT₁ | hT₁ST₂)
          . apply ihT₁ (σ' := σ') at hT₁
            left ; exact hT₁
          . right
            apply previous_intro_succ
            apply since_intro
            apply ihk'
            apply previous_inversion_succ_bool at hT₁ST₂
            apply since_inversion_bool at hT₁ST₂
            exact hT₁ST₂
      . apply ihT₂ (σ' := σ') at hT₂
        apply disjunction_intro_left
        exact hT₂
      . apply conjunction_inversion at hT₁ST₂
        rcases hT₁ST₂ with ⟨hT₁, hT₁ST₂⟩
        apply previous_inversion_succ at hT₁ST₂
        apply disjunction_intro_right
        apply conjunction_intro
        . apply ihT₁ (σ' := σ') at hT₁
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
      intros σ k b σ'
      intros h
      apply until_inversion_zero_bool at h
      apply until_intro_zero
      apply ihT₂ (σ' := σ') at h
      exact h
    | succ n' ihn' =>
      intros σ k b σ'
      intros h
      apply until_inversion_succ_bool at h
      apply until_intro_succ
      apply disjunction_inversion_bool at h
      rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩)
      . apply disjunction_intro_false
        . apply ihT₂ (σ' := σ') at hT₂
          exact hT₂
        . apply conjunction_inversion_false at hT₁UT₂
          apply conjunction_intro_false
          rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
          . left
            apply ihT₁ (σ' := σ') at hT₁
            exact hT₁
          . apply next_inversion_bool at hT₁UT₂
            specialize ihn' (σ := σ) (σ' := σ') (k := k + 1) (b := false)
            apply ihn' at hT₁UT₂
            right
            apply next_intro
            exact hT₁UT₂
      . apply disjunction_intro_left
        apply ihT₂ (σ' := σ') at hT₂
        exact hT₂
      . apply conjunction_inversion at hT₁UT₂
        rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
        apply disjunction_intro_right
        apply conjunction_intro
        . apply ihT₁ (σ' := σ') at hT₁
          exact hT₁
        . apply next_inversion at hT₁UT₂
          specialize ihn' (σ := σ) (σ' := σ') (k := k + 1) (b := true)
          apply ihn' at hT₁UT₂
          apply next_intro
          exact hT₁UT₂
  | function F Es ihF =>
    intros σ k b σ'
    intros h
    apply function_inversion_bool at h
    apply function_intro
    . normalize at h
      rw [NumericExpressionList.eq_literalize (σ' := σ') (τ' := τ)] at h
      apply ihF at h
      exact h
  | universal_quantification x T' ihT' =>
    intros σ k b σ'
    simp [literalize]
    intros h
    apply universal_quantification_inversion at h
    apply universal_quantification_intro
    intros v'
    normalize
    specialize h (σ ⋆^x)
    apply ihT' (σ' := σ'[⋆^x ↦ v']) at h
    rw [Store.same_term_replacement] at h
    exact h

lemma double_trace_replace {T : TraceAssertion} {E₁ E₂ E₁' : NumericExpression} :
  ⟦ E₁[ℓ ↦ E₂] ⟧(σ, τ) = ⟦ E₁' ⟧(σ, τ) ->
  E₁.containsLogicalVariables = false ->
  E₂.containsLogicalVariables = false ->
  E₁'.containsLogicalVariables = false ->
  (⋆ σ, τ, k ⊧ₜ[ b ] T[ℓ ↦ E₁][ℓ ↦ E₂] <->
  ⋆ σ, τ, k ⊧ₜ[ b ] T[ℓ ↦ E₁']) := by
  intros hE₁' hE₁lv hE₂lv hE₁'lv
  revert σ k b
  induction T with
  | top => normalize
  | atomic Es =>
   intros σ k b hE₁'
   constructor <;>
   intros h <;>
   apply atomic_inversion_bool at h <;>
   rcases h with ⟨hbound, hevent⟩
   . rw [NumericExpressionList.double_trace_replace] at hevent ; rotate_left
     . exact hE₁'
     apply atomic_intro
     . rw [hevent]
   . apply atomic_intro
     . rw [NumericExpressionList.double_trace_replace] ; rotate_left
       . exact hE₁'
       rw [hevent]
  | negation T' ihT' =>
   intros σ k b hE₁'
   constructor <;>
   intros h <;>
   apply negation_inversion at h <;>
   apply negation_intro <;>
   normalize at h <;>
   specialize ihT' (σ := σ) (k := k) (b := !b) hE₁' <;>
   normalize
   . rw [ihT'] at h
     exact h
   . rw [ihT']
     exact h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b hE₁'
    constructor <;>
    intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩) <;>
    (try normalize at hT₁) <;>
    (try normalize at hT₂) <;>
    (try rw [ihT₁] at hT₁ ; rotate_left ; exact hE₁') <;>
    (try rw [ihT₂] at hT₂ ; rotate_left ; exact hE₁') <;>
    (try normalize at hT₂) <;>
    (try apply disjunction_intro_false) <;>
    normalize <;>
    (try rw [ihT₁] ; rotate_left ; exact hE₁') <;>
    (try rw [ihT₂] ; rotate_left ; exact hE₁') <;>
    (try exact hT₁) <;>
    (try exact hT₂)
    . apply disjunction_intro_left
      exact hT₁
    . apply disjunction_intro_right
      exact hT₂
    . apply disjunction_intro_left
      rw [ihT₁] ; rotate_left
      . exact hE₁'
      exact hT₁
    . apply disjunction_intro_right
      rw [ihT₂] ; rotate_left
      . exact hE₁'
      exact hT₂
  | previous T' ihT' =>
    intros σ k b hE₁'
    constructor <;>
    intros h <;>
    apply previous_inversion_bool at h <;>
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩) <;>
    normalize at h <;>
    normalize <;>
    (try exact previous_intro_zero) <;>
    apply previous_intro_succ
    . rw [ihT'] at h ; rotate_left
      . exact hE₁'
      exact h
    . rw [ihT'] ; rotate_left
      . exact hE₁'
      exact h
  | next T' ihT' =>
    intros σ k b hE₁'
    constructor <;>
    intros h <;>
    apply next_inversion_bool at h <;>
    apply next_intro <;>
    normalize at h <;>
    normalize <;>
    specialize ihT' (σ := σ) (k := k + 1) (b := b) hE₁'
    . rw [ihT'] at h
      exact h
    . rw [ihT']
      exact h
  | since T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b hE₁'
    constructor <;>
    intros h <;>
    apply since_inversion_bool at h <;>
    normalize at h <;>
    apply since_intro <;>
    normalize <;>
    induction k <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hT₂, hT₁T₁ST₂⟩ | ⟨rfl, (hT₂ | hT₁T₁ST₂)⟩) <;>
    (try apply conjunction_inversion at hT₁T₁ST₂ ; rcases hT₁T₁ST₂ with ⟨hT₁, hT₁ST₂⟩) <;>
    (try apply conjunction_inversion_false at hT₁T₁ST₂ ; rcases hT₁T₁ST₂ with (hT₁ | hT₁ST₂)) <;>
    (try apply disjunction_intro_false) <;>
    (try apply conjunction_intro_false) <;>
    normalize at hT₂ <;>
    normalize at hT₁ <;>
    normalize at hT₁ST₂ <;>
    (try rw [ihT₂] at hT₂ ; rotate_left ; exact hE₁') <;>
    (try rw [ihT₁] at hT₁ ; rotate_left ; exact hE₁') <;>
    (try rw [ihT₂] ; rotate_left ; exact hE₁') <;>
    (try rw [ihT₁] ; rotate_left ; exact hE₁') <;>
    (try (right ; exact previous_intro_zero)) <;>
    (try (apply disjunction_intro_left ; exact hT₂)) <;>
    (try exact hT₂) <;>
    (try (apply previous_inversion_zero at hT₁ST₂ ; contradiction)) <;>
    (try (left ; exact hT₁)) <;>
    (try (apply disjunction_intro_left ; rw [ihT₂] ; rotate_left ; exact hE₁' ; exact hT₂))
    . case since.mp.a.succ.inl.intro.intro.inr.a.a k' ihk' =>
      right
      apply previous_intro_succ
      apply since_intro
      apply ihk'
      apply previous_inversion_succ_bool at hT₁ST₂
      apply since_inversion_bool at hT₁ST₂
      exact hT₁ST₂
    . case since.mp.a.succ.inr.intro.inr.intro k' ihk' =>
      apply disjunction_intro_right
      apply conjunction_intro hT₁
      apply previous_inversion_succ at hT₁ST₂
      apply since_inversion at hT₁ST₂
      apply previous_intro_succ
      apply since_intro
      apply ihk'
      apply disjunction_inversion at hT₁ST₂
      rcases hT₁ST₂ with (hT₂ | hT₁ST₂)
      . apply disjunction_intro_left
        exact hT₂
      . apply disjunction_intro_right
        exact hT₁ST₂
    . case since.mpr.a.succ.inl.intro.intro.inr.a.a k' ihk' =>
      right
      apply previous_intro_succ
      apply since_intro
      apply ihk'
      apply previous_inversion_succ_bool at hT₁ST₂
      apply since_inversion_bool at hT₁ST₂
      exact hT₁ST₂
    . case since.mpr.a.succ.inr.intro.inr.intro k' ihk' =>
      apply disjunction_intro_right
      apply previous_inversion_succ at hT₁ST₂
      apply since_inversion_bool at hT₁ST₂
      apply disjunction_inversion at hT₁ST₂
      rcases hT₁ST₂ with (hT₂ | hT₁ST₂) <;>
      apply conjunction_intro
      . rw [models_true, ihT₁] ; rotate_left ; exact hE₁'
        exact hT₁
      . apply previous_intro_succ
        apply since_intro
        apply ihk'
        apply disjunction_intro_left
        exact hT₂
      . rw [models_true, ihT₁] ; rotate_left ; exact hE₁'
        exact hT₁
      . apply previous_intro_succ
        apply since_intro
        apply ihk'
        apply disjunction_intro_right
        exact hT₁ST₂
  | «until» T₁ T₂ n ihT₁ ihT₂ =>
    induction n with
    | zero =>
      intros σ k b hE₁'
      constructor <;>
      intros h
      . normalize at h
        apply until_inversion_zero_bool at h
        apply until_intro_zero
        rw [ihT₂] at h ; rotate_left
        . exact hE₁'
        exact h
      . normalize
        apply until_inversion_zero_bool at h
        apply until_intro_zero
        rw [ihT₂] ; rotate_left
        . exact hE₁'
        exact h
    | succ n' ihn' =>
      intros σ k b hE₁'
      constructor <;>
      intros h
      . normalize at h
        apply until_inversion_succ_bool at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂] at hT₂ ; rotate_left
            . exact hE₁'
            exact hT₂
          . apply conjunction_inversion_false at hT₁UT₂
            apply conjunction_intro_false
            rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
            . left
              rw [ihT₁] at hT₁ ; rotate_left
              . exact hE₁'
              exact hT₁
            . apply next_inversion_bool at hT₁UT₂
              specialize ihn' (σ := σ) (k := k + 1) (b := false) hE₁'
              normalize at ihn'
              rw [ihn'] at hT₁UT₂
              right
              apply next_intro
              exact hT₁UT₂
        . apply disjunction_intro_left
          rw [models_true, ihT₂] at hT₂ ; rotate_left
          . exact hE₁'
          exact hT₂
        . apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁] at hT₁ ; rotate_left
            . exact hE₁'
            exact hT₁
          . apply next_inversion at hT₁UT₂
            specialize ihn' (σ := σ) (k := k + 1) (b := true) hE₁'
            normalize at ihn'
            rw [models_true, ihn'] at hT₁UT₂
            apply next_intro
            exact hT₁UT₂
      . normalize
        apply until_inversion_succ_bool at h
        apply until_intro_succ
        apply disjunction_inversion_bool at h
        rcases h with (⟨rfl, hT₂, hT₁UT₂⟩ | ⟨rfl, (hT₂ | hT₁UT₂)⟩)
        . apply disjunction_intro_false
          . rw [ihT₂] ; rotate_left
            . exact hE₁'
            exact hT₂
          . apply conjunction_inversion_false at hT₁UT₂
            apply conjunction_intro_false
            rcases hT₁UT₂ with (hT₁ | hT₁UT₂)
            . left
              rw [ihT₁] ; rotate_left
              . exact hE₁'
              exact hT₁
            . apply next_inversion_bool at hT₁UT₂
              specialize ihn' (σ := σ) (k := k + 1) (b := false) hE₁'
              normalize at ihn'
              right
              apply next_intro
              rw [ihn']
              exact hT₁UT₂
        . apply disjunction_intro_left
          rw [ihT₂] ; rotate_left
          . exact hE₁'
          exact hT₂
        . apply conjunction_inversion at hT₁UT₂
          rcases hT₁UT₂ with ⟨hT₁, hT₁UT₂⟩
          apply disjunction_intro_right
          apply conjunction_intro
          . rw [models_true, ihT₁] ; rotate_left
            . exact hE₁'
            exact hT₁
          . apply next_inversion at hT₁UT₂
            specialize ihn' (σ := σ) (k := k + 1) (b := true) hE₁'
            normalize at ihn'
            apply next_intro
            rw [ihn']
            exact hT₁UT₂
  | function F Es ihF =>
    intros σ k b hE₁'
    constructor <;>
    intros h <;>
    apply function_inversion_bool at h <;>
    apply function_intro <;>
    normalize at h <;>
    normalize
    . rw [NumericExpressionList.double_trace_replace, ihF] at h ; rotate_left
      . exact hE₁'
      . exact hE₁'
      exact h
    . rw [NumericExpressionList.double_trace_replace, ihF] ; rotate_left
      . exact hE₁'
      . exact hE₁'
      exact h
  | universal_quantification x T' ihT' =>
    intros σ k b hE₁'
    constructor <;>
    intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihT'] at h ; rotate_left
      . rw [NumericExpression.logical_state_independence, NumericExpression.logical_state_independence] ; rotate_left
        . exact hE₁'lv
        . apply NumericExpression.term_replacement_preserves_logical_variable_absence
          . exact hE₁lv
          . exact hE₂lv
        exact hE₁'
      exact h
    . rw [ihT'] ; rotate_left
      . rw [NumericExpression.logical_state_independence, NumericExpression.logical_state_independence] ; rotate_left
        . exact hE₁'lv
        . apply NumericExpression.term_replacement_preserves_logical_variable_absence
          . exact hE₁lv
          . exact hE₂lv
        exact hE₁'
      exact h
