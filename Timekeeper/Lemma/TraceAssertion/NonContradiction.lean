import Timekeeper.Lemma.TraceAssertion.Inversion

namespace Timekeeper.TraceAssertion
open Models

lemma non_contradiction :
  ⋆ σ, τ, k ⊧ₜ[ b₁ ] T ->
  ⋆ σ, τ, k ⊧ₜ[ b₂ ] T ->
  b₁ = b₂ := by
  revert k b₁ b₂
  induction T with
  | top =>
    intros k b₁ b₂ h₁ h₂
    apply top_inversion at h₁
    apply top_inversion at h₂
    rcases h₁ with rfl
    rcases h₂ with rfl
    trivial
  | atomic Es =>
    intros k b₁ b₂ h₁ h₂
    apply atomic_inversion_bool at h₁
    rcases h₁ with ⟨k₁, hkbound₁, rfl⟩
    apply atomic_inversion_bool at h₂
    rcases h₂ with ⟨k₂, hkbound₂, rfl⟩
    trivial
  | negation T' ihT' =>
    intros k b₁ b₂ h₁ h₂
    apply negation_inversion at h₁
    apply negation_inversion at h₂
    specialize ihT' (k := k) (b₁ := !b₁) (b₂ := !b₂) h₁ h₂
    simp at ihT'
    exact ihT'
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros k b₁ b₂ h₁ h₂
    apply disjunction_inversion_bool at h₁
    apply disjunction_inversion_bool at h₂
    rcases h₁ with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩) <;>
    rcases h₂ with (⟨rfl, hT₁', hT₂'⟩ | ⟨rfl, (hT₁' | hT₂')⟩) <;>
    (try trivial) <;>
    (try specialize ihT₁ hT₁ hT₁') <;>
    (try specialize ihT₂ hT₂ hT₂') <;>
    contradiction
  | previous T' ihT' =>
    intros k b₁ b₂ h₁ h₂
    apply previous_inversion_bool at h₁
    apply previous_inversion_bool at h₂
    rcases h₁ with (⟨rfl, rfl⟩ | ⟨k'₁, rfl, h₁⟩) <;>
    rcases h₂ with (⟨⟨⟩, rfl⟩ | ⟨k'₂, ⟨⟩, h₂⟩) <;>
    (try trivial)
    exact ihT' h₁ h₂
  | next T' ihT' =>
    intros k b₁ b₂ h₁ h₂
    apply next_inversion_bool at h₁
    apply next_inversion_bool at h₂
    exact ihT' h₁ h₂
  | since φ ψ ihφ ihψ =>
    intros k
    induction k with
    | zero =>
      intros b₁ b₂ h₁ h₂
      apply since_inversion_bool at h₁
      apply since_inversion_bool at h₂
      apply disjunction_inversion_bool at h₁
      apply disjunction_inversion_bool at h₂
      rcases h₁ with (⟨rfl, hψ₁, hφφSψ₁⟩ | ⟨rfl, (hψ₁ | hφφSψ₁)⟩) <;>
      rcases h₂ with (⟨rfl, hψ₂, hφφSψ₂⟩ | ⟨rfl, (hψ₂ | hφφSψ₂)⟩) <;>
      (try trivial)
      . apply conjunction_inversion_false at hφφSψ₁
        specialize ihψ hψ₁ hψ₂ ; contradiction
      . specialize ihψ hψ₁ hψ₂ ; contradiction
    | succ k' ihk' =>
      intros b₁ b₂ h₁ h₂
      apply since_inversion_bool at h₁
      apply since_inversion_bool at h₂
      apply disjunction_inversion_bool at h₁
      apply disjunction_inversion_bool at h₂
      rcases h₁ with (⟨rfl, hψ₁, hφφSψ₁⟩ | ⟨rfl, (hψ₁ | hφφSψ₁)⟩) <;>
      rcases h₂ with (⟨rfl, hψ₂, hφφSψ₂⟩ | ⟨rfl, (hψ₂ | hφφSψ₂)⟩) <;>
      (try trivial)
      . apply conjunction_inversion_false at hφφSψ₁
        specialize ihψ hψ₁ hψ₂ ; contradiction
      . apply conjunction_inversion_false at hφφSψ₁
        apply conjunction_inversion at hφφSψ₂
        rcases hφφSψ₂ with ⟨hφ₂, hφSψ₂⟩
        rcases hφφSψ₁ with (hφ₁ | hφSψ₁)
        . specialize ihφ hφ₁ hφ₂ ; contradiction
        . apply previous_inversion_succ_bool at hφSψ₁
          apply previous_inversion at hφSψ₂
          rcases hφSψ₂ with ⟨k'₂, ⟨⟩, hφSψ₂⟩
          specialize ihk' hφSψ₁ hφSψ₂
          contradiction
      . specialize ihψ hψ₁ hψ₂ ; contradiction
      . apply conjunction_inversion at hφφSψ₁
        rcases hφφSψ₁ with ⟨hφ₁, hφSψ₁⟩
        apply conjunction_inversion_false at hφφSψ₂
        rcases hφφSψ₂ with (hφ₂ | hφSψ₂)
        . specialize ihφ hφ₁ hφ₂ ; contradiction
        . apply previous_inversion at hφSψ₁
          rcases hφSψ₁ with ⟨k'₁, ⟨⟩, hφSψ₁⟩
          apply previous_inversion_succ_bool at hφSψ₂
          specialize ihk' hφSψ₁ hφSψ₂
          contradiction
  | «until» φ ψ n ihφ ihψ =>
    induction n with
    | zero =>
      intros k b₁ b₂ h₁ h₂
      apply until_inversion_zero_bool at h₁
      apply until_inversion_zero_bool at h₂
      exact ihψ h₁ h₂
    | succ n' ihn' =>
      intros k b₁ b₂ h₁ h₂
      apply until_inversion_succ_bool at h₁
      apply until_inversion_succ_bool at h₂
      apply disjunction_inversion_bool at h₁
      apply disjunction_inversion_bool at h₂
      rcases h₁ with (⟨rfl, hψ₁, hφφUψ₁⟩ | ⟨rfl, (hψ₁ | hφφUψ₁)⟩) <;>
      rcases h₂ with (⟨rfl, hψ₂, hφφUψ₂⟩ | ⟨rfl, (hψ₂ | hφφUψ₂)⟩) <;>
      (try trivial)
      . specialize ihψ hψ₁ hψ₂ ; contradiction
      . apply conjunction_inversion_false at hφφUψ₁
        apply conjunction_inversion at hφφUψ₂
        rcases hφφUψ₂ with ⟨hφ₂, hφUψ₂⟩
        rcases hφφUψ₁ with (hφ₁ | hφUψ₁)
        . specialize ihφ hφ₁ hφ₂ ; contradiction
        . apply next_inversion_bool at hφUψ₁
          apply next_inversion at hφUψ₂
          specialize ihn' hφUψ₁ hφUψ₂ ; contradiction
      . specialize ihψ hψ₁ hψ₂ ; contradiction
      . apply conjunction_inversion_false at hφφUψ₂
        apply conjunction_inversion at hφφUψ₁
        rcases hφφUψ₁ with ⟨hφ₂, hφUψ₂⟩
        rcases hφφUψ₂ with (hφ₁ | hφUψ₁)
        . specialize ihφ hφ₁ hφ₂ ; contradiction
        . apply next_inversion_bool at hφUψ₁
          apply next_inversion at hφUψ₂
          specialize ihn' hφUψ₁ hφUψ₂ ; contradiction
  | function F Es ihF =>
    intros k b₁ b₂ h₁ h₂

    apply function_inversion_bool at h₁
    apply function_inversion_bool at h₂

    apply ihF
    . exact h₁
    . exact h₂
  | universal_quantification x T' ihT' =>
    intros k b₁ b₂ h₁ h₂
    apply ihT'
    . apply universal_quantification_inversion at h₁
      specialize h₁ (σ ⋆^x)
      rw [Store.same_term_replacement] at h₁
      exact h₁
    . apply universal_quantification_inversion at h₂
      specialize h₂ (σ ⋆^x)
      rw [Store.same_term_replacement] at h₂
      exact h₂
