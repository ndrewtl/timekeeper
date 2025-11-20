import Timekeeper.Lemma.TraceAssertion
import Timekeeper.Lemma.GeneralAssertion.Inversion
import Timekeeper.Lemma.Store

namespace Timekeeper.GeneralAssertion
open Models

lemma non_contradiction :
  ⋆ σ, τ ⊧[ b₁ ] P ->
  ⋆ σ, τ ⊧[ b₂ ] P ->
  b₁ = b₂ := by
  revert b₁ b₂
  induction P with
  | expression B =>
    intros b₁ b₂ h₁ h₂
    apply expression_inversion at h₁
    apply expression_inversion at h₂
    rw [<-h₁, <-h₂]
  | negation A' ihA' =>
    intros b₁ b₂ h₁ h₂
    apply negation_inversion at h₁
    apply negation_inversion at h₂
    specialize ihA' (b₁ := !b₁) (b₂ := !b₂) h₁ h₂
    exact Bool.not_inj_iff.mp ihA'
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    intros b₁ b₂ h₁ h₂
    apply disjunction_inversion_bool at h₁
    apply disjunction_inversion_bool at h₂

    rcases h₁ with (⟨rfl, hA₁, hA₂⟩ | ⟨rfl, (hA₁ | hA₂)⟩) <;>
    rcases h₂ with (⟨rfl, hA₁', hA₂'⟩ | ⟨rfl, (hA₁' | hA₂')⟩) <;>
    (try trivial) <;>
    (try specialize ihA₁ hA₁ hA₁') <;>
    (try specialize ihA₂ hA₂ hA₂') <;>
    contradiction
  | trace T E =>
    intros b₁ b₂ h₁ h₂
    apply trace_inversion at h₁
    apply trace_inversion at h₂
    -- Need trace non-contradiction here
    exact TraceAssertion.non_contradiction h₁ h₂
  | universal_quantification x A ih =>
    intros b₁ b₂ h₁ h₂
    apply universal_quantification_inversion at h₁
    apply universal_quantification_inversion at h₂

    apply ih
    . specialize h₁ (σ ⋆^x)
      rw [Store.same_term_replacement] at h₁
      exact h₁
    . specialize h₂ (σ ⋆^x)
      rw [Store.same_term_replacement] at h₂
      exact h₂
