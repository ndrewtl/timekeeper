import Timekeeper.Tactics
import Timekeeper.Lemma.GeneralAssertion.Inversion
import Timekeeper.Lemma.GeneralAssertion.Introduction

namespace Timekeeper.GeneralAssertion.Models

lemma expression_conjunction_iff {B₁ B₂ : BooleanExpression} :
  ⋆ σ, τ ⊧[ b ] B₁ ⋆∧ B₂ <-> ⟦ B₁ ⋆∧ B₂ ⟧(σ, τ) = b := by
  constructor <;> rcases b <;> intros h
  . apply conjunction_inversion_false at h
    normalize
    rcases h with (hB₁ | hB₂)
    . apply expression_inversion at hB₁
      rw [hB₁]
      simp
    . apply expression_inversion at hB₂
      rw [hB₂]
      simp
  . apply conjunction_inversion at h
    rcases h with ⟨hB₁, hB₂⟩
    apply expression_inversion at hB₁
    apply expression_inversion at hB₂
    normalize
    rw [hB₁, hB₂]
    simp
  . normalize at h
    rw [Bool.and_eq_false_iff] at h
    apply conjunction_intro_false
    rcases h with (hB₁ | hB₂)
    . left ; exact expression_intro hB₁
    . right ; exact expression_intro hB₂
  . normalize at h
    rw [Bool.and_eq_true_iff] at h
    rcases h with ⟨hB₁, hB₂⟩
    apply conjunction_intro <;> apply expression_intro
    . exact hB₁
    . exact hB₂
