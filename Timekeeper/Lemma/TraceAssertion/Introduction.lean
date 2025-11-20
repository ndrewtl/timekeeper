import Timekeeper.Tactics
import Timekeeper.Lemma.NumericExpression
import Timekeeper.Lemma.NumericExpressionList
import Timekeeper.Lemma.TraceAssertion.Inversion
import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Logic.Evaluation.TraceAssertion

namespace Timekeeper.TraceAssertion.Models

lemma conjunction_intro :
  ⋆ σ, τ, k ⊧ₜ T₁ ->
  ⋆ σ, τ, k ⊧ₜ T₂ ->
  ⋆ σ, τ, k ⊧ₜ T₁ ⋆∧ T₂ := by
  intros hT₁ hT₂
  apply negation_intro
  apply disjunction_intro_false
  . apply negation_intro
    exact hT₁
  . apply negation_intro
    exact hT₂

lemma conjunction_intro_false :
  ⋆ σ, τ, k ⊧ₜ[ false ] T₁ ∨
  ⋆ σ, τ, k ⊧ₜ[ false ] T₂ ->
  ⋆ σ, τ, k ⊧ₜ[ false ] T₁ ⋆∧ T₂ := by
  intros h
  rcases h with (hT₁ | hT₂) <;>
  apply negation_intro
  . apply disjunction_intro_left
    apply negation_intro
    exact hT₁
  . apply disjunction_intro_right
    apply negation_intro
    exact hT₂

lemma bot_intro :
  ⋆ σ, τ, k ⊧ₜ[ false ] ⋆⊥ₜ := by
  apply negation_intro
  apply top_intro

lemma atomic_intro_false_distinct :
  ⋆ σ, τ, k ⊧ₜ ⋆!Es₁ ->
  ⟦ Es₁ ⟧(σ, τ) ≠ ⟦ Es₂ ⟧(σ, τ) ->
  ⋆ σ, τ, k ⊧ₜ[ false ] ⋆!Es₂ := by
  intros hEs₁ hdistinct
  apply atomic_inversion at hEs₁
  rcases hEs₁ with ⟨hkbound, hEs₁⟩
  apply atomic_intro
  . rw [hEs₁]
    exact beq_false_of_ne hdistinct

lemma eventually_intro :
  ⋆ σ, τ, k' ⊧ₜ T ->
  k ≤ k' ->
  k' ≤ k + n ->
  ⋆ σ, τ, k ⊧ₜ ✧( n ) T := by
  revert k k'
  induction n with
  | zero =>
    intros k k' hT hkk' hk'k
    apply until_intro_zero
    have hkeqk' : k = k' := by
      rw [Nat.eq_iff_le_and_ge]
      constructor
      . exact hk'k
      . exact hkk'
    rw [hkeqk'] at hT
    exact hT
  | succ n' ihn' =>
    intros k k' hT hkk' hk'k
    apply until_intro_succ
    by_cases hkeqk' : k = k'
    . -- left
      apply disjunction_intro_left
      rw [<-hkeqk']
      exact hT
    . -- right
      apply disjunction_intro_right
      apply conjunction_intro top_intro
      apply next_intro
      rw [<-eventually]
      apply ihn'
      . exact hT
      . apply Nat.add_one_le_of_lt
        apply Nat.lt_of_le_of_ne
        . exact hkk'
        . exact fun a => hkeqk' (id (Eq.symm a))
      . grind
