import Timekeeper.Lemma.GeneralAssertion.NonContradiction

namespace Timekeeper.GeneralAssertion.Models

lemma implication_inversion {A₁ A₂ : GeneralAssertion} :
  (⋆ σ, τ ⊧ A₁ ⋆→ A₂) ->
  (⋆ σ, τ ⊧ A₁) ->
  ⋆ σ, τ ⊧ A₂ := by
  intros himp hA₁
  simp at hA₁ himp

  apply disjunction_inversion at himp
  rcases himp with (hA₁' | hA₂)
  . apply negation_inversion at hA₁'
    set contr := non_contradiction hA₁ hA₁'
    contradiction
  . exact hA₂

lemma implication_intro :
  ⋆ σ, τ ⊧[ b ] P ->
  (⋆ σ, τ ⊧ P -> ⋆ σ, τ ⊧ Q) ->
  ⋆ σ, τ ⊧ P ⋆→ Q := by
  intros hP hPQ
  rcases b
  . apply disjunction_intro_left
    apply negation_intro
    exact hP
  . apply disjunction_intro_right
    exact hPQ hP
