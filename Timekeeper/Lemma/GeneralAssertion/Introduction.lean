import Timekeeper.Logic.Evaluation.GeneralAssertion

namespace Timekeeper.GeneralAssertion.Models

lemma conjunction_intro :
  ⋆ σ, τ ⊧ P ->
  ⋆ σ, τ ⊧ Q ->
  ⋆ σ, τ ⊧ P ⋆∧ Q := by
  intros hP hQ
  apply negation_intro
  apply disjunction_intro_false
  . exact negation_intro hP
  . exact negation_intro hQ

lemma conjunction_intro_false :
  ⋆ σ, τ ⊧[ false ] P ∨ ⋆ σ, τ ⊧[ false ] Q ->
  ⋆ σ, τ ⊧[ false ] P ⋆∧ Q := by
  intros hPQ
  apply negation_intro
  rcases hPQ with (hP | hQ)
  . apply disjunction_intro_left
    apply negation_intro
    exact hP
  . apply disjunction_intro_right
    apply negation_intro
    exact hQ

lemma expression_true_or_false {B : BooleanExpression}:
  ⋆ σ, τ ⊧[ false ] B ∨
  ⋆ σ, τ ⊧[ true ] B := by
  rcases hB : ⟦ B ⟧(σ, τ)
  . left ; exact expression_intro hB
  . right ; exact expression_intro hB

lemma expression_true_or_false' {B : BooleanExpression}:
  ∃ b, ⋆ σ, τ ⊧[ b ] B := by
  rcases expression_true_or_false with (hB | hB)
  . exists false
  . exists true
