import Mathlib.Tactic.Linarith
import Timekeeper.Logic.Evaluation.GeneralAssertion

namespace Timekeeper.GeneralAssertion.Models

lemma expression_inversion :
  Models σ τ (~B) b -> ⟦ B ⟧(σ, τ) = b := by
  intros h
  rcases h with ⟨h⟩
  exact h

lemma negation_inversion :
  Models σ τ ⋆¬φ b -> Models σ τ φ !b := by
  intros h
  rcases h with (_ | ⟨h⟩)
  exact h

lemma disjunction_inversion :
  ⋆ σ, τ ⊧ (A₁ ⋆∨ A₂) ->
  ⋆ σ, τ ⊧ A₁ ∨ ⋆ σ, τ ⊧ A₂ := by
  intros h
  rcases h with (_ | _ | hA₁ | hA₂)
  . left ; exact hA₁
  . right ; exact hA₂

lemma disjunction_inversion_false :
  ⋆ σ, τ ⊧[ false ] (A₁ ⋆∨ A₂) ->
  ⋆ σ, τ ⊧[ false ] A₁ ∧ ⋆ σ, τ ⊧[ false ] A₂ := by
  intros h
  rcases h with (_ | _ | _ | _ | ⟨hT₁, hT₂⟩)
  exact ⟨hT₁, hT₂⟩

lemma disjunction_inversion_bool :
  ⋆ σ, τ ⊧[ b ] (A₁ ⋆∨ A₂) ->
  (b = false ∧
    (⋆ σ, τ ⊧[ false ] A₁ ∧ ⋆ σ, τ ⊧[ false ] A₂)
  ) ∨
  (b = true ∧
    (⋆ σ, τ ⊧ A₁ ∨ ⋆ σ, τ ⊧ A₂)
  ) := by
  intros h
  rcases b
  . apply disjunction_inversion_false at h
    left
    constructor
    . trivial
    . exact h
  . apply disjunction_inversion at h
    right
    constructor
    . trivial
    . rcases h with (hA₁ | hA₂)
      . left ; exact hA₁
      . right ; exact hA₂

lemma conjunction_inversion_false :
  ⋆ σ, τ ⊧[ false ] A₁ ⋆∧ A₂ ->
  ⋆ σ, τ ⊧[ false ] A₁ ∨
  ⋆ σ, τ ⊧[ false ] A₂ := by
  intros h
  apply negation_inversion at h
  apply disjunction_inversion at h
  rcases h with (hA₁ | hA₂)
  . apply negation_inversion at hA₁
    left ; exact hA₁
  . apply negation_inversion at hA₂
    right ; exact hA₂

lemma conjunction_inversion :
  ⋆ σ, τ ⊧ (A₁ ⋆∧ A₂) ->
  ⋆ σ, τ ⊧ A₁ ∧
  ⋆ σ, τ ⊧ A₂ := by
  intros h
  apply negation_inversion at h
  apply disjunction_inversion_false at h
  rcases h with ⟨hA₁, hA₂⟩
  apply negation_inversion at hA₁
  apply negation_inversion at hA₂
  constructor
  . exact hA₁
  . exact hA₂

lemma trace_inversion :
  ⋆ σ, τ ⊧[ b ] (T ⋆@ E) ->
  ⋆ σ, τ, ⟦ E ⟧(σ, τ) ⊧ₜ[ b ] T := by
  intros h
  rcases h with (_ | _ | _ | _ | _ |h)
  exact h

lemma universal_quantification_inversion :
  ⋆ σ, τ ⊧[ b ] ⋆∀ x : A ->
  ∀ v', ⋆ σ[⋆^x ↦ v'], τ ⊧[ b ] A := by
  intros h
  rcases h with (_|_|_|_|_|_|h)
  intros v'
  specialize h v'
  exact h
