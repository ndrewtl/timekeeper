import Timekeeper.Types
import Timekeeper.Notation.TermReplacement
import Timekeeper.Language.Semantics.Store

namespace Store
open Timekeeper

lemma same_term_replacement {σ : Store} :
  σ[x ↦ (σ x)] = σ := by
  funext x'
  simp [Store.update]
  intros h
  simp [h]

lemma replacement_different_variables_reordering
  {σ : Store} {x₁ x₂ : Variable} :
  x₁ ≠ x₂ ->
  σ[x₁ ↦ v₁][x₂ ↦ v₂] = σ[x₂ ↦ v₂][x₁ ↦ v₁] := by
  intros hx₁x₂

  funext x
  by_cases hx₁ : (x = x₁)
  . rw [hx₁]
    simp [Store.update, hx₁x₂]
  . by_cases hx₂ : (x = x₂)
    . simp [Store.update, hx₁]
    . simp [Store.update, hx₁]

end Store
