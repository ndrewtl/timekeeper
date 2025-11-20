import Timekeeper.Language.Command
import Timekeeper.Language.Semantics.SmallStep

namespace Timekeeper.SmallStep
open Command

lemma skip_inversion : (skip, σ, τ) ⇝ (skip, σ', τ') -> σ' = σ ∧ τ' = τ := by
  intros hstep
  rcases hstep with (_|hskip)
  . simp

lemma emit_inversion :
  (emit Es, σ, τ) ⇝ (skip, σ', τ') ->
  σ' = σ ∧ τ' = τ ++ [{ store := σ, event :=  ⟦ Es ⟧(σ, τ) }] := by
  intro hstep
  rcases hstep
  constructor <;> trivial

lemma resolve_inversion :
  (resolve ω, σ, τ) ⇝ (skip, σ', τ') ->
  σ' = σ ∧ τ' = τ := by
  intro hstep
  rcases hstep
  exact ⟨rfl, rfl⟩

lemma assign_inversion :
  (set ⋆$x ⋆:= E, σ, τ) ⇝ (skip, σ', τ') ->
  σ' = σ[⋆$x ↦ ⟦E⟧(σ, τ)] ∧ τ' = τ := by
  intro hstep
  rcases hstep
  exact ⟨rfl, rfl⟩

end SmallStep

namespace SmallStepRTC
open Command
open SmallStep

section -- Inversion lemmas

lemma skip_inversion : (skip, σ, τ) ⇝* (skip, σ', τ') -> σ' = σ ∧ τ' = τ := by
  intros hstep
  generalize hC₁ : skip = C₁
  generalize hC₂ : skip = C₂
  conv at hstep =>
    congr
    . rw [hC₁]
    . skip
    . skip
    . rw [hC₂]
  induction hstep with
  | refl => simp
  | step hfirst hrest ih =>
    rw [<-hC₁] at hfirst
    rcases hfirst
    specialize ih _ hC₂
    . simp
    rcases ih with ⟨rfl, rfl⟩
    simp


lemma emit_inversion :
  (emit Es, σ, τ) ⇝* (skip, σ', τ') ->
  σ' = σ ∧ τ' = τ ++ [{store := σ, event := ⟦ Es ⟧(σ, τ)}] := by
  intro hstep
  rcases hstep with (_ | ⟨hfirst, hrest⟩)
  rcases hfirst
  rcases hrest with (_ | ⟨hfirst, hrest⟩)
  . apply SmallStep.emit_inversion
    exact small_step_emit Es σ τ
  . rcases hfirst
    apply skip_inversion at hrest
    exact hrest

lemma resolve_inversion :
  (resolve ω, σ, τ) ⇝* (skip, σ', τ') ->
  σ' = σ ∧ τ' = τ := by
  intro hstep
  rcases hstep with (_ | ⟨hfirst, hrest⟩)
  rcases hfirst
  rcases hrest with (_ | ⟨hfirst, hrest⟩)
  . exact And.symm ⟨rfl, rfl⟩
  . rcases hfirst
    apply skip_inversion at hrest
    exact hrest

lemma assign_inversion :
  (set ⋆$x ⋆:= E, σ, τ) ⇝* (skip, σ', τ') ->
  σ' = σ[⋆$x ↦ ⟦E⟧(σ, τ)] ∧ τ' = τ := by

  intro hstep
  rcases hstep with (_ | ⟨hfirst, hrest⟩)
  rcases hfirst
  rcases hrest with (_ | ⟨hfirst, hrest⟩)
  . exact And.symm ⟨rfl, rfl⟩
  . rcases hfirst
    apply skip_inversion at hrest
    exact hrest

end

-- This lemma states that if C₁ steps to C₁', then
-- C₁ ; C₂ steps to C₁' ; C₂
lemma seq_lift :
  (C₁, σ, τ) ⇝* (C₁', σ', τ') ->
  (C₁ ⋆; C₂, σ, τ) ⇝* (C₁' ⋆; C₂, σ', τ') := by
  intros hC₁
  induction hC₁ with
  | refl =>
    apply SmallStepRTC.refl
  | step hfirst hrest ih =>
    apply SmallStepRTC.step
    . apply SmallStep.small_step_seq_reduce
      . apply hfirst
    . exact ih
