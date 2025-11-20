import Timekeeper.Evaluation.Main.Specification
import Timekeeper.Evaluation.Main.Invariants
import Timekeeper.Tactics

namespace Timekeeper.Evaluation.Main

@[simp]
lemma hSwf : ∀ Es, (S Es).wellFormed := by
  intros Es
  by_cases h : ∃ id purpose, Es = [Use, id, purpose]
  . rcases h with ⟨id, purpose, rfl⟩
    simp [S]
    auto_wf
  . simp at h
    simp [S]
    exact trivial

@[simp]
lemma hKwf : ∀ Es, (K Es).wellFormed := by
  intros Es
  by_cases h : ∃ id, Es = [RequestDeletion, id]
  . rcases h with ⟨id, rfl⟩
    simp [K]
    auto_wf
  . simp at h
    simp [K]
    exact trivial

@[simp]
lemma consent_invariant_well_formed :
  consent_invariant.wellFormed := by
  rw [consent_invariant]
  auto_wf

@[simp]
lemma consent_invariant'_well_formed :
  consent_invariant'.wellFormed := by
  rw [consent_invariant']
  auto_wf

@[simp]
lemma request_deletion_invariant₁_well_formed :
  request_deletion_invariant₁.wellFormed := by
  rw [request_deletion_invariant₁]
  auto_wf

@[simp]
lemma request_deletion_invariant₂_well_formed :
  request_deletion_invariant₂.wellFormed := by
  rw [request_deletion_invariant₂]
  auto_wf

@[simp]
lemma deletion_invariant₁_well_formed :
  deletion_invariant₁.wellFormed := by
  rw [deletion_invariant₁]
  auto_wf

@[simp]
lemma deletion_invariant₂_well_formed :
  deletion_invariant₂.wellFormed := by
  rw [deletion_invariant₂]
  auto_wf

@[simp]
lemma counter_invariant₁_well_formed :
  counter_invariant₁.wellFormed := by
  rw [counter_invariant₁]
  auto_wf

@[simp]
lemma counter_invariant₂_well_formed :
  counter_invariant₂.wellFormed := by
  rw [counter_invariant₂]
  auto_wf

@[simp]
lemma counter_invariant₂'_well_formed :
  counter_invariant₂'.wellFormed := by
  rw [counter_invariant₂']
  auto_wf
