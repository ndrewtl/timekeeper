import Timekeeper.Evaluation.Main.Components
import Timekeeper.Evaluation.Main.Lemma.Invariants
import Timekeeper.Evaluation.Main.Lemma.WellFormedness

namespace Timekeeper.Evaluation.Main

open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future

lemma block₁_sound :
  (S, K) ⊢ ⟪ ⋆⊤ ⟫ ⦃ ⋆⊤ ⦄ block₁ ⦃ consent_invariant ⦄ ⟪ ⋆⊤ ⟫ := by
  rw [block₁]
  apply seq_rule (Q := ⋆⊤) (β := ⋆⊤)
  . apply assign_rule (P := ⋆⊤) (α := ⋆⊤)
  . apply conseq_rule_P
    . apply assign_rule (P := consent_invariant) (α := ⋆⊤)
    . intros σ τ h
      rw [consent_invariant]
      apply universal_quantification_intro
      intros vid
      apply universal_quantification_intro
      intros vpurpose
      apply disjunction_intro_left
      apply negation_intro
      normalize
      apply expression_intro
      rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]
      normalize
      simp [Store.update]
      rw [PrimesMap.get_zero_is_zero, PrimesMap.get_zero_is_zero]
      simp
    . rw [consent_invariant] ; auto_wf
    . auto_wf
    . auto_wf
    . auto_wf
  . auto_wf
  . auto_wf

lemma block₂_sound :
  (S, K) ⊢ ⟪ ⋆⊤ ⟫ ⦃ consent_invariant ⦄ block₂ ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⦄ ⟪ deletion_invariant₁ ⟫ := by
    rw [block₂]
    apply seq_rule
    . apply conseq_rule_P
      . apply conseq_rule_α
        . apply assign_rule
            (P := counter_invariant₁ ⋆∧ consent_invariant)
            (α := ⋆⊤)
        . exact future_implies_top
        . rw [consent_invariant, counter_invariant₁] ; auto_wf
        . auto_wf
        . auto_wf
        . auto_wf
      . intros σ τ h
        apply conjunction_intro
        . rw [counter_invariant₁]
          normalize
          apply expression_intro
          normalize
        . exact h
      . rw [consent_invariant, counter_invariant₁] ; auto_wf
      . auto_wf
      . auto_wf
      . auto_wf
    . apply conseq_rule
      . apply assign_rule
          (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
          (α := ⋆⊤)
      . intros σ τ h
        apply conjunction_intro <;> normalize
        . rw [nonexistent_variable_replacement, nonexistent_variable_replacement] ; rotate_left
          . rw [consent_invariant] ; auto_contains
          . rw [counter_invariant₁] ; auto_contains
          exact h
        . rw [request_deletion_invariant₁]
          apply universal_quantification_intro
          intros vidx
          normalize
          apply conjunction_intro
          . apply disjunction_intro_right
            apply disjunction_intro_left
            normalize
            apply negation_intro
            apply expression_intro
            conv_rhs => simp
            rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]
            normalize
            simp [Store.update]
            rw [PrimesMap.get_zero_is_zero]
            rw [PrimesMap.get_zero_is_zero]
            simp
          . apply disjunction_intro_right
            apply expression_intro
            rw [BooleanExpression.eq_correct]
            normalize
            simp [Store.update]
            rw [PrimesMap.get_zero_is_zero]
      . exact fun σ τ a => a
      . exact future_implies_top
      . exact future_implies_top
      . rw [consent_invariant, counter_invariant₁, request_deletion_invariant₁] ; auto_wf
      . rw [consent_invariant, request_deletion_invariant₁] ; auto_wf
      . auto_wf
      . auto_wf
    . rw [consent_invariant] ; auto_wf
    . auto_wf

lemma block₃_sound :
  (S, K) ⊢ ⟪ deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] ⟫ ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] ⦄ block₃ ⦃ counter_invariant₁' ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⦄ ⟪ deletion_invariant₁ ⟫ := by
    rw [block₃]
    apply seq_rule
      (Q := ⋆$"k" ⋆< ♯30 ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1])
      (β := deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1])
    . apply conseq_rule
      . apply assign_rule
          (P := ⋆$"k" ⋆< ♯30 ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1])
          (α := deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1])
      . intros σ τ h
        rw [nonexistent_variable_replacement] ; rotate_left
        . rw [consent_invariant, request_deletion_invariant₁] ; auto_contains
        exact h
      . exact fun σ τ a => a
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hconsentinv, hdeleteinv⟩
        rw [nonexistent_variable_replacement] at hdeleteinv ; rotate_left
        . rw [deletion_invariant₁] ; auto_contains
        exact hdeleteinv
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hconsentinv, hdeleteinv⟩
        exact hdeleteinv
      . rw [consent_invariant, request_deletion_invariant₁] ; auto_wf
      . rw [consent_invariant, request_deletion_invariant₁] ; auto_wf
      . rw [deletion_invariant₁] ; auto_wf
      . rw [deletion_invariant₁] ; auto_wf
    . apply conseq_rule
      . apply assign_rule
          (P := counter_invariant₁' ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
          (α := deletion_invariant₁)
      . intros σ τ h
        apply conjunction_inversion at h
        rcases h with ⟨hleft, hreqdelinv⟩
        apply conjunction_inversion at hleft
        rcases hleft with ⟨hklt30, hconsentinv⟩
        repeat apply conjunction_intro <;> normalize
        . rw [counter_invariant₁']
          normalize
          apply expression_intro
          rw [BooleanExpression.le_correct]
          apply expression_inversion at hklt30
          rw [BooleanExpression.lt_correct] at hklt30
          exact hklt30
        . normalize
          rw [nonexistent_variable_replacement] ; rotate_left
          . rw [consent_invariant] ; auto_contains
          exact hconsentinv
        . normalize
          exact hreqdelinv
      . exact fun σ τ a => a
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hconsentinv, hdeleteinv⟩
        clear hconsentinv
        normalize at hdeleteinv
        rw [nonexistent_term_replacement] at hdeleteinv ; rotate_left
        . rw [deletion_invariant₁] ; auto_contains
        rw [nonexistent_term_replacement] ; rotate_left
        . rw [deletion_invariant₁] ; auto_contains

        exact hdeleteinv
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hconsentinv, hdeleteinv⟩
        exact hdeleteinv
      . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁'] ; auto_wf
      . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁'] ; auto_wf
      . rw [deletion_invariant₁] ; auto_wf
      . rw [deletion_invariant₁] ; auto_wf
    . rw [consent_invariant, request_deletion_invariant₁] ; auto_wf
    . rw [deletion_invariant₁] ; auto_wf
