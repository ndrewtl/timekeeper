import Timekeeper.Evaluation.Main.Components
import Timekeeper.Evaluation.Main.Lemma.Invariants
import Timekeeper.Evaluation.Main.Lemma.WellFormedness

namespace Timekeeper.Evaluation.Main
open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future
open Command

lemma revoke_branch_sound :
  (S, K) ⊢ ⟪ deletion_invariant₁ ⟫ ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⦄ revoke_branch ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦  ⋆$"k" ⋆+ ♯1] ⦄ ⟪ deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] ⟫ := by
    rw [revoke_branch]
    apply seq_rule
      (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
      (β := deletion_invariant₁)
    . apply conseq_rule
      . apply assign_rule
          (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
          (α := deletion_invariant₁)
      . intros σ τ h
        exact h
      . exact fun σ τ a => a
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hleft, h⟩
        exact h
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hleft, h⟩
        exact h
      . rw [counter_invariant₁, consent_invariant, request_deletion_invariant₁] ; auto_wf
      . auto_wf
      . rw [deletion_invariant₁] ; auto_wf
      . auto_wf
    . apply seq_rule
        (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
        (β := deletion_invariant₁)
      . apply assign_rule
          (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
          (α := deletion_invariant₁)
      . apply seq_rule
          (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⋆∧
                (⋆$"consent_db")[ ⋆$"user_id" ]ₑ[ ⋆$"purpose" ]ₑ ⋆= ♯0)
          (β := deletion_invariant₁)
        . apply conseq_rule
          . apply assign_rule
              (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⋆∧
                    (⋆$"consent_db")[ ⋆$"user_id" ]ₑ[ ⋆$"purpose" ]ₑ ⋆= ♯0)
              (α := deletion_invariant₁)
          . intros σ τ hleft
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdel⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hcounterinv, hconsentinv⟩

            repeat apply conjunction_intro <;> normalize
            . exact hcounterinv
            . rw [consent_invariant] at hconsentinv
              rw [consent_invariant]

              apply universal_quantification_intro
              intros vuid
              apply universal_quantification_intro
              intros vpurpose

              normalize

              apply universal_quantification_inversion at hconsentinv
              specialize hconsentinv vuid
              apply universal_quantification_inversion at hconsentinv
              specialize hconsentinv vpurpose

              by_cases hvuidvpurpose :
                σ (⋆$"user_id") = vuid ∧
                σ (⋆$"purpose") = vpurpose
              . rcases hvuidvpurpose with ⟨hvuid, hvpurpose⟩
                apply disjunction_intro_left
                apply negation_intro
                normalize
                apply expression_intro
                rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]
                normalize
                simp [Store.update]
                rw [hvuid, hvpurpose]
                rw [PrimesMap.set_correct, PrimesMap.set_correct]
                simp
              . apply implication_intro
                . exact expression_intro rfl
                intros hconsentdb

                apply implication_inversion at hconsentinv
                specialize hconsentinv _
                . apply expression_intro

                  apply expression_inversion at hconsentdb
                  rw [BooleanExpression.eq_correct] at hconsentdb
                  normalize at hconsentdb
                  simp[Store.update] at hconsentdb

                  rw [BooleanExpression.eq_correct]
                  normalize
                  simp [Store.update]

                  by_cases hvuid : σ (⋆$"user_id") = vuid
                  . rw [hvuid, PrimesMap.set_correct] at hconsentdb
                    rw [PrimesMap.set_limited] at hconsentdb ; rotate_left
                    . simp at hvuidvpurpose
                      exact hvuidvpurpose hvuid
                    exact hconsentdb
                  . rw [PrimesMap.set_limited] at hconsentdb ; rotate_left
                    . exact hvuid
                    exact hconsentdb
                exact hconsentinv
            . exact hreqdel
            . apply expression_intro
              rw [BooleanExpression.eq_correct]
              normalize
              rw [PrimesMap.set_correct]
              rw [PrimesMap.set_correct]
          . exact fun σ τ a => a
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, h⟩
            exact h
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, h⟩
            exact h
          . rw [counter_invariant₁, consent_invariant, request_deletion_invariant₁] ; auto_wf
          . auto_wf
          . rw [deletion_invariant₁] ; auto_wf
          . auto_wf
        . apply conseq_rule
          . apply emit_rule
              (P := counter_invariant₁ ⋆∧ consent_invariant[ℓ ↦ ℓ ⋆- ♯1] ⋆∧ request_deletion_invariant₁[ℓ ↦ ℓ ⋆- ♯1] ⋆∧
                    (⋆$"consent_db")[ ⋆⋆$"user_id" ]ₑ[ ⋆⋆$"purpose" ]ₑ ⋆= ♯0)
              (α := deletion_invariant₁)
          . intros σ τ hleft
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hconsentdb⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hcounterinv, hconsentinv⟩

            apply conjunction_intro <;> normalize
            . apply trace_intro
              apply TraceAssertion.Models.function_intro
              simp [S] ; normalize
              exact TraceAssertion.Models.top_intro
            . repeat apply conjunction_intro <;> normalize
              . exact hcounterinv
              . exact trace_sub_add_cancel.mpr hconsentinv
              . exact trace_sub_add_cancel.mpr hreqdelinv
              . exact hconsentdb
          . intros σ τ hleft
            normalize at hleft
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hevent⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hconsentdb⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hcounterinv, hconsentinv⟩

            repeat apply conjunction_intro <;> normalize
            . exact hcounterinv
            . apply reestablish_consent_invariant_trace_extension_revoke
              . exact hconsentinv
              . exact trace_inversion hevent
              . exact hconsentdb
            . apply request_deletion_invariant₁_decrement_trace_length_implies_request_deletion_invariant₁_increment_k
              exact hreqdelinv
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, h⟩
            exact h
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, h⟩
            clear hleft
            normalize at h
            apply conjunction_intro
            . normalize
              rw [nonexistent_term_replacement] ; rotate_left
              . rw [deletion_invariant₁] ; auto_contains
              rw [nonexistent_term_replacement] at h ; rotate_left
              . rw [deletion_invariant₁] ; auto_contains
              apply deletion_invariant₁'_implies_deletion_invariant₁
              exact h
            . apply trace_intro
              apply TraceAssertion.Models.function_intro
              simp [K]
              normalize
              exact TraceAssertion.Models.top_intro
          . rw [counter_invariant₁, consent_invariant, request_deletion_invariant₁] ; auto_wf
          . rw [consent_invariant, request_deletion_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
        . auto_wf
        . auto_wf
      . auto_wf
      . auto_wf
    . auto_wf
    . auto_wf
