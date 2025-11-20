import Timekeeper.Evaluation.Main.Components
import Timekeeper.Evaluation.Main.Lemma.Temporal
import Timekeeper.Evaluation.Main.Lemma.Invariants
import Timekeeper.Evaluation.Main.Lemma.WellFormedness

namespace Timekeeper.Evaluation.Main
open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future
open Command

lemma use_branch_sound :
  (S, K) ⊢ ⟪ deletion_invariant₁ ⟫ ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⦄ use_branch ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦  ⋆$"k" ⋆+ ♯1] ⦄ ⟪ deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] ⟫ := by
    apply seq_rule
      (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
      (β := deletion_invariant₁)
    . apply conseq_rule
      . apply assign_rule
          (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
          (α := deletion_invariant₁)
      . exact fun σ τ a => a
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
      . apply conseq_rule
        . apply assign_rule
            (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
            (α := deletion_invariant₁)
        . exact fun σ τ a => a
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
      . apply if_rule
        . apply seq_rule
            (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⋆∧
                  (⋆$"consent_db")[ ⋆⋆$"user_id" ]ₑ[ ⋆⋆$"purpose" ]ₑ ⋆= ♯1)
            (β := deletion_invariant₁)
          . apply conseq_rule
            . apply assign_rule
                (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⋆∧
                      (⋆$"consent_db")[ ⋆⋆$"user_id" ]ₑ[ ⋆⋆$"purpose" ]ₑ ⋆= ♯1)
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
          . apply conseq_rule
            . apply emit_rule
                (P := counter_invariant₁ ⋆∧ consent_invariant[ℓ ↦ ℓ ⋆- ♯1] ⋆∧ request_deletion_invariant₁[ℓ ↦ ℓ ⋆- ♯1] ⋆∧
                      (⋆$"consent_db")[ ⋆$"user_id" ]ₑ[ ⋆$"purpose" ]ₑ ⋆= ♯1)
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
                simp [S]
                normalize

                rw [consent_invariant] at hconsentinv
                apply universal_quantification_inversion at hconsentinv
                specialize hconsentinv (σ (⋆$"user_id"))
                apply universal_quantification_inversion at hconsentinv
                specialize hconsentinv (σ (⋆$"purpose"))

                apply implication_inversion at hconsentinv
                specialize hconsentinv _
                . apply expression_intro
                  rw [BooleanExpression.eq_correct]
                  normalize
                  simp [Store.update]
                  apply expression_inversion at hconsentdb
                  rw [BooleanExpression.eq_correct] at hconsentdb
                  normalize at hconsentdb
                  exact hconsentdb
                apply trace_inversion at hconsentinv
                normalize at hconsentinv
                apply TraceAssertion.implies_literalize (σ' := σ) at hconsentinv
                simp [TraceAssertion.literalize, NumericExpressionList.literalize, NumericExpression.literalize, Store.update] at hconsentinv
                normalize at hconsentinv

                have hτpos : 0 < τ.length := by
                  apply not_event_since_event_implies_nonzero_trace
                  exact hconsentinv

                apply Nat.ne_zero_of_lt at hτpos
                apply Nat.exists_eq_succ_of_ne_zero at hτpos
                rcases hτpos with ⟨k, hk⟩
                rw [hk]
                apply TraceAssertion.Models.previous_intro_succ
                rw [hk] at hconsentinv
                normalize at hconsentinv
                exact hconsentinv
              . repeat apply conjunction_intro <;> normalize
                . exact hcounterinv
                . exact trace_sub_add_cancel.mpr hconsentinv
                . exact trace_sub_add_cancel.mpr hreqdelinv
                . exact hconsentdb
            . intros σ τ hleft
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
              . apply reestablish_consent_invariant_trace_extension
                . exact hconsentinv
                . apply trace_inversion at hevent
                  exact hevent
                . intros id purpose
                  normalize
                  grind
              . apply request_deletion_invariant₁_decrement_trace_length_implies_request_deletion_invariant₁_increment_k
                exact hreqdelinv
            . intros σ τ τext h
              apply conjunction_inversion at h
              rcases h with ⟨hleft, h⟩
              exact h
            . intros σ τ τext h
              apply conjunction_inversion at h
              rcases h with ⟨hleft, hdelinv⟩
              clear hleft
              apply conjunction_intro <;> normalize
              . normalize at hdelinv
                rw [nonexistent_term_replacement] at hdelinv ; rotate_left
                . rw [deletion_invariant₁] ; auto_contains
                rw [nonexistent_term_replacement] ; rotate_left
                . rw [deletion_invariant₁] ; auto_contains
                apply deletion_invariant₁'_implies_deletion_invariant₁
                exact hdelinv
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
        . apply conseq_rule
          . apply skip_rule
              (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦ ⋆⋆$"k" ⋆+ ♯1])
              (α := deletion_invariant₁[⋆$"k" ↦ ⋆⋆$"k" ⋆+ ♯1])
          . intros σ τ hleft
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hconsentdb⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hcounterinv, hconsentinv⟩
            repeat apply conjunction_intro <;> normalize
            . exact hcounterinv
            . exact hconsentinv
            . apply request_deletion_invariant₁_implies_request_deletion_invariant₁_increment_k
              exact hreqdelinv
          . exact fun σ τ a => a
          . intros σ τ τext hleft
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hdelinv⟩
            clear hleft
            normalize at hdelinv
            normalize
            rw [nonexistent_term_replacement] at hdelinv ; rotate_left
            . rw [deletion_invariant₁] ; auto_contains
            rw [nonexistent_term_replacement] ; rotate_left
            . rw [deletion_invariant₁] ; auto_contains
            apply deletion_invariant₁'_implies_deletion_invariant₁
            exact hdelinv
          . intros σ τ τext hleft
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hdelinv⟩
            clear hleft
            exact hdelinv
          . rw [request_deletion_invariant₁] ; auto_wf
          . rw [request_deletion_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
      . auto_wf
      . auto_wf
    . auto_wf
    . auto_wf
