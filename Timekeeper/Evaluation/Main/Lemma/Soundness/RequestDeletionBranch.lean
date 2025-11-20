import Timekeeper.Evaluation.Main.Components
import Timekeeper.Evaluation.Main.Lemma.Invariants
import Timekeeper.Evaluation.Main.Lemma.WellFormedness

namespace Timekeeper.Evaluation.Main
open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future

lemma request_deletion_branch_sound :
  (S, K) ⊢ ⟪ deletion_invariant₁ ⟫ ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⦄ request_deletion_branch ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦  ⋆$"k" ⋆+ ♯1] ⦄ ⟪ deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] ⟫ := by
    rw [request_deletion_branch]
    apply seq_rule
      (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
      (β := deletion_invariant₁)
    . apply conseq_rule
      . apply assign_rule
          (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
          (α := deletion_invariant₁)
      . intros σ τ h
        rw [nonexistent_variable_replacement] ; rotate_left
        . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_contains
        exact h
      . exact fun σ τ a => a
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hleft, hdeleteinv⟩
        rw [nonexistent_variable_replacement] at hdeleteinv ; rotate_left
        . rw [deletion_invariant₁] ; auto_contains
        exact hdeleteinv
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hleft, hdeleteinv⟩
        exact hdeleteinv
      . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
      . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
      . rw [deletion_invariant₁] ; auto_wf
      . rw [deletion_invariant₁] ; auto_wf
    . apply seq_rule
        (Q := counter_invariant₁ ⋆∧
          consent_invariant ⋆∧ request_deletion_invariant₁ ⋆∧
          ⋆$"request" ⋆= ⋆{}[ ♯0 := ♯RequestDeletion ]ₑ[ ♯1 := ⋆⋆$"user_id" ]ₑ[ ♯2 := ℓ ]ₑ)
        (β := deletion_invariant₁)
      . apply conseq_rule
        . apply assign_rule
            (P := counter_invariant₁ ⋆∧
              consent_invariant ⋆∧ request_deletion_invariant₁ ⋆∧
              ⋆$"request" ⋆= ⋆{}[ ♯0 := ♯RequestDeletion ]ₑ[ ♯1 := ⋆⋆$"user_id" ]ₑ[ ♯2 := ℓ ]ₑ)
            (α := deletion_invariant₁)
        . intros σ τ h
          apply conjunction_intro
          . rw [<-variable_replacement, nonexistent_variable_replacement] ; rotate_left
            . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_contains
            exact h
          . normalize
            apply expression_intro
            rw [BooleanExpression.eq_correct]
        . exact fun σ τ a => a
        . intros σ τ τext h
          apply conjunction_inversion at h
          rcases h with ⟨hleft, hdelinv⟩
          rw [nonexistent_variable_replacement] at hdelinv ; rotate_left
          . rw [deletion_invariant₁] ; auto_contains
          exact hdelinv
        . intros σ τ τext h
          apply conjunction_inversion at h
          rcases h with ⟨hleft, hdelinv⟩
          exact hdelinv
        . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
        . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
        . rw [deletion_invariant₁] ; auto_wf
        . rw [deletion_invariant₁] ; auto_wf
      . apply seq_rule
          (Q := counter_invariant₁ ⋆∧
            consent_invariant ⋆∧ request_deletion_invariant₁' ⋆∧
            ⋆$"request" ⋆= ⋆{}[ ♯0 := ♯RequestDeletion ]ₑ[ ♯1 := ⋆⋆$"user_id" ]ₑ[ ♯2 := ℓ ]ₑ ⋆∧
            (⋆$"deletion_requests")[ ⋆$"k" ]ₑ ⋆= ⋆$"request")
          (β := deletion_invariant₁)
        . apply conseq_rule
          . apply assign_rule
              (P := counter_invariant₁ ⋆∧
                consent_invariant ⋆∧ request_deletion_invariant₁' ⋆∧
                ⋆$"request" ⋆= ⋆{}[ ♯0 := ♯RequestDeletion ]ₑ[ ♯1 := ⋆⋆$"user_id" ]ₑ[ ♯2 := ℓ ]ₑ ⋆∧
                (⋆$"deletion_requests")[ ⋆$"k" ]ₑ ⋆= ⋆$"request")
              (α := deletion_invariant₁)
          . intros σ τ h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hcounterinv, hconsentinv⟩

            repeat apply conjunction_intro <;> normalize
            . exact hcounterinv
            . rw [nonexistent_variable_replacement] ; rotate_left
              . rw [consent_invariant] ; auto_contains
              exact hconsentinv
            . apply request_deletion_invariant₁_implies_request_deletion_invariant₁'_k_update
              exact hreqdelinv
            . exact hreq
            . apply expression_intro
              rw [BooleanExpression.eq_correct]
              rw [NumericExpression.lookup_same_index]
              . trivial
          . exact fun σ τ a => a
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hdelinv⟩
            clear hleft
            normalize at hdelinv
            rw [nonexistent_term_replacement] at hdelinv ; rotate_left
            . rw [deletion_invariant₁] ; auto_contains
            rw [nonexistent_term_replacement] ; rotate_left
            . rw [deletion_invariant₁] ; auto_contains
            rw [<-models_true, deletion_invariant₁_deletion_requests_k_replacement_iff_deletion_invariant₁'] at hdelinv
            exact hdelinv
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hdelinv⟩
            clear hleft
            exact hdelinv
          . rw [consent_invariant, request_deletion_invariant₁', counter_invariant₁] ; auto_wf
          . rw [consent_invariant, request_deletion_invariant₁', counter_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
        . apply conseq_rule
          . apply emit_rule
              (P := counter_invariant₁ ⋆∧
                consent_invariant[ℓ ↦ ℓ ⋆- ♯1] ⋆∧ request_deletion_invariant₁'[ℓ ↦ ℓ ⋆- ♯1] ⋆∧
                (⋆$"request" ⋆= ⋆{}[ ♯0 := ♯RequestDeletion ]ₑ[ ♯1 := ⋆⋆$"user_id" ]ₑ[ ♯2 := ℓ ]ₑ)[ℓ ↦ ℓ ⋆- ♯1] ⋆∧
                (⋆$"deletion_requests")[ ⋆$"k" ]ₑ ⋆= ⋆$"request")
              (α := deletion_invariant₁)
          . intros σ τ h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hdelreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hcounterinv, hconsentinv⟩

            apply conjunction_intro <;> repeat apply conjunction_intro <;> normalize
            . apply trace_intro
              apply TraceAssertion.Models.function_intro
              simp [S]
              normalize
              exact TraceAssertion.Models.top_intro
            . exact hcounterinv
            . normalize
              rw [trace_sub_add_cancel]
              exact hconsentinv
            . normalize
              rw [trace_sub_add_cancel]
              exact hreqdelinv
            . normalize
              apply expression_intro
              rw [BooleanExpression.eq_correct]
              normalize
              apply expression_inversion at hreq
              rw [BooleanExpression.eq_correct] at hreq
              normalize at hreq
              exact hreq
            . normalize
              exact hdelreq
          . intros σ τ h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hevent⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hdelreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hcounterinv, hconsentinv⟩

            repeat apply conjunction_intro
            . exact hcounterinv
            . clear hdelreq hreq hreqdelinv
              apply trace_inversion at hevent
              apply reestablish_consent_invariant_trace_extension
              . exact hconsentinv
              . exact hevent
              . intros id purpose
                normalize
                grind
            . clear hconsentinv
              apply request_deletion_invariant₁'_implies_request_deletion_invariant₁'
              . exact hreqdelinv
              . apply expression_intro
                rw [BooleanExpression.eq_correct]
                apply expression_inversion at hdelreq
                rw [BooleanExpression.eq_correct] at hdelreq
                normalize at hdelreq
                normalize at hreq
                apply expression_inversion at hreq
                rw [BooleanExpression.eq_correct] at hreq
                normalize at hreq

                normalize
                rw [hdelreq]
                rw [hreq]
                rw [PrimesMap.set_correct]
              . apply trace_inversion at hevent
                apply TraceAssertion.Models.atomic_inversion_bound at hevent
                normalize at hevent
                exact hevent

          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hdelinv⟩
            clear hleft
            exact hdelinv
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hevent⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hdelreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hklt30, hconsentinv⟩

            normalize at hdelinv

            apply conjunction_intro
            . normalize
              clear hconsentinv hklt30 hreq hevent hdelreq hreqdelinv
              rw [nonexistent_term_replacement] at hdelinv ; rotate_left
              . rw [deletion_invariant₁] ; auto_contains
              rw [nonexistent_term_replacement] ; rotate_left
              . rw [deletion_invariant₁] ; auto_contains
              apply deletion_invariant₁'_implies_deletion_invariant₁
              exact hdelinv
            . clear hconsentinv hklt30 hevent hreqdelinv

              normalize at hdelreq
              normalize at hreq

              apply trace_intro
              apply TraceAssertion.Models.function_intro
              rw [<-NumericExpressionList.numeric_replacement]
              rw [NumericExpressionList.nonexistent_term_replacement] ; rotate_left
              . auto_contains
              simp [K]
              normalize

              apply expression_inversion at hdelreq
              rw [BooleanExpression.eq_correct] at hdelreq
              apply expression_inversion at hreq
              rw [BooleanExpression.eq_correct] at hreq

              rw [deletion_invariant₁] at hdelinv
              apply universal_quantification_inversion at hdelinv
              specialize hdelinv (σ (⋆$"k"))

              apply implication_inversion at hdelinv
              specialize hdelinv _
              . normalize
                apply expression_intro
                rw [BooleanExpression.lt_correct]
                normalize
                simp [Store.update]
                apply Nat.lt_succ_self

              apply implication_inversion at hdelinv
              specialize hdelinv _
              . normalize
                apply expression_intro
                rw [BooleanExpression.eq_correct]
                normalize
                simp [Store.update]
                normalize at hdelreq
                rw [hdelreq]
                normalize at hreq
                rw [hreq]
                rw [PrimesMap.set_limited, PrimesMap.set_limited, PrimesMap.set_correct] ; rotate_left
                . trivial
                . trivial
              normalize at hdelinv
              apply trace_inversion at hdelinv
              normalize at hdelinv
              simp [Store.update] at hdelinv
              apply TraceAssertion.Models.eventually_inversion at hdelinv
              rcases hdelinv with ⟨k', hbound₁, hbound₂, hdelinv⟩
              apply TraceAssertion.Models.atomic_inversion at hdelinv
              rcases hdelinv with ⟨hkbound, hdelinv⟩
              normalize at hdelinv
              normalize at hdelreq
              normalize at hreq
              rw [hdelreq, hreq] at hdelinv
              rw [PrimesMap.set_limited, PrimesMap.set_correct] at hdelinv ; rotate_left
              . trivial

              rw [hdelreq, hreq] at hbound₁
              rw [PrimesMap.set_correct] at hbound₁
              rw [hdelreq, hreq] at hbound₂
              rw [PrimesMap.set_correct] at hbound₂

              apply TraceAssertion.Models.eventually_intro
              . apply TraceAssertion.Models.atomic_intro
                normalize
                exact hdelinv
              . exact hbound₁
              . exact hbound₂
          . rw [consent_invariant, request_deletion_invariant₁', counter_invariant₁] ; auto_wf
          . rw [consent_invariant, request_deletion_invariant₁', counter_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
          . rw [deletion_invariant₁] ; auto_wf
        . rw [consent_invariant, request_deletion_invariant₁', counter_invariant₁] ; auto_wf
        . rw [deletion_invariant₁] ; auto_wf
      . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
      . rw [deletion_invariant₁] ; auto_wf
    . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
    . rw [deletion_invariant₁] ; auto_wf
