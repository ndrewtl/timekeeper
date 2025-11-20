import Timekeeper.Evaluation.Main.Components
import Timekeeper.Evaluation.Main.Lemma.Invariants
import Timekeeper.Evaluation.Main.Lemma.WellFormedness

namespace Timekeeper.Evaluation.Main

open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future

lemma consent_branch_sound :
  (S, K) ⊢ ⟪ deletion_invariant₁ ⟫ ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁ ⦄ consent_branch ⦃ counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦  ⋆$"k" ⋆+ ♯1] ⦄ ⟪ deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] ⟫ := by
  rw [consent_branch]
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
      rcases h with ⟨hconsentinv, hdeleteinv⟩
      rw [nonexistent_variable_replacement] at hdeleteinv ; rotate_left
      . rw [deletion_invariant₁] ; auto_contains
      exact hdeleteinv
    . intros σ τ τext h
      apply conjunction_inversion at h
      rcases h with ⟨hconsentinv, hdeleteinv⟩
      exact hdeleteinv
    . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
    . auto_wf
    . rw [deletion_invariant₁] ; auto_wf
    . auto_wf
  . apply seq_rule
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
        rcases h with ⟨hconsentinv, hdeleteinv⟩
        rw [nonexistent_variable_replacement] at hdeleteinv ; rotate_left
        . rw [deletion_invariant₁] ; auto_contains
        exact hdeleteinv
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hconsentinv, hdeleteinv⟩
        exact hdeleteinv
      . rw [consent_invariant, request_deletion_invariant₁, counter_invariant₁] ; auto_wf
      . auto_wf
      . rw [deletion_invariant₁] ; auto_wf
      . auto_wf
    . apply seq_rule
        (Q := counter_invariant₁ ⋆∧ consent_invariant' ⋆∧ request_deletion_invariant₁)
        (β := deletion_invariant₁)
      . apply conseq_rule
        . apply assign_rule
            (P := counter_invariant₁ ⋆∧ consent_invariant' ⋆∧ request_deletion_invariant₁)
            (α := deletion_invariant₁)
        . intros σ τ h
          apply conjunction_inversion at h
          rcases h with ⟨hleft, hreqdelinv⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hcounterinv, hconsentinv⟩

          repeat apply conjunction_intro <;> normalize
          . exact hcounterinv
          . rw [consent_invariant']
            normalize
            apply universal_quantification_intro
            intros vuid
            apply universal_quantification_intro
            intros vpurpose
            by_cases hvuidvpurpose: vuid = σ (⋆$"user_id") ∧ vpurpose = σ (⋆$"purpose")
            . rcases hvuidvpurpose with ⟨rfl, rfl⟩
              apply disjunction_intro_left
              apply negation_intro
              apply negation_intro
              apply conjunction_intro <;>
              apply expression_intro <;>
              rw [BooleanExpression.eq_correct] <;>
              normalize <;>
              simp [Store.update]
            . simp at hvuidvpurpose
              rw [consent_invariant] at hconsentinv
              apply universal_quantification_inversion at hconsentinv
              specialize hconsentinv vuid
              apply universal_quantification_inversion at hconsentinv
              specialize hconsentinv vpurpose
              apply implication_inversion at hconsentinv
              apply disjunction_intro_right
              apply implication_intro
              . apply expression_intro
                normalize
              intros hlookup
              apply expression_inversion at hlookup
              rw [BooleanExpression.eq_correct] at hlookup
              normalize at hlookup
              simp [Store.update] at hlookup

              by_cases hvuid : vuid = σ (⋆$"user_id")
              . specialize hvuidvpurpose hvuid
                rename' hvuidvpurpose => hvpurpose
                symm at hvuid
                rw [hvuid] at hlookup
                rw [PrimesMap.set_correct] at hlookup
                rw [PrimesMap.set_limited] at hlookup ; rotate_left
                . exact fun a => hvpurpose (id (Eq.symm a))

                specialize hconsentinv _
                . apply expression_intro
                  rw [BooleanExpression.eq_correct]
                  normalize
                  simp [Store.update]
                  exact hlookup
                exact hconsentinv
              . clear hvuidvpurpose
                rw [PrimesMap.set_limited] at hlookup ; rotate_left
                . exact fun a => hvuid (id (Eq.symm a))

                specialize hconsentinv _
                . apply expression_intro
                  rw [BooleanExpression.eq_correct]
                  normalize
                  simp [Store.update]
                  exact hlookup
                exact hconsentinv
          . exact hreqdelinv


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
        . rw [consent_invariant', request_deletion_invariant₁, counter_invariant₁] ; auto_wf
        . rw [consent_invariant'] ; auto_wf
        . rw [deletion_invariant₁] ; auto_wf
        . auto_wf
      . apply conseq_rule
        . apply emit_rule
            (P := counter_invariant₁ ⋆∧ consent_invariant'[ℓ ↦ ℓ ⋆- ♯1] ⋆∧ request_deletion_invariant₁[ℓ ↦ ℓ ⋆- ♯1])
            (α := deletion_invariant₁)
        . intros σ τ h
          apply conjunction_inversion at h
          rcases h with ⟨hleft, hreqdelinv⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hcounterinv, hconsentinv⟩

          apply conjunction_intro
          . apply trace_intro
            apply TraceAssertion.Models.function_intro
            rw [S] ; rotate_left
            . normalize
            exact TraceAssertion.Models.top_intro
          . repeat apply conjunction_intro <;> normalize
            . exact hcounterinv
            . exact trace_sub_add_cancel.mpr hconsentinv
            . exact trace_sub_add_cancel.mpr hreqdelinv
        . intros σ τ h
          apply conjunction_inversion at h
          rcases h with ⟨hleft, hevent⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hleft, hreqdelinv⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hcounterinv, hconsentinv⟩
          repeat apply conjunction_intro
          . exact hcounterinv
          . rw [consent_invariant'] at hconsentinv
            rw [consent_invariant]
            apply universal_quantification_intro
            intros vuid
            apply universal_quantification_intro
            intros vpurpose
            apply universal_quantification_inversion at hconsentinv
            specialize hconsentinv vuid
            apply universal_quantification_inversion at hconsentinv
            specialize hconsentinv vpurpose

            apply implication_intro
            . apply expression_intro
              normalize
            intros hlookup
            by_cases hvuidvpurpose: vuid = σ (⋆$"user_id") ∧ vpurpose = σ (⋆$"purpose")
            . rcases hvuidvpurpose with ⟨rfl, rfl⟩
              apply trace_inversion at hevent
              apply TraceAssertion.Models.atomic_inversion at hevent
              rcases hevent with ⟨hkbound, hevent⟩
              normalize at hkbound hevent
              apply trace_intro
              apply TraceAssertion.Models.since_intro
              apply TraceAssertion.Models.disjunction_intro_left
              apply TraceAssertion.Models.atomic_intro
              . normalize
                simp [Store.update]
                rw [hevent]
              . normalize
                exact hkbound
            . simp at hvuidvpurpose
              apply implication_inversion at hconsentinv
              specialize hconsentinv _
              . apply negation_intro
                normalize
                apply conjunction_intro_false
                normalize
                by_cases hvuid : vuid = σ (⋆$"user_id")
                . right
                  apply expression_intro
                  rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]
                  exact hvuidvpurpose hvuid
                . left
                  apply expression_intro
                  rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]
                  exact hvuid
              apply implication_inversion at hconsentinv
              specialize hconsentinv _
              . apply expression_intro
                rw [BooleanExpression.nonexistent_term_replacement] ; rotate_left
                . auto_contains
                rw [BooleanExpression.eq_correct]
                normalize
                simp [Store.update]
                apply expression_inversion at hlookup
                rw [BooleanExpression.eq_correct] at hlookup
                normalize at hlookup
                simp [Store.update] at hlookup
                exact hlookup
              normalize at hconsentinv
              apply trace_inversion at hconsentinv
              apply TraceAssertion.Models.since_inversion at hconsentinv
              normalize at hconsentinv
              apply trace_intro
              apply TraceAssertion.Models.since_intro
              apply trace_inversion at hevent
              apply TraceAssertion.Models.atomic_inversion at hevent
              rcases hevent with ⟨hkbound, hevent⟩
              normalize at hevent
              normalize
              by_cases hτlen : τ.length = 1
              . rw [hτlen] at hkbound
                normalize at hkbound
                rw [hkbound] at hconsentinv
                rw [hkbound]
                have h0m1 : 0 - 1 = 0 := by exact rfl
                rw [h0m1] at hconsentinv
                exact hconsentinv
              . have hτlen : τ.length - 1 ≠ 0 := by grind
                apply Nat.exists_eq_succ_of_ne_zero at hτlen
                rcases hτlen with ⟨τlenm1, hτlen⟩
                apply TraceAssertion.Models.disjunction_intro_right
                apply TraceAssertion.Models.conjunction_intro
                . apply TraceAssertion.Models.negation_intro
                  apply TraceAssertion.Models.atomic_intro
                  rw [hevent]
                  normalize
                . rw [hτlen]
                  apply TraceAssertion.Models.previous_intro_succ
                  apply TraceAssertion.Models.since_intro
                  simp_rw [hτlen] at hevent
                  rw [hτlen] at hconsentinv
                  rw [<-Nat.add_one] at hconsentinv
                  rw [Nat.add_sub_cancel] at hconsentinv
                  exact hconsentinv
          . apply request_deletion_invariant₁_decrement_trace_length_implies_request_deletion_invariant₁_increment_k
            exact hreqdelinv
        . intros σ τ τext h
          apply conjunction_inversion at h
          rcases h with ⟨_, hdeleteinv⟩
          exact hdeleteinv
        . intros σ τ τext h
          apply conjunction_intro
          apply conjunction_inversion at h
          rcases h with ⟨hleft, hdeleteinv⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hleft, hevent⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hleft, hreqdelinv⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hklt30, hconsentinv⟩
          normalize at hdeleteinv
          . normalize
            rw [nonexistent_term_replacement] ; rotate_left
            . rw [deletion_invariant₁] ; auto_contains
            rw [nonexistent_term_replacement] at hdeleteinv ; rotate_left
            . rw [deletion_invariant₁] ; auto_contains
            apply deletion_invariant₁'_implies_deletion_invariant₁
            exact hdeleteinv
          . apply trace_intro
            apply TraceAssertion.Models.function_intro
            rw [K]
            . normalize
              exact TraceAssertion.Models.top_intro
            . intros id
              normalize
        . rw [consent_invariant', request_deletion_invariant₁, counter_invariant₁] ; auto_wf
        . rw [consent_invariant', request_deletion_invariant₁] ; auto_wf
        . rw [deletion_invariant₁] ; auto_wf
        . rw [deletion_invariant₁] ; auto_wf
      . auto_wf
      . auto_wf
    . auto_wf
    . auto_wf
  . auto_wf
  . auto_wf
