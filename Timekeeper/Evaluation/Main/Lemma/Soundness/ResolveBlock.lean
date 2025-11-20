import Timekeeper.Evaluation.Main.Components
import Timekeeper.Evaluation.Main.Lemma.Invariants
import Timekeeper.Evaluation.Main.Lemma.WellFormedness

namespace Timekeeper.Evaluation.Main
open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future
open Command

lemma resolve_block_sound :
  (S, K) ⊢ ⟪ deletion_invariant₂ ⟫ ⦃ counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⦄ resolve_block ⦃ counter_invariant₂' ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⦄ ⟪ deletion_invariant₂ ⟫ := by
    rw [resolve_block]
    apply seq_rule
      (Q := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧ ⋆$"request" ⋆= (⋆$"deletion_requests")[ ⋆$"k'" ]ₑ)
      (β := deletion_invariant₂)
    . apply conseq_rule
      . apply assign_rule
          (P := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧ ⋆$"request" ⋆= (⋆$"deletion_requests")[ ⋆$"k'" ]ₑ)
          (α := deletion_invariant₂)
      . intros σ τ h
        apply conjunction_intro
        . rw [<-variable_replacement]
          rw [nonexistent_variable_replacement] ; rotate_left
          . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂] ; auto_contains
          exact h
        . apply expression_intro
          normalize
      . exact fun σ τ a => a
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hleft, hdeleteinv⟩
        exact hdeleteinv
      . intros σ τ τext h
        apply conjunction_inversion at h
        rcases h with ⟨hleft, hdeleteinv⟩
        exact hdeleteinv
      . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂] ; auto_wf
      . auto_wf
      . rw [deletion_invariant₂] ; auto_wf
      . auto_wf
    . apply seq_rule
        (Q := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂[⋆$"k'" ↦ ⋆$"k'" ⋆+ ♯1])
        (β := deletion_invariant₂[⋆$"k'" ↦ ⋆$"k'" ⋆+ ♯1])
      . apply if_rule
        . apply seq_rule
            (Q := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧
              ⋆$"request" ⋆= (⋆$"deletion_requests")[⋆$"k'"]ₑ ⋆∧
              (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
              (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id")
            (β := deletion_invariant₂)
          . apply conseq_rule
            . apply assign_rule
                (P := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧
                  ⋆$"request" ⋆= (⋆$"deletion_requests")[⋆$"k'"]ₑ ⋆∧
                  (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                  (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id")
                (α := deletion_invariant₂)
            . intros σ τ h
              apply conjunction_inversion at h
              rcases h with ⟨hleft, hreq₀⟩
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hreq⟩
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hreqdelinv⟩
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hconsentinv⟩
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hk0, hk'k⟩


              repeat apply conjunction_intro <;> normalize
              . exact hk0
              . exact hk'k
              . rw [nonexistent_variable_replacement] ; rotate_left
                . rw [consent_invariant] ; auto_contains
                exact hconsentinv
              . rw [nonexistent_variable_replacement] ; rotate_left
                . rw [request_deletion_invariant₂] ; auto_contains
                exact hreqdelinv
              . exact hreq
              . apply expression_inversion at hreq
                rw [BooleanExpression.eq_correct] at hreq
                normalize at hreq

                apply expression_inversion at hreq₀
                rw [BooleanExpression.eq_correct] at hreq₀
                normalize at hreq₀

                apply expression_intro
                rw [BooleanExpression.eq_correct]
                normalize
                rw [<-hreq]
                exact hreq₀
              . apply expression_inversion at hreq
                rw [BooleanExpression.eq_correct] at hreq
                normalize at hreq
                apply expression_intro
                rw [BooleanExpression.eq_correct]
                normalize
                rw [<-hreq]
            . exact fun σ τ a => a
            . intros σ τ τext h
              apply conjunction_inversion at h
              rcases h with ⟨hleft, hdeleteinv⟩
              rw [nonexistent_variable_replacement] at hdeleteinv ; rotate_left
              . rw [deletion_invariant₂] ; auto_contains
              exact hdeleteinv
            . intros σ τ τext h
              apply conjunction_inversion at h
              rcases h with ⟨hleft, hdeleteinv⟩
              exact hdeleteinv
            . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂] ; auto_wf
            . auto_wf
            . rw [deletion_invariant₂] ; auto_wf
            . auto_wf
          . apply seq_rule
              (Q := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧
                ⋆$"request" ⋆= (⋆$"deletion_requests")[⋆$"k'"]ₑ ⋆∧
                (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id" ⋆∧
                (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯2 ]ₑ ⋆= ⋆$"request_time")
              (β := deletion_invariant₂)
            . apply conseq_rule
              . apply assign_rule
                  (P := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧
                    ⋆$"request" ⋆= (⋆$"deletion_requests")[⋆$"k'"]ₑ ⋆∧
                    (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                    (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id" ⋆∧
                    (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯2 ]ₑ ⋆= ⋆$"request_time")
                  (α := deletion_invariant₂)
              . intros σ τ h
                apply conjunction_intro
                . normalize
                  rw [nonexistent_variable_replacement] ; rotate_left
                  . rw [counter_invariant₂] ; auto_contains
                  exact h
                . normalize
                  apply expression_intro
                  rw [BooleanExpression.eq_correct]
                  apply conjunction_inversion at h
                  rcases h with ⟨hleft, _⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hleft, _⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hleft, hreq⟩
                  apply expression_inversion at hreq
                  rw [BooleanExpression.eq_correct] at hreq
                  normalize at hreq
                  normalize
                  rw [hreq]
              . exact fun σ τ a => a
              . intros σ τ τext h
                apply conjunction_inversion at h
                rcases h with ⟨_, h⟩
                normalize at h
                rw [nonexistent_variable_replacement] at h ; rotate_left
                . rw [deletion_invariant₂] ; auto_contains
                exact h
              . intros σ τ τext h
                apply conjunction_inversion at h
                rcases h with ⟨_, h⟩
                normalize at h
                exact h
              . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂] ; auto_wf
              . auto_wf
              . rw [deletion_invariant₂] ; auto_wf
              . auto_wf
            . apply seq_rule
                (Q := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧
                  (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                  (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id" ⋆∧
                  (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯2 ]ₑ ⋆= ⋆$"request_time")
                (β := deletion_invariant₂)
              . apply conseq_rule
                . apply assign_rule
                    (P := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧
                      (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                      (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id" ⋆∧
                      (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯2 ]ₑ ⋆= ⋆$"request_time")
                    (α := deletion_invariant₂)
                . intros σ τ h
                  rw [nonexistent_variable_replacement] ; rotate_left
                  . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂] ; auto_contains
                  apply conjunction_inversion at h
                  rcases h with ⟨hleft, hreqtime⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hleft, huserid⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hleft, hreq₀⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hleft, hreq⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hleft, hreqdelinv⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hleft, hconsentinv⟩
                  apply conjunction_inversion at hleft
                  rcases hleft with ⟨hk0, hk'k⟩

                  repeat apply conjunction_intro
                  . exact hk0
                  . exact hk'k
                  . exact hconsentinv
                  . exact hreqdelinv
                  . exact hreq₀
                  . exact huserid
                  . exact hreqtime
                . exact fun σ τ a => a
                . intros σ τ τext h
                  apply conjunction_inversion at h
                  rcases h with ⟨_, h⟩
                  normalize at h
                  rw [nonexistent_variable_replacement] at h ; rotate_left
                  . rw [deletion_invariant₂] ; auto_contains
                  exact h
                . intros σ τ τext h
                  apply conjunction_inversion at h
                  rcases h with ⟨_, h⟩
                  normalize at h
                  exact h
                . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂] ; auto_wf
                . auto_wf
                . rw [deletion_invariant₂] ; auto_wf
                . auto_wf
              . apply seq_rule
                  (Q := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂[ℓ ↦ ℓ ⋆- ♯1] ⋆∧
                    (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                    (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id" ⋆∧
                    (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯2 ]ₑ ⋆= ⋆$"request_time" ⋆∧
                    ⋆![♯PerformDeletion, ⋆$"user_id"] ⋆@ ℓ ⋆- ♯1
                    )
                  (β := deletion_invariant₂)
                . apply conseq_rule
                  . apply emit_rule
                      (P := counter_invariant₂ ⋆∧ consent_invariant[ℓ ↦ ℓ ⋆- ♯1] ⋆∧ request_deletion_invariant₂[ℓ ↦ ℓ ⋆- ♯1] ⋆∧
                        (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                        (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id" ⋆∧
                        (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯2 ]ₑ ⋆= ⋆$"request_time")
                      (α := deletion_invariant₂)
                  . intros σ τ h
                    apply conjunction_inversion at h
                    rcases h with ⟨hleft, hreqtime⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, huserid⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreq₀⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreqdelinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hconsentinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hk0, hk'k⟩

                    apply conjunction_intro
                    . apply trace_intro
                      apply TraceAssertion.Models.function_intro
                      rw [S] ; rotate_left
                      . intros id purpose
                        normalize
                      . exact TraceAssertion.Models.top_intro
                    repeat apply conjunction_intro <;> normalize
                    . exact hk0
                    . exact hk'k
                    . exact trace_sub_add_cancel.mpr hconsentinv
                    . exact trace_sub_add_cancel.mpr hreqdelinv
                    . exact hreq₀
                    . exact huserid
                    . exact hreqtime
                  . intros σ τ h
                    apply conjunction_inversion at h
                    rcases h with ⟨hleft, hevent⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreqtime⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, huserid⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreq₀⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreqdelinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hconsentinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hk0, hk'k⟩

                    repeat apply conjunction_intro
                    . exact hk0
                    . exact hk'k
                    . apply reestablish_consent_invariant_trace_extension
                      . exact hconsentinv
                      . apply trace_inversion at hevent
                        normalize at hevent
                        exact hevent
                      . intros id purpose
                        normalize
                        grind
                    . exact hreqdelinv
                    . exact hreq₀
                    . exact huserid
                    . exact hreqtime
                    . exact hevent
                  . intros σ τ τext h
                    apply conjunction_inversion at h
                    rcases h with ⟨h, hdeleteinv⟩
                    exact hdeleteinv
                  . intros σ τ τext h
                    apply conjunction_inversion at h
                    rcases h with ⟨h, hdeleteinv⟩
                    apply conjunction_intro
                    . exact hdeleteinv
                    . apply trace_intro
                      apply TraceAssertion.Models.function_intro
                      rw [K]
                      . normalize
                        exact TraceAssertion.Models.top_intro
                      . intros id
                        normalize
                  . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂] ; auto_wf
                  . rw [consent_invariant, request_deletion_invariant₂] ; auto_wf
                  . rw [deletion_invariant₂] ; auto_wf
                  . rw [deletion_invariant₂] ; auto_wf
                . apply conseq_rule
                  . apply resolve_rule
                      (P := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂[ℓ ↦ ℓ ⋆- ♯1] ⋆∧
                        (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯0 ]ₑ ⋆= ♯RequestDeletion ⋆∧
                        (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯1 ]ₑ ⋆= ⋆$"user_id" ⋆∧
                        (⋆$"deletion_requests")[⋆$"k'"]ₑ[ ♯2 ]ₑ ⋆= ⋆$"request_time" ⋆∧
                        ⋆![♯PerformDeletion, ⋆⋆$"user_id"] ⋆@ ℓ ⋆- ♯1)
                      (α := deletion_invariant₂[⋆$"k'" ↦ ⋆$"k'" ⋆+ ♯1])
                  . intros σ τ h
                    apply conjunction_inversion at h
                    rcases h with ⟨hleft, hevent⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hrequesttime⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, huserid⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreq₀⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreqdelinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hconsentinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hk0, hk'k⟩

                    -- Unpack some assumptions
                    apply expression_inversion at hk'k
                    rw [BooleanExpression.lt_correct] at hk'k
                    normalize at hk'k

                    repeat apply conjunction_intro
                    . exact hk0
                    . apply expression_intro
                      rw [BooleanExpression.lt_correct]
                      exact hk'k
                    . -- TODO break this out into a lemma
                      exact hconsentinv

                    . exact hreqdelinv
                    . exact hreq₀
                    . exact huserid
                    . exact hrequesttime
                    . exact hevent
                    . apply trace_inversion at hevent
                      apply TraceAssertion.Models.atomic_inversion at hevent
                      rcases hevent with ⟨hkbound, hevent⟩
                      normalize at hevent

                      -- Get hreqdelinv ready
                      rw [request_deletion_invariant₂] at hreqdelinv
                      normalize at hreqdelinv
                      apply universal_quantification_inversion at hreqdelinv
                      specialize hreqdelinv (σ (⋆$"k'"))
                      apply implication_inversion at hreqdelinv
                      specialize hreqdelinv _
                      . apply conjunction_intro <;> apply expression_intro
                        . rw [BooleanExpression.le_correct]
                          normalize
                          simp [Store.update]
                          apply Nat.le_refl
                        . rw [BooleanExpression.lt_correct]
                          normalize
                          simp [Store.update]
                          exact hk'k
                      apply implication_inversion at hreqdelinv
                      specialize hreqdelinv _
                      . apply expression_intro
                        apply expression_inversion at hreq₀
                        rw [BooleanExpression.eq_correct]
                        rw [BooleanExpression.eq_correct] at hreq₀
                        normalize
                        simp [Store.update]
                        normalize at hreq₀
                        exact hreq₀

                      apply conjunction_inversion at hreqdelinv
                      rcases hreqdelinv with ⟨hℓle, hltℓ⟩

                      apply expression_inversion at hrequesttime
                      rw [BooleanExpression.eq_correct] at hrequesttime

                      apply trace_intro
                      apply TraceAssertion.Models.eventually_intro
                      . apply TraceAssertion.Models.atomic_intro
                        normalize
                        exact hevent
                      . clear huserid hreq₀ hconsentinv hk'k hℓle hkbound hevent
                        apply expression_inversion at hltℓ
                        rw [BooleanExpression.lt_correct] at hltℓ
                        normalize at hltℓ
                        simp [Store.update] at hltℓ
                        normalize at hrequesttime
                        rw [hrequesttime] at hltℓ
                        normalize

                        apply Nat.le_of_lt
                        exact hltℓ
                      . clear huserid hreq₀ hconsentinv hltℓ hkbound hevent
                        apply expression_inversion at hℓle
                        rw [BooleanExpression.le_correct] at hℓle
                        normalize at hℓle
                        simp [Store.update] at hℓle
                        normalize at hrequesttime
                        rw [hrequesttime] at hℓle

                        conv_rhs =>
                          simp [NumericExpression.evaluate]

                        rw [Nat.sub_add_cancel] at hℓle ; rotate_left
                        . apply Nat.le_trans
                          . apply Nat.le_of_lt
                            exact hk'k
                          . apply Nat.le_add_left
                        exact hℓle

                  . intros σ τ h
                    -- Introduce assumptions
                    apply conjunction_inversion at h
                    rcases h with ⟨hleft, heventually⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hevent⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hrequesttime⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, huserid⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreq₀⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreqdel⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hconsentinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hk0, hk'k⟩

                    repeat apply conjunction_intro <;> normalize
                    . exact hk0
                    . exact hk'k
                    . exact hconsentinv
                    . apply request_deletion_invariant₂_decrement_ℓ_implies_request_deletion_invariant₂_increment_k'
                      . exact hreqdel
                      . apply trace_inversion at hevent
                        apply TraceAssertion.Models.atomic_inversion_bound at hevent
                        normalize at hevent
                        exact hevent

                  . intros σ τ τext h
                    apply conjunction_inversion at h
                    rcases h with ⟨hleft, hright⟩
                    apply conjunction_inversion at hright
                    rcases hright with ⟨hdeleteinv, heventually⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, heventually'⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hevent⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hrequesttime⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, huserid⟩

                    normalize at hdeleteinv
                    rw [nonexistent_term_replacement] at hdeleteinv ; rotate_left
                    . rw [deletion_invariant₂] ; auto_contains
                    rw [nonexistent_term_replacement] ; rotate_left
                    . rw [deletion_invariant₂] ; auto_contains
                    apply deletion_invariant₂_increment_k'_implies_deletion_invariant₂
                    . exact hdeleteinv
                    . apply trace_intro
                      apply trace_inversion at heventually
                      apply TraceAssertion.Models.eventually_inversion at heventually
                      rcases heventually with ⟨k', hbound₁, hbound₂, heventually⟩
                      apply TraceAssertion.Models.atomic_inversion at heventually
                      rcases heventually with ⟨hkbound, heventually⟩
                      normalize at heventually

                      normalize at hrequesttime
                      apply expression_inversion at hrequesttime
                      rw [BooleanExpression.eq_correct] at hrequesttime
                      normalize at hrequesttime

                      apply TraceAssertion.Models.eventually_intro
                      . apply TraceAssertion.Models.atomic_intro
                        . normalize at huserid
                          apply expression_inversion at huserid
                          rw [BooleanExpression.eq_correct] at huserid
                          normalize at huserid
                          normalize
                          rw [huserid]
                          exact heventually
                      . normalize
                        rw [hrequesttime]
                        normalize at hbound₁
                        exact hbound₁
                      . normalize
                        rw [hrequesttime]
                        normalize at hbound₂
                        exact hbound₂
                  . intros σ τ τext h
                    apply conjunction_inversion at h
                    rcases h with ⟨hleft, hdeleteinv⟩
                    exact hdeleteinv
                  . rw [consent_invariant , request_deletion_invariant₂] ; auto_wf
                  . rw [consent_invariant , request_deletion_invariant₂] ; auto_wf
                  . rw [deletion_invariant₂] ; auto_wf
                  . rw [deletion_invariant₂] ; auto_wf
                . rw [request_deletion_invariant₂] ; auto_wf
                . auto_wf
              . auto_wf
              . auto_wf
            . auto_wf
            . auto_wf
          . auto_wf
          . auto_wf
        . apply conseq_rule
          . apply skip_rule
              (P := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂ ⋆∧
                ⋆$"request" ⋆= (⋆$"deletion_requests")[ ⋆$"k'" ]ₑ ⋆∧
                (⋆$"request")[ ♯0 ]ₑ ⋆≠ ♯RequestDeletion
                )
              (α := deletion_invariant₂[⋆$"k'" ↦ ⋆$"k'" ⋆+ ♯1])
          . intros σ τ h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hreqk⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreq⟩
            apply conjunction_intro
            . apply conjunction_intro
              . exact hleft
              . exact hreq
            . apply negation_inversion at hreqk
              apply expression_inversion at hreqk
              conv_rhs at hreqk => simp
              rw [BooleanExpression.eq_false_iff] at hreqk
              apply expression_intro
              exact hreqk
          . intros σ τ h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, _⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreq⟩
            clear hreq
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hconsentinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hk0, hk'k⟩

            repeat apply conjunction_intro <;> normalize
            . exact hk0
            . apply expression_intro
              rw [BooleanExpression.lt_correct]
              apply expression_inversion at hk'k
              rw [BooleanExpression.lt_correct] at hk'k
              normalize at hk'k
              normalize
              exact hk'k
            . exact hconsentinv
            . apply request_deletion_invariant₂_implies_request_deletion₂_increment_k'
              exact hreqdelinv
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hdeleteinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreq⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqk⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hreqdelinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hleft, hconsentinv⟩
            apply conjunction_inversion at hleft
            rcases hleft with ⟨hk0, hk'k⟩
            clear hconsentinv
            -- Get assumptions tied up
            normalize at hdeleteinv
            rw [nonexistent_term_replacement] at hdeleteinv ; rotate_left
            . rw [deletion_invariant₂] ; auto_contains

            apply expression_inversion at hreq
            rw [BooleanExpression.nonexistent_term_replacement] at hreq ; rotate_left
            . auto_contains
            rw [BooleanExpression.ne_correct] at hreq

            apply expression_inversion at hreqk
            rw [BooleanExpression.nonexistent_term_replacement] at hreqk ; rotate_left
            . auto_contains
            rw [BooleanExpression.eq_correct] at hreqk

            rw [<-numeric_replacement, nonexistent_term_replacement] at hk'k ; rotate_left
            . auto_contains

            rw [nonexistent_term_replacement] ; rotate_left
            . rw [deletion_invariant₂] ; auto_contains

            -- TODO break this into a lemma
            -- Proceed to prove the goal
            rw [deletion_invariant₂] at hdeleteinv
            rw [deletion_invariant₂]

            normalize
            apply universal_quantification_intro
            intros vidx
            apply universal_quantification_inversion at hdeleteinv
            specialize hdeleteinv vidx

            apply implication_intro
            . rw [expression_conjunction_iff]
            intros hidxbounds

            by_cases hvidx : vidx = σ (⋆$"k'")
            . apply disjunction_intro_left
              apply negation_intro
              apply expression_intro
              conv_rhs => simp
              rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]
              normalize
              simp [Store.update]
              normalize at hreqk
              normalize at hreq
              rw [hreqk] at hreq
              rw [<-hvidx] at hreq
              exact hreq
            . apply conjunction_inversion at hidxbounds
              rcases hidxbounds with ⟨hk'idx, hidxk⟩
              apply expression_inversion at hk'idx
              rw [BooleanExpression.le_correct] at hk'idx
              normalize at hk'idx
              simp [Store.update] at hk'idx

              apply expression_inversion at hidxk
              rw [BooleanExpression.lt_correct] at hidxk
              normalize at hidxk
              simp [Store.update] at hidxk

              apply implication_inversion at hdeleteinv
              specialize hdeleteinv _
              . apply conjunction_intro <;> normalize <;> apply expression_intro
                . rw [BooleanExpression.le_correct]
                  simp [Store.update]
                  apply Nat.succ_le_of_lt
                  apply Nat.lt_of_le_of_ne
                  . exact hk'idx
                  . exact fun a => hvidx (id (Eq.symm a))
                . rw [BooleanExpression.lt_correct]
                  simp [Store.update]
                  exact hidxk
              exact hdeleteinv
          . intros σ τ τext h
            apply conjunction_inversion at h
            rcases h with ⟨hleft, hdeleteinv⟩
            exact hdeleteinv
          . auto_wf
          . auto_wf
          . rw [deletion_invariant₂] ; auto_wf
          . rw [deletion_invariant₂] ; auto_wf
      . apply conseq_rule
        . apply assign_rule
            (P := counter_invariant₂' ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂)
            (α := deletion_invariant₂)
        . intros σ τ h
          apply conjunction_inversion at h
          rcases h with ⟨hleft, hreqdelinv⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hleft, hconsentinv⟩
          apply conjunction_inversion at hleft
          rcases hleft with ⟨hk0, hk'k⟩
          repeat apply conjunction_intro <;> normalize
          . exact hk0
          . apply expression_inversion at hk'k
            rw [BooleanExpression.lt_correct] at hk'k
            normalize at hk'k
            apply expression_intro
            rw [BooleanExpression.le_correct]
            normalize
            exact hk'k
          . normalize
            rw [nonexistent_variable_replacement] ; rotate_left
            . rw [consent_invariant] ; auto_contains
            exact hconsentinv
          . exact hreqdelinv
        . exact fun σ τ a => a
        . intros σ τ τext h

          rw [nonexistent_term_replacement] ; rotate_left
          . rw [deletion_invariant₂] ; auto_contains

          apply conjunction_inversion at h
          rcases h with ⟨hleft, hdeleteinv⟩ ; clear hleft
          normalize at hdeleteinv
          rw [nonexistent_term_replacement] at hdeleteinv ; rotate_left
          . rw [deletion_invariant₂] ; auto_contains

          rw [deletion_invariant₂] at hdeleteinv
          normalize at hdeleteinv
          rw [deletion_invariant₂]
          exact hdeleteinv
        . intros σ τ τext h
          apply conjunction_inversion at h
          rcases h with ⟨h, hdeleteinv⟩
          exact hdeleteinv
        . rw [consent_invariant, request_deletion_invariant₂, counter_invariant₂'] ; auto_wf
        . auto_wf
        . rw [deletion_invariant₂] ; auto_wf
        . auto_wf
      . rw [request_deletion_invariant₂] ; auto_wf
      . rw [deletion_invariant₂] ; auto_wf
    . auto_wf
    . auto_wf
