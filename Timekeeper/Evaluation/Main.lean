import Timekeeper.Evaluation.Main.Lemma.Soundness.Blocks
import Timekeeper.Evaluation.Main.Lemma.Soundness.ConsentBranch
import Timekeeper.Evaluation.Main.Lemma.Soundness.RevokeBranch
import Timekeeper.Evaluation.Main.Lemma.Soundness.RequestDeletionBranch
import Timekeeper.Evaluation.Main.Lemma.Soundness.ResolveBlock
import Timekeeper.Evaluation.Main.Lemma.Soundness.RevokeBranch
import Timekeeper.Evaluation.Main.Lemma.Soundness.UseBranch

namespace Timekeeper.Evaluation.Main
open GeneralAssertion
open GeneralAssertion.Models
open Soundness.Future
open Command

def program : Command :=
  set ⋆$"i" ⋆:= ♯0 ⋆;
  set ⋆$"consent_db" ⋆:= ⋆{} ⋆; -- Used to setup consent_invariant
  while: ⋆$"i" ⋆< ⋆$"nactions" do:
    set ⋆$"k" ⋆:= ♯0 ⋆;
    set ⋆$"deletion_requests" ⋆:= ⋆{} ⋆;
    while: ⋆$"k" ⋆< ♯30 do:
      set ⋆$"action" ⋆:= (⋆$"actions")[⋆$"i"]ₑ ⋆;
      if: (⋆$"action")[♯0]ₑ ⋆= ♯Consent then:
        set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
        set ⋆$"purpose" ⋆:= (⋆$"action")[♯2]ₑ ⋆;
        set ⋆$"consent_db" ⋆:= (⋆$"consent_db")[⋆$"user_id" := (⋆$"consent_db")[⋆$"user_id"]ₑ[⋆$"purpose" := ♯1]ₑ]ₑ ⋆;
        emit [♯Consent, ⋆$"user_id", ⋆$"purpose"]
      else: if: (⋆$"action")[♯0]ₑ ⋆= ♯Revoke then:
        set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
        set ⋆$"purpose" ⋆:= (⋆$"action")[♯2]ₑ ⋆;
        set ⋆$"consent_db" ⋆:= (⋆$"consent_db")[⋆$"user_id" := (⋆$"consent_db")[⋆$"user_id"]ₑ[⋆$"purpose" := ♯0]ₑ]ₑ ⋆;
        emit [♯Revoke, ⋆$"user_id", ⋆$"purpose"]
      else: if: (⋆$"action")[♯0]ₑ ⋆= ♯Use then:
        set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
        set ⋆$"purpose" ⋆:= (⋆$"action")[♯2]ₑ ⋆;
        if: (⋆$"consent_db")[⋆$"user_id"]ₑ[⋆$"purpose"]ₑ ⋆= ♯TrueVal then:
          set ⋆$"output" ⋆:= (⋆$"data_store")[⋆$"user_id"]ₑ ⋆;
          emit [♯Use, ⋆$"user_id", ⋆$"purpose"]
        else:
          -- Use disallowed
          skip
        end
      else: if: (⋆$"action")[♯0]ₑ ⋆= ♯RequestDeletion then:
        set ⋆$"user_id" ⋆:= (⋆$"action")[♯1]ₑ ⋆;
        set ⋆$"request" ⋆:= ⋆{}[♯0 := ♯RequestDeletion]ₑ[♯1 := ⋆$"user_id"]ₑ[♯2 := ℓ]ₑ ⋆;
        set ⋆$"deletion_requests" ⋆:= (⋆$"deletion_requests")[⋆$"k" := ⋆$"request"]ₑ ⋆;
        emit [♯RequestDeletion, ⋆$"user_id"]
      else:
        -- unrecognized action
        skip
      end end end end ⋆; -- end the if/else if part of the code
      -- Increment both idx and k
      set ⋆$"i" ⋆:= ⋆$"i" ⋆+ ♯1 ⋆;
      set ⋆$"k" ⋆:= ⋆$"k" ⋆+ ♯1
    end ⋆;

    set ⋆$"k'" ⋆:= ♯0 ⋆;
    while: ⋆$"k'" ⋆< ⋆$"k" do:
      set ⋆$"request" ⋆:= (⋆$"deletion_requests")[⋆$"k'"]ₑ ⋆;
      if: (⋆$"request")[ ♯0 ]ₑ ⋆= ♯RequestDeletion
        then:
          set ⋆$"user_id" ⋆:= (⋆$"request")[♯1]ₑ ⋆;
          set ⋆$"request_time" ⋆:= (⋆$"request")[♯2]ₑ ⋆;
          set ⋆$"data_store" ⋆:= (⋆$"data_store")[⋆$"user_id" := ♯0]ₑ ⋆;
          emit [♯PerformDeletion, ⋆$"user_id"] ⋆;
          resolve ( ✧( 30 ) ⋆!([♯PerformDeletion, ⋆$"user_id"]) ⋆@ ⋆$"request_time")
        else:
          -- No deletion was requested, so none must be performed
          skip
      end ⋆;
      set ⋆$"k'" ⋆:= ⋆$"k'" ⋆+ ♯1
    end
  end

lemma soundness :
  (S, K) ⊢ ⟪ ⋆⊤ ⟫ ⦃ ⋆⊤ ⦄ program ⦃ ⋆⊤ ⦄ ⟪ ⋆⊤ ⟫ := by
  apply seq_rule_assoc
  apply seq_rule
  . rw [<-block₁] ; exact block₁_sound
  . apply conseq_rule
    . apply while_rule
        (P := consent_invariant)
        (α := ⋆⊤)
      . apply seq_rule_assoc
        apply seq_rule
          (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
          (β := deletion_invariant₁)
        . apply conseq_rule_P
          . rw [<-block₂] ; exact block₂_sound
          . intros σ τ h
            apply conjunction_inversion at h
            rcases h with ⟨h, _⟩
            exact h
          . auto_wf
          . auto_wf
          . auto_wf
          . auto_wf
        . apply seq_rule
            (Q := ⋆$"k" ⋆= ♯30 ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
            (β := deletion_invariant₁)
          . apply conseq_rule
            . apply while_rule
                (P := counter_invariant₁' ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
                (α := deletion_invariant₁)
              . apply seq_rule
                  (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
                  (β := deletion_invariant₁)
                . apply conseq_rule
                  . apply assign_rule
                      (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
                      (α := deletion_invariant₁)
                  . intros σ τ hleft
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hlt30⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreqdelinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hkle30, hconsentinv⟩

                    apply expression_inversion at hlt30
                    rw [BooleanExpression.lt_correct] at hlt30

                    repeat apply conjunction_intro <;> normalize
                    . rw [counter_invariant₁]
                      normalize
                      apply expression_intro
                      rw [BooleanExpression.lt_correct]
                      exact hlt30
                    . exact hconsentinv
                    . exact hreqdelinv
                  . exact fun σ τ a => a
                  . intros σ τ τext hleft
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨_, hdelinv⟩
                    exact hdelinv
                  . intros σ τ τext hleft
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨_, hdelinv⟩
                    exact hdelinv
                  . rw [counter_invariant₁, consent_invariant, request_deletion_invariant₁] ; auto_wf
                  . auto_wf
                  . rw [deletion_invariant₁] ; auto_wf
                  . auto_wf
                . apply seq_rule
                    (Q := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1])
                    (β := deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1])
                  . apply if_rule
                    . apply conseq_rule
                      . apply consent_branch_sound
                      . intros σ τ h
                        apply conjunction_inversion at h
                        rcases h with ⟨h, _⟩
                        exact h
                      . exact fun σ τ a => a
                      . intros σ τ τext h
                        apply conjunction_inversion at h
                        rcases h with ⟨_, h⟩
                        exact h
                      . intros σ τ τext h
                        apply conjunction_inversion at h
                        rcases h with ⟨_, h⟩
                        exact h
                      . auto_wf
                      . rw [request_deletion_invariant₁] ; auto_wf
                      . auto_wf
                      . rw [deletion_invariant₁] ; auto_wf
                    . apply if_rule
                      . apply conseq_rule
                        . apply revoke_branch_sound
                        . intros σ τ h
                          apply conjunction_inversion at h
                          rcases h with ⟨h, _⟩
                          apply conjunction_inversion at h
                          rcases h with ⟨h, _⟩
                          exact h
                        . exact fun σ τ a => a
                        . intros σ τ τext h
                          apply conjunction_inversion at h
                          rcases h with ⟨_, h⟩
                          exact h
                        . intros σ τ τext h
                          apply conjunction_inversion at h
                          rcases h with ⟨_, h⟩
                          exact h
                        . auto_wf
                        . rw [request_deletion_invariant₁] ; auto_wf
                        . auto_wf
                        . rw [deletion_invariant₁] ; auto_wf
                      . apply if_rule
                        . apply conseq_rule
                          . apply use_branch_sound
                          . intros σ τ h
                            apply conjunction_inversion at h
                            rcases h with ⟨h, _⟩
                            apply conjunction_inversion at h
                            rcases h with ⟨h, _⟩
                            apply conjunction_inversion at h
                            rcases h with ⟨h, _⟩
                            exact h
                          . exact fun σ τ a => a
                          . intros σ τ τext h
                            apply conjunction_inversion at h
                            rcases h with ⟨_, h⟩
                            exact h
                          . intros σ τ τext h
                            apply conjunction_inversion at h
                            rcases h with ⟨_, h⟩
                            exact h
                          . auto_wf
                          . rw [request_deletion_invariant₁] ; auto_wf
                          . auto_wf
                          . rw [deletion_invariant₁] ; auto_wf
                        . apply if_rule
                          . apply conseq_rule
                            . apply request_deletion_branch_sound
                            . intros σ τ h
                              apply conjunction_inversion at h
                              rcases h with ⟨h, _⟩
                              apply conjunction_inversion at h
                              rcases h with ⟨h, _⟩
                              apply conjunction_inversion at h
                              rcases h with ⟨h, _⟩
                              apply conjunction_inversion at h
                              rcases h with ⟨h, _⟩
                              exact h
                            . exact fun σ τ a => a
                            . intros σ τ τext h
                              apply conjunction_inversion at h
                              rcases h with ⟨_, h⟩
                              exact h
                            . intros σ τ τext h
                              apply conjunction_inversion at h
                              rcases h with ⟨_, h⟩
                              exact h
                            . rw [counter_invariant₁, consent_invariant, request_deletion_invariant₁] ; auto_wf
                            . rw [request_deletion_invariant₁] ; auto_wf
                            . auto_wf
                            . rw [deletion_invariant₁] ; auto_wf
                          . apply conseq_rule
                            . apply skip_rule
                                (P := counter_invariant₁ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁[⋆$"k" ↦ ⋆⋆$"k" ⋆+ ♯1])
                                (α := deletion_invariant₁[⋆$"k" ↦ ⋆⋆$"k" ⋆+ ♯1])
                            . intros σ τ hleft
                              apply conjunction_inversion at hleft
                              rcases hleft with ⟨hleft, _⟩
                              apply conjunction_inversion at hleft
                              rcases hleft with ⟨hleft, _⟩
                              apply conjunction_inversion at hleft
                              rcases hleft with ⟨hleft, _⟩
                              apply conjunction_inversion at hleft
                              rcases hleft with ⟨hleft, _⟩
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
                              rcases hleft with ⟨hleft, h⟩
                              apply deletion_invariant₁'_implies_deletion_invariant₁
                              exact h
                            . intros σ τ τext hleft
                              apply conjunction_inversion at hleft
                              rcases hleft with ⟨hleft, h⟩
                              exact h
                            . rw [counter_invariant₁, consent_invariant, request_deletion_invariant₁] ; auto_wf
                            . rw [request_deletion_invariant₁] ; auto_wf
                            . rw [deletion_invariant₁] ; auto_wf
                            . rw [deletion_invariant₁] ; auto_wf
                  . apply block₃_sound
                  . rw [request_deletion_invariant₁] ; auto_wf
                  . rw [deletion_invariant₁] ; auto_wf
                . auto_wf
                . auto_wf
            . intros σ τ hleft
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hreqdelinv⟩
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hcounterinv, hconsentinv⟩

              repeat apply conjunction_intro <;> normalize
              . rw [counter_invariant₁']
                rw [counter_invariant₁] at hcounterinv
                apply expression_inversion at hcounterinv
                rw [BooleanExpression.lt_correct] at hcounterinv
                apply expression_intro
                rw [BooleanExpression.le_correct]
                apply Nat.le_of_lt
                exact hcounterinv
              . exact hconsentinv
              . exact hreqdelinv
            . intros σ τ hleft
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hknlt30⟩
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hreqdelinv⟩
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hcounterinv, hconsentinv⟩
              apply negation_inversion at hknlt30
              apply expression_inversion at hknlt30
              conv_rhs at hknlt30 => simp
              rw [BooleanExpression.lt_false_iff, BooleanExpression.le_correct] at hknlt30

              repeat apply conjunction_intro <;> normalize
              . apply expression_intro
                rw [BooleanExpression.eq_correct]
                rw [counter_invariant₁'] at hcounterinv
                apply expression_inversion at hcounterinv
                rw [BooleanExpression.le_correct] at hcounterinv
                rw [Nat.eq_iff_le_and_ge]
                exact ⟨hcounterinv, hknlt30⟩
              . exact hconsentinv
              . exact hreqdelinv
            . intros σ τ τext hleft
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hdelinv⟩
              exact hdelinv
            . intros σ τ τext hleft
              apply conjunction_inversion at hleft
              rcases hleft with ⟨hleft, hdelinv⟩
              exact hdelinv
            . rw [counter_invariant₁', consent_invariant, request_deletion_invariant₁] ; auto_wf
            . rw [counter_invariant₁', request_deletion_invariant₁] ; auto_wf
            . auto_wf
            . auto_wf
          . apply seq_rule
              (Q := counter_invariant₂ ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂)
              (β := deletion_invariant₂)
            . apply conseq_rule
              . apply assign_rule
                  (P := ⋆$"k" ⋆= ♯30 ⋆∧ ⋆$"k'" ⋆= ♯0 ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₁)
                  (α := deletion_invariant₁)
              . intros σ τ h
                apply conjunction_inversion at h
                rcases h with ⟨hleft, hreqdelinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hk, hconsentinv⟩

                repeat apply conjunction_intro <;> normalize
                . exact hk
                . exact expression_intro rfl
                . rw [nonexistent_variable_replacement] ; rotate_left
                  . rw [consent_invariant] ; auto_contains
                  exact hconsentinv
                . rw [nonexistent_variable_replacement] ; rotate_left
                  . rw [request_deletion_invariant₁] ; auto_contains
                  exact hreqdelinv
              . intros σ τ h
                apply conjunction_inversion at h
                rcases h with ⟨hleft, hreqdelinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hconsentinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hk, hk'⟩

                repeat apply conjunction_intro <;> normalize
                . exact hk
                . apply expression_inversion at hk'
                  rw [BooleanExpression.eq_correct] at hk'
                  apply expression_intro
                  rw [BooleanExpression.lt_correct]
                  rw [hk']
                  exact BooleanExpression.lt_correct.mp rfl
                . exact hconsentinv
                . apply request_deletion_invariant₁_implies_request_deletion_invariant₂
                  . exact hreqdelinv
                  . exact hk
                  . exact hk'
              . intros σ τ τext h
                apply conjunction_inversion at h
                rcases h with ⟨_, h⟩
                normalize at h
                rw [nonexistent_variable_replacement] at h ; rotate_left
                . rw [deletion_invariant₁] ; auto_contains
                exact h
              . intros σ τ τext h
                apply conjunction_inversion at h
                rcases h with ⟨hleft, hdelinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hreqdelinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hconsentinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hk, hk'⟩

                rw [nonexistent_term_replacement] ; rotate_left
                . rw [deletion_invariant₁] ; auto_contains

                normalize at hk'

                apply deletion_invariant₂_implies_deletion_invariant₁
                . exact hdelinv
                . exact hk'
              . rw [consent_invariant, request_deletion_invariant₁] ; auto_wf
              . rw [request_deletion_invariant₁] ; auto_wf
              . rw [deletion_invariant₁] ; auto_wf
              . auto_wf
            . apply conseq_rule
              . apply while_rule
                  (P := counter_invariant₂' ⋆∧ consent_invariant ⋆∧ request_deletion_invariant₂)
                  (α := deletion_invariant₂)
                . apply conseq_rule
                  . apply resolve_block_sound
                  . intros σ τ hleft
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hk'k⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hreqdelinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hconsentinv⟩
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hk30, hk'le30⟩

                    repeat apply conjunction_intro <;> normalize
                    . exact hk30
                    . apply expression_intro
                      rw [BooleanExpression.lt_correct]
                      normalize
                      apply expression_inversion at hk'k
                      rw [BooleanExpression.lt_correct] at hk'k
                      normalize at hk'k
                      apply expression_inversion at hk30
                      rw [BooleanExpression.eq_correct] at hk30
                      normalize at hk30
                      rw [hk30] at hk'k
                      exact hk'k
                    . exact hconsentinv
                    . exact hreqdelinv
                  . exact fun σ τ a => a
                  . intros σ τ τext hleft
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hdelinv⟩
                    exact hdelinv
                  . intros σ τ τext hleft
                    apply conjunction_inversion at hleft
                    rcases hleft with ⟨hleft, hdelinv⟩
                    exact hdelinv
                  . auto_wf
                  . auto_wf
                  . auto_wf
                  . auto_wf
              . intros σ τ hleft
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hreqdelinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hconsentinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hk, hk'⟩

                repeat apply conjunction_intro <;> normalize
                . exact hk
                . apply expression_intro
                  rw [BooleanExpression.le_correct]
                  apply expression_inversion at hk'
                  rw [BooleanExpression.lt_correct] at hk'
                  apply Nat.le_of_lt
                  exact hk'
                . exact hconsentinv
                . exact hreqdelinv
              . intros σ τ hleft
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hk'k⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hreqdelinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hcounterinv, hconsentinv⟩
                exact hconsentinv
              . intros σ τ τext h
                apply conjunction_inversion at h
                rcases h with ⟨_, h⟩
                normalize at h
                exact h
              . intros σ τ τext h
                normalize at h
                apply conjunction_inversion at h
                rcases h with ⟨hleft, htop⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hk'k⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hreqdelinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hleft, hconsentinv⟩
                apply conjunction_inversion at hleft
                rcases hleft with ⟨hk, hk'⟩

                normalize at hk
                apply expression_inversion at hk
                rw [BooleanExpression.eq_correct] at hk
                normalize at hk'
                apply expression_inversion at hk'
                rw [BooleanExpression.le_correct] at hk'
                apply negation_inversion at hk'k
                apply expression_inversion at hk'k
                conv_rhs at hk'k => simp
                rw [BooleanExpression.lt_false_iff] at hk'k
                rw [BooleanExpression.le_correct] at hk'k
                rw [hk] at hk'k

                normalize at hk'
                normalize at hk'k

                have hk'eq30 : σ (⋆$"k'") = 30 := by
                  rw [Nat.eq_iff_le_and_ge]
                  exact ⟨hk', hk'k⟩

                rw [deletion_invariant₂]
                normalize
                apply universal_quantification_intro
                intros vidx
                apply disjunction_intro_left
                apply negation_intro
                normalize
                rw [expression_conjunction_iff]
                rw [BooleanExpression.conj_false_iff]
                rw [BooleanExpression.le_false_iff]
                rw [BooleanExpression.lt_correct]
                rw [BooleanExpression.lt_false_iff]
                rw [BooleanExpression.le_correct]
                normalize
                simp [Store.update]
                normalize at hk
                rw [hk, hk'eq30]
                apply Nat.lt_or_ge
              . auto_wf
              . auto_wf
              . auto_wf
              . auto_wf
            . auto_wf
            . auto_wf
          . auto_wf
          . auto_wf
        . auto_wf
        . auto_wf
    . exact fun σ τ a => a
    . exact present_implies_top
    . exact future_implies_top
    . exact future_implies_top
    . auto_wf
    . auto_wf
    . auto_wf
    . auto_wf
  . auto_wf
  . auto_wf
