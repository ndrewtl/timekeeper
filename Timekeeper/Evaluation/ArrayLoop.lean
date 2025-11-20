import Timekeeper.Lemma.Soundness.Past
import Timekeeper.Lemma.TraceAssertion

namespace Timekeeper.Evaluation.ArrayLoop
open Command
open Soundness.Basic
open GeneralAssertion
open GeneralAssertion.Models
open BinOp
open Variable
open NumericExpression


def program : Command :=
  -- Loop invariant: ∀ x: x < i -> arr[x] = 42
  while: (⋆$"i") ⋆< ♯5
   do:
     set ⋆$"arr" ⋆:= (⋆$"arr")[⋆$"i" := ♯42]ₑ ⋆;
     set ⋆$"i" ⋆:= ⋆$"i" ⋆+ ♯1
    end

lemma soundness : ⦃ ⋆$"i" ⋆= ♯0 ⦄ program ⦃ ⋆∀ "x": (⋆^"x" ⋆< ♯5 ⋆→ (⋆$"arr")[ ⋆^"x" ]ₑ ⋆= ♯42) ⦄ := by
  apply conseq_rule
  . apply while_rule
      (P := ⋆$"i" ⋆≤ ♯5 ⋆∧ (⋆∀ "x": (⋆^"x" ⋆< ⋆$"i" ⋆→ (⋆$"arr")[ ⋆^"x" ]ₑ ⋆= ♯42)))
    . apply seq_rule
      . apply conseq_rule
          (Q' := (⋆$"i" ⋆≤ ♯5 ⋆∧ (⋆∀ "x" : (⋆⋆^"x" ⋆< ⋆⋆$"i" ⋆→ (⋆⋆$"arr")[ ⋆⋆^"x" ]ₑ ⋆= ♯42)))[⋆$"i" ↦ ⋆⋆$"i" ⋆+ ♯1])
        . apply assign_rule
           (P := (⋆$"i" ⋆≤ ♯4 ⋆∧ (⋆∀ "x" : (⋆⋆^"x" ⋆< ⋆⋆$"i" ⋆+ ♯1 ⋆→ (⋆$"arr")[ ⋆^"x" ]ₑ ⋆= ♯42))))
        . intros σ τ h
          apply conjunction_inversion at h
          rcases h with ⟨h, hilt⟩
          apply conjunction_inversion at h
          rcases h with ⟨hibound, hquant⟩
          apply conjunction_intro <;> normalize
          . apply expression_intro
            rw [BooleanExpression.le_correct]
            normalize
            normalize at hilt
            apply expression_inversion at hilt
            rw [BooleanExpression.lt_correct] at hilt
            normalize at hilt
            apply Nat.le_of_lt_succ
            exact hilt
          apply universal_quantification_intro
          intros v'
          apply universal_quantification_inversion at hquant
          specialize hquant v'
          apply disjunction_inversion at hquant
          set σ' := σ[⋆^"x" ↦ v']
          set x := ⋆^"x"
          set i := ⋆$"i"
          by_cases hieqx : σ' i = σ' x
          . apply disjunction_intro_right
            apply expression_intro
            rw [BooleanExpression.eq_correct]
            normalize
            rw [hieqx, PrimesMap.set_correct]
          . rcases hquant with (hxi | harrx42)
            . apply negation_inversion at hxi
              apply expression_inversion at hxi
              normalize at hxi
              have hieqx : i ≠ x := by exact not_eq_of_beq_eq_false rfl
              have hix : σ' i < σ' x := by grind
              clear hxi hieqx
              apply disjunction_intro_left
              apply negation_intro
              apply expression_intro
              unfold x i
              normalize
              grind
            . apply disjunction_intro_right
              apply expression_inversion at harrx42
              normalize at harrx42
              apply expression_intro
              normalize
              rw [PrimesMap.set_limited] ; rotate_left
              . exact hieqx
              . exact harrx42
        . intros σ τ h
          apply conjunction_inversion at h
          rcases h with ⟨hilt, h⟩
          apply conjunction_intro
          . normalize
            apply expression_intro
            rw [BooleanExpression.le_correct]
            normalize
            apply expression_inversion at hilt
            rw [BooleanExpression.le_correct] at hilt
            normalize at hilt
            apply Nat.le_succ_of_pred_le
            exact hilt
          apply universal_quantification_intro
          intros v'
          apply universal_quantification_inversion at h
          specialize h v'
          apply disjunction_inversion at h
          rcases h with (hxi | harrx42)
          . apply negation_inversion at hxi
            apply expression_inversion at hxi
            conv_rhs at hxi => simp
            rw [BooleanExpression.lt_false_iff, BooleanExpression.le_correct] at hxi
            normalize
            apply disjunction_intro_left
            apply negation_intro
            normalize
            apply expression_intro
            rw [BooleanExpression.lt_false_iff, BooleanExpression.le_correct]
            exact hxi
          . apply expression_inversion at harrx42
            normalize at harrx42
            apply disjunction_intro_right
            apply expression_intro
            normalize
            exact harrx42
        . auto_wf
        . auto_wf
      . apply assign_rule
      . auto_wf
  . intros σ τ h
    apply expression_inversion at h
    rw [BooleanExpression.eq_correct] at h
    normalize at h
    apply conjunction_intro <;> normalize
    . apply expression_intro
      rw [BooleanExpression.le_correct]
      normalize
      rw [h]
      trivial
    . apply universal_quantification_intro
      intros v'
      apply disjunction_intro_left
      apply negation_intro
      normalize
      apply expression_intro
      rw [BooleanExpression.lt_false_iff, BooleanExpression.le_correct]
      normalize
      simp [Store.update]
      rw [h]
      apply Nat.zero_le
  . intros σ τ h
    apply conjunction_inversion at h
    rcases h with ⟨h, hibound⟩
    apply conjunction_inversion at h
    rcases h with ⟨hileq5, hquant⟩
    apply expression_inversion at hileq5
    rw [BooleanExpression.le_correct] at hileq5
    normalize at hileq5
    apply negation_inversion at hibound
    normalize at hibound
    apply expression_inversion at hibound
    rw [BooleanExpression.lt_false_iff, BooleanExpression.le_correct] at hibound
    normalize at hibound
    have hieq5 : σ (⋆$"i") = 5 := by
      rw [Nat.eq_iff_le_and_ge]
      exact ⟨hileq5, hibound⟩
    apply universal_quantification_intro
    intros v'
    clear hibound
    apply universal_quantification_inversion at hquant
    specialize hquant v'

    apply disjunction_inversion at hquant
    rcases hquant with (hxi | harrx42)
    . apply disjunction_intro_left
      apply negation_inversion at hxi
      normalize at hxi
      apply expression_inversion at hxi
      rw [BooleanExpression.lt_false_iff, BooleanExpression.le_correct] at hxi
      normalize at hxi
      simp [Store.update] at hxi
      apply negation_intro
      normalize
      apply expression_intro
      rw [BooleanExpression.lt_false_iff, BooleanExpression.le_correct]
      normalize
      simp [Store.update]
      rw [hieq5] at hxi
      exact hxi
    . apply expression_inversion at harrx42
      normalize at harrx42
      apply disjunction_intro_right
      apply expression_intro
      normalize
      exact harrx42
  . auto_wf
  . auto_wf
