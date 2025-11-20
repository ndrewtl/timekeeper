-- This proof strategy is derived from the one exhibited in
-- Cornell CS 6115 - Certified Software Systems, taught by Nate Foster and Jules -- Jacobs.
-- https://www.cs.cornell.edu/courses/cs6115/2024fa/lectures/lec08_small_step.html
import Timekeeper.Language.Semantics.SmallStep
import Timekeeper.Language.Semantics.BigStep
import Timekeeper.Lemma.SmallStep

namespace Timekeeper.StepEquivalence
open Command
open SmallStep
open SmallStepRTC
open BigStep

lemma big_step_implies_small_step :
  ((C, σ, τ) ↓ (σ', τ'))->
  (C, σ, τ) ⇝* (skip, σ' ,τ') := by
  intros hbig
  induction hbig with
  | big_step_skip =>
    apply SmallStepRTC.refl
  | big_step_assign =>
    apply SmallStepRTC.step
    . apply small_step_assign
    . apply SmallStepRTC.refl
  | big_step_emit =>
    apply SmallStepRTC.step
    . apply small_step_emit
    . apply SmallStepRTC.refl
  | big_step_resolve =>
    apply SmallStepRTC.step
    . apply small_step_resolve
    . apply SmallStepRTC.refl
  | big_step_seq hC₁ hC₂ ihC₁ ihC₂ =>
    apply SmallStepRTC.trans
    . apply SmallStepRTC.seq_lift ihC₁
    . apply SmallStepRTC.step _ ihC₂
      apply small_step_seq
  | big_step_if_false hB _ hsmallC₂ =>
    apply SmallStepRTC.step
    . apply small_step_if_false
      exact ne_true_of_eq_false hB
    . exact hsmallC₂
  | big_step_if_true hB _ hsmallC₁ =>
    apply SmallStepRTC.step
    . apply small_step_if_true
      exact hB
    . exact hsmallC₁
  | big_step_while_false hB =>
    apply SmallStepRTC.step
    . apply small_step_while
    . apply SmallStepRTC.step
      . apply small_step_if_false
        exact ne_true_of_eq_false hB
      . apply SmallStepRTC.refl
  | big_step_while_true hB hbig hsmall ihC ihwhile =>
    apply step
    . apply small_step_while
    . apply step
      . apply small_step_if_true
        exact hB
      . apply SmallStepRTC.trans
        . apply SmallStepRTC.seq_lift
          exact ihC
        . apply step
          . apply small_step_seq
          . exact ihwhile

-- Adding a single leading small step to a big-step relation preserves the big
-- step outcome
lemma small_step_preserves_big_step :
  (C, σ, τ) ⇝ (C', σ', τ') ->
  (C', σ', τ') ↓ (σ'', τ'') ->
  (C, σ, τ) ↓ (σ'', τ'') := by
  intros hsmall hbig
  revert C σ τ hsmall
  induction hbig with
  | big_step_skip =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_skip σ τ =>
      apply big_step_skip
    | small_step_assign x E σ τ =>
      apply big_step_assign
    | small_step_emit E σ τ =>
      apply big_step_emit
    | small_step_resolve ω σ τ =>
      apply big_step_resolve
    | small_step_seq C₂ σ τ =>
      apply big_step_seq <;> apply big_step_skip
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true
      . exact hB
      . exact big_step_skip
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB
        exact hB
      . exact big_step_skip
  | big_step_assign =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_assign
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true hB
      exact big_step_assign
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB; exact hB
      . exact big_step_assign
  | big_step_emit =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_emit
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true hB
      exact big_step_emit
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB; exact hB
      . exact big_step_emit
  | big_step_resolve =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_resolve
    | small_step_if_true B C₁ C₂ σ τ hB =>
      simp [big_step_if_true, hB, big_step_resolve]
    | small_step_if_false B C₁ C₂ σ τ hB =>
      simp [big_step_if_false, hB, big_step_resolve]
  | big_step_seq hbig₁ hbig₂ ih₁ ih₂ =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq_reduce C₁ C₁' C₂ σ τ σ' τ' ih =>
      exact big_step_seq (ih₁ ih) hbig₂
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_seq hbig₁ hbig₂
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true
      . exact hB
      . exact big_step_seq hbig₁ hbig₂
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB; exact hB
      . exact big_step_seq hbig₁ hbig₂
  | big_step_if_false hB hbig ih =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_if_false hB hbig
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true hB
      apply big_step_if_false
      . simp [*]
      . exact hbig
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB
        exact hB
      . apply big_step_if_false
        . simp [*]
        . exact hbig
    | small_step_while B C σ τ =>
      rcases hbig
      apply big_step_while_false
      exact hB
  | big_step_if_true hB hbig ih =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_if_true hB hbig
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true
      . exact hB
      . apply big_step_if_true
        . simp [*]
        . exact hbig
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB; exact hB
      . apply big_step_if_true
        . simp [*]
        . exact hbig
    | small_step_while B C σ τ =>
      cases hbig with
      | big_step_seq hbigC hbigwhile =>
        exact big_step_while_true hB hbigC hbigwhile
  | big_step_while_false hB =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_while_false hB
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true
      . exact hB
      . apply big_step_while_false
        simp [*]
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB; exact hB
      . apply big_step_while_false
        simp [*]
  | big_step_while_true hB hbigC hbigwhile ih₁ ih₂ =>
    intros C σ τ hsmall
    cases hsmall with
    | small_step_seq C₂ σ τ =>
      apply big_step_seq
      . exact big_step_skip
      . exact big_step_while_true hB hbigC hbigwhile
    | small_step_if_true B C₁ C₂ σ τ hB =>
      apply big_step_if_true hB
      . apply big_step_while_true _ hbigC hbigwhile
        simp [*]
    | small_step_if_false B C₁ C₂ σ τ hB =>
      apply big_step_if_false
      . simp at hB ; exact hB
      . apply big_step_while_true _ hbigC hbigwhile
        simp [*]

lemma small_step_implies_big_step :
  (C, σ, τ) ⇝* (skip, σ', τ') ->
  (C, σ, τ) ↓ (σ', τ') := by
  intros hsmall
  generalize hskip : skip = Cskip at hsmall
  induction hsmall with
  | refl =>
    rw [<-hskip]
    exact big_step_skip
  | step hfirst hrest ih =>
    apply small_step_preserves_big_step
    . exact hfirst
    . apply ih hskip

lemma big_step_iff_small_step :
  (C, σ, τ) ⇝* (skip, σ', τ') <->
  (C, σ, τ) ↓ (σ', τ') := by
  constructor
  . exact small_step_implies_big_step
  . exact big_step_implies_small_step
