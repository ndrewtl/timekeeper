import Timekeeper.Language.Semantics.Store
import Timekeeper.Language.Semantics.BigStep
import Timekeeper.Logic.Correctness.Basic
import Timekeeper.Logic.Evaluation.GeneralAssertion
import Timekeeper.Lemma.TraceAssertion
import Timekeeper.Lemma.StepEquivalence
import Timekeeper.Lemma.SmallStep
import Timekeeper.Lemma.GeneralAssertion
import Timekeeper.Lemma.BigStep

namespace Timekeeper.Soundness.Basic
open Relation
open Command
open SmallStep
open GeneralAssertion
open GeneralAssertion.Models
open StepEquivalence

lemma skip_rule :
  ⦃ P ⦄ skip ⦃ P ⦄ := by
  intros hprewf hcwf hpostwf σ τ σ' τ' hpre hstep
  apply SmallStepRTC.skip_inversion at hstep
  rcases hstep with ⟨hσ', hτ'⟩
  rw [hσ', hτ']
  exact hpre

lemma emit_rule :
  ⦃ S⋆(Es) ⋆@ ℓ ⋆∧ P[ℓ ↦ (ℓ ⋆+ ♯1)] ⦄ emit Es ⦃ P ⋆∧ ⋆!Es⋆@(ℓ ⋆- ♯1) ⦄ := by
  intros hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  simp [GeneralAssertion.wellFormed] at hprewf
  rcases hprewf with ⟨hSwf, hPwf⟩
  normalize at hPwf
  rw [trace_length_addition_preserves_well_formedness] at hPwf

  apply conjunction_inversion at hpre
  rcases hpre with ⟨hSpre, hPpre⟩
  apply conjunction_intro
  . rcases hstep with (contr | ⟨hfirst, hrest⟩)
    . rcases _ : hfirst
      apply SmallStepRTC.skip_inversion at hrest
      rcases hrest with ⟨hσ, hτ⟩
      rw [hσ, hτ]
      set e := ⟦ Es ⟧(σ, τ)
      apply GeneralAssertion.trace_extension_plus_one hPpre
      . exact hPwf
  . rcases _ : hstep with (_ | ⟨hfirst, hrest⟩)
    rcases _ : hfirst
    apply SmallStepRTC.skip_inversion at hrest
    rcases hrest with ⟨rfl, rfl⟩
    apply trace_intro
    normalize
    apply TraceAssertion.Models.atomic_intro
    . normalize
      simp [GeneralAssertion.wellFormed] at hpostwf
      rcases hpostwf with ⟨hPwf, hEswf⟩
      simp [TraceAssertion.wellFormed] at hEswf
      simp [NumericExpressionList.containsExpression] at hEswf
      intros E hEEs
      normalize
      rw [NumericExpression.trace_independence]
      . exact hEswf E hEEs
    simp

lemma resolve_rule :
  ⦃ P ⋆∧ ω ⦄ resolve ω ⦃ P ⋆∧ ω ⦄ := by
  intros hprewf hwf hpostwf σ τ σ' τ' hpre hstep
  rcases hstep with (_ | ⟨hfirst, hrest⟩)
  rcases hfirst
  apply SmallStepRTC.skip_inversion at hrest
  rcases hrest with ⟨hσ', hτ'⟩
  rw [hσ', hτ']
  exact hpre

lemma if_rule :
  ⦃ P ⋆∧ ~B ⦄ C₁ ⦃ P' ⦄ ->
  ⦃ P ⋆∧ ⋆¬(~B) ⦄ C₂ ⦃ P' ⦄ ->
  ⦃ P ⦄ if: B then: C₁ else: C₂ end ⦃ P' ⦄ := by
  intros hC₁ hC₂ hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
  simp [Command.wellFormed, Command.numericExpressionPredicate] at hCwf
  rcases hCwf with ⟨hBwf, hC₁wf, hC₂wf⟩
  rcases hstep with (_ | ⟨hfirst, hrest⟩)

  cases _ : hfirst with
  | small_step_if_true b c₁ c₂ σ τ hB' =>
    rcases hB : ⟦B⟧(σ, τ) <;> try simp [hB'] at hB
    apply hC₁
    . simp [GeneralAssertion.wellFormed]
      exact hprewf
    . simp [Command.wellFormed]
      exact hC₁wf
    . exact hpostwf
    . apply conjunction_intro
      . exact hpre
      . apply expression_intro
        simp [hB']
    . exact hrest
  | small_step_if_false b c₁ c₂ σ τ hB' =>
    rcases hB : ⟦B⟧(σ, τ) <;> try simp [hB'] at hB
    apply hC₂
    . simp [GeneralAssertion.wellFormed]
      exact hprewf
    . simp [Command.wellFormed]
      exact hC₂wf
    . exact hpostwf
    . apply conjunction_intro
      . exact hpre
      . apply negation_intro
        apply expression_intro
        simp [hB']
    . exact hrest

lemma seq_rule :
  ⦃ P ⦄ C₁ ⦃ Q ⦄ ->
  ⦃ Q ⦄ C₂ ⦃ R ⦄ ->
  Q.wellFormed ->
  ⦃ P ⦄ C₁ ⋆; C₂ ⦃ R ⦄ := by
  intros hC₁ hC₂ hQwf hprewf hwf hpostwf σ τ σ' τ' hpre hstep

  -- Pull out well-formedness information
  simp [Command.wellFormed, Command.numericExpressionPredicate] at hwf
  rcases hwf with ⟨hC₁wf, hC₂wf⟩

  apply small_step_implies_big_step at hstep
  cases hstep with
  | big_step_seq hC₁big hC₂big =>
    set hC₁small := big_step_implies_small_step hC₁big
    set hC₂small := big_step_implies_small_step hC₂big
    apply hC₂
    . exact hQwf
    . simp [Command.wellFormed]
      exact hC₂wf
    . exact hpostwf
    apply hC₁
    . exact hprewf
    . simp [Command.wellFormed]
      exact hC₁wf
    . exact hQwf
    . exact hpre
    . exact hC₁small
    . exact hC₂small

lemma disj_rule :
  ⦃ P₁ ⦄ C ⦃ Q₁ ⦄ ->
  ⦃ P₂ ⦄ C ⦃ Q₂ ⦄ ->
  ⦃ P₁ ⋆∨ P₂ ⦄ C ⦃ Q₁ ⋆∨ Q₂ ⦄ := by
  intros h₁ h₂ hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  -- Simplify well-formedness lemmas
  simp [GeneralAssertion.wellFormed] at hprewf
  rcases hprewf with ⟨hP₁wf, hP₂wf⟩
  simp [GeneralAssertion.wellFormed] at hpostwf
  rcases hpostwf with ⟨hQ₁wf, hQ₂wf⟩

  simp at hpre
  apply disjunction_inversion at hpre
  rcases hpre with (hP₁ | hP₂)
  . apply disjunction_intro_left
    simp at hP₁
    exact h₁ hP₁wf hCwf hQ₁wf σ τ σ' τ' hP₁ hstep
  . apply disjunction_intro_right
    simp at hP₂
    exact h₂ hP₂wf hCwf hQ₂wf σ τ σ' τ' hP₂ hstep

lemma conj_rule :
  ⦃ P₁ ⦄ C ⦃ Q₁ ⦄ ->
  ⦃ P₂ ⦄ C ⦃ Q₂ ⦄ ->
  ⦃ P₁ ⋆∧ P₂ ⦄ C ⦃ Q₁ ⋆∧ Q₂ ⦄ := by
  intros h₁ h₂ hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  simp [GeneralAssertion.wellFormed] at hprewf
  rcases hprewf with ⟨hP₁wf, hP₂wf⟩

  simp [GeneralAssertion.wellFormed] at hpostwf
  rcases hpostwf with ⟨hQ₁wf, hQ₂wf⟩

  apply conjunction_inversion at hpre
  rcases hpre with ⟨hP₁, hP₂⟩
  simp
  apply conjunction_intro
  . exact h₁ hP₁wf hCwf hQ₁wf σ τ σ' τ' hP₁ hstep
  . exact h₂ hP₂wf hCwf hQ₂wf σ τ σ' τ' hP₂ hstep

lemma conseq_rule {P P' Q Q' : GeneralAssertion} :
  ⦃ P ⦄ C ⦃ Q ⦄ ->
  P' ⋆-> P ->
  Q ⋆-> Q' ->
  P.wellFormed ->
  Q.wellFormed ->
  ⦃ P' ⦄ C ⦃ Q' ⦄ := by
  intros hPQ hP'P hQQ' hPwf hQwf hprewf hCwf hpostwf σ τ σ' τ' hP' hstep

  specialize hP'P σ τ
  specialize hQQ' σ' τ'
  specialize hPQ hPwf hCwf hQwf σ τ σ' τ' _ hstep

  apply hP'P
  . exact hP'
  . exact hQQ' hPQ

lemma conseq_rule_P {P P' Q : GeneralAssertion} :
  ⦃ P ⦄ C ⦃ Q ⦄ ->
  P' ⋆-> P ->
  P.wellFormed ->
  Q.wellFormed ->
  ⦃ P' ⦄ C ⦃ Q ⦄ := by
  intros hPQ hP'P hPwf hQwf
  apply conseq_rule hPQ hP'P _ hPwf hQwf
  . intros σ τ h ; exact h

lemma conseq_rule_Q {P Q : GeneralAssertion} :
  ⦃ P ⦄ C ⦃ Q ⦄ ->
  Q ⋆-> Q' ->
  P.wellFormed ->
  Q.wellFormed ->
  ⦃ P ⦄ C ⦃ Q' ⦄ := by
  intros hPQ hQQ' hPwf hQwf
  apply conseq_rule hPQ _ hQQ' hPwf hQwf
  . intros σ τ h ; exact h

lemma assign_rule :
  ⦃ P[⋆$x ↦ E] ⦄ set ⋆$x ⋆:= E ⦃ P ⦄ := by
  intros hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  -- Ascertain the values of σ' and τ'
  rcases hstep with (_ | ⟨hfirst, hrest⟩)

  rcases _ : hfirst
  apply SmallStepRTC.skip_inversion at hrest
  rcases hrest with ⟨hσ', hτ'⟩
  rw [hσ', hτ']

  simp at hpre
  rw [<-GeneralAssertion.variable_replacement] at hpre
  set hremap := GeneralAssertion.evaluation_remapping (E := E)
  specialize hremap _
  . simp [Command.wellFormed, Command.numericExpressionPredicate] at hCwf
    exact hCwf
  rw [hremap] at hpre
  exact hpre

lemma while_rule :
  ⦃ P ⋆∧ ~B ⦄ C ⦃ P ⦄ ->
  ⦃ P ⦄ while: B do: C end ⦃ P ⋆∧ ⋆¬~B ⦄ := by
  intros hC hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
  apply small_step_implies_big_step at hstep
  simp [Command.wellFormed, Command.numericExpressionPredicate] at hCwf
  rcases hCwf with ⟨hBwf, hCwf⟩
  generalize hC' : (while: B do: C end) = C' at hstep
  revert B C
  induction hstep <;> try simp
  case big_step_while_false hB =>
    intros B C hC hprewf hBwf hCwf hB' hC'
    apply conjunction_intro hpre
    . apply negation_intro
      apply expression_intro
      rw [hB']
      simp [hB]
  case big_step_while_true hB hCbig hwhilebig ih₁ ih₂ =>
    intros B C hC hprewf' hBwf hCwf hB' hC'
    rw [<-hC'] at hCbig
    rw [<-hB'] at hB
    apply ih₂ _ hC hprewf' hBwf hCwf
    . rw [<-hB', <-hC']
    . apply hC
      . exact hprewf'
      . simp [Command.wellFormed]
        exact hCwf
      . (expose_names; exact hprewf)
      . apply conjunction_intro hpre
        . apply expression_intro
          simp [hB]
      . exact big_step_implies_small_step hCbig
