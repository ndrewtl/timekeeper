import Timekeeper.Logic.Correctness.Past
import Timekeeper.Lemma.Soundness.Basic
import Timekeeper.Lemma.BigStep
import Timekeeper.Lemma.TraceAssertion

namespace Timekeeper.Soundness.Past
open Correctness.Past
open Command
open GeneralAssertion.Models
open StepEquivalence

lemma skip_rule :
  S ⊢ ⦃ P ⦄ skip ⦃ P ⦄ := by
  intros hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
  constructor
  . apply Basic.skip_rule hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
  . intros hSwf hSτ
    apply SmallStepRTC.skip_inversion at hstep
    rcases hstep with ⟨⟨⟩, ⟨⟩⟩
    exact hSτ

lemma emit_rule :
  S ⊢ ⦃ S⋆(Es) ⋆@ ℓ ⋆∧ P[ℓ ↦ (ℓ ⋆+ ♯1)] ⦄ emit Es ⦃ P ⋆∧ ⋆!Es⋆@(ℓ ⋆- ♯1) ⦄ := by
  intros hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  constructor
  . apply Basic.emit_rule hprewf hCwf hpostwf
    . exact hpre
    . exact hstep
  . intros hSwf hSτ

    simp [GeneralAssertion.wellFormed] at hprewf
    simp [Specification.wellFormed] at hSwf

    apply conjunction_inversion at hpre
    rcases hpre with ⟨hpreS, hpreP⟩
    apply trace_inversion at hpreS
    apply TraceAssertion.Models.function_inversion at hpreS
    simp [NumericExpression.evaluate] at hpreS
    rw [<-NumericExpressionList.eval] at hpreS

    apply SmallStepRTC.emit_inversion at hstep
    rcases hstep with ⟨⟨⟩, ⟨⟩⟩

    apply extend_trace_invariant
    . simp [Specification.wellFormed]
      exact fun E => hSwf E
    . exact hSτ

    exact hpreS

lemma resolve_rule :
  S ⊢ ⦃ P ⋆∧ ω ⦄ resolve ω ⦃ P ⋆∧ ω ⦄ := by
  intros hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
  constructor
  . apply Basic.resolve_rule hprewf hCwf hpostwf
    . exact hpre
    . exact hstep
  . intros hSwf hSτ
    apply SmallStepRTC.resolve_inversion at hstep
    rcases hstep with ⟨⟨⟩, ⟨⟩⟩
    exact hSτ

lemma if_rule :
  S ⊢ ⦃ P ⋆∧ ~B ⦄ C₁ ⦃ P' ⦄ ->
  S ⊢ ⦃ P ⋆∧ ⋆¬(~B) ⦄ C₂ ⦃ P' ⦄ ->
  S ⊢ ⦃ P ⦄ if: B then: C₁ else: C₂ end ⦃ P' ⦄ := by
  intros hC₁ hC₂ hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  constructor
  . apply Basic.if_rule _ _ hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
    . exact implies_basic_validity hC₁
    . exact implies_basic_validity hC₂
  . intros hSwf hSτ

    -- Pull out well-formedness information
    simp [Command.wellFormed, Command.numericExpressionPredicate] at hCwf
    rcases hCwf with ⟨hBwf, hC₁wf, hC₂wf⟩

    rcases hB : ⟦B⟧(σ, τ)
    . specialize hC₂ _ _ hpostwf σ τ σ' τ' _ _
      . simp [GeneralAssertion.wellFormed]
        exact hprewf
      . simp [Command.wellFormed]
        exact hC₂wf
      . apply conjunction_intro
        . exact hpre
        . apply negation_intro
          apply expression_intro
          simp [hB]
      . apply small_step_implies_big_step at hstep
        apply BigStep.if_false_inversion at hstep
        specialize hstep hB
        exact big_step_implies_small_step hstep
      rcases hC₂ with ⟨hP', hSτ'⟩
      exact hSτ' hSwf hSτ
    . specialize hC₁ _ _ hpostwf σ τ σ' τ' _ _
      . simp [GeneralAssertion.wellFormed]
        exact hprewf
      . simp [Command.wellFormed]
        exact hC₁wf
      . apply conjunction_intro
        . exact hpre
        . apply expression_intro
          simp [hB]
      . apply small_step_implies_big_step at hstep
        apply BigStep.if_true_inversion at hstep
        specialize hstep hB
        exact big_step_implies_small_step hstep
      rcases hC₁ with ⟨hP', hSτ'⟩
      exact hSτ' hSwf hSτ

lemma seq_rule :
  S ⊢ ⦃ P ⦄ C₁ ⦃ Q ⦄ ->
  S ⊢ ⦃ Q ⦄ C₂ ⦃ R ⦄ ->
  Q.wellFormed ->
  S ⊢ ⦃ P ⦄ C₁ ⋆; C₂ ⦃ R ⦄ := by

  intros hC₁ hC₂ hQwf hprewf hCwf hpostwf σ τ σ'' τ'' hpre hstep
  constructor
  . apply Basic.seq_rule _ _ hQwf hprewf hCwf hpostwf
    . exact hpre
    . exact hstep
    . exact implies_basic_validity hC₁
    . exact implies_basic_validity hC₂
  . intros hSwf hSτ

    -- Pull out C₁ and C₂ well-formedness
    simp [Command.wellFormed, Command.numericExpressionPredicate] at hCwf
    rcases hCwf with ⟨hC₁wf, hC₂wf⟩

    apply small_step_implies_big_step at hstep
    apply BigStep.seq_inversion at hstep
    rcases hstep with ⟨σ', τ', hC₁step, hC₂step⟩
    apply big_step_implies_small_step at hC₁step
    apply big_step_implies_small_step at hC₂step

    specialize hC₁ hprewf _ hQwf σ τ σ' τ' hpre hC₁step
    . simp [Command.wellFormed]
      exact hC₁wf

    rcases hC₁ with ⟨hQ, hC₁⟩
    specialize hC₁ hSwf hSτ

    specialize hC₂ hQwf _ hpostwf σ' τ' σ'' τ'' hQ hC₂step
    . simp [Command.wellFormed]
      exact hC₂wf

    rcases hC₂ with ⟨hR, hC₂⟩
    specialize hC₂ hSwf hC₁

    exact hC₂

lemma disj_rule :
  S ⊢ ⦃ P₁ ⦄ C ⦃ Q₁ ⦄ ->
  S ⊢ ⦃ P₂ ⦄ C ⦃ Q₂ ⦄ ->
  S ⊢ ⦃ P₁ ⋆∨ P₂ ⦄ C ⦃ Q₁ ⋆∨ Q₂ ⦄ := by
  intros h₁ h₂ hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  constructor
  . apply Basic.disj_rule _ _ hprewf hCwf hpostwf _ _
    . exact hpre
    . exact hstep
    . exact implies_basic_validity h₁
    . exact implies_basic_validity h₂
  . intros hS hSτ
    -- Pull out well-formedness
    simp [GeneralAssertion.wellFormed] at hprewf
    rcases hprewf with ⟨hP₁wf, hP₂wf⟩

    simp [GeneralAssertion.wellFormed] at hpostwf
    rcases hpostwf with ⟨hQ₁wf, hQ₂wf⟩

    -- Case match on which of P₁ and P₂ holds
    apply disjunction_inversion at hpre
    rcases hpre with (hP₁ | hP₂)
    . specialize h₁ hP₁wf hCwf hQ₁wf σ τ σ' τ' hP₁ hstep
      rcases h₁ with ⟨hQ₁, h₁⟩
      exact h₁ hS hSτ
    . specialize h₂ hP₂wf hCwf hQ₂wf σ τ σ' τ' hP₂ hstep
      rcases h₂ with ⟨hQ₂, h₂⟩
      exact h₂ hS hSτ


lemma conj_rule :
  S ⊢ ⦃ P₁ ⦄ C ⦃ Q₁ ⦄ ->
  S ⊢ ⦃ P₂ ⦄ C ⦃ Q₂ ⦄ ->
  S ⊢ ⦃ P₁ ⋆∧ P₂ ⦄ C ⦃ Q₁ ⋆∧ Q₂ ⦄ := by
  intros h₁ h₂ hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  constructor
  . apply Basic.conj_rule _ _ hprewf hCwf hpostwf _ _
    . exact hpre
    . exact hstep
    . exact implies_basic_validity h₁
    . exact implies_basic_validity h₂
  . intros hSwf hSτ
    -- Pull out well-formedness
    simp [GeneralAssertion.wellFormed] at hprewf
    rcases hprewf with ⟨hP₁wf, hP₂wf⟩

    simp [GeneralAssertion.wellFormed] at hpostwf
    rcases hpostwf with ⟨hQ₁wf, hQ₂wf⟩

    apply conjunction_inversion at hpre

    -- We only need one of these to prove the correct trace result
    rcases hpre with ⟨hP₁, hP₂⟩

    specialize h₁ hP₁wf hCwf hQ₁wf σ τ σ' τ' hP₁ hstep
    rcases h₁ with ⟨hQ₁, h₁⟩
    specialize h₁ hSwf hSτ

    exact h₁

lemma conseq_rule {P P' Q Q' : GeneralAssertion} :
  S ⊢ ⦃ P ⦄ C ⦃ Q ⦄ ->
  P' ⋆-> P ->
  Q ⋆-> Q' ->
  P.wellFormed ->
  Q.wellFormed ->
  S ⊢ ⦃ P' ⦄ C ⦃ Q' ⦄ := by

  intros htriple hP'P hQQ' hPwf hQwf
  intros hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  constructor
  . apply Basic.conseq_rule _ hP'P hQQ' hPwf hQwf hprewf hCwf hpostwf
    . exact hpre
    . exact hstep
    . exact implies_basic_validity htriple
  . intros hSwf hSτ
    specialize htriple hPwf hCwf hQwf σ τ σ' τ' _ hstep
    . exact hP'P σ τ hpre
    rcases htriple with ⟨hQ, htriple⟩
    specialize htriple hSwf hSτ
    exact htriple

lemma conseq_rule_P {P P' Q : GeneralAssertion} :
  S ⊢ ⦃ P ⦄ C ⦃ Q ⦄ ->
  P' ⋆-> P ->
  P.wellFormed ->
  Q.wellFormed ->
  S ⊢ ⦃ P' ⦄ C ⦃ Q ⦄ := by
  intros hPQ hP'P hPwf hQwf
  apply conseq_rule hPQ hP'P _ hPwf hQwf
  . intros σ τ h ; exact h

lemma conseq_rule_Q {P Q : GeneralAssertion} :
  S ⊢ ⦃ P ⦄ C ⦃ Q ⦄ ->
  Q ⋆-> Q' ->
  P.wellFormed ->
  Q.wellFormed ->
  S ⊢ ⦃ P ⦄ C ⦃ Q' ⦄ := by
  intros hPQ hQQ' hPwf hQwf
  apply conseq_rule hPQ _ hQQ' hPwf hQwf
  . intros σ τ h ; exact h

lemma assign_rule :
  S ⊢ ⦃ P[⋆$x ↦ E] ⦄ set ⋆$x ⋆:= E ⦃ P ⦄ := by
  intros hprewf hCwf hpostwf σ τ σ' τ' hpre hstep

  constructor
  . apply Basic.assign_rule hprewf hCwf hpostwf
    . exact hpre
    . exact hstep

  . intros hSwf hSστ
    apply SmallStepRTC.assign_inversion at hstep
    rcases hstep with ⟨⟨⟩, ⟨⟩⟩
    exact hSστ

lemma while_rule :
  S ⊢ ⦃ P ⋆∧ ~B ⦄ C ⦃ P ⦄ ->
  S ⊢ ⦃ P ⦄ while: B do: C end ⦃ P ⋆∧ ⋆¬~B ⦄ := by
  intros hC hprewf hCwf hpostwf σ τ σ'' τ'' hpre hstep
  constructor
  . apply Basic.while_rule _ hprewf hCwf hpostwf
    . exact hpre
    . exact hstep
    . exact implies_basic_validity hC
  . intros hSwf hSτ

    simp [Command.wellFormed, numericExpressionPredicate] at hCwf
    rcases hCwf with ⟨hBwf, hCwf⟩

    apply small_step_implies_big_step at hstep
    generalize hC' : (while: B do: C end) = C' at hstep
    revert B C
    induction hstep <;> try simp
    . case big_step_while_false hB =>
      intros B C hC hprewf hBwf hCwf hB' hC'
      exact hSτ
    . case big_step_while_true hB hCstep hwhilestep ihC ihwhile =>
      -- Get rid of old names before we introduce new ones
      clear ihC σ τ σ'' τ''
      intros B C hCtriple _ hBwf hCwf hB' hC'
      rw [<-hB'] at hB
      rw [<-hC'] at hCstep

      -- Re-expose a few names
      expose_names

      set hSτ' := hCtriple hpostwf
      specialize hSτ' _ hprewf σ τ σ' τ' _ _
      . simp [Command.wellFormed]
        exact hCwf
      . apply conjunction_intro hpre
        . apply expression_intro
          simp [hB]
      . exact big_step_implies_small_step hCstep

      rcases hSτ' with ⟨hpostC, hSτ'⟩
      specialize hSτ' hSwf hSτ

      specialize @ihwhile hpostC hSτ' B C hCtriple hpostwf hBwf hCwf _
      . rw [<-hB', <-hC']
      exact ihwhile
