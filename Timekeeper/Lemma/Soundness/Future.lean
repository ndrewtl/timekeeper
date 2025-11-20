import Timekeeper.Logic.Correctness.Future
import Timekeeper.Lemma.GeneralAssertion
import Timekeeper.Lemma.Soundness.Past

namespace Timekeeper.Soundness.Future
open Correctness.Future
open Command
open GeneralAssertion
open GeneralAssertion.Models

lemma skip_rule :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ skip ⦃ P ⦄ ⟪ α ⟫ := by
  intros hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  set h := Past.skip_rule hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  rcases h with ⟨hpost, hpast⟩
  constructor
  . exact hpost
  intros hSwf hSτ
  constructor
  . exact hpast hSwf hSτ

  intros hCwf hαwf hβwf hCτα
  apply SmallStepRTC.skip_inversion at hstep
  rcases hstep with ⟨⟨⟩, ⟨⟩⟩
  exact hCτα

lemma emit_rule :
  (S, K) ⊢ ⟪ α[ℓ ↦ ℓ ⋆+ ♯1] ⟫ ⦃ S⋆(Es) ⋆@ ℓ ⋆∧ P[ℓ ↦ (ℓ ⋆+ ♯1)] ⦄ emit Es ⦃ P ⋆∧ ⋆!Es⋆@(ℓ ⋆- ♯1) ⦄ ⟪ α ⋆∧ K⋆(Es) ⋆@ (ℓ ⋆- ♯1) ⟫ := by

  intros hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  set h := Past.emit_rule hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  rcases h with ⟨hpost, hpast⟩

  constructor
  . exact hpost
  intros hSwf hSτ
  constructor
  . exact hpast hSwf hSτ

  intros hKwf hαwf hβwf hKτα
  apply SmallStepRTC.emit_inversion at hstep
  rcases hstep with ⟨⟨⟩, ⟨⟩⟩

  simp [GeneralAssertion.wellFormed] at hpostwf
  rcases hpostwf with ⟨hPwf, hEswf⟩
  simp [TraceAssertion.wellFormed] at hEswf

  apply extend_trace_invariant
  . exact hKwf
  . rw [trace_length_addition_preserves_well_formedness] at hαwf
    exact hαwf
  . exact hEswf
  . exact hKτα

lemma resolve_rule :
  (S, K) ⊢ ⟪ α ⋆∧ ω ⟫ ⦃ P ⋆∧ ω ⦄ resolve ω ⦃ P ⋆∧ ω ⦄ ⟪ α ⟫ := by

  intros hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  set hpast := Past.resolve_rule (S := S) hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  rcases hpast with ⟨hpost, hpast⟩

  constructor
  . exact hpost
  intros hSwf hSτ
  constructor
  . exact hpast hSwf hSτ

  intros hCwf hpreobwf hpostobwf hinvariant

  -- Simplify out hpre
  apply conjunction_inversion at hpre
  rcases hpre with ⟨hP, hω⟩

  -- Simplify out hstep
  apply SmallStepRTC.resolve_inversion at hstep
  rcases hstep with ⟨⟨⟩, ⟨⟩⟩

  apply discharge_obligation
  . exact hinvariant
  . exact hω
  . simp [GeneralAssertion.wellFormed] at hprewf
    rcases hprewf with ⟨hPwf, hωwf⟩
    exact hωwf

lemma if_rule :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⋆∧ ~B ⦄ C₁ ⦃ P' ⦄ ⟪ β ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⋆∧ ⋆¬(~B) ⦄ C₂ ⦃ P' ⦄ ⟪ β ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ if: B then: C₁ else: C₂ end ⦃ P' ⦄ ⟪ β ⟫ := by
  intros hC₁ hC₂ hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep

  set hpast := Past.if_rule
    (S := S) (P := P) (B := B) (P' := P') (C₁ := C₁) (C₂ := C₂)

  specialize hpast _ _
  . exact implies_past_validity hC₁
  . exact implies_past_validity hC₂

  specialize hpast hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  rcases hpast with ⟨hpost, hpast⟩

  constructor
  . exact hpost

  intros hSwf hSτ

  specialize hpast hSwf hSτ
  constructor
  . exact hpast

  -- Real proof begins here

  intros hKwf hαwf hβwf hKστα

  -- Get our assumptions ready
  simp [Command.wellFormed, Command.numericExpressionPredicate] at hprogwf
  rcases hprogwf with ⟨hBwf, hC₁wf, hC₂wf⟩

  apply StepEquivalence.small_step_implies_big_step at hstep

  rcases hB : ⟦ B ⟧(σ, τ)
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
    . apply BigStep.if_false_inversion at hstep
      exact StepEquivalence.big_step_implies_small_step (hstep hB)
    rcases hC₂ with ⟨hpost, hC₂⟩
    specialize hC₂ hSwf hSτ
    rcases hC₂ with ⟨hSτ', hC₂⟩

    exact hC₂ hKwf hαwf hβwf hKστα
  . specialize hC₁ _ _ hpostwf σ τ σ' τ' _ _
    . simp [GeneralAssertion.wellFormed]
      exact hprewf
    . simp [Command.wellFormed]
      exact hC₁wf
    . apply conjunction_intro
      . exact hpre
      . apply expression_intro
        simp [hB]
    . apply BigStep.if_true_inversion at hstep
      exact StepEquivalence.big_step_implies_small_step (hstep hB)
    rcases hC₁ with ⟨hpost, hC₁⟩
    specialize hC₁ hSwf hSτ
    rcases hC₁ with ⟨hSτ', hC₁⟩

    exact hC₁ hKwf hαwf hβwf hKστα

lemma seq_rule :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C₁ ⦃ Q ⦄ ⟪ β ⟫ ->
  (S, K) ⊢ ⟪ β ⟫ ⦃ Q ⦄ C₂ ⦃ R ⦄ ⟪ γ ⟫ ->
  Q.wellFormed ->
  β.wellFormed ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C₁ ⋆; C₂ ⦃ R ⦄ ⟪ γ ⟫ := by
  intros hC₁ hC₂ hQwf hβwf hprewf hprogwf hpostwf σ τ σ'' τ'' hpre hstep

  set hpast := Past.seq_rule
    (S := S) (P := P) (C₁ := C₁) (Q := Q) (C₂ := C₂) (R := R)

  specialize hpast _ _ hQwf hprewf hprogwf hpostwf σ τ σ'' τ'' hpre hstep
  . exact implies_past_validity hC₁
  . exact implies_past_validity hC₂

  rcases hpast with ⟨hpost, hpast⟩

  constructor
  . exact hpost

  intros hSwf hSτ
  specialize hpast hSwf hSτ

  constructor
  . exact hpast

  -- Real proof begins here
  intros hCwf hαwf hγwf hCστα

  -- Get assumptions ready
  simp [Command.wellFormed, Command.numericExpressionPredicate] at hprogwf
  rcases hprogwf with ⟨hC₁wf, hC₂wf⟩

  apply StepEquivalence.small_step_implies_big_step at hstep
  apply BigStep.seq_inversion at hstep
  rcases hstep with ⟨σ', τ', hstepC₁, hstepC₂⟩


  -- Specialize hC₁
  specialize hC₁ hprewf _ hQwf σ τ σ' τ' hpre _
  . simp [Command.wellFormed]
    exact hC₁wf
  . exact StepEquivalence.big_step_implies_small_step hstepC₁

  rcases hC₁ with ⟨hQ, hC₁⟩
  specialize hC₁ hSwf hSτ

  rcases hC₁ with ⟨hSτ', hC₁⟩
  specialize hC₁ hCwf hαwf hβwf hCστα

  -- Specialize hC₂
  specialize hC₂ hQwf _ hpostwf σ' τ' σ'' τ'' hQ _
  . simp [Command.wellFormed]
    exact hC₂wf
  . exact StepEquivalence.big_step_implies_small_step hstepC₂

  rcases hC₂ with ⟨hpost, hC₂⟩

  specialize hC₂ hSwf hSτ'

  rcases hC₂ with ⟨hSτ'', hC₂⟩

  specialize hC₂ hCwf hβwf hγwf hC₁
  exact hC₂

lemma seq_rule_assoc :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ (C₁ ⋆; C₂) ⋆; C₃ ⦃ R ⦄ ⟪ γ ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C₁ ⋆; C₂ ⋆; C₃ ⦃ R ⦄ ⟪ γ ⟫ := by
  intros h hprewf hprogwf hpostwf σ τ σ₃ τ₃ hpre hstep
  apply h hprewf _ hpostwf σ τ σ₃ τ₃ hpre _
  . simp [Command.wellFormed, NumericExpression.containsLogicalVariables, Command.numericExpressionPredicate] at hprogwf
    rcases hprogwf with ⟨hC₁wf, hC₂wf, hC₃wf⟩
    simp [Command.wellFormed, NumericExpression.containsLogicalVariables, Command.numericExpressionPredicate]
    constructor
    . exact ⟨hC₁wf, hC₂wf⟩
    . exact hC₃wf
  . apply StepEquivalence.big_step_implies_small_step
    rw [BigStep.seq_assoc]
    apply StepEquivalence.small_step_implies_big_step
    exact hstep

lemma disj_rule :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P₁ ⦄ C ⦃ Q₁ ⦄ ⟪ β ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P₂ ⦄ C ⦃ Q₂ ⦄ ⟪ β ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P₁ ⋆∨ P₂ ⦄ C ⦃ Q₁ ⋆∨ Q₂ ⦄ ⟪ β ⟫ := by
  intros h₁ h₂ hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep

  set hpast := Past.disj_rule
    (S := S) (P₁ := P₁) (C := C) (Q₁ := Q₁) (P₂ := P₂) (Q₂ := Q₂)

  specialize hpast _ _ hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  . exact implies_past_validity h₁
  . exact implies_past_validity h₂

  rcases hpast with ⟨hpost, hpast⟩

  constructor
  . exact hpost

  intros hSwf hSτ

  constructor
  . exact hpast hSwf hSτ

  intros hCwf hαwf hβwf hCστα

  simp [GeneralAssertion.wellFormed] at hprewf
  rcases hprewf with ⟨hP₁wf, hP₂wf⟩

  simp [GeneralAssertion.wellFormed] at hpostwf
  rcases hpostwf with ⟨hQ₁wf, hQ₂wf⟩

  apply disjunction_inversion at hpre

  rcases hpre with (hP₁ | hP₂)
  . specialize h₁ hP₁wf hprogwf hQ₁wf σ τ σ' τ' hP₁ hstep
    rcases h₁ with ⟨hQ₁, h₁⟩
    specialize h₁ hSwf hSτ
    rcases h₁ with ⟨hSτ', h₁⟩
    exact h₁ hCwf hαwf hβwf hCστα
  . specialize h₂ hP₂wf hprogwf hQ₂wf σ τ σ' τ' hP₂ hstep
    rcases h₂ with ⟨hQ₂, h₂⟩
    specialize h₂ hSwf hSτ
    rcases h₂ with ⟨hSτ', h₂⟩
    exact h₂ hCwf hαwf hβwf hCστα

lemma conj_rule :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P₁ ⦄ C ⦃ Q₁ ⦄ ⟪ β ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P₂ ⦄ C ⦃ Q₂ ⦄ ⟪ β ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P₁ ⋆∧ P₂ ⦄ C ⦃ Q₁ ⋆∧ Q₂ ⦄ ⟪ β ⟫ := by
  intros h₁ h₂ hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep

  set hpast := Past.conj_rule
    (S := S) (P₁ := P₁) (C := C) (Q₁ := Q₁) (P₂ := P₂) (Q₂ := Q₂)

  specialize hpast _ _ hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  . exact implies_past_validity h₁
  . exact implies_past_validity h₂

  rcases hpast with ⟨hpost, hpast⟩

  constructor
  . exact hpost

  intros hSwf hSτ
  specialize hpast hSwf hSτ

  constructor
  . exact hpast

  intros hKwf hαwf hβwf hKστα

  simp [GeneralAssertion.wellFormed] at hprewf
  rcases hprewf with ⟨hP₁wf, hP₂wf⟩

  simp [GeneralAssertion.wellFormed] at hpostwf
  rcases hpostwf with ⟨hQ₁wf, hQ₂wf⟩

  apply conjunction_inversion at hpre
  rcases hpre with ⟨hP₁, hP₂⟩


  specialize h₁ hP₁wf hprogwf hQ₁wf σ τ σ' τ' hP₁ hstep
  rcases h₁ with ⟨hQ₁, h₁⟩
  specialize h₁ hSwf hSτ
  rcases h₁ with ⟨hSτ', h₁⟩
  exact h₁ hKwf hαwf hβwf hKστα

lemma conseq_rule {P P' Q Q' : GeneralAssertion} :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C ⦃ Q ⦄ ⟪ β ⟫ ->
  P' ⋆-> P ->
  Q ⋆-> Q' ->
  P ⋆∧ α ⋆->> α' ->
  Q ⋆∧ β' ⋆->> β ->
  P.wellFormed ->
  Q.wellFormed ->
  α.wellFormed ->
  β.wellFormed ->
  (S, K) ⊢ ⟪ α' ⟫ ⦃ P' ⦄ C ⦃ Q' ⦄ ⟪ β' ⟫ := by
  intros h hP'P hQQ' hαα' hβ'β hPwf hQwf hαwf hβwf
  intros hP'wf hprogwf hQ'wf σ τ σ' τ' hpre hstep

  set hpast := Past.conseq_rule (S := S) (P := P) (P' := P') (C := C) (Q := Q) (Q' := Q')

  specialize hpast _ hP'P hQQ' hPwf hQwf hP'wf hprogwf hQ'wf σ τ σ' τ' hpre hstep
  . exact implies_past_validity h

  rcases hpast with ⟨hQ', hpast⟩
  constructor
  . exact hQ'

  intros hSwf hSτ
  specialize hpast hSwf hSτ
  constructor
  . exact hpast

  intros hKwf hα'wf hβ'wf hinvariant

  specialize h hPwf hprogwf hQwf σ τ σ' τ' _ hstep
  . exact hP'P σ τ hpre

  rcases h with ⟨hQ, h⟩

  specialize h hSwf hSτ
  rcases h with ⟨hSτ', h⟩

  specialize h hKwf hαwf hβwf _
  . intros k hkbound τext hα
    specialize hinvariant k hkbound τext
    apply hinvariant

    apply hαα'
    apply conjunction_intro
    . apply trace_extension_minus
      . exact hP'P σ τ hpre
      . exact hPwf
    . exact hα

  intros k hkbound τext hβ
  specialize h k hkbound τext
  apply h

  apply hβ'β
  apply conjunction_intro
  . apply trace_extension_minus
    . exact hQ
    . exact hQwf
  . exact hβ

-- Note that some of the well-formedness assumptions here are unnecessary,
-- re-proving directly would allow them to be dropped
lemma conseq_rule_P {P P' Q : GeneralAssertion} :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C ⦃ Q ⦄ ⟪ β ⟫ ->
  P' ⋆-> P ->
  P.wellFormed ->
  Q.wellFormed ->
  α.wellFormed ->
  β.wellFormed ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P' ⦄ C ⦃ Q ⦄ ⟪ β ⟫ := by
  intros h hP'P hPwf hQwf hαwf hβwf
  apply conseq_rule h hP'P _ _ _ hPwf hQwf hαwf hβwf
  . intros σ τ h ; exact h
  . intros σ τ τext h
    apply conjunction_inversion at h
    rcases h with ⟨_, hα⟩
    exact hα
  . intros σ τ τext h
    apply conjunction_inversion at h
    rcases h with ⟨_, hβ⟩
    exact hβ

lemma conseq_rule_Q {P Q Q' : GeneralAssertion} :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C ⦃ Q ⦄ ⟪ β ⟫ ->
  Q ⋆-> Q' ->
  P.wellFormed ->
  Q.wellFormed ->
  α.wellFormed ->
  β.wellFormed ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C ⦃ Q' ⦄ ⟪ β ⟫ := by
  intros h hQQ' hPwf hQwf hαwf hβwf
  apply conseq_rule h _ hQQ' _ _ hPwf hQwf hαwf hβwf
  . intros σ τ h ; exact h
  . intros σ τ τext h
    apply conjunction_inversion at h
    rcases h with ⟨_, hα⟩
    exact hα
  . intros σ τ τext h
    apply conjunction_inversion at h
    rcases h with ⟨_, hβ⟩
    exact hβ

lemma conseq_rule_α {P Q : GeneralAssertion} :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C ⦃ Q ⦄ ⟪ β ⟫ ->
  P ⋆∧ α ⋆->> α' ->
  P.wellFormed ->
  Q.wellFormed ->
  α.wellFormed ->
  β.wellFormed ->
  (S, K) ⊢ ⟪ α' ⟫ ⦃ P ⦄ C ⦃ Q ⦄ ⟪ β ⟫ := by
  intros h hαα' hPwf hQwf hαwf hβwf
  apply conseq_rule h _ _ hαα' _ hPwf hQwf hαwf hβwf
  . intros σ τ h ; exact h
  . intros σ τ h ; exact h
  . intros σ τ τext h
    apply conjunction_inversion at h
    rcases h with ⟨_, hα⟩
    exact hα

lemma conseq_rule_β {P Q : GeneralAssertion} :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C ⦃ Q ⦄ ⟪ β ⟫ ->
  Q ⋆∧ β' ⋆->> β ->
  P.wellFormed ->
  Q.wellFormed ->
  α.wellFormed ->
  β.wellFormed ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ C ⦃ Q ⦄ ⟪ β' ⟫ := by
  intros h hβ'β hPwf hQwf hαwf hβwf
  apply conseq_rule h _ _ _ hβ'β hPwf hQwf hαwf hβwf
  . intros σ τ h ; exact h
  . intros σ τ h ; exact h
  . intros σ τ τext h
    apply conjunction_inversion at h
    rcases h with ⟨_, hα⟩
    exact hα

lemma assign_rule :
  (S, K) ⊢ ⟪ α[⋆$x ↦ E] ⟫ ⦃ P[⋆$x ↦ E] ⦄ set ⋆$x ⋆:= E ⦃ P ⦄ ⟪ α ⟫ := by
  intros hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep

  set hpast := Past.assign_rule (S := S) (P := P) (x := x) (E := E)
  specialize hpast hprewf hprogwf hpostwf σ τ σ' τ' hpre hstep
  rcases hpast with ⟨hpost, hpast⟩
  constructor
  . exact hpost

  intros hSwf hSτ
  specialize hpast hSwf hSτ
  constructor
  . exact hpast

  intros hKwf hαwf hα'wf hKστα
  apply SmallStepRTC.assign_inversion at hstep
  rcases hstep with ⟨rfl, rfl⟩

  intros k hkbound τext hα

  specialize hKστα k hkbound τext

  apply hKστα
  clear hKστα

  -- This is an instance of a special lemma we wrote for this particular circumstance
  set hspecial := GeneralAssertion.evaluation_remapping_trace_extension_minus
    (A := α) (τext := τext) (τ := τ') (σ := σ) (x := x) (E := E)

  specialize hspecial _
  . simp [Command.wellFormed, Command.numericExpressionPredicate] at hprogwf
    exact hprogwf

  rw [hspecial]
  exact hα

lemma while_rule :
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⋆∧ ~B ⦄ C ⦃ P ⦄ ⟪ α ⟫ ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ P ⦄ while: B do: C end ⦃ P ⋆∧ ⋆¬~B ⦄ ⟪ α ⟫ := by

  intros h hprewf hprogwf hpostwf σ τ σ'' τ'' hpre hstep

  set hpast := Past.while_rule (S := S) (P := P) (B := B) (C := C)

  specialize hpast _ hprewf hprogwf hpostwf σ τ σ'' τ'' hpre hstep
  . exact implies_past_validity h
  rcases hpast with ⟨hpost, hpast⟩
  constructor
  . exact hpost

  intros hSwf hSτ
  specialize hpast hSwf hSτ
  constructor
  . exact hpast

  intros hKwf hαwf _ hKστα

  apply StepEquivalence.small_step_implies_big_step at hstep

  generalize hC' : (while: B do: C end) = C' at hstep
  revert B C
  induction hstep <;> try simp
  case big_step_while_false hB =>
    exact fun {B_2} {C} h hprogwf hpostwf hpost a a => hKστα
  case big_step_while_true hB hCstep hwhilestep ih₁ ih₂ =>
    intros B C hC hwhilewf hpostwf hpost hB' hC'

    clear σ τ σ'' τ''
    expose_names
    rcases hB' with rfl
    rcases hC' with rfl

    simp [Command.wellFormed, Command.numericExpressionPredicate] at hwhilewf
    rcases hwhilewf with ⟨hBwf, hCwf⟩

    set hKσ'τ'α := hC

    specialize hKσ'τ'α _ _ hprewf σ τ σ' τ' _ _
    . simp [GeneralAssertion.wellFormed]
      exact hprewf
    . simp [Command.wellFormed]
      exact hCwf
    . apply conjunction_intro
      . exact hpre
      . apply expression_intro
        simp [hB]
    . exact StepEquivalence.big_step_implies_small_step hCstep
    rcases hKσ'τ'α with ⟨hσ'τ'P, hCσ'τ'α⟩

    specialize hCσ'τ'α hSwf hSτ
    rcases hCσ'τ'α with ⟨hSτ', hCσ'τ'α⟩

    specialize hCσ'τ'α hKwf hαwf hαwf hKστα

    specialize ih₂ hσ'τ'P hSτ' hpast hCσ'τ'α (B := B) (C := C) _ _ hpostwf hpost _
    . exact hC
    . simp [Command.wellFormed, Command.numericExpressionPredicate]
      constructor
      . exact hBwf
      . exact hCwf
    . trivial

    exact ih₂
