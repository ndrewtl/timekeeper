import Timekeeper.Tactics
import Timekeeper.Lemma.BooleanExpression
import Timekeeper.Lemma.GeneralAssertion.Inversion
import Timekeeper.Lemma.TraceAssertion

namespace Timekeeper.GeneralAssertion
open Models

lemma trace_extension_plus_one :
  ⋆ σ, τ ⊧[ b ] P[ℓ ↦ ℓ ⋆+ ♯1] ->
  P.wellFormed ->
  ⋆ σ, τ ++ [e] ⊧[ b ] P := by
  revert b σ τ
  induction P with
  | expression B =>
    intros σ τ b hB hwf
    apply expression_inversion at hB
    apply expression_intro
    rw [BooleanExpression.trace_extension_plus_one]
    trivial
  | negation φ ihφ =>
    intros σ τ b hP hwf
    apply negation_intro
    specialize ihφ (σ := σ) (τ := τ) (b := !b)
    apply ihφ
    . simp [replaceNumericExpression] at hP
      rw [<-numeric_replacement] at hP
      apply negation_inversion at hP
      exact hP
    . simp [wellFormed] at hwf
      exact hwf
  | disjunction φ ψ ihφ ihψ =>
    intros σ τ b hP hwf
    simp [wellFormed] at hwf
    rcases hwf with ⟨hφwf, hψwf⟩
    apply disjunction_inversion_bool at hP
    normalize at hP
    rcases hP with (⟨rfl, hφ, hψ⟩ | ⟨rfl, (hφ | hψ)⟩) <;>
    (try apply ihφ at hφ) <;>
    (try apply ihψ at hψ)
    . apply disjunction_intro_false
      . exact hφ hφwf
      . exact hψ hψwf
    . apply disjunction_intro_left
      exact hφ hφwf
    . apply disjunction_intro_right
      exact hψ hψwf
  | trace T E =>
    intros σ τ b hP hwf
    simp [wellFormed] at hwf
    apply trace_intro
    apply trace_inversion at hP
    rw [NumericExpression.trace_extension_plus_one]
    rw [TraceAssertion.nonexistent_term_replacement] at hP
    . apply TraceAssertion.definiteness_single
      . exact hwf
      . exact hP
    . exact TraceAssertion.well_formed_does_not_contain_trace_length hwf
  | universal_quantification x A ih =>
    intros σ τ b hP hwf
    apply universal_quantification_intro
    intros v'
    specialize ih (σ := σ[⋆^x ↦ v']) (τ := τ) (b := b)
    apply ih
    . exact universal_quantification_inversion hP v'
    . exact hwf

lemma trace_extension_minus :
  ⋆ σ, τ ⊧[ b ] P ->
  P.wellFormed ->
  ⋆ σ, τ ++ τext ⊧[ b ] P[ℓ ↦ ℓ ⋆- ♯τext.length] := by
  intros hP hPwf
  revert b σ
  induction P with
  | expression B =>
    intros σ b hB
    apply expression_inversion at hB
    apply expression_intro
    rw [BooleanExpression.trace_extension_minus]
    exact hB
  | negation P' ihP' =>
    intros σ b hP'
    simp [wellFormed] at hPwf
    apply negation_inversion at hP'
    apply negation_intro
    rw [<-GeneralAssertion.numeric_replacement]
    apply ihP' hPwf
    . exact hP'
  | disjunction l r ihl ihr =>
    intros σ b hlr

    simp [wellFormed] at hPwf
    rcases hPwf with ⟨hlwf, hrwf⟩

    apply disjunction_inversion_bool at hlr

    rcases hlr with (⟨rfl, hl, hr⟩ | ⟨rfl, (hl | hr)⟩)
    . apply disjunction_intro_false
      . exact ihl hlwf hl
      . exact ihr hrwf hr
    . apply disjunction_intro_left
      exact ihl hlwf hl
    . apply disjunction_intro_right
      exact ihr hrwf hr
  | trace T E =>
    intros σ b hTE

    simp [wellFormed] at hPwf

    apply trace_inversion at hTE

    apply trace_intro
    rw [NumericExpression.trace_extension_minus]
    apply TraceAssertion.definiteness
    . rw [TraceAssertion.trace_length_subtraction_preserves_well_formedness]
      exact hPwf
    . rw [TraceAssertion.nonexistent_term_replacement]
      . exact hTE
      . exact TraceAssertion.well_formed_does_not_contain_trace_length hPwf
  | universal_quantification x A' ihA' =>
    intros σ b hA'

    simp [wellFormed] at hPwf
    apply universal_quantification_intro
    intros v'

    apply universal_quantification_inversion at hA'
    specialize hA' v'

    exact ihA' hPwf hA'

lemma trace_extension_minus_one :
  ⋆ σ, τ ⊧[ b ] P ->
  P.wellFormed ->
  ⋆ σ, τ ++ [e] ⊧[ b ] P[ℓ ↦ ℓ ⋆- ♯1] := by
  intros hP hPwf
  apply trace_extension_minus hP hPwf
