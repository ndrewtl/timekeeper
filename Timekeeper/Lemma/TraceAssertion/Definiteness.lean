import Timekeeper.Types
import Timekeeper.Notation.Logic
import Timekeeper.Language.Expression.NumericExpression
import Timekeeper.Language.Expression.BooleanExpression
import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Logic.Evaluation.TraceAssertion
import Timekeeper.Lemma.NumericExpression
import Timekeeper.Lemma.NumericExpressionList
import Timekeeper.Lemma.TraceAssertion.Inversion
import Timekeeper.Lemma.TraceAssertion.Introduction

namespace Timekeeper.TraceAssertion
open Models

lemma definiteness_single {T : TraceAssertion}:
  T.wellFormed ->
  ⋆ σ, τ, k ⊧ₜ[ b ] T -> ⋆ σ, τ ++ [e], k ⊧ₜ[ b ] T := by
  intros hwf
  revert σ k b
  induction T with
  | top =>
    intros σ k b h
    apply top_inversion at h
    rcases h with rfl
    exact top_intro
  | atomic Es =>
    intros σ k b h
    apply atomic_inversion_bool at h
    rcases h with ⟨hkbound, hτk⟩
    apply atomic_intro
    have hkbound' : k < (τ ++ [e]).length := by grind
    have hsame : (τ ++ [e])[k] = τ[k] := by exact List.getElem_append_left hkbound
    simp_rw [hsame]
    . rw [NumericExpressionList.trace_independence]
      . exact hτk
      . simp [wellFormed] at hwf
        simp [NumericExpressionList.containsTraceLength]
        exact hwf
    . grind
  | negation T' ihT' =>
    intros σ k b h
    apply negation_inversion at h
    apply negation_intro
    exact ihT' hwf h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intros σ k b h
    simp [wellFormed] at hwf
    rcases hwf with ⟨hT₁wf, hT₂wf⟩

    specialize @ihT₁ _
    . exact hT₁wf
    specialize @ihT₂ _
    . exact hT₂wf

    apply disjunction_inversion_bool at h

    rcases h with (⟨rfl, hT₁, hT₂⟩ | ⟨rfl, (hT₁ | hT₂)⟩)
    . apply disjunction_intro_false
      . exact ihT₁ hT₁
      . exact ihT₂ hT₂
    . exact disjunction_intro_left (ihT₁ hT₁)
    . exact disjunction_intro_right (ihT₂ hT₂)
  | previous T' ihT' =>
    intros σ k b h
    simp [wellFormed] at hwf
    specialize @ihT' hwf

    apply previous_inversion_bool at h
    rcases h with (⟨rfl, rfl⟩ | ⟨k', rfl, h⟩)
    . exact previous_intro_zero
    . apply previous_intro_succ
      exact ihT' h
  | next T' ihT' =>
    intros σ k b h
    simp [wellFormed] at hwf
    specialize @ihT' hwf

    apply next_inversion_bool at h
    exact next_intro (ihT' h)
  | since φ ψ ihφ ihψ =>
    intros σ k b h

    simp [wellFormed] at hwf
    rcases hwf with ⟨hφwf, hψwf⟩
    specialize @ihφ hφwf
    specialize @ihψ hψwf

    apply since_inversion_bool at h
    induction k with
    | zero =>
      apply since_intro
      apply disjunction_inversion_bool at h
      rcases h with (⟨rfl, hψ, hφSψ⟩ | ⟨rfl, (hψ | hφSψ)⟩)
      . apply disjunction_intro_false
        . exact ihψ hψ
        . apply conjunction_intro_false
          apply conjunction_inversion_false at hφSψ
          rcases hφSψ with (hφ | hφSψ)
          . left ; exact ihφ hφ
          . right ; exact previous_intro_zero
      . apply disjunction_intro_left
        exact ihψ hψ
      . apply disjunction_intro_right
        apply conjunction_inversion at hφSψ
        cases hφSψ with
        | intro hφ hφSψ =>
          apply conjunction_intro
          . exact ihφ hφ
          . apply previous_inversion_zero at hφSψ
            contradiction
    | succ k' ihk' =>
      apply disjunction_inversion_bool at h
      rcases h with (⟨rfl, hψ, hφSψ⟩ | ⟨rfl, (hψ | hφSψ)⟩)
      . apply since_intro
        apply disjunction_intro_false
        . exact ihψ hψ
        . apply conjunction_intro_false
          apply conjunction_inversion_false at hφSψ
          rcases hφSψ with (hφ | hφSψ)
          . left ; exact ihφ hφ
          . right
            apply previous_inversion_succ_bool at hφSψ
            apply previous_intro_succ
            apply ihk'
            apply since_inversion_bool at hφSψ
            exact hφSψ
      . apply since_intro
        apply disjunction_intro_left
        exact ihψ hψ
      . apply since_intro
        apply disjunction_intro_right
        apply conjunction_inversion at hφSψ
        cases hφSψ with
        | intro hφ hφSψ =>
          apply conjunction_intro
          . exact ihφ hφ
          . apply previous_intro_succ
            apply previous_inversion at hφSψ
            cases hφSψ with
            | intro k' hφSψ =>
              rcases hφSψ with ⟨⟨⟩, hφSψ⟩
              apply ihk'
              exact since_inversion_bool hφSψ
  | «until» φ ψ n ihφ ihψ =>
    simp [wellFormed] at hwf
    rcases hwf with ⟨hφwf, hψwf⟩
    specialize @ihφ hφwf
    specialize @ihψ hψwf

    induction n with
    | zero =>
      intros σ k b h
      apply until_inversion_zero_bool at h
      apply until_intro_zero
      exact ihψ h
    | succ n' ihn' =>
      intros σ k b h
      apply until_inversion_succ_bool at h
      apply disjunction_inversion_bool at h
      apply until_intro_succ
      rcases h with (⟨rfl, hψ, hφUψ⟩ | ⟨rfl, (hψ | hφUψ)⟩)
      . apply conjunction_inversion_false at hφUψ
        rcases hφUψ with (hφ | hφUψ)
        . apply disjunction_intro_false
          . exact ihψ hψ
          . apply conjunction_intro_false
            left ; exact ihφ hφ
        . apply disjunction_intro_false
          . exact ihψ hψ
          . apply next_inversion_bool at hφUψ
            apply conjunction_intro_false
            right
            apply next_intro
            exact ihn' hφUψ
      . exact disjunction_intro_left (ihψ hψ)
      . apply conjunction_inversion at hφUψ
        rcases hφUψ with ⟨hφ, hφUψ⟩
        apply next_inversion at hφUψ
        apply disjunction_intro_right
        apply conjunction_intro
        . exact ihφ hφ
        . apply next_intro
          exact ihn' hφUψ
  | function F Es ihF =>
    intros σ k b h
    simp [wellFormed] at hwf
    rcases hwf with ⟨hFwf, hEswf⟩
    apply function_inversion_bool at h

    apply function_intro
    rw [NumericExpressionList.trace_independence] ; rotate_left
    . exact hEswf

    exact ihF (⟦ Es ⟧(σ, τ)) (hFwf (⟦ Es ⟧(σ, τ))) h
  | universal_quantification x T' ihT' =>
    intros σ k b h
    simp [wellFormed] at hwf
    apply universal_quantification_intro
    intros v'
    apply ihT' hwf
    apply universal_quantification_inversion at h
    exact h v'


lemma definiteness {T : TraceAssertion}:
  T.wellFormed ->
  ⋆ σ, τ, k ⊧ₜ[ b ] T -> ⋆ σ, τ ++ τext, k ⊧ₜ[ b ] T := by
  intros hℓ h
  rw [<-List.reverse_reverse τext]
  set τ'rev := List.reverse τext
  induction τ'rev with
  | nil => simp ; exact h
  | cons last allButLast ih =>
    have hreverse : (last :: allButLast).reverse = (allButLast.reverse ++ [last]) := by exact
      List.reverse_cons
    rw [hreverse]
    have hassoc : τ ++ (allButLast.reverse ++ [last]) = (τ ++ allButLast.reverse) ++ [last] := by
      exact Eq.symm (List.append_assoc τ allButLast.reverse [last])
    rw [hassoc]
    set τ' := τ ++ allButLast.reverse
    exact definiteness_single hℓ ih
