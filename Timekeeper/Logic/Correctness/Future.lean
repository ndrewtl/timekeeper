import Timekeeper.Logic.Correctness.Basic
import Timekeeper.Logic.Correctness.Past
import Timekeeper.Lemma.GeneralAssertion

namespace Timekeeper.Correctness.Future
open Command
open GeneralAssertion
open GeneralAssertion.Models

def trace_invariant
  (K : Specification) (σ : Store) (τ : Trace) (Ω : GeneralAssertion) (k : Nat) (_ : k < τ.length) : Prop :=
      let σ_k := τ[k].store
      let e_k := τ[k].event
      let ω := K e_k
      -- For all trace extensions that make Ω true, they also make ω true at k
      ∀ τext, ⋆ σ, (τ ++ τext) ⊧ Ω[ℓ ↦ ℓ ⋆- ♯τext.length] -> ⋆ σ_k, (τ ++ τext), k ⊧ₜ ω

-- Want to be able to case match over ω.evaluate

def valid (S K : Specification) (α P: GeneralAssertion) (W : Command) (Q β: GeneralAssertion) : Prop :=
  P.wellFormed ->
  W.wellFormed ->
  Q.wellFormed ->
  ∀ σ τ σ' τ',
    (⋆ σ, τ ⊧ P) ->
    (W, σ, τ) ⇝* (skip, σ', τ') ->
    (⋆ σ', τ' ⊧ Q) ∧ (
      S.wellFormed ->
      (∀ k, (hkbound : k < τ.length) -> Past.trace_invariant S τ k hkbound) ->
      (∀ k', (hkbound : k' < τ'.length) -> Past.trace_invariant S τ' k' hkbound) ∧ (
        K.wellFormed ->
        α.wellFormed ->
        β.wellFormed ->
        (∀ k, (hkbound : k < τ.length) -> trace_invariant K σ τ α k hkbound) ->
        ∀ k', (hkbound : k' < τ'.length) -> trace_invariant K σ' τ' β k' hkbound
      )
    )

notation:232 "(" S ", " K ")" " ⊢ " " ⟪ " α " ⟫ " "⦃ " P " ⦄ " W " ⦃ " Q " ⦄" " ⟪ " β " ⟫" => valid S K α P W Q β

lemma extend_trace_invariant :
  K.wellFormed ->
  α.wellFormed ->
  Es.containsExpression ℓ = false ->
  (∀ k, (hkbound : k < τ.length) -> trace_invariant K σ τ (α[ℓ ↦ ℓ ⋆+ ♯1]) k hkbound) ->
  let entry : TraceEntry := {store := σ, event := ⟦ Es ⟧(σ, τ)}
  ∀ k, (hkbound : k < (τ ++ [entry]).length) ->
    trace_invariant K σ
      (τ ++ [entry])
      (α ⋆∧ K⋆(Es) ⋆@ (ℓ ⋆- ♯1))
      k hkbound := by
  intros hKwf hαwf hEswf hinvariant entry k hkbound
  simp [Specification.wellFormed] at hKwf

  by_cases hk : k = τ.length
  . intros τ' hpost
    simp_rw [hk]
    simp

    apply conjunction_inversion at hpost
    rcases hpost with ⟨hα, hK⟩
    apply trace_inversion at hK
    apply TraceAssertion.Models.function_inversion at hK
    normalize at hK
    rw [NumericExpressionList.nonexistent_term_replacement, TraceAssertion.nonexistent_term_replacement] at hK ; rotate_left
    . exact
      TraceAssertion.well_formed_does_not_contain_trace_length (hKwf (⟦ Es ⟧(σ, τ ++ entry :: τ')))
    . exact hEswf

    have hlen : τ.length + (τ'.length + 1) - τ'.length - 1 = τ.length := by
      rw [Nat.sub_right_comm, Nat.add_sub_assoc] ; rotate_left
      . simp
      simp

    rw [hlen] at hK
    normalize at hK
    clear hlen
    set τext := entry :: τ'
    unfold entry
    normalize
    rw [NumericExpressionList.trace_independence] at hK ; rotate_left
    . exact hEswf

    exact hK

  . have hkbound' : k < τ.length := by grind
    have hτk : (τ ++ [entry])[k] = τ[k] := by
      exact List.getElem_append_left hkbound'
    intros τext hΩ
    conv =>
      congr
      . rw [hτk]
      . skip
      . skip
      . rw [hτk]

    apply conjunction_inversion at hΩ
    rcases hΩ with ⟨hα, hC⟩
    rw [<-GeneralAssertion.numeric_replacement] at hα

    specialize hinvariant k hkbound' ([entry] ++ τext) _
    . conv =>
        congr
        . skip
        . rw [<-List.append_assoc]
        . congr
          . skip
      have hlen : ([entry] ++ τext).length = 1 + τext.length := by
        exact Nat.succ_eq_one_add ([].append τext).length
      rw [hlen]

      rw [models_true, double_trace_replace (E₁' := ℓ ⋆- ♯(τext.length))] ; rotate_left
      . normalize
        rw [Nat.Simproc.sub_add_eq_comm]
        rw [Nat.sub_add_cancel]
        rw [Nat.add_sub_assoc] ; rotate_left
        . apply Nat.le_add_right
        rw [Nat.sub_add_comm] ; rotate_left
        . apply Nat.le_refl
        simp
      . simp [NumericExpression.containsLogicalVariables, NumericExpression.predicateHoldsSubtree, NumericExpression.isLogicalVariable]
      . simp [NumericExpression.containsLogicalVariables, NumericExpression.predicateHoldsSubtree, NumericExpression.isLogicalVariable]
      . simp [NumericExpression.containsLogicalVariables, NumericExpression.predicateHoldsSubtree, NumericExpression.isLogicalVariable]
      normalize at hα
      normalize
      exact hα

    conv at hinvariant =>
      congr
      . skip
      . rw [<-List.append_assoc]
    exact hinvariant

lemma discharge_obligation :
  (∀ k, (hkbound : k < τ.length) -> trace_invariant K σ τ (α ⋆∧ ω) k hkbound) ->
  ⋆ σ, τ ⊧ ω ->
  ω.wellFormed ->
  ∀ k, (hkbound : k < τ.length) -> trace_invariant K σ τ α k hkbound := by
  intros hinv hω hωwf k hkbound τext hα

  apply hinv

  apply conjunction_intro <;> normalize
  . exact hα
  . apply GeneralAssertion.trace_extension_minus
    . exact hω
    . exact hωwf

lemma implies_past_validity :
  (S, C) ⊢ ⟪ α ⟫ ⦃ P ⦄ W ⦃ Q ⦄ ⟪ β ⟫ ->
  S ⊢ ⦃ P ⦄ W ⦃ Q ⦄ := by
  intros h hPwf hWwf hQwf σ τ σ' τ' hpre hstep

  specialize h hPwf hWwf hQwf σ τ σ' τ' hpre hstep

  rcases h with ⟨hQ, h⟩

  constructor
  . exact hQ

  intros hSwf hSτ

  specialize h hSwf hSτ

  rcases h with ⟨hSτ', h⟩
  exact hSτ'
