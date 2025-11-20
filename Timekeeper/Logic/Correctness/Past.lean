import Timekeeper.Logic.Correctness.Basic

namespace Timekeeper.Correctness.Past
open Command

-- Preconditions are evaluated _at the event that would create them_
def trace_invariant (S : Specification) (τ : Trace) (k : Nat) (hkbound : k < τ.length) : Prop :=
  ⋆ τ[k].store, τ, k ⊧ₜ S τ[k].event

lemma extend_trace_invariant :
  S.wellFormed ->
  (∀ k, (hkbound : k < τ.length) -> trace_invariant S τ k hkbound) ->
  let entry : TraceEntry := {store := σ, event := e}
  ⋆ σ, τ, τ.length ⊧ₜ (S e) ->
  ∀ k, (hkbound : k < (τ ++ [entry]).length) -> trace_invariant S (τ ++ [entry]) k hkbound:= by
  intros hSwf hSτk entry hlast k hkbound
  unfold entry at *

  simp [Specification.wellFormed] at hSwf
  simp [trace_invariant]

  by_cases hk : k = τ.length
  . simp_rw [hk]
    simp
    apply TraceAssertion.definiteness_single
    . exact hSwf e
    . exact hlast
  . have hk : k < τ.length := by grind
    specialize hSτk k hk

    have hτk : (τ ++ [{event := e, store := σ}])[k] = τ[k] := by
      exact List.getElem_append_left hk
    rw [hτk]

    set hdefiniteness := TraceAssertion.definiteness_single
      (e := {event := e, store := σ}) (τ := τ) (k := k) (σ := τ[k].store) (T := S τ[k].event)
    specialize hdefiniteness _ _
    . exact hSwf τ[k].event
    . exact hSτk

    exact hdefiniteness

def valid (S : Specification) (P : GeneralAssertion) (C : Command) (Q: GeneralAssertion) : Prop :=
  P.wellFormed ->
  C.wellFormed ->
  Q.wellFormed ->
  ∀ σ τ σ' τ',
    (⋆ σ, τ ⊧ P) ->
    (C, σ, τ) ⇝* (skip, σ', τ') ->
    (⋆ σ', τ' ⊧ Q) ∧ (
      S.wellFormed ->
      (∀ k, (hkbound : k < τ.length) -> trace_invariant S τ k hkbound) ->
      (∀ k, (hkbound : k < τ'.length) -> trace_invariant S τ' k hkbound)
    )

notation:231 S " ⊢ " " ⦃ " P " ⦄ " C " ⦃ " Q " ⦄" => valid S P C Q

lemma implies_basic_validity :
  S ⊢ ⦃ P ⦄ C  ⦃ Q ⦄ -> ⦃ P ⦄ C ⦃ Q ⦄ := by
  intros h hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
  specialize h hprewf hCwf hpostwf σ τ σ' τ' hpre hstep
  rcases h with ⟨hQ, _⟩
  exact hQ
