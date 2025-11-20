import Timekeeper.Logic.Correctness.Past
import Timekeeper.Logic.Correctness.Future
import Timekeeper.Lemma.GeneralAssertion

namespace Timekeeper.Result
open Correctness
open Command
open GeneralAssertion
open GeneralAssertion.Models

def σ₀ : Store := fun _ => 0
def τ₀ : Trace := []

lemma past_result :
  S.wellFormed ->
  C.wellFormed ->
  Q.wellFormed ->
  S ⊢ ⦃ ⋆⊤ ⦄ C ⦃ Q ⦄ ->
  (C, σ, []) ⇝* (skip, σ', τ') ->
  ∀ (k : Nat), (_ : k < τ'.length) ->
  ⋆ τ'[k].store, τ', k ⊧ₜ (S τ'[k].event) := by
  intros hSwf hprogwf hQwf htriple hstep k hkbound

  specialize htriple top_well_formed hprogwf hQwf σ [] σ' τ' top_valid hstep
  rcases htriple with ⟨hQ, htriple⟩

  specialize htriple hSwf _
  . simp [Past.trace_invariant]

  simp [Past.trace_invariant] at htriple

  specialize htriple k hkbound
  exact htriple

lemma future_result :
  S.wellFormed ->
  K.wellFormed ->
  α.wellFormed ->
  C.wellFormed ->
  Q.wellFormed ->
  (S, K) ⊢ ⟪ α ⟫ ⦃ ⋆⊤ ⦄ C ⦃ Q ⦄ ⟪ ⋆⊤ ⟫ ->
  (C, σ, []) ⇝* (skip, σ', τ') ->
  ∀ (k : Nat), (_ : k < τ'.length) ->
  ⋆ τ'[k].store, τ', k ⊧ₜ S τ'[k].event ⋆∧ K τ'[k].event := by
  intros hSwf hKwf hαwf hprogwf hQwf htriple hstep k hkbound

  specialize htriple top_well_formed hprogwf hQwf σ [] σ' τ' top_valid hstep
  rcases htriple with ⟨hQ, htriple⟩

  specialize htriple hSwf _
  . simp [Past.trace_invariant]

  rcases htriple with ⟨hpast, htriple⟩

  specialize htriple hKwf hαwf top_well_formed _
  . simp [Future.trace_invariant]

  specialize htriple k hkbound [] _
  . simp [GeneralAssertion.replaceNumericExpression, GeneralAssertion.top, BooleanExpression.replaceNumericExpression, NumericExpression.replaceNumericExpression]
    apply expression_intro
    simp [BooleanExpression.evaluate]

  apply TraceAssertion.Models.conjunction_intro
  . specialize hpast k hkbound
    exact hpast
  . simp at htriple
    exact htriple
