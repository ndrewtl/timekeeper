import Timekeeper.Language.Command
import Timekeeper.Language.Configuration
import Timekeeper.Language.Semantics.SmallStep
import Timekeeper.Logic.Assertion.GeneralAssertion
import Timekeeper.Logic.Evaluation.GeneralAssertion
import Timekeeper.Lemma.TraceAssertion

namespace Timekeeper.Correctness.Basic
open Command

def valid (P : GeneralAssertion) (C : Command) (Q: GeneralAssertion) : Prop :=
  P.wellFormed ->
  C.wellFormed ->
  Q.wellFormed ->
  ∀ σ τ σ' τ',
    (⋆ σ, τ ⊧ P) ->
    (C, σ, τ) ⇝* (skip, σ', τ') ->
    (⋆ σ', τ' ⊧ Q)

notation:230 "⦃ " P " ⦄ " C " ⦃ " Q " ⦄" => valid P C Q
