import Timekeeper.Types
import Timekeeper.Language.Expression.NumericExpression
import Timekeeper.Language.Semantics.Store
import Timekeeper.Logic.Assertion.GeneralAssertion
import Timekeeper.Logic.Evaluation.TraceAssertion

namespace Timekeeper.GeneralAssertion

inductive Models : Store -> Trace -> GeneralAssertion -> Bool -> Prop where
| expression_intro {b : Bool} :
  ⟦ B ⟧(σ, τ) = b ->
  Models σ τ (~B) b
| negation_intro :
  Models σ τ A !b ->
  Models σ τ ⋆¬A b
| disjunction_intro_left :
  Models σ τ φ true ->
  Models σ τ (φ ⋆∨ ψ) true
| disjunction_intro_right :
  Models σ τ ψ true ->
  Models σ τ (φ ⋆∨ ψ) true
| disjunction_intro_false :
  Models σ τ φ false ->
  Models σ τ ψ false ->
  Models σ τ (φ ⋆∨ ψ) false
| trace_intro :
  ⋆ σ, τ, ⟦ E ⟧(σ, τ) ⊧ₜ[ b ] T ->
  Models σ τ (T ⋆@ E) b
| universal_quantification_intro {x : VariableName} :
  (∀ (v' : Val), Models (σ[⋆^x ↦ v']) τ A b) ->
  Models σ τ (⋆∀ x : A) b

open Models

notation:213 "⋆ " σ ", " τ " ⊧[ " v " ] " A:214 => Models σ τ A v

-- Convenience method to easen notation
@[simp]
def models_true (σ : Store) (τ : Trace) (A : GeneralAssertion) : Prop :=
  ⋆ σ, τ ⊧[true] A

notation:215 "⋆ " σ ", " τ " ⊧ " A:216 => models_true σ τ A

def valid_assertion (A : GeneralAssertion) : Prop :=
  ∀ σ τ, ⋆ σ, τ ⊧ A

prefix:217 "⋆⊧ " => valid_assertion

def valid_implication (A₁ A₂ : GeneralAssertion) : Prop :=
  ∀ σ τ, ⋆ σ, τ ⊧ A₁ -> ⋆ σ, τ ⊧ A₂

infixl:218 " ⋆-> " => valid_implication

def valid_obligation_implication (A₁ A₂ : GeneralAssertion) : Prop :=
  ∀ σ τ τext, ⋆ σ, τ ++ τext ⊧ A₁[ℓ ↦ ℓ ⋆- ♯τext.length] -> ⋆ σ, τ ++ τext ⊧ A₂[ℓ ↦ ℓ ⋆- ♯τext.length]

infixl:219 " ⋆->> " => valid_obligation_implication
