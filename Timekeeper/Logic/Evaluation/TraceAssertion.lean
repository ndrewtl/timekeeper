import Timekeeper.Language.Expression.NumericExpressionList
import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Language.Semantics.Store

namespace Timekeeper.TraceAssertion

inductive Models : TraceAssertion -> Store -> Trace -> Nat -> Bool -> Prop where
| top_intro :
  Models ⋆⊤ₜ σ τ k true
| atomic_intro {τ : Trace} {Es : NumericExpressionList} :
  (_ : k < τ.length) ->
  (τ[k].event == ⟦ Es ⟧(σ, τ)) = b ->
  Models ⋆!(Es) σ τ k b
| negation_intro :
  Models T' σ τ k !b ->
  Models ⋆¬T' σ τ k b
| disjunction_intro_left :
  Models T₁ σ τ k true ->
  Models (T₁ ⋆∨ T₂) σ τ k true
| disjunction_intro_right :
  Models T₂ σ τ k true ->
  Models (T₁ ⋆∨ T₂) σ τ k true
| disjunction_intro_false :
  Models T₁ σ τ k false ->
  Models T₂ σ τ k false ->
  Models (T₁ ⋆∨ T₂) σ τ k false
| previous_intro_zero :
  Models ●T' σ τ 0 false
| previous_intro_succ :
  Models T' σ τ k b ->
  Models ●T' σ τ (k + 1) b
| next_intro :
  Models T' σ τ (k + 1) b ->
  Models ◯T' σ τ k b
| since_intro :
  Models (ψ ⋆∨ (φ ⋆∧ ●(φ ⋆S ψ))) σ τ k b ->
  Models (φ ⋆S ψ) σ τ k b
| until_intro_zero :
  Models ψ σ τ k b ->
  Models (φ ⋆U( 0 ) ψ) σ τ k b
| until_intro_succ :
  Models (ψ ⋆∨ (φ ⋆∧ ◯(φ ⋆U( n' ) ψ))) σ τ k b ->
  Models (φ ⋆U( n' + 1 ) ψ) σ τ k b
| function_intro :
  Models (F (⟦ Es ⟧(σ, τ))) σ τ k b ->
  Models (F⋆(Es)) σ τ k b
| universal_quantification_intro {x : VariableName} :
  (∀ (v' : Val), Models T' (σ[⋆^x ↦ v']) τ k b) ->
  Models (⋆∀ₜ x : T') σ τ k b

notation:210 "⋆ " σ ", " τ ", " k " ⊧ₜ[ " b " ] " T:211 => Models T σ τ k b

@[simp]
def models_true (σ : Store) (τ : Trace) (k : Nat) (T : TraceAssertion) : Prop :=
  ⋆ σ, τ, k ⊧ₜ[ true ] T

notation:212 "⋆ " σ ", " τ ", " k " ⊧ₜ " T:213 => models_true σ τ k T

def valid_implication (T₁ T₂ : TraceAssertion) : Prop :=
  ∀ σ τ k, ⋆ σ, τ, k ⊧ₜ T₁ -> ⋆ σ, τ, k ⊧ₜ T₂

notation:214 "⋆⊧ₜ " T₁:215 " ->> " T₂:216 => valid_implication T₁ T₂
