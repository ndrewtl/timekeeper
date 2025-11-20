import Mathlib.Logic.Relation
import Timekeeper.Language.Expression.NumericExpression
import Timekeeper.Language.Expression.NumericExpressionList
import Timekeeper.Language.Command
import Timekeeper.Language.Configuration
import Timekeeper.Language.Semantics.Store
import Timekeeper.Language.Semantics.SmallStep

namespace Timekeeper
open Command
open SmallStep
open SmallStepRTC

inductive BigStep : Command -> Store -> Trace -> Store -> Trace -> Prop where
| big_step_skip :
  BigStep skip σ τ σ τ
| big_step_assign :
  BigStep (set ⋆$x ⋆:= E) σ τ (σ[⋆$x ↦ ⟦E⟧(σ, τ)]) τ
| big_step_emit :
  BigStep (emit Es) σ τ σ (τ ++ [{store := σ, event := ⟦ Es ⟧(σ, τ) }])
| big_step_resolve :
  BigStep (resolve ω) σ τ σ τ
| big_step_seq :
  BigStep C₁ σ τ σ' τ' ->
  BigStep C₂ σ' τ' σ'' τ'' ->
  BigStep (C₁ ⋆; C₂) σ τ σ'' τ''
| big_step_if_false {B : BooleanExpression} :
  ⟦B⟧(σ, τ) = false ->
  BigStep C₂ σ τ σ' τ' ->
  BigStep (if: B then: C₁ else: C₂ end) σ τ σ' τ'
| big_step_if_true :
  ⟦B⟧(σ, τ) = true ->
  BigStep C₁ σ τ σ' τ' ->
  BigStep (if: B then: C₁ else: C₂ end) σ τ σ' τ'
| big_step_while_false :
  ⟦B⟧(σ, τ) = false ->
  BigStep (while: B do: C end) σ τ σ τ
| big_step_while_true :
  ⟦B⟧(σ, τ) = true ->
  BigStep C σ τ σ' τ' ->
  BigStep (while: B do: C end) σ' τ' σ'' τ'' ->
  BigStep (while: B do: C end) σ τ σ'' τ''

notation:184 "(" C ", " σ ", " τ ")" " ↓ " "(" σ' ", " τ' ")" => BigStep C σ τ σ' τ'
