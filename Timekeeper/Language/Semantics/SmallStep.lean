import Mathlib.Logic.Relation
import Timekeeper.Language.Expression.NumericExpression
import Timekeeper.Language.Expression.NumericExpressionList
import Timekeeper.Language.Command
import Timekeeper.Language.Configuration
import Timekeeper.Language.Semantics.Store

namespace Timekeeper
open Command
open Relation

inductive SmallStep : Command -> Store -> Trace -> Command -> Store -> Trace -> Prop
| small_step_skip σ τ :
  SmallStep skip σ τ skip σ τ
| small_step_assign x E σ τ :
  SmallStep (set ⋆$x ⋆:= E) σ τ skip (σ[⋆$x ↦ ⟦E⟧(σ, τ)]) τ
| small_step_emit Es σ τ :
  SmallStep (emit Es) σ τ skip σ (τ ++ [{ store := σ, event := ⟦ Es ⟧(σ, τ)}] )
| small_step_resolve ω σ τ :
  SmallStep (resolve ω) σ τ skip σ τ
| small_step_seq_reduce C₁ C₁' C₂ σ τ σ' τ' :
  SmallStep C₁ σ τ C₁' σ' τ' ->
  SmallStep (C₁ ⋆; C₂) σ τ (C₁' ⋆; C₂) σ' τ'
| small_step_seq C₂ σ τ :
  SmallStep (skip ⋆; C₂) σ τ C₂ σ τ
| small_step_if_true B C₁ C₂ σ τ :
  (⟦B⟧(σ, τ) : Bool) ->
  SmallStep (if: B then: C₁ else: C₂ end) σ τ C₁ σ τ
| small_step_if_false B C₁ C₂ σ τ :
  ¬⟦B⟧(σ, τ) ->
  SmallStep (if: B then: C₁ else: C₂ end) σ τ C₂ σ τ
| small_step_while B C  σ τ:
  SmallStep (while: B do: C end) σ τ (if: B then: (C ⋆; (while: B do: C end)) else: skip end) σ τ

open SmallStep

inductive SmallStepRTC : Command -> Store -> Trace -> Command -> Store -> Trace -> Prop
| refl :
  SmallStepRTC C σ τ C σ τ
| step :
  SmallStep C σ τ C' σ' τ' ->
  SmallStepRTC C' σ' τ' C'' σ'' τ'' ->
  SmallStepRTC C σ τ C'' σ'' τ''

namespace SmallStepRTC

-- Combine two RTC's to form another one
lemma trans :
  SmallStepRTC C₁ σ₁ τ₁ C₂ σ₂ τ₂ ->
  SmallStepRTC C₂ σ₂ τ₂ C₃ σ₃ τ₃ ->
  SmallStepRTC C₁ σ₁ τ₁ C₃ σ₃ τ₃ := by
  intros hC₁ hC₂
  induction hC₁ with
  | refl =>
    exact hC₂
  | step hfirst hrest ih =>
    apply SmallStepRTC.step
    . exact hfirst
    . exact ih hC₂

-- Lift the small-step operation to configurations
def small_step_configuration (π₁ π₂: Configuration) : Prop :=
  match (π₁, π₂) with
  | ((C₁, σ₁, τ₁), (C₂, σ₂, τ₂)) => SmallStep C₁ σ₁ τ₁ C₂ σ₂ τ₂

-- Convert a SmallStepRTC to a ReflTransGen
lemma is_rtc :
  SmallStepRTC C₁ σ₁ τ₁ C₂ σ₂ τ₂ <->
  ReflTransGen small_step_configuration (C₁, σ₁, τ₁) (C₂, σ₂, τ₂) := by
  constructor <;> intros h
  . induction h with
    | refl =>
      apply ReflTransGen.refl
    | step hfirst hrest ih =>
      expose_names
      apply ReflTransGen.head (b := (C', σ', τ'))
      . simp [small_step_configuration]
        exact hfirst
      . exact ih
  . generalize hπ₁ : (C₁, σ₁, τ₁) = π₁ at h
    generalize hπ₂ : (C₂, σ₂, τ₂) = π₂ at h
    revert C₁ σ₁ τ₁ C₂ σ₂ τ₂
    induction h using ReflTransGen.head_induction_on with
    | refl =>
      intros C₁ σ₁ τ₁ C₂ σ₂ τ₂ hπ₁ hπ₂
      rw [<-hπ₁] at hπ₂
      rcases hπ₂
      apply refl
    | head hfirst hrest ih =>
      intros C₁ σ₁ τ₁ C₂ σ₂ τ₂ hπ₁ hπ₂
      expose_names
      rw [<-hπ₁] at hfirst
      simp [small_step_configuration] at hfirst
      apply step
      . exact hfirst
      . apply ih
        . exact rfl
        . exact hπ₂

notation:192 "(" C ", " σ ", " τ ")" " ⇝ " "(" C' ", " σ' ", " τ' ")" => SmallStep C σ τ C' σ' τ'
-- notation:181 π " ⇝[ " k " ] " π' => small_step_n π k π'
notation:193 "(" C ", " σ ", " τ ")" " ⇝* " "(" C' ", " σ' ", " τ' ")" => SmallStepRTC C σ τ C' σ' τ'
