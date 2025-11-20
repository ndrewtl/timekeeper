import Timekeeper.Tactics
import Timekeeper.Lemma.NumericExpression
import Timekeeper.Lemma.BooleanExpression
import Timekeeper.Lemma.TraceAssertion
import Timekeeper.Lemma.GeneralAssertion.Inversion

namespace Timekeeper.GeneralAssertion
open Models

lemma evaluation_remapping {E : NumericExpression} :
  E.containsLogicalVariables = false ->
  (⋆ σ, τ ⊧[v] P[⋆$x ↦ E] <-> ⋆ (σ[⋆$x ↦ ⟦ E ⟧(σ, τ)]), τ ⊧[v] P) := by
  intros hLV
  revert σ τ v
  . induction P with
  | expression B =>
    intros v σ τ
    constructor <;>
    intros hP <;>
    apply expression_inversion at hP <;>
    apply expression_intro
    . simp at hP
      normalize at hP
      rw [BooleanExpression.evaluation_remapping] at hP
      exact hP
    . simp at hP
      rw [<-BooleanExpression.eval, <-Store.replacement] at hP
      simp
      rw [<-BooleanExpression.variable_replacement, <-BooleanExpression.eval]
      rw [BooleanExpression.evaluation_remapping]
      exact hP
  | negation φ ihφ =>
    intros σ τ v
    constructor <;>
    intros hP <;>
    apply negation_inversion at hP <;>
    apply negation_intro
    . rw [<-variable_replacement] at hP
      rw [ihφ] at hP
      exact hP
    . rw [<-variable_replacement]
      rw [ihφ]
      exact hP
  | disjunction φ ψ ihφ ihψ =>
    intros σ τ v
    simp [variable_replacement, replaceNumericExpression]
    rw [<-Store.replacement, <-variable_replacement, <-variable_replacement]
    constructor <;>
    intros hP <;>
    apply disjunction_inversion_bool at hP <;>
    normalize at hP <;>
    normalize <;>
    rcases hP with (⟨rfl, hφ, hψ⟩ | ⟨rfl, (hφ | hψ)⟩)
    . apply disjunction_intro_false
      . rw [ihφ] at hφ ; exact hφ
      . rw [ihψ] at hψ ; exact hψ
    . apply disjunction_intro_left
      rw [ihφ] at hφ ; exact hφ
    . apply disjunction_intro_right
      rw [ihψ] at hψ ; exact hψ
    . apply disjunction_intro_false
      . rw [ihφ] ; exact hφ
      . rw [ihψ] ; exact hψ
    . apply disjunction_intro_left
      rw [ihφ] ; exact hφ
    . apply disjunction_intro_right
      rw [ihψ] ; exact hψ
  | trace T E' =>
    intros σ τ v
    constructor <;> intros hP <;>
    apply trace_inversion at hP <;>
    apply trace_intro
    . normalize at hP
      rw [NumericExpression.evaluation_remapping, TraceAssertion.evaluation_remapping] at hP ; rotate_left
      . exact hLV
      exact hP
    . normalize
      rw [NumericExpression.evaluation_remapping, TraceAssertion.evaluation_remapping] ; rotate_left
      . exact hLV
      exact hP
  | universal_quantification x' A ih =>
    intros σ τ v
    constructor <;> intros hP <;>
    apply universal_quantification_inversion at hP <;>
    apply universal_quantification_intro
    . intros v'
      specialize hP v'
      rw [<-variable_replacement] at hP
      rw [ih] at hP
      rw [Store.replacement_different_variables_reordering]
      rw [NumericExpression.logical_variable_independence] at hP
      exact hP
      . exact hLV
      . simp
    . intros v'
      specialize hP v'
      rw [<-variable_replacement]
      rw [ih]
      rw [Store.replacement_different_variables_reordering] at hP
      rw [NumericExpression.logical_variable_independence]
      exact hP
      . exact hLV
      . simp

lemma store_independence {A : GeneralAssertion} :
  ¬(A.containsVariables) ->
  (⋆ σ₁, τ ⊧[ b ] A <-> ⋆ σ₂, τ ⊧[ b ] A) := by
  intros hcont
  revert σ₁ σ₂ b
  induction A with
  | expression B =>
    intros σ₁ b σ₂
    simp [containsVariables, numericExpressionPredicate] at hcont
    constructor <;>
    intros h <;>
    apply expression_inversion at h <;>
    apply expression_intro
    . rw [BooleanExpression.store_independence (σ₂ := σ₂)] at h ; rotate_left
      . simp [BooleanExpression.containsVariables] ; exact hcont
      exact h
    . rw [BooleanExpression.store_independence (σ₂ := σ₂)] ; rotate_left
      . simp [BooleanExpression.containsVariables] ; exact hcont
      exact h
  | negation A' ihA' =>
    intros σ₁ b σ₂
    constructor <;>
    intros h <;>
    apply negation_inversion at h <;>
    apply negation_intro
    . rw [ihA' (σ₂ := σ₂)] at h ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
    . rw [ihA' (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
  | disjunction A₁ A₂ ihA₁ ihA₂ =>
    intros σ b σ₂
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hcont₁, hcont₂⟩
    constructor <;>
    intros h <;>
    apply disjunction_inversion_bool at h <;>
    rcases h with (⟨rfl, hA₁, hA₂⟩ | ⟨rfl, (hA₁ | hA₂)⟩) <;>
    (try normalize at hA₁) <;>
    (try normalize at hA₂) <;>
    (try rw [ihA₁ (σ₂ := σ₂)] at hA₁ ; rotate_left ; simp [containsVariables] ; exact hcont₁) <;>
    (try rw [ihA₂ (σ₂ := σ₂)] at hA₂ ; rotate_left ; simp [containsVariables] ; exact hcont₂) <;>
    (try apply disjunction_intro_false) <;>
    normalize <;>
    (try rw [ihA₁ (σ₂ := σ₂)] ; rotate_left ; simp [containsVariables] ; exact hcont₁) <;>
    (try rw [ihA₂ (σ₂ := σ₂)] ; rotate_left ; simp [containsVariables] ; exact hcont₂) <;>
    (try exact hA₁) <;>
    (try exact hA₂)
    . apply disjunction_intro_left
      exact hA₁
    . apply disjunction_intro_right
      exact hA₂
    . apply disjunction_intro_left
      rw [ihA₁ (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont₁
      exact hA₁
    . apply disjunction_intro_right
      rw [ihA₂ (σ₂ := σ₂)] ; rotate_left
      . simp [containsVariables] ; exact hcont₂
      exact hA₂
  | trace T E =>
    intros σ b σ₂
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hcontT, hcontE⟩
    constructor <;>
    intros h <;>
    apply trace_inversion at h <;>
    apply trace_intro
    . rw [NumericExpression.store_independence (σ₂ := σ₂), TraceAssertion.store_independence (σ₂ := σ₂)] at h ; rotate_left
      . simp [TraceAssertion.containsVariables] ; exact hcontT
      . simp [NumericExpression.containsVariables] ; exact hcontE
      exact h
    . rw [NumericExpression.store_independence (σ₂ := σ₂), TraceAssertion.store_independence (σ₂ := σ₂)] ; rotate_left
      . simp [TraceAssertion.containsVariables] ; exact hcontT
      . simp [NumericExpression.containsVariables] ; exact hcontE
      exact h
  | universal_quantification x A' ihA' =>
    intros σ₁ b σ₂
    simp [containsVariables, numericExpressionPredicate] at hcont
    constructor <;>
    intros h <;>
    apply universal_quantification_inversion at h <;>
    apply universal_quantification_intro <;>
    intros v' <;>
    specialize h v' <;>
    normalize at h <;>
    normalize
    . rw [ihA' (σ₂ := σ₂[⋆^x ↦ v'])] at h ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
    . rw [ihA' (σ₂ := σ₂[⋆^x ↦ v'])] ; rotate_left
      . simp [containsVariables] ; exact hcont
      exact h
