import Timekeeper.Tactics
import Timekeeper.Language.Expression.BooleanExpression
import Timekeeper.Lemma.NumericExpression

namespace Timekeeper.BooleanExpression

lemma evaluation_remapping
  {B : BooleanExpression} {E : NumericExpression} {x : Variable} :
  ⟦B[x ↦ E]⟧(σ, τ) = ⟦B⟧(σ[x ↦ ⟦ E ⟧(σ, τ)], τ) := by
  induction B with
  | negation B' ihB' =>
    simp [
      BooleanExpression.evaluate,
      BooleanExpression.variable_replacement,
      BooleanExpression.replaceNumericExpression
    ]
    rw [<-BooleanExpression.variable_replacement]
    rw [<-Store.replacement]
    rw [<-BooleanExpression.eval]
    rw [<-NumericExpression.eval]
    rw [<-BooleanExpression.eval]
    rw [<-ihB']
  | disjunction l r ihl ihr =>
    simp [
      BooleanExpression.evaluate,
      BooleanExpression.variable_replacement,
      BooleanExpression.replaceNumericExpression
    ]
    -- simp [evaluate_boolean_expression, evaluateBooleanExpression, replaceExpressionBooleanExpression]
    repeat rw [<-Store.replacement]
    repeat rw [<-BooleanExpression.variable_replacement]
    repeat rw [<-BooleanExpression.eval]
    repeat rw [<-NumericExpression.eval]
    rw [ihl, ihr]
  | lessThanOrEqualTo E₁ E₂ =>
    simp [
      BooleanExpression.evaluate,
      BooleanExpression.variable_replacement,
      BooleanExpression.replaceNumericExpression,
    ]
    repeat rw [<-Store.replacement]
    repeat rw [<-NumericExpression.variable_replacement]
    repeat rw [<-NumericExpression.eval]
    repeat rw [NumericExpression.evaluation_remapping]

lemma equivalent_replacement {B : BooleanExpression} {E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⟧(σ, τ) = ⟦ E₂ ⟧(σ, τ) ->
  ⟦ B[E₁ ↦ E₂] ⟧(σ, τ) = ⟦ B ⟧(σ, τ) := by
  intros hE₁E₂
  induction B with
  | negation B' ihB' =>
    normalize
    rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    normalize
    rw [ihB₁, ihB₂]
  | lessThanOrEqualTo E₃ E₄ =>
    normalize
    rw [NumericExpression.equivalent_replacement, NumericExpression.equivalent_replacement] ; rotate_left
    . exact hE₁E₂
    . exact hE₁E₂

lemma store_independence {B : BooleanExpression} :
  B.containsVariables = false ->
  ⟦ B ⟧(σ₁, τ) = ⟦ B ⟧(σ₂, τ) := by
  induction B with
  | negation B' ihB' =>
    intros hcont
    simp [containsVariables] at hcont
    specialize ihB' _
    . simp [containsVariables] ; exact hcont
    normalize
    rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    intros hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hcont₁, hcont₂⟩
    specialize ihB₁ _
    . simp [containsVariables] ; exact hcont₁
    specialize ihB₂ _
    . simp [containsVariables] ; exact hcont₂
    normalize
    rw [ihB₁, ihB₂]
  | lessThanOrEqualTo E₁ E₂ =>
    intros hcont
    simp [containsVariables, numericExpressionPredicate] at hcont
    rcases hcont with ⟨hcont₁, hcont₂⟩
    normalize
    rw [NumericExpression.store_independence (σ₁ := σ₁) (σ₂ := σ₂), NumericExpression.store_independence (σ₁ := σ₁) (σ₂ := σ₂)] ; rotate_left
    . simp [NumericExpression.containsVariables] ; exact hcont₁
    . simp [NumericExpression.containsVariables] ; exact hcont₂

lemma nonexistent_term_replacement {B : BooleanExpression} :
  B.containsNumericExpression E = false -> B[E ↦ E'] = B := by
  intros hcont
  induction B with
  | negation B' ihB' =>
    specialize ihB' _
    . simp [containsNumericExpression] at hcont
      exact hcont
    normalize
    rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hB₁cont, hB₂cont⟩
    specialize ihB₁ hB₁cont
    specialize ihB₂ hB₂cont
    normalize
    rw [ihB₁, ihB₂]
    trivial
  | lessThanOrEqualTo E₁ E₂ =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hE₁cont, hE₂cont⟩
    normalize
    constructor
    . rw [NumericExpression.nonexistent_term_replacement]
      exact hE₁cont
    . rw [NumericExpression.nonexistent_term_replacement]
      exact hE₂cont

lemma trace_extension_plus_one {B : BooleanExpression} :
  ⟦ B ⟧(σ, τ ++ [e]) = ⟦ B[ℓ ↦ ℓ ⋆+ ♯1] ⟧(σ, τ) := by
  induction B with
  | negation B' ihB' =>
    simp [eval, evaluate, replaceNumericExpression] at *
    rw [<-ihB']
  | disjunction l r ihl ihr =>
    simp [eval, evaluate, replaceNumericExpression] at *
    rw [ihl, ihr]
  | lessThanOrEqualTo E₁ E₂ =>
    normalize
    repeat rw [<-NumericExpression.trace_extension_plus_one]

lemma trace_extension_minus_one {B : BooleanExpression} :
  ⟦B[ℓ ↦ ℓ ⋆- ♯1]⟧(σ, τ ++ [e]) = ⟦B⟧(σ, τ) := by
  induction B with
  | negation B' ihB' =>
    normalize
    rw [ihB']
  | disjunction l r ihl ihr =>
    normalize
    rw [ihl, ihr]
  | lessThanOrEqualTo E₁ E₂ =>
    normalize
    rw [NumericExpression.trace_extension_minus_one, NumericExpression.trace_extension_minus_one]

lemma trace_extension_minus {B : BooleanExpression} :
  ⟦B[ℓ ↦ ℓ ⋆- ♯τext.length]⟧(σ, τ ++ τext) = ⟦B⟧(σ, τ) := by
  induction B with
  | negation B' ihB' =>
    normalize
    rw [ihB']
  | disjunction l r ihl ihr =>
    normalize
    rw [ihl, ihr]
  | lessThanOrEqualTo E₁ E₂ =>
    normalize
    rw [NumericExpression.trace_extension_minus, NumericExpression.trace_extension_minus]

lemma trace_subtraction_replacement {B : BooleanExpression} :
  ⟦ B[ℓ ↦ (ℓ ⋆- ♯p)][ℓ ↦ (ℓ ⋆- ♯q)] ⟧(σ, τ) =
  ⟦ B[ℓ ↦ (ℓ ⋆- ♯(p + q))] ⟧(σ, τ) := by
  induction B with
  | negation B' ihB' =>
    normalize
    rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    normalize
    rw [ihB₁, ihB₂]
  | lessThanOrEqualTo E₁ E₂ =>
    normalize
    repeat rw [NumericExpression.trace_subtraction_replacement]

lemma evaluation_remapping_trace_extension_minus {B : BooleanExpression} {E : NumericExpression} :
  ⟦ B[⋆$x ↦ E][ℓ ↦ ℓ ⋆- ♯τext.length] ⟧(σ, τ ++ τext) =
  ⟦ B[ℓ ↦ ℓ ⋆- ♯τext.length] ⟧(σ[⋆$x ↦ ⟦ E ⟧(σ, τ)], τ ++ τext) := by
  induction B with
  | negation B' ihB' =>
    simp [replaceNumericExpression, evaluate]
    simp at ihB'
    rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    simp [replaceNumericExpression, evaluate]
    simp at ihB₁ ihB₂
    rw [ihB₁, ihB₂]
  | lessThanOrEqualTo E₁ E₂ =>
    normalize
    repeat rw [<-NumericExpression.evaluation_remapping_trace_extension_minus]

lemma le_correct :
  ⟦ E₁ ⋆≤ E₂ ⟧(σ, τ) <-> ⟦ E₁ ⟧(σ, τ) ≤ ⟦ E₂ ⟧(σ, τ) := by
  simp [evaluate]

lemma eq_correct :
  ⟦ E₁ ⋆= E₂ ⟧(σ, τ) <-> ⟦ E₁ ⟧(σ, τ) = ⟦ E₂ ⟧(σ, τ) := by
  simp [evaluate] ; exact eq_comm

lemma ne_correct :
  ⟦ E₁ ⋆≠ E₂ ⟧(σ, τ) <-> ⟦ E₁ ⟧(σ, τ) ≠ ⟦ E₂ ⟧(σ, τ) := by
  simp [evaluate] ; exact ne_comm

lemma lt_correct :
  ⟦ E₁ ⋆< E₂ ⟧(σ, τ) <-> ⟦ E₁ ⟧(σ, τ) < ⟦ E₂ ⟧(σ, τ) := by
  simp [evaluate]
  constructor <;> intros h
  . rcases h with ⟨hle, hne⟩
    apply Nat.lt_of_le_of_ne
    . exact hle
    . exact fun a => hne (id (Eq.symm a))
  . constructor
    . apply Nat.le_of_lt
      exact h
    . change E₂.evaluate σ τ ≠ E₁.evaluate σ τ
      rw [ne_comm]
      apply Nat.ne_of_lt
      exact h

lemma conj_correct {B₁ B₂ : BooleanExpression} :
  ⟦ B₁ ⋆∧ B₂ ⟧(σ, τ) <-> ⟦ B₁ ⟧(σ, τ) ∧ ⟦ B₂ ⟧(σ, τ) := by
  simp [evaluate]

lemma conj_false_iff {B₁ B₂ : BooleanExpression} :
  ⟦ B₁ ⋆∧ B₂ ⟧(σ, τ) = false <-> ⟦ B₁ ⟧(σ, τ) = false ∨ ⟦ B₂ ⟧(σ, τ) = false := by
  simp [evaluate]
  rw [Bool.and_eq_false_iff]

lemma and_false_iff {B₁ B₂ : BooleanExpression} : ⟦ B₁ ⋆∧ B₂ ⟧(σ, τ) = false <-> ⟦ B₁ ⟧(σ, τ) = false ∨ ⟦ B₂ ⟧(σ, τ) = false := by
  simp [evaluate] ; rw [Bool.and_eq_false_iff]

lemma le_false_iff {E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⋆≤ E₂ ⟧(σ, τ) = false <-> ⟦ E₂ ⋆< E₁ ⟧(σ, τ) := by
  rw [Bool.eq_false_iff]
  change ¬(⟦ E₁ ⋆≤ E₂ ⟧(σ, τ) = true) <-> ⟦ E₂ ⋆< E₁ ⟧(σ, τ)
  rw [Iff.not le_correct, lt_correct]
  constructor <;> intros h
  . exact Nat.lt_of_not_le h
  . exact Nat.not_le_of_lt h

lemma eq_false_iff {E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⋆= E₂ ⟧(σ, τ) = false <-> ⟦ E₁ ⋆≠ E₂ ⟧(σ, τ) = true := by
  rw [Bool.eq_false_iff]
  simp [evaluate]
  rw [Bool.not_iff_not]
  simp

lemma lt_false_iff {E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⋆< E₂ ⟧(σ, τ) = false <-> ⟦ E₂ ⋆≤ E₁ ⟧(σ, τ) := by
  rw [Bool.eq_false_iff]
  change ¬(⟦ E₁ ⋆< E₂ ⟧(σ, τ) = true) <-> ⟦ E₂ ⋆≤ E₁ ⟧(σ, τ) = true
  rw [Iff.not lt_correct, le_correct]
  constructor <;> intros h
  . exact Nat.le_of_not_lt h
  . exact Nat.not_lt_of_le h

lemma trace_sub_add_cancel {B : BooleanExpression} :
  ⟦ B[ℓ ↦ ℓ ⋆- ♯k][ℓ ↦ ℓ ⋆+ ♯k] ⟧(σ, τ) = ⟦ B ⟧(σ, τ) := by
  induction B with
  | negation B' ihB' =>
    normalize
    rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    normalize
    rw [ihB₁, ihB₂]
  | lessThanOrEqualTo E₁ E₂ =>
    normalize
    rw [NumericExpression.trace_sub_add_cancel]
    rw [NumericExpression.trace_sub_add_cancel]

lemma eq_literalize {B : BooleanExpression} :
  ⟦ B ⟧(σ, τ) = ⟦ B.literalize σ τ ⟧(σ', τ') := by
  induction B with
  | negation B' ihB' =>
    simp [literalize]
    normalize
    rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    simp [literalize]
    normalize
    rw [ihB₁, ihB₂]
  | lessThanOrEqualTo E₁ E₂ =>
    simp [literalize]
    normalize
    rw [NumericExpression.eq_literalize (E := E₁) (σ' := σ') (τ' := τ'), NumericExpression.eq_literalize (E := E₂) (σ' := σ') (τ' := τ')]

lemma double_trace_replace {B : BooleanExpression} {E₁ E₂ E₁' : NumericExpression} :
   ⟦ E₁[ℓ ↦ E₂] ⟧(σ, τ) = ⟦ E₁' ⟧(σ, τ) ->
  (⟦ B[ℓ ↦ E₁][ℓ ↦ E₂] ⟧(σ, τ) =
  ⟦ B[ℓ ↦ E₁'] ⟧(σ, τ)) := by
  intros hE₁'
  induction B with
  | negation B' ihB' =>
    normalize ; rw [ihB']
  | disjunction B₁ B₂ ihB₁ ihB₂ =>
    normalize ; rw [ihB₁, ihB₂]
  | lessThanOrEqualTo E₃ E₄ =>
    normalize
    rw [NumericExpression.double_trace_replace, NumericExpression.double_trace_replace]
    . exact hE₁'
    . exact hE₁'
