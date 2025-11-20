-- This file contains lemmas that state properties about numeric expressions
import Mathlib.Tactic.Lemma
import Timekeeper.Tactics
import Timekeeper.Language.Expression.NumericExpression

namespace Timekeeper.NumericExpression

lemma predicate_binary_operation :
  predicateHoldsSubtree P (binaryOperation op E₁ E₂) <->
  P (binaryOperation op E₁ E₂) ∨ predicateHoldsSubtree P E₁ ∨ predicateHoldsSubtree P E₂ := by
  constructor <;> intros h
  . simp [predicateHoldsSubtree] at h
    rcases h with (hlr | hl | hr)
    . left; exact hlr
    . right; left; exact hl
    . right; right; exact hr
  . simp [predicateHoldsSubtree]
    rcases h with (hlr | hl | hr)
    . left; exact hlr
    . right; left; exact hl
    . right; right; exact hr

lemma trace_independence {E : NumericExpression} :
  E.containsTraceLength = false ->
  ⟦ E ⟧(σ, τ ++ τ') = ⟦ E ⟧(σ, τ) := by
  induction E with
  | numericLiteral _ =>
    simp [NumericExpression.evaluate]
  | var _ =>
    simp [NumericExpression.evaluate]
  | traceLength =>
    intros h
    simp [containsTraceLength, containsExpression, predicateHoldsSubtree] at h
  | binaryOperation op l r ihl ihr =>
    intros hℓ
    specialize ihl _
    . simp [containsTraceLength, containsExpression, predicateHoldsSubtree] at hℓ
      simp [containsTraceLength, containsExpression]
      simp [hℓ]
    specialize ihr _
    . simp [containsTraceLength, containsExpression, predicateHoldsSubtree] at hℓ
      simp [containsTraceLength, containsExpression]
      simp [hℓ]
    simp [NumericExpression.evaluate] at *
    rw [ihl, ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    intros hℓ
    simp [containsTraceLength, containsExpression, predicateHoldsSubtree] at hℓ
    rcases hℓ with ⟨hℓE₁, hℓE₂, hℓE₃⟩
    specialize ihE₁ _
    . simp [containsTraceLength, containsExpression]
      exact hℓE₁
    specialize ihE₂ _
    . simp [containsTraceLength, containsExpression]
      exact hℓE₂
    specialize ihE₃ _
    . simp [containsTraceLength, containsExpression]
      exact hℓE₃
    simp [NumericExpression.evaluate]
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma store_independence {E : NumericExpression} :
  E.containsVariables = false ->
  ⟦ E ⟧(σ₁, τ) = ⟦ E ⟧(σ₂, τ) := by
  induction E with
  | numericLiteral _ =>
    normalize
  | var x =>
    intros hcont
    simp [containsVariables, predicateHoldsSubtree, isVariable] at hcont
  | traceLength =>
    intros hcont
    normalize
  | binaryOperation op l r ihl ihr =>
    intros hcont
    simp [containsVariables, predicateHoldsSubtree] at hcont
    rcases hcont with ⟨heq, hcontl, hcontr⟩
    specialize ihl _
    . simp [containsVariables] ; exact hcontl
    specialize ihr _
    . simp [containsVariables] ; exact hcontr
    normalize
    rw [ihl, ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    intros hcont
    simp [containsVariables, predicateHoldsSubtree] at hcont
    rcases hcont with ⟨heq, hcont₁, hcont₂, hcont₃⟩
    specialize ihE₁ _
    . simp [containsVariables] ; exact hcont₁
    specialize ihE₂ _
    . simp [containsVariables] ; exact hcont₂
    specialize ihE₃ _
    . simp [containsVariables] ; exact hcont₃
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma logical_variable_independence {E : NumericExpression} :
  E.containsLogicalVariables = false -> ⟦ E ⟧(σ[⋆^x ↦ v], τ) = ⟦ E ⟧(σ, τ) := by
  intros hLV
  induction E with
  | numericLiteral _ =>
    simp [Store.update, NumericExpression.evaluate]
  | var x =>
    simp [containsLogicalVariables, predicateHoldsSubtree, isLogicalVariable] at hLV
    rcases x with (x | x)
    . simp at hLV -- This case is contradictory
    . simp [NumericExpression.evaluate, Store.update]
  | traceLength =>
    simp [Store.update, NumericExpression.evaluate]
  | binaryOperation op l r ihl ihr =>
    simp [containsLogicalVariables, predicateHoldsSubtree] at hLV
    rcases hLV with ⟨_, hLVl, hLVr⟩
    simp only [NumericExpression.eval, NumericExpression.evaluate]
    rw [<-NumericExpression.eval, <-NumericExpression.eval]
    rw [ihl, ihr]
    simp
    . exact hLVr
    . exact hLVl
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    simp [containsLogicalVariables, predicateHoldsSubtree] at hLV
    rcases hLV with ⟨_, hLVE₁, hLVE₂, hLVE₃⟩
    specialize ihE₁ _
    . simp [containsLogicalVariables] ; exact hLVE₁
    specialize ihE₂ _
    . simp [containsLogicalVariables] ; exact hLVE₂
    specialize ihE₃ _
    . simp [containsLogicalVariables] ; exact hLVE₃
    simp [NumericExpression.evaluate]
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma evaluation_remapping {E E' : NumericExpression} {x : Variable} :
  ⟦ E[x ↦ E'] ⟧(σ, τ) = ⟦ E ⟧(σ[x ↦ ⟦ E' ⟧(σ, τ)], τ) := by
  induction E with
  | numericLiteral n =>
    simp [evaluate, replaceNumericExpression, Store.update]
  | var x' =>
    by_cases hx'x : x' = x
    . rw [hx'x]
      simp [
        replaceNumericExpression,
        evaluate,
        Store.replacement,
        Store.update
      ]
    . simp [
        replaceNumericExpression,
        evaluate,
        Store.replacement,
        Store.update,
        hx'x
      ]
  | traceLength =>
    simp [evaluate, replaceNumericExpression]
  | binaryOperation op l r ihl ihr =>
    simp [
      evaluate,
      replaceNumericExpression
    ]
    repeat rw [<-variable_replacement]
    repeat rw [<-eval]
    rw [ihl, ihr]
    simp
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma equivalent_replacement {E₀ E₁ E₂ : NumericExpression} :
  ⟦ E₁ ⟧(σ, τ) = ⟦ E₂ ⟧(σ, τ) ->
  ⟦ E₀[E₁ ↦ E₂] ⟧(σ, τ) = ⟦ E₀ ⟧(σ, τ) := by
  intros hE₁E₂
  induction E₀ with
  | numericLiteral n =>
    normalize
    split
    case isTrue h =>
      rw [<-h] at hE₁E₂
      rw [<-hE₁E₂]
      normalize
    case isFalse h =>
      normalize
  | var x =>
    normalize
    split
    case isTrue h =>
      rw [<-h] at hE₁E₂
      rw [<-hE₁E₂]
      normalize
    case isFalse h =>
      normalize
  | traceLength =>
    normalize
    split
    case isTrue h =>
      rw [<-h] at hE₁E₂
      rw [<-hE₁E₂]
      normalize
    case isFalse h =>
      normalize
  | binaryOperation op E₃ E₄ ihE₃ ihE₄ =>
    normalize
    split
    case isTrue h =>
      rw [<-h] at hE₁E₂
      rw [<-hE₁E₂]
      normalize
    case isFalse h =>
      normalize
      rw [ihE₃, ihE₄]
  | trinaryOperation op E₃ E₄ E₅ ihE₃ ihE₄ ihE₅ =>
    normalize
    split
    case isTrue h =>
      rw [<-h] at hE₁E₂
      rw [<-hE₁E₂]
      normalize
    case isFalse h =>
      normalize
      rw [ihE₃, ihE₄, ihE₅]

lemma distribute_substitution {E₁ E₂ E₃ E₄ : NumericExpression}:
  E₃ ≠ binaryOperation op E₁ E₂ ->
  (binaryOperation op E₁ E₂)[E₃ ↦ E₄] = (binaryOperation op (E₁[E₃ ↦ E₄]) (E₂[E₃ ↦ E₄])) := by
  intros hE₃
  simp [replaceNumericExpression]
  intros contr
  rw [contr] at hE₃
  contradiction

lemma nonexistent_term_replacement {E E₀ E₁ : NumericExpression} :
  E.containsExpression E₀ = false ->
  E[E₀ ↦ E₁] = E := by
  intros hcont
  induction E with
  | numericLiteral n =>
    simp [containsExpression, predicateHoldsSubtree] at hcont
    simp [replaceNumericExpression]
    exact fun a => False.elim (hcont (id (Eq.symm a)))
  | var x =>
    simp [containsExpression, predicateHoldsSubtree] at hcont
    simp [replaceNumericExpression]
    exact fun a => False.elim (hcont (id (Eq.symm a)))
  | traceLength =>
    simp [containsExpression, predicateHoldsSubtree] at hcont
    simp [replaceNumericExpression]
    exact fun a => False.elim (hcont (id (Eq.symm a)))
  | binaryOperation op l r ihl ihr =>
    simp [containsExpression, predicateHoldsSubtree] at hcont
    rcases hcont with ⟨hlr, hl, hr⟩
    simp [containsExpression] at ihl ihr
    specialize ihl hl
    specialize ihr hr
    have hlr : NumericExpression.binaryOperation op l r ≠ E₀ :=
      by exact fun a => hlr (id (Eq.symm a))
    simp [replaceNumericExpression, hlr]
    rw [ihl, ihr]
    exact ⟨rfl, rfl⟩
  | trinaryOperation op Ea Ei Ev ihEa ihEi ihEv =>
    simp [containsExpression, predicateHoldsSubtree] at hcont
    rcases hcont with ⟨hEcont, hEacont, hEicont, hEvcont⟩
    specialize ihEa _
    . simp [containsExpression] ; exact hEacont
    specialize ihEi _
    . simp [containsExpression] ; exact hEicont
    specialize ihEv _
    . simp [containsExpression] ; exact hEvcont
    normalize
    rw [ihEa, ihEi, ihEv]
    rcases op
    rw [<-arrayAssign] at hEcont
    have h : Ea[ Ei := Ev ]ₑ ≠ E₀ := by exact fun a => hEcont (id (Eq.symm a))
    split
    . expose_names ; contradiction
    . trivial

lemma logical_state_independence {E : NumericExpression} :
  E.containsLogicalVariables = false ->
  ⟦ E ⟧(σ[⋆^x ↦ v], τ) = ⟦ E ⟧(σ, τ) := by
  intros hE
  induction E with
  | numericLiteral n =>
    simp [evaluate]
  | var x' =>
    simp [evaluate, Store.update]
    intros contr
    rw [contr] at hE
    contradiction
  | traceLength =>
    simp [evaluate]
  | binaryOperation op l r ihl ihr =>
    simp [containsLogicalVariables, predicateHoldsSubtree] at hE
    rcases hE with ⟨hlr, hl, hr⟩
    specialize ihl _
    . simp [containsLogicalVariables] ; exact hl
    specialize ihr _
    . simp [containsLogicalVariables] ; exact hr
    simp [evaluate]
    repeat rw [<-eval]
    repeat rw [<-Store.replacement]
    repeat rw [ihl]
    repeat rw [ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    simp [containsLogicalVariables, predicateHoldsSubtree] at hE
    rcases hE with ⟨_, hE₁, hE₂, hE₃⟩
    specialize ihE₁ _
    . simp [containsLogicalVariables] ; exact hE₁
    specialize ihE₂ _
    . simp [containsLogicalVariables] ; exact hE₂
    specialize ihE₃ _
    . simp [containsLogicalVariables] ; exact hE₃
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma state_independence {E : NumericExpression} :
  ¬(E.containsExpression (var x)) ->
  ⟦ E ⟧(σ[x ↦ v], τ) = ⟦ E ⟧(σ, τ) := by
  intros hE
  induction E with
  | numericLiteral n =>
    simp [evaluate]
  | var x' =>
    simp [containsExpression, predicateHoldsSubtree] at hE
    simp [evaluate, Store.update]
    intros contr
    rw [contr] at hE
    contradiction
  | traceLength =>
    simp [evaluate]
  | binaryOperation op l r ihl ihr =>
    simp [containsExpression, predicateHoldsSubtree] at hE
    rcases hE with ⟨hl, hr⟩
    specialize ihl _
    . simp [containsExpression] ; exact hl
    specialize ihr _
    . simp [containsExpression] ; exact hr
    simp [evaluate]
    repeat rw [<-eval]
    repeat rw [<-Store.replacement]
    repeat rw [ihl]
    repeat rw [ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    simp [containsExpression, predicateHoldsSubtree] at hE
    rcases hE with ⟨hE₁, hE₂, hE₃⟩
    specialize ihE₁ _
    . simp [containsExpression] ; exact hE₁
    specialize ihE₂ _
    . simp [containsExpression] ; exact hE₂
    specialize ihE₃ _
    . simp [containsExpression] ; exact hE₃
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma  trace_extension_plus_one :
  ⟦E⟧(σ, τ ++ [e]) = ⟦(E : NumericExpression)[ℓ ↦ ℓ ⋆+ ♯1]⟧(σ, τ) := by
  induction E with
  | numericLiteral n =>
    simp
    rw [replaceNumericExpression, evaluate] <;> try simp
    simp [evaluate]
  | var x =>
    simp
    rw [replaceNumericExpression] <;> try simp
    simp [evaluate]
  | traceLength =>
    simp
    normalize
  | binaryOperation op l r ihl ihr =>
    normalize
    have hlrℓ : ((l.binaryOperation op r) == ℓ) = false := by exact rfl
    rcases op <;> normalize <;> rw [ihl, ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma trace_extension_minus {E : NumericExpression} :
  ⟦ E[ℓ ↦ ℓ ⋆- ♯τ'.length] ⟧(σ, τ ++ τ') = ⟦ E ⟧(σ, τ) := by
  induction E with
  | numericLiteral n =>
    have hnℓ : (♯n == ℓ) = false := by exact rfl
    simp [evaluate, replaceNumericExpression, hnℓ]
  | var x =>
    simp [evaluate, replaceNumericExpression]
  | traceLength => normalize
  | binaryOperation op l r ihl ihr =>
    simp [evaluate, replaceNumericExpression]
    simp at ihl ihr
    rw [ihl, ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma trace_extension_minus_one {E : NumericExpression} :
  ⟦ E[ℓ ↦ ℓ ⋆- ♯1] ⟧(σ, τ ++ [e]) = ⟦ E ⟧(σ, τ) := by
  have helen : 1 = [e].length := by exact rfl
  rw [helen]
  apply trace_extension_minus

section -- Special cases

lemma trace_subtraction_replacement {E : NumericExpression} :
  ⟦ E[ℓ ↦ (ℓ ⋆- ♯p)][ℓ ↦ (ℓ ⋆- ♯q)] ⟧(σ, τ) =
  ⟦ E[ℓ ↦ (ℓ ⋆- ♯(p + q))] ⟧(σ, τ) := by
  induction E with
  | numericLiteral n =>
    simp [replaceNumericExpression, evaluate]
  | var x =>
    simp [replaceNumericExpression, evaluate]
  | traceLength =>
    simp [replaceNumericExpression, evaluate]
    rw [Nat.Simproc.sub_add_eq_comm]
  | binaryOperation op l r ihl ihr =>
    normalize
    rw [ihl, ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma evaluation_remapping_trace_extension_minus {E E' : NumericExpression} :
  ⟦ E[⋆$x ↦ E'][ℓ ↦ ℓ ⋆- ♯τext.length] ⟧(σ, τ ++ τext) =
  ⟦ E[ℓ ↦ ℓ ⋆- ♯τext.length] ⟧(σ[⋆$x ↦ ⟦ E' ⟧(σ, τ)], τ ++ τext) := by
  induction E with
  | numericLiteral n =>
    simp [replaceNumericExpression, evaluate]
  | var x' =>
    simp [replaceNumericExpression, evaluate]
    rw [<-eval, <-Store.replacement]
    rcases x' with (x' | x')
    . simp [Store.update, replaceNumericExpression, evaluate]
    . by_cases hx'x : x' = x <;> simp [hx'x]
      . simp [Store.update]
        rw [<-eval, <-eval, <-numeric_replacement]
        exact trace_extension_minus
      . simp [Store.update, hx'x, replaceNumericExpression, evaluate]
  | traceLength =>
    simp [replaceNumericExpression, evaluate]
  | binaryOperation op l r ihl ihr =>
    normalize
    rw [ihl, ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma double_trace_replace {E₀ E₁ E₂ E₁' : NumericExpression} :
   ⟦ E₁[ℓ ↦ E₂] ⟧(σ, τ) = ⟦ E₁' ⟧(σ, τ) ->
  (⟦ E₀[ℓ ↦ E₁][ℓ ↦ E₂] ⟧(σ, τ) =
  ⟦ E₀[ℓ ↦ E₁'] ⟧(σ, τ)) := by
  intros hE₁'
  induction E₀ with
  | numericLiteral n => normalize
  | var x => normalize
  | traceLength =>
    normalize
    exact hE₁'
  | binaryOperation op E₃ E₄ ihE₃ ihE₄ =>
    normalize
    rw [ihE₃, ihE₄]
  | trinaryOperation op E₃ E₄ E₅ ihE₃ ihE₄ ihE₅ =>
    normalize
    rw [ihE₃, ihE₄, ihE₅]

lemma trace_length_substitution_preserves_trace_length_presence {E : NumericExpression} :
  E[ℓ ↦ binaryOperation op ℓ ♯n].containsTraceLength = E.containsTraceLength := by
  induction E with
  | numericLiteral n' =>
    simp [containsTraceLength, replaceNumericExpression]
  | var x =>
    simp [containsTraceLength, replaceNumericExpression]
  | traceLength =>
    simp [replaceNumericExpression, containsTraceLength, containsExpression, predicateHoldsSubtree]
  | binaryOperation op' l r ihl ihr =>
    simp [replaceNumericExpression, containsTraceLength, containsExpression, predicateHoldsSubtree]
    repeat rw [<-numeric_replacement]
    repeat rw [<-containsExpression]
    repeat rw [<-containsTraceLength]
    rw [ihl, ihr]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    simp [replaceNumericExpression, containsTraceLength, containsExpression, predicateHoldsSubtree]
    repeat rw [<-numeric_replacement]
    repeat rw [<-containsExpression]
    repeat rw [<-containsTraceLength]
    rw [ihE₁, ihE₂, ihE₃]

lemma lookup_same_index :
  ⟦ E₂ ⟧(σ, τ) = ⟦ E₄ ⟧(σ, τ) ->
  ⟦ E₁[ E₂ := E₃ ]ₑ[ E₄ ]ₑ ⟧(σ, τ) = ⟦ E₃ ⟧(σ, τ) := by
  intros h
  normalize
  rw [h]
  rw [PrimesMap.set_correct]

lemma lookup_different_index :
  ⟦ E₂ ⟧(σ, τ) ≠ ⟦ E₄ ⟧(σ, τ) ->
  ⟦ E₁[ E₂ := E₃ ]ₑ[ E₄ ]ₑ ⟧(σ, τ) = ⟦ E₁[ E₄ ]ₑ ⟧(σ, τ) := by
  intros h
  normalize
  rw [PrimesMap.set_limited]
  exact h

lemma trace_sub_add_cancel {E : NumericExpression} :
  ⟦ E[ℓ ↦ ℓ ⋆- ♯k][ℓ ↦ ℓ ⋆+ ♯k] ⟧(σ, τ) = ⟦ E ⟧(σ, τ) := by
  induction E with
  | numericLiteral _ => normalize
  | var _ => normalize
  | traceLength => normalize
  | binaryOperation op E₁ E₂ ihE₁ ihE₂ =>
    normalize
    rw [ihE₁, ihE₂]
  | trinaryOperation op E₁ E₂ E₃ ihE₁ ihE₂ ihE₃ =>
    normalize
    rw [ihE₁, ihE₂, ihE₃]

lemma replacement_preserves_does_not_contain_trace_length {E₀ E₁ E₂ : NumericExpression} :
  E₀.containsExpression ℓ = false ->
  E₂.containsExpression ℓ = false ->
  E₀[E₁ ↦ E₂].containsExpression ℓ = false := by
  intros hE₀ hE₂
  induction E₀ with
  | numericLiteral _ =>
    normalize
    split
    . exact hE₂
    . exact hE₀
  | var _ =>
    normalize
    split
    . exact hE₂
    . exact hE₀
  | traceLength => -- contradiction
    simp [containsExpression, predicateHoldsSubtree] at hE₀
  | binaryOperation op E₃ E₄ ihE₃ ihE₄ =>
    simp [containsExpression, replaceNumericExpression]
    split
    . simp [containsExpression] at hE₂
      exact hE₂
    . simp [predicateHoldsSubtree]
      normalize
      simp [containsExpression, predicateHoldsSubtree] at hE₀
      rcases hE₀ with ⟨hE₃, hE₄⟩
      constructor
      . simp [containsExpression] at ihE₃
        apply ihE₃
        exact hE₃
      . simp [containsExpression] at ihE₄
        apply ihE₄
        exact hE₄
  | trinaryOperation op E₃ E₄ E₅ ihE₃ ihE₄ ihE₅ =>
    simp [containsExpression, replaceNumericExpression]
    split
    . simp [containsExpression] at hE₂
      exact hE₂
    . simp [predicateHoldsSubtree]
      normalize
      simp [containsExpression, predicateHoldsSubtree] at hE₀
      rcases hE₀ with ⟨hE₃, hE₄, hE₅⟩
      constructor <;> try constructor
      . simp [containsExpression] at ihE₃
        apply ihE₃
        exact hE₃
      . simp [containsExpression] at ihE₄
        apply ihE₄
        exact hE₄
      . simp [containsExpression] at ihE₅
        apply ihE₅
        exact hE₅

lemma eq_literalize {E : NumericExpression} :
  ⟦ E ⟧(σ, τ) = ⟦ E.literalize σ τ ⟧(σ', τ') := by
  simp [literalize] ; normalize

lemma term_replacement_preserves_logical_variable_absence {E₀ E₁ E₂ : NumericExpression} :
  E₀.containsLogicalVariables = false ->
  E₂.containsLogicalVariables = false ->
  E₀[E₁ ↦ E₂].containsLogicalVariables = false := by
  induction E₀ with
  | numericLiteral n =>
    intros hE₀ hE₂
    normalize
    split
    . exact hE₂
    . exact hE₀
  | var x =>
    intros hE₀ hE₂
    normalize
    split
    . exact hE₂
    . exact hE₀
  | traceLength =>
    intros hE₀ hE₂
    normalize
    split
    . exact hE₂
    . exact hE₀
  | binaryOperation op E₃ E₄ ihE₃ ihE₄ =>
    intros hE₀ hE₂
    simp [containsLogicalVariables, predicateHoldsSubtree] at hE₀
    rcases hE₀ with ⟨_, hE₃, hE₄⟩
    specialize ihE₃ _ hE₂
    . simp [containsLogicalVariables]
      exact hE₃
    specialize ihE₄ _ hE₂
    . simp [containsLogicalVariables]
      exact hE₄
    normalize
    split
    . exact hE₂
    . simp [containsLogicalVariables, predicateHoldsSubtree]
      constructor <;> normalize
      . simp [isLogicalVariable]
      . exact ⟨ihE₃, ihE₄⟩
  | trinaryOperation op E₃ E₄ E₅ ihE₃ ihE₄ ihE₅ =>
    intros hE₀ hE₂
    simp [containsLogicalVariables, predicateHoldsSubtree] at hE₀
    rcases hE₀ with ⟨_, hE₃, hE₄, hE₅⟩
    specialize ihE₃ _ hE₂
    . simp [containsLogicalVariables]
      exact hE₃
    specialize ihE₄ _ hE₂
    . simp [containsLogicalVariables]
      exact hE₄
    specialize ihE₅ _ hE₂
    . simp [containsLogicalVariables]
      exact hE₅
    normalize
    split
    . exact hE₂
    . simp [containsLogicalVariables, predicateHoldsSubtree]
      constructor <;> normalize
      . simp [isLogicalVariable]
      . exact ⟨ihE₃, ihE₄, ihE₅⟩
