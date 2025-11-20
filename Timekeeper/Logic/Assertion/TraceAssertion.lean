import Timekeeper.Language.Expression.NumericExpression
import Timekeeper.Language.Expression.NumericExpressionList
import Timekeeper.Notation.Logic
import Timekeeper.Notation.TermReplacement

namespace Timekeeper
open Notation

inductive TraceAssertion where
  | top : TraceAssertion
  | atomic : NumericExpressionList -> TraceAssertion
  | negation : TraceAssertion -> TraceAssertion
  | disjunction : TraceAssertion -> TraceAssertion -> TraceAssertion
  | previous : TraceAssertion -> TraceAssertion
  | next : TraceAssertion -> TraceAssertion
  | since : TraceAssertion -> TraceAssertion -> TraceAssertion
  | until : TraceAssertion -> TraceAssertion -> Nat -> TraceAssertion
  | function : (Event -> TraceAssertion) -> NumericExpressionList -> TraceAssertion
  | universal_quantification : VariableName -> TraceAssertion -> TraceAssertion

namespace TraceAssertion

instance : Negation TraceAssertion where
  not := negation

@[simp]
lemma negation_trace_assertion : Negation.not φ = TraceAssertion.negation φ := by
  dsimp [Negation.not]

instance : Disjunction TraceAssertion where
  or := TraceAssertion.disjunction

@[simp]
lemma disjunction_trace_assertion : Disjunction.or φ ψ = TraceAssertion.disjunction φ ψ := by
  dsimp [Disjunction.or]

instance : Conjunction TraceAssertion where
  and φ ψ := ⋆¬(⋆¬φ ⋆∨ ⋆¬ψ)

@[simp]
lemma conjunction_trace_assertion : Conjunction.and (φ : TraceAssertion) ψ = ⋆¬(⋆¬φ ⋆∨ ⋆¬ψ) := by
  dsimp [Conjunction.and]

instance : Implication TraceAssertion where
  implies T₁ T₂ := ⋆¬T₁ ⋆∨ T₂

@[simp]
lemma implication_trace_assertion {T₁ T₂ : TraceAssertion} : Implication.implies T₁ T₂ = ⋆¬T₁ ⋆∨ T₂ := by
  dsimp [Implication.implies]

prefix:max "⋆!" => atomic
prefix:max "●" => previous -- ci
prefix:max "◯" => next -- ciO
notation:311 φ:312 " ⋆U( " n " ) " ψ:312 => «until» φ ψ n
infixl:310 " ⋆S " => since
notation:315 F:316 "⋆( " Es:317 " )" => function F Es
notation:317 "⋆∀ₜ " x:317 " : " T:317 => universal_quantification x T
notation:max "⋆⊤ₜ" => top
def bot := ⋆¬⋆⊤ₜ
notation:max "⋆⊥ₜ" => bot

-- Eventually, within n steps
@[simp]
def eventually (T' : TraceAssertion) (n : Nat) : TraceAssertion :=
  ⋆⊤ₜ ⋆U( n ) T'

-- \ lozenge
notation:310 "✧( " n:310 " ) " T':310 => eventually T' n

@[simp]
def once (T' : TraceAssertion) : TraceAssertion :=
  ⋆⊤ₜ ⋆S T'

-- \ blacklozenge
notation:310 "✦ " T':310 => once T'

@[simp]
def pastAlways (T' : TraceAssertion) : TraceAssertion :=
  T' ⋆S ⋆⊥ₜ

notation:310 "▪ " T':310 => pastAlways T'

def numericExpressionPredicate (P : NumericExpression -> Bool) (T : TraceAssertion) : Prop :=
  match T with
  | top => false
  | atomic Es => Es.numericExpressionPredicate P
  | negation T' => T'.numericExpressionPredicate P
  | disjunction φ ψ => φ.numericExpressionPredicate P ∨ ψ.numericExpressionPredicate P
  | previous T' => T'.numericExpressionPredicate P
  | next T' => T'.numericExpressionPredicate P
  | since φ ψ => φ.numericExpressionPredicate P ∨ ψ.numericExpressionPredicate P
  | «until» φ ψ _ => φ.numericExpressionPredicate P ∨ ψ.numericExpressionPredicate P
  | function F Es => Es.numericExpressionPredicate P ∨ ∃ σ τ, (F (⟦ Es ⟧(σ, τ))).numericExpressionPredicate P
  | universal_quantification _ T' => T'.numericExpressionPredicate P

def replaceNumericExpression : TraceAssertion -> NumericExpression -> NumericExpression -> TraceAssertion
  | assertion, oldExpr, newExpr =>
    match assertion with
    | top => ⋆⊤ₜ
    | atomic Es => TraceAssertion.atomic $ Es[oldExpr ↦ newExpr]
    | negation φ => ⋆¬(φ.replaceNumericExpression oldExpr newExpr)
    | disjunction φ ψ => (φ.replaceNumericExpression oldExpr newExpr) ⋆∨ (ψ.replaceNumericExpression oldExpr newExpr)
    | previous φ => ●(φ.replaceNumericExpression oldExpr newExpr)
    | next φ => ◯(φ.replaceNumericExpression oldExpr newExpr)
    | since φ ψ => φ.replaceNumericExpression oldExpr newExpr ⋆S ψ.replaceNumericExpression oldExpr newExpr
    | «until» φ ψ n => φ.replaceNumericExpression oldExpr newExpr ⋆U( n ) ψ.replaceNumericExpression oldExpr newExpr
    | function F Es => function (fun event => (F event).replaceNumericExpression oldExpr newExpr) (Es.replaceNumericExpression oldExpr newExpr)
    | universal_quantification x T => ⋆∀ₜ x : T.replaceNumericExpression oldExpr newExpr

noncomputable def literalize (T : TraceAssertion) (σ : Store) (τ : Trace) : TraceAssertion :=
  match T with
  | .top => ⋆⊤ₜ
  | .atomic Es => ⋆!(Es.literalize σ τ)
  | .negation T' => ⋆¬(T'.literalize σ τ)
  | .disjunction T₁ T₂ => (T₁.literalize σ τ) ⋆∨ (T₂.literalize σ τ)
  | .previous T' => ●(T'.literalize σ τ)
  | .next T' => ◯(T'.literalize σ τ)
  | .since T₁ T₂ => T₁.literalize σ τ ⋆S T₂.literalize σ τ
  | .until T₁ T₂ n => T₁.literalize σ τ ⋆U( n ) T₂.literalize σ τ
  | .function F Es => (fun ev => (F ev).literalize σ τ) ⋆( Es.literalize σ τ )
  | .universal_quantification x T' => ⋆∀ₜ x : T'.literalize σ τ

instance : TermReplacement TraceAssertion NumericExpression where
  γ := NumericExpression
  replace := replaceNumericExpression

instance : TermReplacement TraceAssertion Variable where
  γ := NumericExpression
  replace σ x := replaceNumericExpression σ (NumericExpression.var x)

@[simp]
lemma numeric_replacement :
  TermReplacement.replace T old new = replaceNumericExpression T old new := by
  dsimp [TermReplacement.replace]

@[simp]
lemma variable_replacement :
  TermReplacement.replace T x new = replaceNumericExpression T (NumericExpression.var x) new :=
  by dsimp [TermReplacement.replace]

def containsNumericExpression : TraceAssertion -> NumericExpression -> Prop
  | top, _ => False
  | atomic Es, term =>
    Es.containsExpression term
  | negation φ, term =>
    containsNumericExpression φ term
  | disjunction φ ψ, term =>
    containsNumericExpression φ term ∨ containsNumericExpression ψ term
  | previous φ, term =>
    containsNumericExpression φ term
  | next φ, term =>
    containsNumericExpression φ term
  | since φ ψ, term =>
    containsNumericExpression φ term ∨ containsNumericExpression ψ term
  | «until» φ ψ _, term =>
    containsNumericExpression φ term ∨ containsNumericExpression ψ term
  | function F Es, term => (∃ ev, (F ev).containsNumericExpression term) ∨ Es.containsExpression term
  | universal_quantification _ T', term => T'.containsNumericExpression term

def wellFormed (T : TraceAssertion) : Prop :=
  match T with
  | top => True
  | atomic Es =>
    ¬Es.containsExpression ℓ
  | negation T' => T'.wellFormed
  | disjunction T₁ T₂ => T₁.wellFormed ∧ T₂.wellFormed
  | previous T' => T'.wellFormed
  | next T' => T'.wellFormed
  | since T₁ T₂ => T₁.wellFormed ∧ T₂.wellFormed
  | «until» T₁ T₂ _ => T₁.wellFormed ∧ T₂.wellFormed
  | function F Es =>
    (∀ event, (F event).wellFormed) ∧ ¬Es.containsExpression ℓ
  | universal_quantification _ T => wellFormed T

def containsVariables (T : TraceAssertion) : Prop :=
  T.numericExpressionPredicate NumericExpression.isVariable
