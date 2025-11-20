import Mathlib.Tactic.Lemma
import Timekeeper.Types
import Timekeeper.Notation.Evaluation
import Timekeeper.Notation.TermReplacement
import Timekeeper.Language.Expression.PrimesMap
import Timekeeper.Language.Semantics.Store

namespace Timekeeper
open Notation
open Variable

inductive BinOp where
  | plus : BinOp
  | minus : BinOp
  | modulo : BinOp
  | index : BinOp
deriving Repr, DecidableEq

inductive TrinOp where
  | arrayAssign : TrinOp
deriving Repr, DecidableEq

inductive NumericExpression where
  | numericLiteral : Nat -> NumericExpression
  | var            : Variable -> NumericExpression
  | traceLength    : NumericExpression
  | binaryOperation : BinOp -> NumericExpression -> NumericExpression -> NumericExpression
  | trinaryOperation : TrinOp -> NumericExpression -> NumericExpression -> NumericExpression -> NumericExpression
deriving Repr, DecidableEq

namespace NumericExpression

prefix:max   "♯" => numericLiteral
notation:399 "⋆$" x:399 => program x
notation:max "⋆⋆$" x:max => var (⋆$ x)
notation:max "⋆^" x:max => logical x
notation:max "⋆⋆^" x:max => var (⋆^ x)
notation:max "ℓ" => traceLength

@[simp]
def add (E₁ E₂ : NumericExpression) : NumericExpression :=
  binaryOperation BinOp.plus E₁ E₂

@[simp]
def sub (E₁ E₂ : NumericExpression) : NumericExpression :=
  binaryOperation BinOp.minus E₁ E₂

@[simp]
def mod (E₁ E₂ : NumericExpression) : NumericExpression :=
  binaryOperation BinOp.modulo E₁ E₂

@[simp]
def index (E₁ E₂ : NumericExpression) : NumericExpression :=
  binaryOperation BinOp.index E₁ E₂

@[simp]
def arrayAssign (E₁ E₂ E₃ : NumericExpression) : NumericExpression :=
  trinaryOperation TrinOp.arrayAssign E₁ E₂ E₃

infixl:390 " ⋆+ " => add
infixl:390 " ⋆- " => sub
infixl:390 " ⋆% " => mod

-- instance : Add NumericExpression where
--   add E₁ E₂ := binaryOperation BinOp.plus E₁ E₂

-- instance : Sub NumericExpression where
--   sub E₁ E₂ := binaryOperation BinOp.minus E₁ E₂

notation:392 E₁:392 "[ " E₂:392 " ]ₑ" => index E₁ E₂
notation:392 E₁:392 "[ " E₂:392 " := " E₃:392 " ]ₑ" => arrayAssign E₁ E₂ E₃

instance : Coe Variable NumericExpression where
  coe id := var id

instance : LawfulBEq NumericExpression where
  rfl := by
    intros a
    simp [BEq.beq]

  eq_of_beq := by
    intros a b hab
    dsimp [BEq.beq] at hab
    simp at hab
    exact hab

noncomputable def evaluate (exp : NumericExpression) (σ : Store) (τ : Trace) : Val :=
  match exp with
  | ♯n => n
  | var id => σ id
  | ℓ  => List.length τ
  | binaryOperation op E₁ E₂ =>
    match op with
    | BinOp.plus => evaluate E₁ σ τ + evaluate E₂ σ τ
    | BinOp.minus => evaluate E₁ σ τ - evaluate E₂ σ τ
    | BinOp.modulo => E₁.evaluate σ τ % E₂.evaluate σ τ
    | BinOp.index =>
      let arr := E₁.evaluate σ τ
      let idx := E₂.evaluate σ τ
      PrimesMap.get arr idx
  | trinaryOperation TrinOp.arrayAssign Earr Eidx Eval =>
    let arr := Earr.evaluate σ τ
    let idx := Eidx.evaluate σ τ
    let val := Eval.evaluate σ τ
    PrimesMap.set arr idx val

noncomputable instance : Evaluation NumericExpression where
  β := Val
  eval := evaluate

instance : LT (Evaluation.β NumericExpression) where
  lt (a : Val) (b : Val) := a < b

instance : LE (Evaluation.β NumericExpression) where
  le (a : Val) (b : Val) := a ≤ b

@[simp]
lemma eval: Evaluation.eval e σ τ = evaluate e σ τ := by
  dsimp [Evaluation.eval]

-- Is the predicate P true for any expression in the subtree of E?
def predicateHoldsSubtree (P : NumericExpression -> Bool) (E : NumericExpression) : Bool :=
  if P E
    then true
    else match E with
    | binaryOperation _ E₁ E₂ => predicateHoldsSubtree P E₁ || predicateHoldsSubtree P E₂
    | trinaryOperation _ E₁ E₂ E₃ => predicateHoldsSubtree P E₁ || (predicateHoldsSubtree P E₂ || predicateHoldsSubtree P E₃)
    | _ => false

def isVariable : NumericExpression -> Bool
| var _ => true
| _ => false

def isLogicalVariable : NumericExpression -> Bool
| var (Variable.logical _) => true
| _ => false

-- Does φ contain ψ?
def containsExpression (haystack needle : NumericExpression) : Bool
  := NumericExpression.predicateHoldsSubtree (BEq.beq needle) haystack

def containsVariables := predicateHoldsSubtree isVariable

def containsLogicalVariables := predicateHoldsSubtree isLogicalVariable

def containsTraceLength (E : NumericExpression) : Bool :=
  E.containsExpression ℓ

def replaceNumericExpression (term : NumericExpression) (oldExpr : NumericExpression) (newExpr : NumericExpression) : NumericExpression :=
  if term == oldExpr
    then newExpr
    else match term with
    | binaryOperation op l r =>
      binaryOperation op (replaceNumericExpression l oldExpr newExpr) (replaceNumericExpression r oldExpr newExpr)
    | trinaryOperation op E₁ E₂ E₃ =>
      trinaryOperation op (E₁.replaceNumericExpression oldExpr newExpr) (E₂.replaceNumericExpression oldExpr newExpr) (E₃.replaceNumericExpression oldExpr newExpr)
    | _ => term

noncomputable def literalize (E : NumericExpression) (σ : Store) (τ : Trace) :=
  ♯(⟦ E ⟧(σ, τ))

instance : TermReplacement NumericExpression NumericExpression where
  γ := NumericExpression
  replace := replaceNumericExpression

instance : TermReplacement NumericExpression Variable where
  γ := NumericExpression
  replace σ x := replaceNumericExpression σ (var x)

@[simp]
lemma numeric_replacement :
  TermReplacement.replace term old new = replaceNumericExpression term old new := by
  dsimp [TermReplacement.replace]

@[simp]
lemma variable_replacement {x : Variable}:
  TermReplacement.replace term x new = replaceNumericExpression term (var x) new := by
  dsimp [TermReplacement.replace]

-- Add some assorted values to be used in a program

-- Represent Boolean True and False
notation:max "FalseVal"            => 0
notation:max "TrueVal"             => 1
-- Represent an empty map
notation:max "⋆{}"                 => ♯0
