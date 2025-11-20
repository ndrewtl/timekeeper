import Mathlib.Tactic.Lemma
import Timekeeper.Types
import Timekeeper.Notation.TermReplacement

namespace Store
open Timekeeper
open Timekeeper.Notation

def update : Store -> Variable -> Val -> Store
| σ, x, v =>
    fun x' => if x' == x then v else σ x'

instance : TermReplacement Store Variable where
  γ := Val
  replace := update

@[simp]
lemma replacement {v : Val} : TermReplacement.replace (σ : Store) x v = update σ x v := by
  dsimp [TermReplacement.replace]
