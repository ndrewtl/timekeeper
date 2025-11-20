import Timekeeper.Logic.Evaluation.GeneralAssertion
import Timekeeper.Lemma.GeneralAssertion.Syntax
import Timekeeper.Lemma.GeneralAssertion.Constants

namespace Timekeeper.GeneralAssertion

lemma present_implies_top : A ⋆-> ⋆⊤ := by
  intros σ τ h
  exact top_valid

lemma future_implies_top : A ⋆->> ⋆⊤ := by
  intros σ τ τext h
  rw [nonexistent_term_replacement] ; rotate_left
  . auto_contains
  exact top_valid
