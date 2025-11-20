import Timekeeper.Lemma.GeneralAssertion.Introduction

namespace Timekeeper.GeneralAssertion
open Models

lemma top_well_formed : (⋆⊤).wellFormed := by
  simp [top, GeneralAssertion.wellFormed]

lemma bot_well_formed : (⋆⊥).wellFormed := by
  simp [bot, top, GeneralAssertion.wellFormed]

lemma top_valid : ⋆ σ, τ ⊧ ⋆⊤ := by
  apply expression_intro
  simp [BooleanExpression.evaluate]

lemma bot_invalid : ⋆ σ, τ ⊧ ⋆¬ (⋆⊥) := by
  apply negation_intro
  apply negation_intro
  apply expression_intro
  simp [BooleanExpression.evaluate]
