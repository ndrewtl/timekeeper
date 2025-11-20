import Timekeeper.Lemma.GeneralAssertion

namespace Timekeeper.Evaluation.Main
open TraceAssertion
open TraceAssertion.Models

lemma not_event_since_event_implies_nonzero_trace :
  ⋆ σ, τ, τ.length - 1 ⊧ₜ[ true ] ⋆¬⋆!Ev₁ ⋆S ⋆!Ev₂ ->
  0 < τ.length := by
  intros h
  apply since_inversion at h
  apply disjunction_inversion at h
  rcases h with (hEv₂ | hsince)
  . apply atomic_inversion_bound at hEv₂
    exact Nat.zero_lt_of_lt hEv₂
  induction τ with
  | nil =>
    apply conjunction_inversion at hsince
    rcases hsince with ⟨_, hcontr⟩
    apply previous_inversion_zero at hcontr
    contradiction
  | cons head tail ih =>
    normalize
