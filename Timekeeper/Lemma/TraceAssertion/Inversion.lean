import Timekeeper.Tactics
import Timekeeper.Lemma.NumericExpression
import Timekeeper.Lemma.NumericExpressionList
import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Logic.Evaluation.TraceAssertion

namespace Timekeeper.TraceAssertion.Models

lemma top_inversion :
  ⋆ σ, τ, k ⊧ₜ[ b ] ⋆⊤ₜ ->
  b = true := by
  intros h
  rcases h
  trivial

lemma atomic_inversion_bool {τ : Trace} :
  ⋆ σ, τ, k ⊧ₜ[ b ] ⋆!(Es) ->
  ∃ hkbound : k < τ.length, (τ[k].event == ⟦ Es ⟧(σ, τ)) = b := by
  intros h
  rcases h with (_ | ⟨hkbound, h⟩)
  exists hkbound

lemma atomic_inversion {τ : Trace} :
  ⋆ σ, τ, k ⊧ₜ ⋆!(Es) ->
  ∃ (hkbound : k < τ.length), τ[k].event = ⟦ Es ⟧(σ, τ) := by
  intros h
  apply atomic_inversion_bool at h
  rcases h with ⟨hkbound, h⟩
  simp at h
  exists hkbound

lemma atomic_inversion_bound :
  ⋆ σ, τ, k ⊧ₜ[ b ] ⋆!(Es) ->
  k < τ.length := by
  intros h
  apply atomic_inversion_bool at h
  rcases h with ⟨hkbound, h⟩
  exact hkbound

lemma negation_inversion :
  ⋆ σ, τ, k ⊧ₜ[ b ] ⋆¬T ->
  ⋆ σ, τ, k ⊧ₜ[ !b ] T := by
  intros h
  rcases h with (_ | _ | h)
  exact h

lemma disjunction_inversion :
  ⋆ σ, τ, k ⊧ₜ (T₁ ⋆∨ T₂) ->
  ⋆ σ, τ, k ⊧ₜ T₁ ∨ ⋆ σ, τ, k ⊧ₜ T₂ := by
  intros h
  rcases h with (_ | _ | _ | hT₁ | hT₂)
  . left ; exact hT₁
  . right ; exact hT₂

lemma disjunction_inversion_false :
  ⋆ σ, τ, k ⊧ₜ[ false ] (T₁ ⋆∨ T₂) ->
  ⋆ σ, τ, k ⊧ₜ[ false ] T₁ ∧ ⋆ σ, τ, k ⊧ₜ[ false ] T₂ := by
  intros h
  rcases h with (_ | _ | _ | _ | _ | ⟨hT₁, hT₂⟩)
  exact ⟨hT₁, hT₂⟩

lemma disjunction_inversion_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] (T₁ ⋆∨ T₂) ->
  (b = false ∧
    (⋆ σ, τ, k ⊧ₜ[ false ] T₁ ∧ ⋆ σ, τ, k ⊧ₜ[ false ] T₂)
  ) ∨
  (b = true ∧
    (⋆ σ, τ, k ⊧ₜ T₁ ∨ ⋆ σ, τ, k ⊧ₜ T₂)
  ) := by
  intros h
  rcases b
  . apply disjunction_inversion_false at h
    left
    constructor
    . trivial
    . exact h
  . apply disjunction_inversion at h
    right
    constructor
    . trivial
    . rcases h with (hT₁ | hT₂)
      . left ; exact hT₁
      . right ; exact hT₂

lemma conjunction_inversion :
  ⋆ σ, τ, k ⊧ₜ (T₁ ⋆∧ T₂) ->
  ⋆ σ, τ, k ⊧ₜ T₁ ∧
  ⋆ σ, τ, k ⊧ₜ T₂ := by
  intros h
  apply negation_inversion at h
  apply disjunction_inversion_false at h
  rcases h with ⟨hT₁, hT₂⟩
  apply negation_inversion at hT₁
  apply negation_inversion at hT₂
  constructor
  . exact hT₁
  . exact hT₂

lemma conjunction_inversion_false :
  ⋆ σ, τ, k ⊧ₜ[ false ] T₁ ⋆∧ T₂ ->
  ⋆ σ, τ, k ⊧ₜ[ false ] T₁ ∨
  ⋆ σ, τ, k ⊧ₜ[ false ] T₂ := by
  intros h
  apply negation_inversion at h
  apply disjunction_inversion at h
  rcases h with (hT₁ | hT₂)
  . apply negation_inversion at hT₁
    left ; exact hT₁
  . apply negation_inversion at hT₂
    right ; exact hT₂

lemma conjunction_inversion_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] (T₁ ⋆∧ T₂) ->
  (b = false ∧
    (⋆ σ, τ, k ⊧ₜ[ false ] T₁ ∨ ⋆ σ, τ, k ⊧ₜ[ false ] T₂)
  ) ∨
  (b = true ∧
    (⋆ σ, τ, k ⊧ₜ T₁ ∧ ⋆ σ, τ, k ⊧ₜ T₂)
  ) := by
  intros h
  rcases b
  . left
    constructor
    . trivial
    exact conjunction_inversion_false h
  . right
    constructor
    . trivial
    exact conjunction_inversion h

lemma previous_inversion_zero_bool :
  ⋆ σ, τ, 0 ⊧ₜ[ b ] ●T ->
  b = false := by
  intros h
  rcases h
  trivial

lemma previous_inversion_succ_bool :
  ⋆ σ, τ, (k + 1) ⊧ₜ[ b ] ●T ->
  ⋆ σ, τ, k ⊧ₜ[ b ] T := by
  intros h
  rcases h with (_ | _ | _ | _ | _ | _ | _ | h)
  exact h

lemma previous_inversion_succ :
  ⋆ σ, τ, (k + 1) ⊧ₜ ●T ->
  ⋆ σ, τ, k ⊧ₜ T := by
  intros h
  apply previous_inversion_succ_bool at h
  exact h

lemma previous_inversion_zero :
  ⋆ σ, τ, 0 ⊧ₜ ●T -> False := by
  intros h
  apply previous_inversion_zero_bool at h
  contradiction

lemma previous_inversion_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] ●T ->
  (k = 0 ∧ b = false) ∨ ∃ k', k = k' + 1 ∧ ⋆ σ, τ, k' ⊧ₜ[ b ] T := by
  intros h
  rcases k with (_ | k')
  . left
    constructor
    . trivial
    . exact previous_inversion_zero_bool h
  . right
    apply previous_inversion_succ_bool at h
    exists k'

lemma previous_inversion :
  ⋆ σ, τ, k ⊧ₜ ●T ->
  ∃ k', k = k' + 1 ∧ ⋆ σ, τ, k' ⊧ₜ T := by
  intros h
  apply previous_inversion_bool at h
  rcases h with (⟨rfl, contr⟩ | ⟨k', rfl, h⟩)
  . contradiction
  . exists k'

lemma next_inversion_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] ◯T ->
  ⋆ σ, τ, (k + 1) ⊧ₜ[ b ] T := by
  intros h
  rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | h)
  exact h

lemma next_inversion :
  ⋆ σ, τ, k ⊧ₜ ◯T ->
  ⋆ σ, τ, (k + 1) ⊧ₜ T := by
  intros h
  apply next_inversion_bool at h
  exact h

lemma since_inversion_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] φ ⋆S ψ ->
  ⋆ σ, τ, k ⊧ₜ[ b ] (ψ ⋆∨ (φ ⋆∧ ●(φ ⋆S ψ))) := by
  intros h
  rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | h)
  exact h

lemma since_inversion :
  ⋆ σ, τ, k ⊧ₜ φ ⋆S ψ ->
  ⋆ σ, τ, k ⊧ₜ (ψ ⋆∨ (φ ⋆∧ ●(φ ⋆S ψ))) := by
  intros h
  apply since_inversion_bool at h
  exact h

lemma until_inversion_zero_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] φ ⋆U( 0 ) ψ ->
  ⋆ σ, τ, k ⊧ₜ[ b ] ψ := by
  intros h
  rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | h)
  exact h

lemma until_inversion_succ_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] φ ⋆U( n' + 1 ) ψ ->
  ⋆ σ, τ, k ⊧ₜ[ b ] (ψ ⋆∨ (φ ⋆∧ ◯(φ ⋆U( n' ) ψ))) := by
  intros h
  rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | h)
  exact h

lemma until_inversion_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] φ ⋆U( n ) ψ ->
  n = 0 ∧ ⋆ σ, τ, k ⊧ₜ[ b ] ψ ∨
  ∃ n', n = n' + 1 ∧ ⋆ σ, τ, k ⊧ₜ[ b ] ψ ⋆∨ φ ⋆∧ ◯(φ ⋆U( n' ) ψ) := by
  intros h
  rcases n with (_ | n')
  . left
    apply until_inversion_zero_bool at h
    constructor
    . trivial
    . exact h
  . apply until_inversion_succ_bool at h
    right
    exists n'

lemma until_inversion :
  ⋆ σ, τ, k ⊧ₜ φ ⋆U( n ) ψ ->
  n = 0 ∧ ⋆ σ, τ, k ⊧ₜ ψ ∨
  ∃ n', n = n' + 1 ∧ (⋆ σ, τ, k ⊧ₜ ψ ∨ ⋆ σ, τ, k ⊧ₜ φ ∧ ⋆ σ, τ, k ⊧ₜ ◯(φ ⋆U( n' ) ψ)) := by
  intros h
  apply until_inversion_bool at h
  rcases h with (⟨rfl, hψ⟩ | ⟨n', rfl, hψφφUψ⟩)
  . left ; exact ⟨rfl, hψ⟩
  . right
    exists n'
    constructor
    . trivial
    apply disjunction_inversion at hψφφUψ
    rcases hψφφUψ with (hψ | hφφUψ)
    . left ; exact hψ
    . right
      apply conjunction_inversion at hφφUψ
      rcases hφφUψ with ⟨hφ, hφUψ⟩
      constructor
      . exact hφ
      . exact hφUψ

lemma until_inversion_zero :
  ⋆ σ, τ, k ⊧ₜ φ ⋆U( 0 ) ψ ->
  ⋆ σ, τ, k ⊧ₜ ψ := by
  intros h
  apply until_inversion_zero_bool at h
  exact h

lemma until_inversion_succ :
  ⋆ σ, τ, k ⊧ₜ φ ⋆U( n' + 1 ) ψ ->
  ⋆ σ, τ, k ⊧ₜ (ψ ⋆∨ (φ ⋆∧ ◯(φ ⋆U( n' ) ψ))) := by
  intros h
  apply until_inversion_succ_bool at h
  exact h

lemma function_inversion_bool :
  ⋆ σ, τ, k ⊧ₜ[ b ] F⋆(Es) ->
  ⋆ σ, τ, k ⊧ₜ[ b ] F (⟦ Es ⟧(σ, τ)) := by
  intros h
  rcases h with (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | h)
  exact h

lemma function_inversion :
  ⋆ σ, τ, k ⊧ₜ F⋆(Es) ->
  ⋆ σ, τ, k ⊧ₜ F (⟦ Es ⟧(σ, τ)) := by
  intros h
  exact function_inversion_bool h

lemma universal_quantification_inversion :
  ⋆ σ, τ, k ⊧ₜ[ b ] ⋆∀ₜ x : T ->
  ∀ v', ⋆ σ[⋆^x ↦ v'], τ, k ⊧ₜ[ b ] T := by
  intros h
  rcases h with (_|_|_|_|_|_|_|_|_|_|_|_|_|h)
  intros v'
  exact h v'

lemma eventually_inversion :
  ⋆ σ, τ, k ⊧ₜ ✧( n ) T ->
  ∃ k', k ≤ k' ∧ k' ≤ k + n ∧ ⋆ σ, τ, k' ⊧ₜ T := by
  revert k
  induction n with
  | zero =>
    intros k hT
    exists k
    constructor
    . exact Nat.le_refl k
    . constructor
      . exact Nat.le_add_right k 0
      . apply until_inversion_zero at hT
        exact hT
  | succ n' ihn' =>
    intros k hT
    rw [eventually] at hT
    apply until_inversion at hT
    rcases hT with (contr | hT)
    . rcases contr with (contr | _)

    rcases hT with ⟨n'', hn''eqn', (hT | ⟨htop, hT⟩)⟩
    . exists k
      constructor
      . trivial
      . constructor
        . exact Nat.le_add_right k (n' + 1)
        . exact hT
    . clear htop
      apply next_inversion at hT
      rw [<-eventually] at hT
      simp at hn''eqn'
      rw [<-hn''eqn'] at hT
      specialize ihn' (k := k + 1) hT
      rcases ihn' with ⟨k', hkk', hk'k, hT⟩
      exists k'
      constructor
      . exact Nat.le_of_succ_le hkk'
      . constructor
        . rw [<-Nat.add_assoc]
          rw [Nat.add_assoc] at hk'k
          conv_rhs at hk'k =>
            congr
            . skip
            . rw [Nat.add_comm]
          rw [<-Nat.add_assoc] at hk'k
          exact hk'k
        . exact hT
