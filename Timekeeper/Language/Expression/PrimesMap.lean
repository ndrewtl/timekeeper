import Mathlib.NumberTheory.PrimeCounting

-- TODO rename to map
namespace Timekeeper.PrimesMap

noncomputable def get (arr idx : Nat) : Nat :=
  (arr + 1).factorization (Nat.nth Nat.Prime idx)

noncomputable def unset (arr idx : Nat) : Nat :=
  ((arr + 1) / (Nat.nth Nat.Prime idx) ^ (get arr idx)) - 1

lemma unset_correct : get (unset arr idx) idx = 0 := by
  unfold unset get
  rw [Nat.sub_add_cancel] ; rotate_left
  . apply Nat.div_pos
    . apply Nat.ordProj_le
      simp
    . apply Nat.pow_pos
      apply Nat.zero_lt_of_ne_zero
      apply Nat.Prime.ne_zero
      apply Nat.prime_nth_prime
  rw [Nat.factorization_ordCompl]
  simp

lemma unset_limited : idx₁ ≠ idx₂ -> get (unset arr idx₁) idx₂ = get arr idx₂ := by
  intros hneq
  unfold unset get
  rw [Nat.sub_add_cancel] ; rotate_left
  . apply Nat.div_pos
    . apply Nat.ordProj_le
      simp
    . apply Nat.pow_pos
      apply Nat.zero_lt_of_ne_zero
      apply Nat.Prime.ne_zero
      apply Nat.prime_nth_prime
  rw [Nat.factorization_ordCompl]
  rw [Finsupp.erase_ne]
  -- apply Function.Injective
  have hinj : Function.Injective (Nat.nth Nat.Prime) := by
    apply Nat.nth_injective
    exact Nat.infinite_setOf_prime
  specialize hinj (a₁ := idx₁) (a₂ := idx₂)
  by_contra contr
  symm at contr
  apply hinj at contr
  contradiction

noncomputable def set_add (arr idx val : Nat) : Nat :=
  (arr + 1) * ((Nat.nth Nat.Prime idx) ^ val) - 1

lemma set_add_correct : get (set_add arr idx val) idx = get arr idx + val := by
  unfold set_add get
  rw [Nat.sub_add_cancel] ; rotate_left
  . apply Nat.mul_pos
    . simp
    . apply Nat.pow_pos
      apply Nat.zero_lt_of_ne_zero
      apply Nat.Prime.ne_zero
      apply Nat.prime_nth_prime

  rw [Nat.factorization_mul] ; rotate_left
  . simp
  . apply Nat.ne_zero_of_lt
    apply Nat.pow_pos
    apply Nat.Prime.pos
    apply Nat.prime_nth_prime
  . simp

lemma set_add_correct' : get arr idx = n₁ -> get (set_add arr idx n₂) idx = n₁ + n₂ := by
  intros h
  rw [set_add_correct, h]

lemma set_add_limited : idx₁ ≠ idx₂ -> get (set_add arr idx₁ val) idx₂ = get arr idx₂ := by
  intros hneq
  unfold set_add get
  rw [Nat.sub_add_cancel] ; rotate_left
  . apply Nat.mul_pos
    . simp
    . apply Nat.pow_pos
      apply Nat.zero_lt_of_ne_zero
      apply Nat.Prime.ne_zero
      apply Nat.prime_nth_prime

  rw [Nat.factorization_mul] ; rotate_left
  . simp
  . apply Nat.ne_zero_of_lt
    apply Nat.pow_pos
    apply Nat.Prime.pos
    simp

  simp

  have hinj : Function.Injective (Nat.nth Nat.Prime) := by
    apply Nat.nth_injective
    exact Nat.infinite_setOf_prime
  specialize hinj (a₁ := idx₁) (a₂ := idx₂)
  simp [hneq] at hinj
  rw [Finsupp.single_apply]
  simp [hinj]

noncomputable def set (arr idx val : Nat) : Nat :=
  let arr' := unset arr idx
  set_add arr' idx val

lemma set_correct : get (set arr idx val) idx = val := by
  unfold set
  simp
  rw [set_add_correct, unset_correct]
  simp

lemma set_limited : idx₁ ≠ idx₂ -> get (set arr idx₁ val) idx₂ = get arr idx₂ := by
  intros h
  unfold set
  simp
  rw [set_add_limited h, unset_limited h]

lemma get_zero_is_zero : get 0 idx = 0 := by
  unfold get ; simp
