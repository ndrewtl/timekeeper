import Timekeeper.Lemma.GeneralAssertion
import Timekeeper.Evaluation.Main.Invariants
import Timekeeper.Evaluation.Main.Lemma.Temporal

namespace Timekeeper.Evaluation.Main
open GeneralAssertion.Models

lemma reestablish_consent_invariant_trace_extension :
  ⋆ σ, τ ⊧ consent_invariant[ℓ ↦ ℓ ⋆- ♯1] ->
  ⋆ σ, τ, τ.length - 1 ⊧ₜ ⋆!Es -> -- ??
  (∀ id purpose, ⟦ Es ⟧(σ, τ) ≠ [Revoke, id, purpose]) ->
  ⋆ σ, τ ⊧ consent_invariant := by
  rw [consent_invariant]
  intros hconsentinv hevent hnotrevoke

  apply universal_quantification_intro
  intros vuid
  apply universal_quantification_intro
  intros vpurpose

  apply universal_quantification_inversion at hconsentinv
  specialize hconsentinv vuid
  apply universal_quantification_inversion at hconsentinv
  specialize hconsentinv vpurpose

  apply implication_intro
  . apply expression_intro
    normalize

  apply implication_inversion at hconsentinv
  intros hconsentdbset
  specialize hconsentinv hconsentdbset

  apply trace_intro
  apply trace_inversion at hconsentinv

  apply TraceAssertion.Models.since_intro
  apply TraceAssertion.Models.since_inversion at hconsentinv
  normalize at hconsentinv


  apply TraceAssertion.Models.atomic_inversion at hevent
  rcases hevent with ⟨hkbound, hevent⟩

  by_cases hτlen : τ.length = 1
  . rw [hτlen] at hconsentinv
    have h0m1 : 0 - 1 = 0 := by exact rfl
    rw [h0m1] at hconsentinv
    normalize
    rw [hτlen]
    normalize
    exact hconsentinv
  . have hτlen : τ.length - 1 ≠ 0 := by grind
    apply Nat.exists_eq_succ_of_ne_zero at hτlen
    rcases hτlen with ⟨τlenm1, hτlen⟩
    apply TraceAssertion.Models.disjunction_intro_right
    apply TraceAssertion.Models.conjunction_intro
    . apply TraceAssertion.Models.negation_intro
      apply TraceAssertion.Models.atomic_intro
      . normalize
        rw [hevent]
        normalize
        simp [Store.update]
        normalize
        specialize hnotrevoke vuid vpurpose
        exact hnotrevoke
      . normalize
        exact Nat.zero_lt_of_lt hkbound
    . normalize
      rw [hτlen]
      apply TraceAssertion.Models.previous_intro_succ
      apply TraceAssertion.Models.since_intro
      simp_rw [hτlen] at hevent
      rw [hτlen] at hconsentinv
      rw [<-Nat.add_one] at hconsentinv
      rw [Nat.add_sub_cancel] at hconsentinv
      exact hconsentinv

lemma reestablish_consent_invariant_trace_extension_revoke :
  ⋆ σ, τ ⊧ consent_invariant[ℓ ↦ ℓ ⋆- ♯1] ->
  ⋆ σ, τ, τ.length - 1 ⊧ₜ ⋆![♯Revoke, E₁, E₂] -> -- ??
  ⋆ σ, τ ⊧ (⋆$"consent_db")[ E₁ ]ₑ[ E₂ ]ₑ ⋆= ♯0 ->
  ⋆ σ, τ ⊧ consent_invariant := by
  rw [consent_invariant]
  intros hconsentinv hevent hconsentdb

  apply universal_quantification_intro
  intros vuid
  apply universal_quantification_intro
  intros vpurpose

  apply universal_quantification_inversion at hconsentinv
  specialize hconsentinv vuid
  apply universal_quantification_inversion at hconsentinv
  specialize hconsentinv vpurpose
  normalize at hconsentinv

  by_cases hE₁E₂ : ⟦ E₁ ⟧(σ, τ) = vuid ∧ ⟦ E₂ ⟧(σ, τ) = vpurpose
  . rcases hE₁E₂ with ⟨hE₁, hE₂⟩
    apply disjunction_intro_left
    apply negation_intro
    normalize
    apply expression_intro
    rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]
    normalize
    simp [Store.update]

    apply expression_inversion at hconsentdb
    rw [BooleanExpression.eq_correct] at hconsentdb
    normalize at hconsentdb
    rw [hE₁, hE₂] at hconsentdb
    rw [hconsentdb]
    simp
  . apply implication_intro
    . apply expression_intro
      normalize

    apply implication_inversion at hconsentinv
    intros hconsentdbset
    specialize hconsentinv hconsentdbset

    apply trace_intro
    apply trace_inversion at hconsentinv

    apply TraceAssertion.Models.since_intro
    apply TraceAssertion.Models.since_inversion at hconsentinv
    normalize at hconsentinv

    apply TraceAssertion.Models.atomic_inversion at hevent
    rcases hevent with ⟨hkbound, hevent⟩

    by_cases hτlen : τ.length = 1
    . rw [hτlen] at hconsentinv
      have h0m1 : 0 - 1 = 0 := by exact rfl
      rw [h0m1] at hconsentinv
      normalize
      rw [hτlen]
      normalize
      exact hconsentinv
    . have hτlen : τ.length - 1 ≠ 0 := by grind
      apply Nat.exists_eq_succ_of_ne_zero at hτlen
      rcases hτlen with ⟨τlenm1, hτlen⟩
      apply TraceAssertion.Models.disjunction_intro_right
      apply TraceAssertion.Models.conjunction_intro
      . apply TraceAssertion.Models.negation_intro
        apply TraceAssertion.Models.atomic_intro
        . normalize
          rw [hevent]
          normalize
          simp [Store.update]
          normalize at hE₁E₂
          exact fun a => hE₁E₂ a
        . normalize
          exact Nat.zero_lt_of_lt hkbound
      . normalize
        rw [hτlen]
        apply TraceAssertion.Models.previous_intro_succ
        apply TraceAssertion.Models.since_intro
        simp_rw [hτlen] at hevent
        rw [hτlen] at hconsentinv
        rw [<-Nat.add_one] at hconsentinv
        rw [Nat.add_sub_cancel] at hconsentinv
        exact hconsentinv

lemma consent_invariant_implies_consent_invariant_decrement_trace_length :
  ⋆ σ, τ ⊧ consent_invariant ->
  ⋆ σ, τ ⊧ ⋆!Es ⋆@ ℓ ⋆- ♯1 ->
  (∀ uid purpose, [Consent, uid, purpose] ≠ ⟦ Es ⟧(σ, τ)) ->
  ⋆ σ, τ ⊧ consent_invariant[ℓ ↦ ℓ ⋆- ♯1] := by
  intros hconsentinv hevent hnotconsent
  rw [consent_invariant] at hconsentinv
  rw [consent_invariant]

  normalize at hconsentinv
  normalize

  apply universal_quantification_intro
  intros vid
  apply universal_quantification_intro
  intros vpurpose

  apply universal_quantification_inversion at hconsentinv
  specialize hconsentinv vid
  apply universal_quantification_inversion at hconsentinv
  specialize hconsentinv vpurpose

  apply implication_intro
  . apply expression_intro
    normalize

  intros hconsentset

  apply implication_inversion at hconsentinv
  specialize hconsentinv hconsentset

  apply trace_inversion at hconsentinv
  normalize at hconsentinv

  have τlenpos : 0 < τ.length := by
    apply not_event_since_event_implies_nonzero_trace
    exact hconsentinv

  apply trace_intro
  normalize
  by_cases hτlen : τ.length = 1
  . -- This branch should be a contradiction
    rw [hτlen]
    normalize
    rw [hτlen] at hconsentinv
    normalize at hconsentinv
    exact hconsentinv
  . have hτlen : τ.length - 1 ≠ 0 := by grind
    apply Nat.exists_eq_succ_of_ne_zero at hτlen
    rcases hτlen with ⟨τlenm1, hτlen⟩
    rw [hτlen]
    rw [<-Nat.add_one, Nat.add_sub_cancel]
    rw [hτlen] at hconsentinv
    apply TraceAssertion.Models.since_inversion at hconsentinv
    apply TraceAssertion.Models.disjunction_inversion at hconsentinv
    rcases hconsentinv with (contr | hconsentinv)
    . -- This case is a contradiction
      apply TraceAssertion.Models.atomic_inversion at contr
      rcases contr with ⟨hkbound', hcontr⟩
      apply trace_inversion at hevent
      apply TraceAssertion.Models.atomic_inversion at hevent
      rcases hevent with ⟨hkbound'', hevent⟩
      normalize at hevent
      simp_rw [hτlen] at hevent
      rw [hevent] at hcontr
      normalize at hcontr
      simp [Store.update] at hcontr
      specialize hnotconsent vid vpurpose
      rw [<-hcontr] at hnotconsent
      contradiction
    apply TraceAssertion.Models.conjunction_inversion at hconsentinv
    rcases hconsentinv with ⟨hevent', hconsentinv⟩
    apply TraceAssertion.Models.previous_inversion at hconsentinv
    rcases hconsentinv with ⟨k', hk', hconsentinv⟩
    simp at hk'
    rw [<-hk'] at hconsentinv
    exact hconsentinv

lemma request_deletion_invariant₁_implies_request_deletion_invariant₁_increment_k :
  ⋆ σ, τ ⊧ request_deletion_invariant₁ ->
  ⋆ σ, τ ⊧ request_deletion_invariant₁[⋆$"k" ↦ ⋆⋆$"k" ⋆+ ♯1] := by
  rw [request_deletion_invariant₁]
  intros h

  apply universal_quantification_intro
  intros vidx

  normalize
  normalize at h

  apply universal_quantification_inversion at h
  specialize h vidx

  apply conjunction_inversion at h
  rcases h with ⟨hleft, hright⟩

  apply conjunction_intro
  . apply implication_intro
    . exact expression_intro rfl

    intros hltk

    by_cases hkvidx : σ (⋆$"k") = vidx
    . apply disjunction_intro_left
      apply negation_intro
      apply expression_intro
      conv_rhs => simp
      rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]

      apply implication_inversion at hright
      specialize hright _
      . apply expression_intro
        rw [BooleanExpression.le_correct]
        normalize
        simp [Store.update]
        apply Nat.le_of_eq
        exact hkvidx

      apply expression_inversion at hright
      rw [BooleanExpression.eq_correct] at hright
      normalize at hright
      simp [Store.update] at hright

      normalize
      simp [Store.update]
      rw [hright]
      rw [PrimesMap.get_zero_is_zero]
      simp
    . apply implication_inversion at hleft
      specialize hleft _
      . apply expression_intro
        rw [BooleanExpression.lt_correct]
        normalize
        simp [Store.update]
        apply expression_inversion at hltk
        rw [BooleanExpression.lt_correct] at hltk
        normalize at hltk
        simp [Store.update] at hltk
        apply Nat.lt_of_le_of_ne
        . apply Nat.le_of_lt_succ
          exact hltk
        . exact fun a => hkvidx (id (Eq.symm a))

      apply implication_intro
      . exact expression_intro rfl
      intros hdelreqset

      apply implication_inversion at hleft
      specialize hleft hdelreqset
      apply conjunction_inversion at hleft
      rcases hleft with ⟨hleft, hright⟩

      apply conjunction_intro <;> apply expression_intro
      . rw [BooleanExpression.le_correct]
        normalize
        simp [Store.update]
        apply expression_inversion at hleft
        rw [BooleanExpression.le_correct] at hleft
        normalize at hleft
        simp [Store.update] at hleft

        apply le_of_eq_of_le (b := List.length τ - 1 - (σ (⋆$"k") - vidx))
        . rw [Nat.sub_add_comm] ; rotate_left
          . apply expression_inversion at hltk
            rw [BooleanExpression.lt_correct] at hltk
            normalize at hltk
            simp [Store.update] at hltk
            apply Nat.le_of_lt_succ
            exact hltk
          ring_nf
          rw [Nat.sub_add_eq]
        . apply Nat.le_trans (m := List.length τ - (σ (⋆$"k") - vidx))
          . rw [Nat.sub_right_comm]
            simp
          . exact hleft
      . rw [BooleanExpression.lt_correct]
        normalize
        simp [Store.update]
        apply expression_inversion at hright
        rw [BooleanExpression.lt_correct] at hright
        normalize at hright
        simp [Store.update] at hright
        exact hright

-- just prove the key steps in lean
  . apply implication_intro
    . exact expression_intro rfl
    intros hkleidx
    apply implication_inversion at hright
    specialize hright _
    . apply expression_intro
      rw [BooleanExpression.le_correct]
      apply expression_inversion at hkleidx
      rw [BooleanExpression.le_correct] at hkleidx
      normalize at hkleidx
      normalize
      apply Nat.le_trans (m := (σ[⋆^"idx" ↦ vidx]) (⋆$"k") + 1)
      . apply Nat.le_add_right
      . exact hkleidx
    exact hright

lemma request_deletion_invariant₁_decrement_trace_length_implies_request_deletion_invariant₁_increment_k :
  ⋆ σ, τ ⊧ request_deletion_invariant₁[ℓ ↦ ℓ ⋆- ♯1] ->
  ⋆ σ, τ ⊧ request_deletion_invariant₁[⋆$"k" ↦ ⋆⋆$"k" ⋆+ ♯1] := by
  rw [request_deletion_invariant₁]
  intros h

  apply universal_quantification_intro
  intros vidx

  normalize
  normalize at h

  apply universal_quantification_inversion at h
  specialize h vidx

  apply conjunction_inversion at h
  rcases h with ⟨hleft, hright⟩

  apply conjunction_intro
  . apply implication_intro
    . exact expression_intro rfl

    intros hltk

    by_cases hkvidx : σ (⋆$"k") = vidx
    . apply disjunction_intro_left
      apply negation_intro
      apply expression_intro
      conv_rhs => simp
      rw [BooleanExpression.eq_false_iff, BooleanExpression.ne_correct]

      apply implication_inversion at hright
      specialize hright _
      . apply expression_intro
        rw [BooleanExpression.le_correct]
        normalize
        simp [Store.update]
        apply Nat.le_of_eq
        exact hkvidx

      apply expression_inversion at hright
      rw [BooleanExpression.eq_correct] at hright
      normalize at hright
      simp [Store.update] at hright

      normalize
      simp [Store.update]
      rw [hright]
      rw [PrimesMap.get_zero_is_zero]
      simp
    . apply implication_inversion at hleft
      specialize hleft _
      . apply expression_intro
        rw [BooleanExpression.lt_correct]
        normalize
        simp [Store.update]
        apply expression_inversion at hltk
        rw [BooleanExpression.lt_correct] at hltk
        normalize at hltk
        simp [Store.update] at hltk
        apply Nat.lt_of_le_of_ne
        . apply Nat.le_of_lt_succ
          exact hltk
        . exact fun a => hkvidx (id (Eq.symm a))

      apply implication_intro
      . exact expression_intro rfl
      intros hdelreqset

      apply implication_inversion at hleft
      specialize hleft hdelreqset
      apply conjunction_inversion at hleft
      rcases hleft with ⟨hleft, hright⟩

      apply conjunction_intro <;> apply expression_intro
      . rw [BooleanExpression.le_correct]
        normalize
        simp [Store.update]
        apply expression_inversion at hleft
        rw [BooleanExpression.le_correct] at hleft
        normalize at hleft
        simp [Store.update] at hleft

        apply le_of_eq_of_le (b := List.length τ - 1 - (σ (⋆$"k") - vidx))
        . rw [Nat.sub_add_comm] ; rotate_left
          . apply expression_inversion at hltk
            rw [BooleanExpression.lt_correct] at hltk
            normalize at hltk
            simp [Store.update] at hltk
            apply Nat.le_of_lt_succ
            exact hltk
          ring_nf
          rw [Nat.sub_add_eq]
        . exact hleft
      . rw [BooleanExpression.lt_correct]
        normalize
        simp [Store.update]
        apply expression_inversion at hright
        rw [BooleanExpression.lt_correct] at hright
        normalize at hright
        simp [Store.update] at hright
        apply Nat.lt_of_lt_pred
        exact hright

-- just prove the key steps in lean
  . apply implication_intro
    . exact expression_intro rfl
    intros hkleidx
    apply implication_inversion at hright
    specialize hright _
    . apply expression_intro
      rw [BooleanExpression.le_correct]
      apply expression_inversion at hkleidx
      rw [BooleanExpression.le_correct] at hkleidx
      normalize at hkleidx
      normalize
      apply Nat.le_trans (m := (σ[⋆^"idx" ↦ vidx]) (⋆$"k") + 1)
      . apply Nat.le_add_right
      . exact hkleidx
    exact hright

lemma request_deletion_invariant₁_implies_request_deletion_invariant₂ :
  ⋆ σ, τ ⊧ request_deletion_invariant₁ ->
  ⋆ σ, τ ⊧ ⋆$"k" ⋆= ♯30 ->
  ⋆ σ, τ ⊧ ⋆$"k'" ⋆= ♯0 ->
  ⋆ σ, τ ⊧ request_deletion_invariant₂ := by
  intros hreqdelinv hk hk'
  rw [request_deletion_invariant₁] at hreqdelinv
  rw [request_deletion_invariant₂]

  apply universal_quantification_intro
  intros vidx

  apply universal_quantification_inversion at hreqdelinv
  specialize hreqdelinv vidx

  apply implication_intro
  . rw [expression_conjunction_iff]

  intros hbounds
  apply conjunction_inversion at hbounds
  rcases hbounds with ⟨hkleidx, hidxltk⟩

  apply conjunction_inversion at hreqdelinv
  rcases hreqdelinv with ⟨hreqdelinv, hreqdelunset⟩

  apply implication_inversion at hreqdelinv
  specialize hreqdelinv _
  . apply expression_intro
    rw [BooleanExpression.lt_correct]
    normalize
    simp [Store.update]
    apply expression_inversion at hk
    rw [BooleanExpression.eq_correct] at hk
    normalize at hk
    rw [hk]
    apply expression_inversion at hidxltk
    rw [BooleanExpression.lt_correct] at hidxltk
    normalize at hidxltk
    simp [Store.update] at hidxltk
    exact hidxltk

  apply implication_intro
  . exact expression_intro rfl

  intros hdelreqset

  apply implication_inversion at hreqdelinv
  specialize hreqdelinv hdelreqset

  apply conjunction_inversion at hreqdelinv

  rcases hreqdelinv with ⟨hcreationbound, hltℓ⟩

  apply conjunction_intro
  . apply expression_inversion at hcreationbound
    rw [BooleanExpression.le_correct] at hcreationbound

    apply expression_intro
    rw [BooleanExpression.le_correct]

    normalize at hcreationbound
    simp [Store.update] at hcreationbound

    normalize
    simp [Store.update]

    rw [Nat.sub_le_iff_le_add] at hcreationbound
    rw [<-Nat.add_sub_assoc] at hcreationbound ; rotate_left
    . apply expression_inversion at hidxltk
      rw [BooleanExpression.lt_correct] at hidxltk
      normalize at hidxltk
      simp [Store.update] at hidxltk
      apply expression_inversion at hk
      rw [BooleanExpression.eq_correct] at hk
      normalize at hk
      rw [hk]
      exact Nat.le_of_succ_le hidxltk

    apply expression_inversion at hk
    rw [BooleanExpression.eq_correct] at hk
    normalize at hk
    rw [hk] at hcreationbound

    apply expression_inversion at hk'
    rw [BooleanExpression.eq_correct] at hk'
    normalize at hk'
    rw [hk']
    exact hcreationbound
  . exact hltℓ

lemma request_deletion_invariant₁_implies_request_deletion_invariant₁'_k_update :
  ⋆ σ, τ ⊧ request_deletion_invariant₁ ->
  ⋆ σ, τ ⊧ request_deletion_invariant₁'[⋆$"deletion_requests" ↦ (⋆$"deletion_requests")[⋆$"k" := E']ₑ] := by
  intros hreqdelinv
  rw [request_deletion_invariant₁] at hreqdelinv
  rw [request_deletion_invariant₁']

  apply universal_quantification_intro
  intros vidx

  apply universal_quantification_inversion at hreqdelinv
  specialize hreqdelinv vidx

  apply conjunction_inversion at hreqdelinv
  rcases hreqdelinv with ⟨hreqdelinv, hreqdelunset⟩

  apply conjunction_intro
  . apply implication_intro
    . apply expression_intro
      normalize

    intros hidxltk
    normalize at hidxltk

    apply implication_inversion at hreqdelinv
    specialize hreqdelinv hidxltk

    apply implication_intro
    . exact expression_intro rfl

    have hkneidx : σ (⋆$"k") ≠ vidx := by
      apply expression_inversion at hidxltk
      rw [BooleanExpression.lt_correct] at hidxltk
      normalize at hidxltk
      simp [Store.update] at hidxltk
      symm
      apply Nat.ne_of_lt
      exact hidxltk

    intros hdelreqset
    normalize at hdelreqset
    apply expression_inversion at hdelreqset
    rw [BooleanExpression.eq_correct] at hdelreqset

    apply implication_inversion at hreqdelinv
    specialize hreqdelinv _
    . apply expression_intro
      rw [BooleanExpression.eq_correct]

      normalize at hdelreqset
      simp [Store.update] at hdelreqset
      rw [PrimesMap.set_limited] at hdelreqset ; rotate_left
      . exact hkneidx

      normalize
      simp [Store.update]
      exact hdelreqset

    apply conjunction_inversion at hreqdelinv
    rcases hreqdelinv with ⟨hℓle, hltℓ⟩
    apply expression_inversion at hℓle
    rw [BooleanExpression.le_correct] at hℓle
    apply expression_inversion at hltℓ
    rw [BooleanExpression.lt_correct] at hltℓ

    apply conjunction_intro <;> normalize <;> apply expression_intro
    . rw [BooleanExpression.le_correct]
      normalize
      rw [PrimesMap.set_limited] ; rotate_left
      . simp [Store.update]
        exact hkneidx
      simp [Store.update]
      normalize at hℓle
      simp [Store.update] at hℓle
      exact hℓle
    . rw [BooleanExpression.lt_correct]
      normalize
      rw [PrimesMap.set_limited] ; rotate_left
      . simp [Store.update]
        exact hkneidx
      simp [Store.update]
      normalize at hltℓ
      simp [Store.update] at hltℓ
      exact hltℓ
  . normalize
    apply implication_intro
    . exact expression_intro rfl
    intros hkidx
    apply implication_inversion at hreqdelunset

    apply expression_inversion at hkidx
    rw [BooleanExpression.le_correct] at hkidx
    normalize at hkidx
    simp [Store.update] at hkidx

    apply expression_intro
    rw [BooleanExpression.eq_correct]
    rw [NumericExpression.lookup_different_index] ; rotate_left
    . normalize
      simp [Store.update]
      apply Nat.ne_of_lt
      apply Nat.lt_of_succ_le
      exact hkidx

    specialize hreqdelunset _
    . apply expression_intro
      rw [BooleanExpression.le_correct]
      normalize
      simp [Store.update]
      apply Nat.le_of_succ_le
      exact hkidx

    apply expression_inversion at hreqdelunset
    exact BooleanExpression.eq_correct.mp hreqdelunset

lemma deletion_invariant₁_deletion_requests_k_replacement_iff_deletion_invariant₁' :
  ⋆ σ, τ ⊧ deletion_invariant₁[⋆$"deletion_requests" ↦ (⋆$"deletion_requests")[⋆$"k" := E']ₑ] <->
  ⋆ σ, τ ⊧ deletion_invariant₁ := by
  rw [deletion_invariant₁]
  constructor <;>
  intros h <;>
  apply universal_quantification_intro <;>
  intros vidx <;>
  apply universal_quantification_inversion at h <;>
  specialize h vidx <;>
  (apply implication_intro ; exact expression_intro rfl) <;>
  intros hidxltk <;>

  apply implication_inversion at h
  . normalize at h
    specialize h _
    . normalize
      apply expression_intro
      rw [BooleanExpression.lt_correct]
      apply expression_inversion at hidxltk
      rw [BooleanExpression.lt_correct] at hidxltk
      exact hidxltk

    have hkneqvidx : σ (⋆$"k") ≠ vidx := by
      apply expression_inversion at hidxltk
      rw [BooleanExpression.lt_correct] at hidxltk
      normalize at hidxltk
      simp [Store.update] at hidxltk
      symm
      apply Nat.ne_of_lt
      exact hidxltk

    apply implication_intro
    . exact expression_intro rfl
    intros hdelreqset

    apply implication_inversion at h
    specialize h _
    . apply expression_intro
      rw [BooleanExpression.eq_correct]
      normalize
      simp [Store.update]
      rw [PrimesMap.set_limited] ; rotate_left
      . exact hkneqvidx
      apply expression_inversion at hdelreqset
      rw [BooleanExpression.eq_correct] at hdelreqset
      normalize at hdelreqset
      simp [Store.update] at hdelreqset
      exact hdelreqset

    normalize at h

    apply trace_intro
    apply trace_inversion at h
    apply TraceAssertion.Models.eventually_inversion at h
    rcases h with ⟨k', hbound₁, hbound₂, h⟩
    apply TraceAssertion.Models.atomic_inversion at h
    rcases h with ⟨hkbound, h⟩
    normalize at h
    rw [PrimesMap.set_limited] at h; rotate_left
    . simp [Store.update]
      exact hkneqvidx
    simp [Store.update] at h
    apply TraceAssertion.Models.eventually_intro
    . apply TraceAssertion.Models.atomic_intro
      normalize
      simp [Store.update]
      exact h
    . normalize at hbound₁
      simp [Store.update] at hbound₁
      rw [PrimesMap.set_limited] at hbound₁ ; rotate_left
      . exact hkneqvidx
      normalize
      simp [Store.update]
      exact hbound₁
    . normalize at hbound₂
      simp [Store.update] at hbound₂
      rw [PrimesMap.set_limited] at hbound₂ ; rotate_left
      . exact hkneqvidx
      normalize
      simp [Store.update]
      exact hbound₂
  . normalize at h
    specialize h _
    . normalize
      apply expression_intro
      rw [BooleanExpression.lt_correct]
      normalize at hidxltk
      apply expression_inversion at hidxltk
      rw [BooleanExpression.lt_correct] at hidxltk
      exact hidxltk

    have hkneqvidx : σ (⋆$"k") ≠ vidx := by
      normalize at hidxltk
      apply expression_inversion at hidxltk
      rw [BooleanExpression.lt_correct] at hidxltk
      normalize at hidxltk
      simp [Store.update] at hidxltk
      symm
      apply Nat.ne_of_lt
      exact hidxltk

    apply implication_intro
    . exact expression_intro rfl
    intros hdelreqset

    apply implication_inversion at h
    specialize h _
    . apply expression_intro
      rw [BooleanExpression.eq_correct]
      normalize
      simp [Store.update]
      normalize at hdelreqset
      apply expression_inversion at hdelreqset
      rw [BooleanExpression.eq_correct] at hdelreqset
      normalize at hdelreqset
      rw [PrimesMap.set_limited] at hdelreqset ; rotate_left
      . exact hkneqvidx
      simp [Store.update] at hdelreqset
      exact hdelreqset

    normalize

    apply trace_intro
    apply trace_inversion at h
    apply TraceAssertion.Models.eventually_inversion at h
    rcases h with ⟨k', hbound₁, hbound₂, h⟩
    apply TraceAssertion.Models.atomic_inversion at h
    rcases h with ⟨hkbound, h⟩
    normalize at h
    simp [Store.update] at h
    apply TraceAssertion.Models.eventually_intro
    . apply TraceAssertion.Models.atomic_intro
      . normalize
        simp [Store.update]
        rw [PrimesMap.set_limited] ; rotate_left
        . exact hkneqvidx
        exact h
    . normalize at hbound₁
      simp [Store.update] at hbound₁
      normalize
      simp [Store.update]
      rw [PrimesMap.set_limited] ; rotate_left
      . exact hkneqvidx
      exact hbound₁
    . normalize at hbound₂
      simp [Store.update] at hbound₂
      normalize
      simp [Store.update]
      rw [PrimesMap.set_limited] ; rotate_left
      . exact hkneqvidx
      exact hbound₂

lemma deletion_invariant₁_does_not_contain_trace_length :
  ¬(deletion_invariant₁.containsNumericExpression ℓ) := by
  rw [deletion_invariant₁] ; auto_contains

lemma deletion_invariant₁'_implies_deletion_invariant₁ :
  deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] ⋆-> deletion_invariant₁ := by
  rw [deletion_invariant₁]
  intros σ τ h
  apply universal_quantification_intro
  intros vidx
  apply universal_quantification_inversion at h
  specialize h vidx
  apply implication_intro
  . apply expression_intro
    exact rfl
  intros hidxltk

  apply implication_inversion at h
  specialize h _
  . normalize at hidxltk
    apply expression_inversion at hidxltk
    rw [BooleanExpression.lt_correct] at hidxltk
    normalize at hidxltk

    normalize
    apply expression_intro
    rw [BooleanExpression.lt_correct]
    normalize
    apply Nat.lt_add_right
    exact hidxltk

  apply implication_intro
  . apply expression_intro
    exact rfl

  intros hdelreqidx
  apply implication_inversion at h
  specialize h hdelreqidx

  exact h

lemma request_deletion_invariant₁'_implies_request_deletion_invariant₁' :
  ⋆ σ, τ ⊧ request_deletion_invariant₁'[ℓ ↦ ℓ ⋆- ♯1] ->
  ⋆ σ, τ ⊧ (⋆$"deletion_requests")[ ⋆$"k" ]ₑ[ ♯2 ]ₑ ⋆= ℓ ⋆- ♯1 ->
  0 < τ.length ->
  ⋆ σ, τ ⊧ request_deletion_invariant₁[⋆$"k" ↦ ⋆$"k" ⋆+ ♯1] := by
  rw [request_deletion_invariant₁, request_deletion_invariant₁']
  intros hreqdelinv hdelreqktime hτlen
  normalize
  apply universal_quantification_intro
  intros vidx

  apply universal_quantification_inversion at hreqdelinv
  specialize hreqdelinv vidx

  normalize at hreqdelinv

  apply conjunction_inversion at hreqdelinv
  rcases hreqdelinv with ⟨hreqdelinv, hreqdelunset⟩

  apply conjunction_intro
  . apply implication_intro
    . apply expression_intro
      normalize

    intros hidxltk
    normalize at hidxltk

    apply expression_inversion at hidxltk
    rw [BooleanExpression.lt_correct] at hidxltk
    normalize at hidxltk
    simp [Store.update] at hidxltk

    by_cases hkvidx : σ (⋆$"k") = vidx
    . clear hreqdelinv
      apply expression_inversion at hdelreqktime
      rw [BooleanExpression.eq_correct] at hdelreqktime
      apply disjunction_intro_right
      apply conjunction_intro
      . apply expression_intro
        rw [BooleanExpression.le_correct]
        normalize at hdelreqktime
        normalize
        simp [Store.update]

        rw [hkvidx] at hdelreqktime
        rw [hdelreqktime]
        rw [hkvidx]
        simp
        apply Nat.le_of_eq
        simp
      . apply expression_intro
        rw [BooleanExpression.lt_correct]
        normalize
        simp [Store.update]
        normalize at hdelreqktime
        rw [hkvidx] at hdelreqktime
        rw [hdelreqktime]
        apply Nat.lt_of_sub_pos
        simp
        exact hτlen
    . apply implication_inversion at hreqdelinv
      specialize hreqdelinv _
      . normalize
        apply expression_intro
        rw [BooleanExpression.lt_correct]
        normalize
        simp [Store.update]
        apply Nat.lt_of_le_of_ne
        . apply Nat.le_of_lt_succ
          exact hidxltk
        . exact fun a => hkvidx (id (Eq.symm a))

      apply implication_intro
      . exact expression_intro rfl

      intros hdelreqset
      apply implication_inversion at hreqdelinv
      specialize hreqdelinv hdelreqset

      apply conjunction_inversion at hreqdelinv
      normalize at hreqdelinv
      rcases hreqdelinv with ⟨hℓle, hltℓ⟩

      apply conjunction_intro
      . clear hltℓ
        apply expression_inversion at hℓle
        rw [BooleanExpression.le_correct] at hℓle
        normalize at hℓle
        simp [Store.update] at hℓle
        apply expression_intro
        rw [BooleanExpression.le_correct]
        normalize
        simp [Store.update]
        rw [Nat.add_comm]
        rw [Nat.add_sub_assoc]
        . rw [Nat.sub_add_eq]
          exact hℓle
        . apply Nat.le_of_lt_succ
          exact hidxltk
      . clear hℓle
        apply expression_inversion at hltℓ
        rw [BooleanExpression.lt_correct] at hltℓ
        normalize at hltℓ
        simp [Store.update] at hltℓ
        apply expression_intro

        rw [BooleanExpression.lt_correct]
        normalize
        simp [Store.update]
        apply Nat.lt_of_lt_pred
        exact hltℓ
  . apply implication_intro
    . exact expression_intro rfl
    intros hkleidx
    apply implication_inversion at hreqdelunset
    specialize hreqdelunset _
    . apply expression_intro
      rw [BooleanExpression.le_correct]
      normalize
      simp [Store.update]
      apply expression_inversion at hkleidx
      rw [BooleanExpression.le_correct] at hkleidx
      normalize at hkleidx
      simp [Store.update] at hkleidx
      exact hkleidx
    exact hreqdelunset

lemma request_deletion_invariant₂_decrement_ℓ_implies_request_deletion_invariant₂_increment_k' :
  ⋆ σ, τ ⊧ request_deletion_invariant₂[ℓ ↦ ℓ ⋆- ♯1] ->
  0 < τ.length ->
  ⋆ σ, τ ⊧ request_deletion_invariant₂[⋆$"k'" ↦ ⋆⋆$"k'" ⋆+ ♯1] := by
  rw [request_deletion_invariant₂]

  intros hreqdelinv hτlen
  normalize at hreqdelinv
  apply universal_quantification_intro
  intros vidx
  apply universal_quantification_inversion at hreqdelinv
  specialize hreqdelinv vidx

  apply implication_inversion at hreqdelinv

  apply implication_intro
  . normalize
    rw [expression_conjunction_iff]

  intros hbounds
  normalize at hbounds
  apply conjunction_inversion at hbounds
  rcases hbounds with ⟨hbound₁, hbound₂⟩
  apply expression_inversion at hbound₁
  rw [BooleanExpression.le_correct] at hbound₁
  apply expression_inversion at hbound₂
  rw [BooleanExpression.lt_correct] at hbound₂

  specialize hreqdelinv _
  . apply conjunction_intro <;> apply expression_intro
    . clear hbound₂
      rw [BooleanExpression.le_correct]
      normalize
      simp [Store.update]
      normalize at hbound₁
      simp [Store.update] at hbound₁
      apply Nat.le_of_succ_le
      exact hbound₁
    . clear hbound₁
      rw [BooleanExpression.lt_correct]
      normalize
      simp [Store.update]
      normalize at hbound₂
      simp [Store.update] at hbound₂
      exact hbound₂
  clear hbound₁ hbound₂

  normalize
  apply implication_intro
  . exact expression_intro rfl

  intros hdelreqset
  apply implication_inversion at hreqdelinv
  specialize hreqdelinv hdelreqset
  clear hdelreqset

  apply conjunction_inversion at hreqdelinv
  rcases hreqdelinv with ⟨hℓle, hltℓ⟩
  apply expression_inversion at hℓle
  rw [BooleanExpression.le_correct] at hℓle
  normalize at hℓle
  simp [Store.update] at hℓle
  apply expression_inversion at hltℓ
  rw [BooleanExpression.lt_correct] at hltℓ
  normalize at hltℓ
  simp [Store.update] at hltℓ

  apply conjunction_intro <;> apply expression_intro
  . rw [BooleanExpression.le_correct]
    normalize
    simp [Store.update]
    -- This is the missing assumption
    -- need some xyz
    clear hltℓ
    set request_time := PrimesMap.get (PrimesMap.get (σ (⋆$"deletion_requests")) vidx) 2

    rw [<-Nat.add_assoc]
    rw [<-Nat.pred_le_iff_le_succ]
    exact hℓle
  . rw [BooleanExpression.lt_correct]
    normalize
    simp [Store.update]
    apply Nat.lt_trans
    . exact hltℓ
    . apply Nat.sub_one_lt
      -- Need 0 < τ.length
      symm
      apply Nat.ne_of_lt
      exact hτlen

lemma request_deletion_invariant₁_implies_request_deletion₁_increment_k' :
  ⋆ σ, τ ⊧ request_deletion_invariant₁ ->
  ⋆ σ, τ ⊧ request_deletion_invariant₁[⋆$"k'" ↦ ⋆⋆$"k'" ⋆+ ♯1] := by
  rw [request_deletion_invariant₁]
  intros hreqdelinv
  normalize

  apply universal_quantification_intro
  intros vidx
  apply universal_quantification_inversion at hreqdelinv
  specialize hreqdelinv vidx

  apply conjunction_inversion at hreqdelinv
  rcases hreqdelinv with ⟨hreqdelinv, hreqdelunset⟩

  apply conjunction_intro
  . apply implication_intro
    . exact expression_intro rfl

    intros hbounds

    apply implication_inversion at hreqdelinv
    specialize hreqdelinv hbounds

    apply implication_intro
    . exact expression_intro rfl

    intros hdelreqset

    apply implication_inversion at hreqdelinv
    specialize hreqdelinv hdelreqset
    clear hdelreqset

    apply conjunction_inversion at hreqdelinv

    rcases hreqdelinv with ⟨hℓle, hltℓ⟩

    apply conjunction_intro
    . clear hltℓ
      apply expression_inversion at hℓle
      rw [BooleanExpression.le_correct] at hℓle
      normalize at hℓle
      simp [Store.update] at hℓle
      apply expression_intro
      rw [BooleanExpression.le_correct]
      normalize
      simp [Store.update]

      apply Nat.le_trans
      . exact hℓle
      . apply Nat.le_refl
    . exact hltℓ
  . exact hreqdelunset

lemma request_deletion_invariant₂_implies_request_deletion₂_increment_k' :
  ⋆ σ, τ ⊧ request_deletion_invariant₂ ->
  ⋆ σ, τ ⊧ request_deletion_invariant₂[⋆$"k'" ↦ ⋆⋆$"k'" ⋆+ ♯1] := by
  rw [request_deletion_invariant₂]
  intros hreqdelinv
  normalize

  apply universal_quantification_intro
  intros vidx
  apply universal_quantification_inversion at hreqdelinv
  specialize hreqdelinv vidx

  apply implication_intro
  . rw [expression_conjunction_iff]

  intros hbounds
  apply conjunction_inversion at hbounds
  rcases hbounds with ⟨hbound₁, hbound₂⟩

  apply implication_inversion at hreqdelinv
  specialize hreqdelinv _
  . apply conjunction_intro
    . clear hbound₂
      apply expression_inversion at hbound₁
      rw [BooleanExpression.le_correct] at hbound₁
      normalize at hbound₁
      simp [Store.update] at hbound₁
      apply expression_intro
      rw [BooleanExpression.le_correct]
      normalize
      simp [Store.update]
      apply Nat.le_of_succ_le
      exact hbound₁
    . exact hbound₂
  clear hbound₁ hbound₂

  apply implication_intro
  . exact expression_intro rfl

  intros hdelreqset

  apply implication_inversion at hreqdelinv
  specialize hreqdelinv hdelreqset
  clear hdelreqset

  apply conjunction_inversion at hreqdelinv

  rcases hreqdelinv with ⟨hℓle, hltℓ⟩

  apply conjunction_intro
  . clear hltℓ
    apply expression_inversion at hℓle
    rw [BooleanExpression.le_correct] at hℓle
    normalize at hℓle
    simp [Store.update] at hℓle
    apply expression_intro
    rw [BooleanExpression.le_correct]
    normalize
    simp [Store.update]

    apply Nat.le_trans
    . exact hℓle
    . rw [<-Nat.add_assoc]
      apply Nat.le_succ
  . exact hltℓ

lemma deletion_invariant₂_increment_k'_implies_deletion_invariant₂ :
  ⋆ σ, τ ⊧ deletion_invariant₂[⋆$"k'" ↦ ⋆⋆$"k'" ⋆+ ♯1] ->
  ⋆ σ, τ ⊧ ✧( 30 ) ⋆![♯PerformDeletion, (⋆$"deletion_requests")[ ⋆$"k'" ]ₑ[ ♯1 ]ₑ] ⋆@ (⋆$"deletion_requests")[ ⋆$"k'" ]ₑ[ ♯2 ]ₑ ->
  ⋆ σ, τ ⊧ deletion_invariant₂ := by
  rw [deletion_invariant₂]
  intros hdeleteinv heventually
  apply universal_quantification_intro
  intros vidx
  apply universal_quantification_inversion at hdeleteinv
  specialize hdeleteinv vidx
  apply implication_inversion at hdeleteinv

  by_cases hk'vidx : σ (⋆$"k'") = vidx
  . apply disjunction_intro_right
    apply implication_intro
    . normalize
      apply expression_intro
      normalize
    . intros hidxbound
      normalize

      apply trace_intro
      normalize

      apply trace_inversion at heventually
      apply TraceAssertion.Models.eventually_inversion at heventually
      rcases heventually with ⟨k', hbound₁, hbound₂, heventually⟩

      apply TraceAssertion.Models.atomic_inversion at heventually
      rcases heventually with ⟨hkbound, heventually⟩


      rw [<-hk'vidx]
      apply TraceAssertion.Models.eventually_intro (k' := k')
      . apply TraceAssertion.Models.atomic_intro
        . normalize
          simp [Store.update]
          exact heventually
      . simp [Store.update]
        normalize at hbound₁
        exact hbound₁
      . simp [Store.update]
        normalize at hbound₂
        exact hbound₂
  . apply implication_intro
    . normalize
      rw [expression_conjunction_iff]
    . intros hidxbound
      specialize hdeleteinv _
      . normalize at hidxbound
        rw [expression_conjunction_iff] at hidxbound
        rw [BooleanExpression.conj_correct] at hidxbound
        rcases hidxbound with ⟨hk'idx, hidxk⟩
        apply conjunction_intro ; rotate_left
        . apply expression_intro
          exact hidxk

        normalize at hk'idx
        simp [Store.update] at hk'idx

        normalize
        apply expression_intro
        rw [BooleanExpression.le_correct]
        normalize
        simp [Store.update]
        apply Nat.succ_le_of_lt
        apply Nat.lt_of_le_of_ne
        . exact hk'idx
        . exact hk'vidx
      exact hdeleteinv

lemma deletion_invariant₂_implies_deletion_invariant₁ :
  ⋆ σ, τ ⊧ deletion_invariant₂ ->
  ⋆ σ, τ ⊧ ⋆$"k'" ⋆= ♯0 ->
  ⋆ σ, τ ⊧ deletion_invariant₁ := by
  rw [deletion_invariant₁, deletion_invariant₂]
  intros hdelinv hk'
  normalize

  apply universal_quantification_intro
  intros vidx
  apply universal_quantification_inversion at hdelinv
  specialize hdelinv vidx

  apply implication_intro
  . exact expression_intro rfl
  intros hbounds

  apply implication_inversion at hdelinv
  specialize hdelinv _
  . apply conjunction_intro
    . apply expression_intro
      apply expression_inversion at hk'
      rw [BooleanExpression.eq_correct] at hk'
      rw [BooleanExpression.le_correct]
      normalize at hk'
      normalize
      simp [Store.update]
      rw [hk']
      apply Nat.zero_le
    . exact hbounds

  apply implication_intro
  . exact expression_intro rfl

  intros hdelreqset

  apply implication_inversion at hdelinv
  specialize hdelinv hdelreqset
  clear hdelreqset

  exact hdelinv
