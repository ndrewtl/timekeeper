import Timekeeper.Language.Semantics.BigStep
import Timekeeper.Language.Command

namespace Timekeeper.BigStep
open Command


lemma seq_inversion :
  (C₁ ⋆; C₂, σ, τ) ↓ (σ'', τ'') ->
  ∃ σ' τ',
  (C₁, σ, τ) ↓ (σ', τ') ∧
  (C₂, σ', τ') ↓ (σ'', τ'') := by
  intros hbig
  rcases hbig with (_ | _ | _ | _ | ⟨hC₁, hC₂⟩)
  expose_names; exists σ', τ'

lemma if_true_inversion :
  (if: B then: C₁ else: C₂ end, σ, τ) ↓ (σ', τ') ->
  ⟦B⟧(σ, τ) = true ->
  BigStep C₁ σ τ σ' τ' := by
  intros hbig hB
  rcases hbig with (_ | _ |_ | _ |_ | ⟨contr, _⟩ | ⟨_, hbig⟩ )
  . rw [hB] at contr; contradiction
  . exact hbig

lemma if_false_inversion :
  (if: B then: C₁ else: C₂ end, σ, τ) ↓ (σ', τ') ->
  ⟦B⟧(σ, τ) = false ->
  BigStep C₂ σ τ σ' τ' := by
  intros hbig hB
  rcases hbig with (_ | _ |_ | _ |_ | ⟨_, hbig⟩ | ⟨contr, _⟩ )
  . exact hbig
  . rw [hB] at contr; contradiction

lemma while_false_inversion :
  (while: B do: C end, σ, τ) ↓ (σ', τ') ->
  ⟦B⟧(σ, τ) = false ->
  σ' = σ ∧ τ' = τ := by
  intros hbig hB
  rcases hbig with (_ | _ |_ | _ |_ | _ | _ | _ | ⟨contr⟩ )
  . exact ⟨rfl, rfl⟩
  . rw [hB] at contr; contradiction

lemma while_true_inversion :
  (while: B do: C end, σ, τ) ↓ (σ'', τ'') ->
  ⟦B⟧(σ, τ) = true ->
  ∃ σ' τ',
  (C, σ, τ) ↓ (σ', τ') ∧
  (while: B do: C end, σ', τ') ↓ (σ'', τ'') := by
  intros hbig hB
  rcases hbig with (_ | _ |_ | _ |_ | _ | _ | contr | ⟨_, hCbig, hwhilebig⟩ )
  . rw [hB] at contr ; contradiction
  . expose_names ; exists σ', τ'

lemma seq_assoc :
  ((C₁ ⋆; C₂) ⋆; C₃, σ₀, τ₀) ↓ (σ₃, τ₃) <->
  (C₁ ⋆; C₂ ⋆; C₃, σ₀, τ₀) ↓ (σ₃, τ₃) := by
  constructor <;>
  intros h <;>
  apply seq_inversion at h

  . rcases h with ⟨σ₂, τ₂, hC₁C₂step, hC₃step⟩
    apply seq_inversion at hC₁C₂step
    rcases hC₁C₂step with ⟨σ₁, τ₁, hC₁step, hC₂step⟩

    apply big_step_seq
    . exact hC₁step
    . apply big_step_seq
      . exact hC₂step
      . exact hC₃step
  . rcases h with ⟨σ₁, τ₁, hC₁step, hC₂C₃step⟩

    apply seq_inversion at hC₂C₃step
    rcases hC₂C₃step with ⟨σ₂, τ₂, hC₂step, hC₃step⟩

    apply big_step_seq
    . apply big_step_seq
      . exact hC₁step
      . exact hC₂step
    . exact hC₃step
