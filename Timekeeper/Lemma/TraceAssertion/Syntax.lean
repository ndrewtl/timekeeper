import Timekeeper.Tactics
import Timekeeper.Logic.Assertion.TraceAssertion
import Timekeeper.Lemma.NumericExpressionList

namespace Timekeeper.TraceAssertion

lemma nonexistent_term_replacement {T : TraceAssertion} :
  ¬T.containsNumericExpression E -> T[E ↦ E'] = T := by
  intros hcont
  induction T with
  | top => normalize
  | atomic Es =>
    simp [containsNumericExpression] at hcont
    apply NumericExpressionList.nonexistent_term_replacement at hcont
    normalize
    normalize at hcont
    rw [hcont]
  | negation φ ihφ =>
    simp [containsNumericExpression] at hcont
    simp [replaceNumericExpression]
    rw [<-numeric_replacement]
    apply ihφ
    exact hcont
  | disjunction φ ψ ihφ ihψ =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hcontφ, hcontψ⟩
    simp [replaceNumericExpression]
    rw [<-numeric_replacement, <-numeric_replacement]
    constructor
    . exact ihφ hcontφ
    . exact ihψ hcontψ
  | previous φ ihφ =>
    simp [containsNumericExpression] at hcont
    simp [replaceNumericExpression]
    rw [<-numeric_replacement]
    exact ihφ hcont
  | next φ ihφ =>
    simp [containsNumericExpression] at hcont
    simp [replaceNumericExpression]
    rw [<-numeric_replacement]
    exact ihφ hcont
  | since φ ψ ihφ ihψ =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hcontφ, hcontψ⟩
    simp [replaceNumericExpression]
    rw [<-numeric_replacement, <-numeric_replacement]
    constructor
    . exact ihφ hcontφ
    . exact ihψ hcontψ
  | «until» φ ψ n ihφ ihψ =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hcontφ, hcontψ⟩
    simp [replaceNumericExpression]
    rw [<-numeric_replacement, <-numeric_replacement]
    constructor
    . exact ihφ hcontφ
    . exact ihψ hcontψ
  | function F Es ihF =>
    simp [containsNumericExpression] at hcont
    rcases hcont with ⟨hFcont, hEscont⟩
    normalize
    constructor
    . exact funext fun x => ihF x (hFcont x)
    . rw [NumericExpressionList.nonexistent_term_replacement]
      exact hEscont
  | universal_quantification _ T' ihT' =>
    simp [containsNumericExpression] at hcont
    simp [replaceNumericExpression]
    rw [<-numeric_replacement]
    exact ihT' hcont

lemma nonexistent_variable_replacement {T : TraceAssertion} {x : Variable} {E : NumericExpression} :
  ¬(T.containsNumericExpression (NumericExpression.var x)) ->
  T[x ↦ E] = T := by
  intros h
  rw [variable_replacement, <-numeric_replacement]
  rw [nonexistent_term_replacement]
  exact h

lemma trace_length_substitution_preserves_well_formedness {T : TraceAssertion} :
  T[ℓ ↦ NumericExpression.binaryOperation op ℓ ♯n].wellFormed = T.wellFormed := by
  induction T with
  | top => normalize
  | atomic Es =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    rw [<-NumericExpressionList.containsTraceLength, <-NumericExpressionList.containsTraceLength]
    rw [NumericExpressionList.trace_length_substitution_preserves_trace_length_presence]
  | negation T' ihT' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    normalize at ihT'
    rw [ihT']
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    normalize at ihT₁ ihT₂
    rw [ihT₁, ihT₂]
  | previous T' ihT' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    normalize at ihT'
    rw [ihT']
  | next T' ihT' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    normalize at ihT'
    rw [ihT']
  | since T₁ T₂ ihT₁ ihT₂ =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    normalize at ihT₁ ihT₂
    rw [ihT₁, ihT₂]
  | «until» T₁ T₂ _ ihT₁ ihT₂ =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    normalize at ihT₁ ihT₂
    rw [ihT₁, ihT₂]
  | function F Es ihF =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    rw [<-NumericExpressionList.containsTraceLength, <-NumericExpressionList.containsTraceLength]
    rw [NumericExpressionList.trace_length_substitution_preserves_trace_length_presence]
    normalize at ihF
    constructor
    . intros h
      rcases h with ⟨hF, hEs⟩
      constructor
      . intros event
        specialize hF event
        rw [ihF] at hF
        exact hF
      . exact hEs
    . intros h
      rcases h with ⟨hF, hEs⟩
      constructor
      . intros event
        specialize hF event
        rw [ihF]
        exact hF
      . exact hEs
  | universal_quantification _ T' ihT' =>
    simp [wellFormed, replaceNumericExpression]
    normalize
    normalize at ihT'
    rw [ihT']

lemma trace_length_addition_preserves_well_formedness {T : TraceAssertion} :
  T[ℓ ↦ ℓ ⋆+ ♯n].wellFormed = T.wellFormed := by
  have h : ℓ ⋆+ ♯n = NumericExpression.binaryOperation BinOp.plus ℓ ♯n := by exact rfl
  rw [h]
  exact trace_length_substitution_preserves_well_formedness

lemma trace_length_subtraction_preserves_well_formedness {T : TraceAssertion} :
  T[ℓ ↦ ℓ ⋆- ♯n].wellFormed = T.wellFormed := by
  have h : ℓ ⋆- ♯n = NumericExpression.binaryOperation BinOp.minus ℓ ♯n := by exact rfl
  rw [h]
  exact trace_length_substitution_preserves_well_formedness

lemma well_formed_does_not_contain_trace_length {T : TraceAssertion} :
  T.wellFormed -> ¬T.containsNumericExpression ℓ := by
  induction T with
  | top => simp [containsNumericExpression]
  | atomic Es =>
    intro h
    simp [wellFormed] at h
    simp [containsNumericExpression]
    exact h
  | negation T' ih =>
    intro h
    simp [containsNumericExpression]
    exact ih h
  | disjunction T₁ T₂ ihT₁ ihT₂ =>
    intro h
    simp [wellFormed] at h
    rcases h with ⟨hT₁, hT₂⟩
    simp [containsNumericExpression]
    exact ⟨ihT₁ hT₁, ihT₂ hT₂⟩
  | previous T' ihT' =>
    intro h
    simp [containsNumericExpression]
    exact ihT' h
  | next T' ihT' =>
    intro h
    simp [containsNumericExpression]
    exact ihT' h
  | since T₁ T₂ ihT₁ ihT₂ =>
    intro h
    simp [wellFormed] at h
    rcases h with ⟨hT₁, hT₂⟩
    simp [containsNumericExpression]
    constructor
    . exact ihT₁ hT₁
    . exact ihT₂ hT₂
  | «until» T₁ T₂ n ihT₁ ihT₂ =>
    intros h
    simp [wellFormed] at h
    rcases h with ⟨hT₁, hT₂⟩
    simp [containsNumericExpression]
    constructor
    . exact ihT₁ hT₁
    . exact ihT₂ hT₂
  | function F Es ihF =>
    intros h
    simp [wellFormed] at h
    rcases h with ⟨hF, hEs⟩
    simp [containsNumericExpression]
    constructor
    . exact fun x => ihF x (hF x)
    . exact hEs
  | universal_quantification _ T' ihT' =>
    intro h
    simp [containsNumericExpression]
    exact ihT' h
