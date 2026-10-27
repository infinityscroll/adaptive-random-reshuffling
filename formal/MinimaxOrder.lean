import Mathlib.Data.ENNReal.Basic

/-! Standard order interfaces. These lemmas do NOT supply a hard instance,
an algorithm, an upper guarantee or a policy-model representation. -/
namespace Gate149.MinimaxOrder
open scoped ENNReal

theorem fixed_witness_both_lower {I A : Type*} (risk : I → A → ℝ≥0∞)
    (c : ℝ≥0∞) (i0 : I) (h : ∀ a, c ≤ risk i0 a) :
    c ≤ (⨆ i, ⨅ a, risk i a) ∧ c ≤ (⨅ a, ⨆ i, risk i a) := by
  constructor
  · exact le_iSup_of_le i0 (le_iInf h)
  · exact le_iInf (fun a => le_iSup_of_le i0 (h a))

theorem uniform_strategy_both_upper {I A : Type*} (risk : I → A → ℝ≥0∞)
    (C : ℝ≥0∞) (a0 : A) (h : ∀ i, risk i a0 ≤ C) :
    (⨆ i, ⨅ a, risk i a) ≤ C ∧ (⨅ a, ⨆ i, risk i a) ≤ C := by
  constructor
  · exact iSup_le (fun i => iInf_le_of_le a0 (h i))
  · exact iInf_le_of_le a0 (iSup_le h)

theorem conditional_sandwich {I A : Type*} (risk : I → A → ℝ≥0∞)
    (c C : ℝ≥0∞) (i0 : I) (a0 : A)
    (hlower : ∀ a, c ≤ risk i0 a) (hupper : ∀ i, risk i a0 ≤ C) :
    c ≤ (⨆ i, ⨅ a, risk i a) ∧ (⨆ i, ⨅ a, risk i a) ≤ C ∧
    c ≤ (⨅ a, ⨆ i, risk i a) ∧ (⨅ a, ⨆ i, risk i a) ≤ C := by
  have hl := fixed_witness_both_lower risk c i0 hlower
  have hu := uniform_strategy_both_upper risk C a0 hupper
  exact ⟨hl.1, hu.1, hl.2, hu.2⟩

#print axioms fixed_witness_both_lower
#print axioms uniform_strategy_both_upper
#print axioms conditional_sandwich
end Gate149.MinimaxOrder
