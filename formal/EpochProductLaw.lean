import JointBankLaw
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Constructions.Pi

/-!
Gate149. The finite uniform permutation-bank law is exactly the product of
independent uniform epoch permutations. A measurable identity pushforward
reconciles the canonical product measurable space with the already fixed
top measurable space on Bank. This changes no tuple, probability or loss.
Root alone compiles; the author performs source/file handling only.
-/
namespace Gate149.EpochProductLaw
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Gate149.JointBankLaw

/-- The actual independent-epoch product measure, transported by the
identity on the tuple to the fixed measurable Bank representation. -/
def independentEpochLaw (n K : ℕ) : Measure (Bank n K) :=
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  @Measure.map (Bank n K) (Bank n K) MeasurableSpace.pi
    (bankMeasurableSpace n K) id
    (Measure.pi (fun _ : Fin K => finiteUniformLaw (Equiv.Perm (Fin n))))

/-- Every full tuple has the product of its K uniform epoch atom masses. -/
theorem independentEpochLaw_singleton (n K : ℕ) (bank : Bank n K) :
    independentEpochLaw n K {bank} =
      ((Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹) ^ K := by
  classical
  letI : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hid : @Measurable (Bank n K) (Bank n K) MeasurableSpace.pi
      (bankMeasurableSpace n K) id :=
    @measurable_of_countable (Bank n K) (Bank n K) MeasurableSpace.pi
      (bankMeasurableSpace n K) inferInstance inferInstance id
  unfold independentEpochLaw
  rw [Measure.map_apply (mα := MeasurableSpace.pi)
    (mβ := bankMeasurableSpace n K) hid (measurableSet_singleton bank)]
  change (Measure.pi (fun _ : Fin K => finiteUniformLaw (Equiv.Perm (Fin n))))
    {bank} = _
  rw [Measure.pi_singleton]
  simp only [finiteUniformLaw_singleton, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- Exact equality of the original finite bank law and independent fresh
uniform epoch sampling. No selector independence is assumed or concluded. -/
theorem bankLaw_eq_independentEpochLaw (n K : ℕ) :
    bankLaw n K = independentEpochLaw n K := by
  classical
  apply Measure.ext_of_singleton
  intro bank
  rw [finiteUniformLaw_singleton, independentEpochLaw_singleton]
  simp only [Bank, Fintype.card_pi_const, Nat.cast_pow, ENNReal.inv_pow]

instance independentEpochLaw_probability (n K : ℕ) :
    IsProbabilityMeasure (independentEpochLaw n K) := by
  rw [← bankLaw_eq_independentEpochLaw]
  infer_instance

#print axioms independentEpochLaw_singleton
#print axioms bankLaw_eq_independentEpochLaw
#print axioms independentEpochLaw_probability

end
end Gate149.EpochProductLaw
