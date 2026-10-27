import FiniteRisk
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
Gate148. Generic independent-private-seed wrapper for a finite uniform bank.
The loss can be unbounded across seeds. The conclusion uses the extended
nonnegative integral and imposes no finite-integrability condition.

The seed is sampled from nu and, for each fixed seed, the inner bank law is
the SAME finite uniform law. Thus this represents an independent seed and
uniform bank, with the chosen loss allowed to depend on their entire pair.
The finite average is identified exactly with a uniformly weighted ENNReal
sum below. No actual policy, seed representation, joint measurability or
product-measure/Tonelli equivalence is claimed by this generic module.
For measurable actual losses it is the corresponding iterated nonnegative
expectation; otherwise the formal expression remains a lower integral.
Root alone compiles this file.
-/
namespace Gate148.RandomizedRisk
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Gate148.FiniteRisk

variable {Bank : Type*} [Fintype Bank] [Nonempty Bank]

/-- The exact uniform probability weighted sum on the finite bank. -/
def uniformENNMean (f : Bank → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ bank, (Fintype.card Bank : ℝ≥0∞)⁻¹ * f bank

/-- Casting a nonnegative finite real average is exactly averaging the
cast losses with uniform ENNReal weights; no expectation surrogate. -/
theorem ofReal_uniformMean (f : Bank → ℝ) (hf : ∀ bank, 0 ≤ f bank) :
    ENNReal.ofReal (uniformMean f) = uniformENNMean (fun bank => ENNReal.ofReal (f bank)) := by
  have hc : (0 : ℝ) < Fintype.card Bank := by positivity
  have hsum : ENNReal.ofReal (∑ bank, f bank) = ∑ bank, ENNReal.ofReal (f bank) :=
    ENNReal.ofReal_sum_of_nonneg (fun bank _ => hf bank)
  unfold uniformMean uniformENNMean
  rw [ENNReal.ofReal_div_of_pos hc, hsum, ENNReal.ofReal_natCast]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_comm]

variable {Seed : Type*} [MeasurableSpace Seed]

/-- Iterated extended loss: private seed outside, exact uniform bank inside. -/
def randomizedLoss (nu : Measure Seed) (loss : Seed → Bank → ℝ) : ℝ≥0∞ :=
  ∫⁻ seed, ENNReal.ofReal (uniformMean (loss seed)) ∂nu

theorem randomizedLoss_eq_uniformENNMean (nu : Measure Seed) (loss : Seed → Bank → ℝ)
    (h0 : ∀ seed bank, 0 ≤ loss seed bank) :
    randomizedLoss nu loss =
      ∫⁻ seed, uniformENNMean (fun bank => ENNReal.ofReal (loss seed bank)) ∂nu := by
  unfold randomizedLoss
  apply lintegral_congr
  intro seed
  exact ofReal_uniformMean (loss seed) (h0 seed)

/-- All-seed finite-bank lower bounds survive arbitrary probability-seed
mixing. The loss need not have a finite expectation; infinity is allowed. -/
theorem randomized_lower (nu : Measure Seed) [IsProbabilityMeasure nu]
    (loss : Seed → Bank → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hmean : ∀ seed, c ≤ uniformMean (loss seed)) :
    ENNReal.ofReal c ≤ randomizedLoss nu loss := by
  unfold randomizedLoss
  calc
    ENNReal.ofReal c = ∫⁻ _seed : Seed, ENNReal.ofReal c ∂nu := by simp
    _ ≤ ∫⁻ seed, ENNReal.ofReal (uniformMean (loss seed)) ∂nu :=
      lintegral_mono (fun seed => ENNReal.ofReal_le_ofReal (hmean seed))

/-- The same conclusion stated directly for the uniformly weighted finite
nonnegative losses, retaining seed/bank dependence in every summand. -/
theorem randomized_lower_weighted (nu : Measure Seed) [IsProbabilityMeasure nu]
    (loss : Seed → Bank → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h0 : ∀ seed bank, 0 ≤ loss seed bank)
    (hmean : ∀ seed, c ≤ uniformMean (loss seed)) :
    ENNReal.ofReal c ≤
      ∫⁻ seed, uniformENNMean (fun bank => ENNReal.ofReal (loss seed bank)) ∂nu := by
  rw [← randomizedLoss_eq_uniformENNMean nu loss h0]
  exact randomized_lower nu loss c hc hmean

#print axioms ofReal_uniformMean
#print axioms randomizedLoss_eq_uniformENNMean
#print axioms randomized_lower
#print axioms randomized_lower_weighted

end
end Gate148.RandomizedRisk
