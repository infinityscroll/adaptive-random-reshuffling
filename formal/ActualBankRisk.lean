import ActualRetention
import FiniteRisk

/-!
Gate148: actual uniform-bank expected loss for arbitrary whole-bank-dependent
legal scalar-step and scalar-output selectors. The SAME actual certificate
is averaged using the proved permutation envelope mean. No independence
between selectors and the bank is required. The remaining scalar bound on
the explicitly derived certificate mean is a tuning condition, not a risk
or desired probabilistic conclusion assumed as input.

Arbitrary private-seed integration and the full zero-case/minimax assembly
are separate interfaces. Root alone compiles this source.
-/
namespace Gate148.ActualBankRisk
noncomputable section
open scoped BigOperators
open Gate146.LabeledBlocks Gate146.FixedPartitionBank
open Gate148.FiniteRisk

abbrev Bank (n K : ℕ) := Fin K → Equiv.Perm (Fin n)

def certificateMeanBound {n : ℕ} (P : Partition n) (K : ℕ)
    (L C b sigma A : ℝ) : ℝ :=
  C / L + 16 * C * A * (K : ℝ) * Real.sqrt (n : ℝ) / sigma +
    4 * C ^ 2 * Real.sqrt (P.count : ℝ) / (sigma * b) +
    C ^ 2 / (24 * sigma * b)

/-- The actual bank certificate mean, obtained from the exact proved
envelope expectation. Its constant terms are preserved, not dropped. -/
theorem actual_certificate_mean {n : ℕ} (hn : 2 ≤ n) (P : Partition n)
    (K : ℕ) (L C b sigma A : ℝ)
    (hC : 0 ≤ C) (hsigma : 0 < sigma) (hA : 0 ≤ A) :
    uniformMean (fun bank : Bank n K => ActualTrim.certificate P bank L C b sigma A) ≤
      certificateMeanBound P K L C b sigma A := by
  have hg : uniformMean (fun bank : Bank n K => partitionG P bank A) ≤
      16 * A * (K : ℝ) * Real.sqrt (n : ℝ) :=
    ActualCharge.actual_envelope_mean hn P K A hA
  have hf : (fun bank : Bank n K => ActualTrim.certificate P bank L C b sigma A) =
      (fun bank : Bank n K =>
        C / L + (C / sigma) * partitionG P bank A +
        4 * C ^ 2 * Real.sqrt (P.count : ℝ) / (sigma * b) +
        C ^ 2 / (24 * sigma * b)) := by
    funext bank
    rw [ActualTrim.certificate_expanded]
    ring
  rw [hf]
  simp only [uniformMean_add, uniformMean_const, uniformMean_mul]
  have hm := mul_le_mul_of_nonneg_left hg (div_nonneg hC (le_of_lt hsigma))
  calc
    _ ≤ C / L + (C / sigma) * (16 * A * (K : ℝ) * Real.sqrt (n : ℝ)) +
        4 * C ^ 2 * Real.sqrt (P.count : ℝ) / (sigma * b) +
        C ^ 2 / (24 * sigma * b) := by linarith
    _ = certificateMeanBound P K L C b sigma A := by
      unfold certificateMeanBound
      ring

def selectedLoss {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (ell mu a sigma D : ℝ) (eta weight : Bank n K → ℕ → ℝ)
    (bank : Bank n K) : ℝ :=
  ActualInstance.mean P mu ell a sigma
    (ActualRetention.output P hn bank ell mu a sigma D (eta bank) (weight bank)) -
    ActualInstance.mean P mu ell a sigma 0

/-- Nonnegativity is obtained from the actual mean's actual minimizer. -/
theorem selectedLoss_nonneg {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (ell mu a sigma D : ℝ) (eta weight : Bank n K → ℕ → ℝ)
    (hmu : 0 ≤ mu) (hell : 0 ≤ ell) (bank : Bank n K) :
    0 ≤ selectedLoss P hn ell mu a sigma D eta weight bank := by
  exact sub_nonneg.mpr (ActualInstance.mean_minimized_at_zero P hn2 mu ell a sigma hmu hell
    (ActualRetention.output P hn bank ell mu a sigma D (eta bank) (weight bank)))

/-- Actual positive-parameter cone expected loss. eta and weight are arbitrary
functions of the ENTIRE bank. The theorem quantifies over every such pair,
with only the original legal scalar-step/convex-output conditions. -/
theorem actual_expected_output_loss {n K : ℕ} (P : Partition n)
    (hn : 0 < n) (hn2 : 2 ≤ n) (L ell mu a sigma D : ℝ)
    (eta weight : Bank n K → ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ bank k, k < n * K → 0 < eta bank k)
    (hetaL : ∀ bank k, k < n * K → eta bank k ≤ 1 / L)
    (hw : ∀ bank i, i ≤ n * K → 0 ≤ weight bank i)
    (hsum : ∀ bank, ∑ i ∈ Finset.range (n * K + 1), weight bank i = 1)
    (b0 h A : ℝ) (hb0 : 0 < b0)
    (hb0def : b0 = ActualRetention.b ell a -
      2 * ActualRetention.C mu ell a D * ell * Real.sqrt (P.count : ℝ) / sigma)
    (hhdef : h = 120 * ActualRetention.C mu ell a D / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * ActualRetention.C mu ell a D / b0)
    (hscalar : certificateMeanBound P K L
      (ActualRetention.C mu ell a D) (ActualRetention.b ell a) sigma A ≤ D / 128) :
    mu * D ^ 2 / 16 ≤ uniformMean (selectedLoss P hn ell mu a sigma D eta weight) := by
  have hb := ActualRetention.b_pos ell a hell ha
  have hC := ActualRetention.C_pos mu ell a D hmu hell ha hD
  have hh : 0 < h := by rw [hhdef]; positivity
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hBmean := (actual_certificate_mean hn2 P K L
    (ActualRetention.C mu ell a D) (ActualRetention.b ell a) sigma A
    hC.le hsigma hA).trans hscalar
  refine cone_loss_from_bank_certificate
    (selectedLoss P hn ell mu a sigma D eta weight)
    (fun bank : Bank n K => ActualTrim.certificate P bank L
      (ActualRetention.C mu ell a D) (ActualRetention.b ell a) sigma A)
    mu D hmu.le hD ?_ hBmean ?_ ?_
  · intro bank
    exact ActualTrim.certificate_nonneg P bank L (ActualRetention.C mu ell a D)
      (ActualRetention.b ell a) sigma A hL hC.le hb hsigma hA
  · intro bank
    exact selectedLoss_nonneg P hn hn2 ell mu a sigma D eta weight hmu.le hell.le bank
  · intro bank hgood
    exact ActualRetention.good_bank_output_loss P hn hn2 bank L ell mu a sigma D
      (eta bank) (weight bank) hL hell hellL hmu hcap ha hsigma hD
      (heta bank) (hetaL bank) b0 h A hb0 hb0def hhdef hAdef hgood (hw bank) (hsum bank)

#print axioms actual_certificate_mean
#print axioms selectedLoss_nonneg
#print axioms actual_expected_output_loss
end
end Gate148.ActualBankRisk
