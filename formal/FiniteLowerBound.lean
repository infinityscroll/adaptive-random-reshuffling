import TunedActualRisk
import QuadraticBranch
import RateLoss

/-! Gate148: parameter-only choice between the two actual hard instances.
The result is over the actual finite uniform permutation bank and arbitrary
whole-bank-dependent legal selectors. It is a lower-bound assembly, not
the inherited upper, a full oracle-model/minimax wrapper or a priority claim. -/
namespace Gate148.FiniteLowerBound
noncomputable section
open scoped BigOperators
open Gate146.LabeledBlocks
open Gate148.FiniteRisk Gate148.ActualBankRisk Gate148.HardParameters Gate148.RateLoss

def LegalSelectors (n K : ℕ) (L : ℝ) (eta weight : Bank n K → ℕ → ℝ) : Prop :=
  (∀ bank k, k < n * K → 0 < eta bank k) ∧
  (∀ bank k, k < n * K → eta bank k ≤ 1 / L) ∧
  (∀ bank i, i ≤ n * K → 0 ≤ weight bank i) ∧
  (∀ bank, ∑ i ∈ Finset.range (n * K + 1), weight bank i = 1)

def quadraticLoss (n K : ℕ) (L D : ℝ) (eta weight : Bank n K → ℕ → ℝ)
    (bank : Bank n K) : ℝ :=
  QuadraticBranch.objective (n * K) L
    (QuadraticBranch.output (n * K) L D (eta bank) (weight bank)) -
  QuadraticBranch.objective (n * K) L 0

def coneLoss {n K : ℕ} (P : Partition n) (hn : 0 < n) (L D sigma : ℝ)
    (eta weight : Bank n K → ℕ → ℝ) : Bank n K → ℝ :=
  selectedLoss P hn (ell n K L D sigma) (mu n K L D sigma)
    (a n K L D sigma) sigma D eta weight

theorem quadratic_mean_lower {n K : ℕ} {L D : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 ≤ D)
    (eta weight : Bank n K → ℕ → ℝ) (hlegal : LegalSelectors n K L eta weight) :
    B0 n K L D / 16 ≤ uniformMean (quadraticLoss n K L D eta weight) := by
  obtain ⟨heta, hetaL, hw, hsum⟩ := hlegal
  have hp : ∀ bank : Bank n K,
      B0 n K L D / 16 ≤ quadraticLoss n K L D eta weight bank := by
    intro bank
    have h := QuadraticBranch.epoch_output_loss n K hn hK L D (eta bank) (weight bank)
      hL hD (heta bank) (hetaL bank) (hw bank) (hsum bank)
    have hid : L * D ^ 2 / (16 * ((n * K : ℕ) : ℝ)) = B0 n K L D / 16 := by
      simp only [B0, A0, Nat.cast_mul]
      ring
    rwa [hid] at h
  have hmean := uniformMean_mono (fun _ : Bank n K => B0 n K L D / 16)
    (quadraticLoss n K L D eta weight) hp
  rwa [uniformMean_const] at hmean

theorem cone_mean_lower {n K : ℕ} (P : Partition n) (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) {L D sigma : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma)
    (eta weight : Bank n K → ℕ → ℝ) (hlegal : LegalSelectors n K L eta weight) :
    M n K L D sigma / 262144 ≤ uniformMean (coneLoss P hn0 L D sigma eta weight) := by
  obtain ⟨heta, hetaL, hw, hsum⟩ := hlegal
  have h := Gate148.TunedActualRisk.actual_tuned_expected_output_loss P hn hK
    L D sigma hL hD hs eta weight heta hetaL hw hsum
  dsimp only at h
  rw [cone_constant hn hK hL hD hs] at h
  exact h

/-- One Boolean choice, depending on parameters only, works for every
allowed bank-dependent pair of scalar selectors. D=0 and sigma=0 select
the legal scalar quadratic and never invoke positive-parameter divisions.
The two real losses are losses at actual vector/scalar convex outputs. -/
theorem one_fixed_branch_uniform_lower {n K : ℕ} (P : Partition n) (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ)
    (hL : 0 < L) (hD : 0 ≤ D) (hs : 0 ≤ sigma) :
    ∃ chooseCone : Bool,
      (chooseCone = true → 0 < D ∧ 0 < sigma) ∧
      ∀ eta weight : Bank n K → ℕ → ℝ, LegalSelectors n K L eta weight →
        Psi n K L D sigma / 524288 ≤
          uniformMean (if chooseCone then coneLoss P hn0 L D sigma eta weight
            else quadraticLoss n K L D eta weight) := by
  have hB : 0 ≤ B0 n K L D := by unfold B0 A0; positivity
  by_cases hDz : D = 0
  · refine ⟨false, by simp, ?_⟩
    intro eta weight hlegal
    have hq := quadratic_mean_lower hn hK hL hD eta weight hlegal
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hDz, zero_distance]
    simp only [B0, A0, hDz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, zero_div] at hq
    simpa using hq
  · have hDp : 0 < D := lt_of_le_of_ne hD (Ne.symm hDz)
    by_cases hsz : sigma = 0
    · refine ⟨false, by simp, ?_⟩
      intro eta weight hlegal
      have hq := quadratic_mean_lower hn hK hL hD eta weight hlegal
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hsz, zero_noise hn hK hL.le]
      linarith
    · have hsp : 0 < sigma := lt_of_le_of_ne hs (Ne.symm hsz)
      have hrate := final_constant_comparison (A0 L D) (B0 n K L D)
        (min (N1 n K D sigma) (N2 n K L D sigma)) hB
      change Psi n K L D sigma / 524288 ≤
        max (B0 n K L D / 16) (M n K L D sigma / 262144) at hrate
      by_cases hchoose : B0 n K L D / 16 ≤ M n K L D sigma / 262144
      · refine ⟨true, fun _ => ⟨hDp, hsp⟩, ?_⟩
        intro eta weight hlegal
        have hc := cone_mean_lower P hn0 hn hK hL hDp hsp eta weight hlegal
        rw [max_eq_right hchoose] at hrate
        exact hrate.trans hc
      · refine ⟨false, by simp, ?_⟩
        intro eta weight hlegal
        have hq := quadratic_mean_lower hn hK hL hD eta weight hlegal
        rw [max_eq_left (le_of_not_ge hchoose)] at hrate
        exact hrate.trans hq

#print axioms quadratic_mean_lower
#print axioms cone_mean_lower
#print axioms one_fixed_branch_uniform_lower
end
end Gate148.FiniteLowerBound
