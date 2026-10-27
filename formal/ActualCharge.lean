import ActualGradientTrajectory
import ActualAllNModel
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity




/-!
# Finite-interval paid auxiliary resets

Pinned source: Gate134, FULL-ORDER-ALL-PARAMETER-SIMPLEX-BLOCK-LOWER-HAND-PROPOSAL,
Sections 3--4, especially (11).

The auxiliary path resets at EVERY safe endpoint. This refines the removed-run
partition in the hand proof. Its outstanding budget pays each removed actual
increment once. No reset-charge bound is an assumption.

All arrays are indexed relative to an arbitrary finite interval [s,s+N).
No stochastic, adaptedness, independence, or actual-confinement assumption occurs.
-/

noncomputable section

open Finset

namespace Gate144.PaidReset

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def auxPath (safe : ℕ → Prop) [DecidablePred safe] (v : ℕ → V) : ℕ → V
  | 0 => if safe 0 then v 0 else 0
  | k + 1 => if safe (k + 1) then v (k + 1) else auxPath safe v k

def resetBudget (safe : ℕ → Prop) [DecidablePred safe]
    (cost : ℕ → ℝ) (initial : ℝ) : ℕ → ℝ
  | 0 => if safe 0 then 0 else initial
  | k + 1 => if safe (k + 1) then 0 else resetBudget safe cost initial k + cost k

theorem auxPath_of_safe (safe : ℕ → Prop) [DecidablePred safe]
    (v : ℕ → V) (k : ℕ) (hs : safe k) : auxPath safe v k = v k := by
  cases k <;> simp [auxPath, hs]

theorem resetBudget_of_safe (safe : ℕ → Prop) [DecidablePred safe]
    (cost : ℕ → ℝ) (initial : ℝ) (k : ℕ) (hs : safe k) :
    resetBudget safe cost initial k = 0 := by
  cases k <;> simp [resetBudget, hs]

theorem auxPath_bounded (safe : ℕ → Prop) [DecidablePred safe]
    (v : ℕ → V) (N : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hsafe : ∀ k ≤ N, safe k → ‖v k‖ ≤ A) :
    ∀ k ≤ N, ‖auxPath safe v k‖ ≤ A := by
  intro k
  induction k with
  | zero =>
      intro hk
      by_cases hs : safe 0
      · simpa [auxPath, hs] using hsafe 0 hk hs
      · simpa [auxPath, hs] using hA
  | succ k ih =>
      intro hk
      by_cases hs : safe (k + 1)
      · simpa [auxPath, hs] using hsafe (k + 1) hk hs
      · simpa [auxPath, hs] using ih (by omega)

theorem kept_endpoints (safe keep : ℕ → Prop)
    [DecidablePred safe] [DecidablePred keep]
    (v : ℕ → V) (N : ℕ)
    (hkeep : ∀ k < N, keep k → safe k ∧ safe (k + 1))
    (k : ℕ) (hk : k < N) (hkk : keep k) :
    auxPath safe v k = v k ∧ auxPath safe v (k + 1) = v (k + 1) := by
  exact ⟨auxPath_of_safe safe v k (hkeep k hk hkk).1,
    auxPath_of_safe safe v (k + 1) (hkeep k hk hkk).2⟩

theorem resetBudget_nonneg (safe : ℕ → Prop) [DecidablePred safe]
    (cost : ℕ → ℝ) (initial : ℝ) (N : ℕ)
    (hi : 0 ≤ initial) (hc : ∀ k < N, 0 ≤ cost k) :
    ∀ k ≤ N, 0 ≤ resetBudget safe cost initial k := by
  intro k
  induction k with
  | zero =>
      intro hk
      by_cases hs : safe 0 <;> simp [resetBudget, hs, hi]
  | succ k ih =>
      intro hk
      by_cases hs : safe (k + 1)
      · simp [resetBudget, hs]
      · simpa [resetBudget, hs] using add_nonneg (ih (by omega)) (hc k (by omega))

/-- The budget bounds the discrepancy against every dual test in the interval.
The test at a later reset may differ from every earlier current test. -/
theorem defect_le_budget (safe : ℕ → Prop) [DecidablePred safe]
    (v : ℕ → V) (φ : ℕ → V →ₗ[ℝ] ℝ) (cost : ℕ → ℝ)
    (initial : ℝ) (N : ℕ)
    (hinit : ∀ j < N, |φ j (v 0)| ≤ initial)
    (hinc : ∀ k < N, ∀ j < N, |φ j (v (k + 1) - v k)| ≤ cost k) :
    ∀ k ≤ N, ∀ j < N,
      |φ j (v k - auxPath safe v k)| ≤ resetBudget safe cost initial k := by
  intro k
  induction k with
  | zero =>
      intro hk j hj
      by_cases hs : safe 0
      · simp [auxPath, resetBudget, hs]
      · simpa [auxPath, resetBudget, hs] using hinit j hj
  | succ k ih =>
      intro hk j hj
      by_cases hs : safe (k + 1)
      · simp [auxPath, resetBudget, hs]
      · simp only [auxPath, resetBudget, if_neg hs]
        have heq : φ j (v (k + 1) - auxPath safe v k) =
            φ j (v (k + 1) - v k) + φ j (v k - auxPath safe v k) := by
          simp only [map_sub]
          ring
        rw [heq]
        calc
          |φ j (v (k + 1) - v k) + φ j (v k - auxPath safe v k)|
              ≤ |φ j (v (k + 1) - v k)| + |φ j (v k - auxPath safe v k)| :=
            abs_add_le _ _
          _ ≤ cost k + resetBudget safe cost initial k :=
            add_le_add (hinc k (by omega) j hj) (ih (by omega) j hj)
          _ = resetBudget safe cost initial k + cost k := add_comm _ _

/-- Every removed-step payment is paid by that step's cost and the decrease
of outstanding budget. Kept steps incur neither removed cost nor payment. -/
theorem payment_ledger (safe keep : ℕ → Prop)
    [DecidablePred safe] [DecidablePred keep]
    (v : ℕ → V) (φ : ℕ → V →ₗ[ℝ] ℝ) (cost : ℕ → ℝ)
    (initial : ℝ) (N : ℕ)
    (hkeep : ∀ k < N, keep k → safe k ∧ safe (k + 1))
    (hinit : ∀ j < N, |φ j (v 0)| ≤ initial)
    (hinc : ∀ k < N, ∀ j < N, |φ j (v (k + 1) - v k)| ≤ cost k)
    (k : ℕ) (hk : k < N) :
    (if keep k then 0 else |φ k (auxPath safe v (k + 1) - auxPath safe v k)|) +
        resetBudget safe cost initial (k + 1)
      ≤ resetBudget safe cost initial k + (if keep k then 0 else cost k) := by
  by_cases hkk : keep k
  · have hs := hkeep k hk hkk
    simp [hkk, resetBudget_of_safe safe cost initial k hs.1,
      resetBudget_of_safe safe cost initial (k + 1) hs.2]
  · by_cases hs : safe (k + 1)
    · rw [if_neg hkk, auxPath_of_safe safe v (k + 1) hs,
        resetBudget_of_safe safe cost initial (k + 1) hs, add_zero, if_neg hkk]
      have heq : φ k (v (k + 1) - auxPath safe v k) =
          φ k (v (k + 1) - v k) + φ k (v k - auxPath safe v k) := by
        simp only [map_sub]
        ring
      rw [heq]
      calc
        |φ k (v (k + 1) - v k) + φ k (v k - auxPath safe v k)|
            ≤ |φ k (v (k + 1) - v k)| + |φ k (v k - auxPath safe v k)| :=
          abs_add_le _ _
        _ ≤ cost k + resetBudget safe cost initial k :=
          add_le_add (hinc k hk k hk)
            (defect_le_budget safe v φ cost initial N hinit hinc k (by omega) k hk)
        _ = resetBudget safe cost initial k + cost k := add_comm _ _
    · simp [hkk, auxPath, resetBudget, hs]

/-- The removed-run charge is a theorem, not a hypothesis. It includes the
initial inherited vector and permits an unsafe final tail with no reset. -/
theorem removed_reset_payment_le (safe keep : ℕ → Prop)
    [DecidablePred safe] [DecidablePred keep]
    (v : ℕ → V) (φ : ℕ → V →ₗ[ℝ] ℝ) (cost : ℕ → ℝ)
    (initial : ℝ) (N : ℕ)
    (hi : 0 ≤ initial) (hc : ∀ k < N, 0 ≤ cost k)
    (hkeep : ∀ k < N, keep k → safe k ∧ safe (k + 1))
    (hinit : ∀ j < N, |φ j (v 0)| ≤ initial)
    (hinc : ∀ k < N, ∀ j < N, |φ j (v (k + 1) - v k)| ≤ cost k) :
    (∑ k ∈ range N,
      if keep k then 0 else |φ k (auxPath safe v (k + 1) - auxPath safe v k)|)
      ≤ initial + ∑ k ∈ range N, if keep k then 0 else cost k := by
  have hsum := Finset.sum_le_sum (fun k hk =>
    payment_ledger safe keep v φ cost initial N hkeep hinit hinc k (mem_range.mp hk))
  simp only [Finset.sum_add_distrib] at hsum
  have htel := Finset.sum_range_sub (resetBudget safe cost initial) N
  rw [Finset.sum_sub_distrib] at htel
  have hn := resetBudget_nonneg safe cost initial N hi hc N (le_refl N)
  have hzero : resetBudget safe cost initial 0 ≤ initial := by
    by_cases hs : safe 0 <;> simp [resetBudget, hs, hi]
  linarith

/-- Summation by parts for a changing linear test. -/
theorem dual_sum_by_parts (φ : ℕ → V →ₗ[ℝ] ℝ) (z : ℕ → V) (N : ℕ) :
    (∑ k ∈ range (N + 1), φ k (z k - z (k + 1))) =
      φ 0 (z 0) - φ N (z (N + 1)) +
        ∑ k ∈ range N, (φ (k + 1) - φ k) (z (k + 1)) := by
  induction N with
  | zero => simp [map_sub]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [map_sub, LinearMap.sub_apply]
      ring

/-- The finite kept-step chain. `hgeo` is the separate dual-table
summation-by-parts bound (source (8)); it is not a reset-charge premise.
The actual trajectory is unrestricted outside safe endpoints of kept steps. -/
theorem paid_reset_chain (safe keep : ℕ → Prop)
    [DecidablePred safe] [DecidablePred keep]
    (v : ℕ → V) (φ : ℕ → V →ₗ[ℝ] ℝ)
    (cost drift eta : ℕ → ℝ) (initial σ A G : ℝ) (N : ℕ)
    (hi : 0 ≤ initial) (hc : ∀ k < N, 0 ≤ cost k) (hA : 0 ≤ A)
    (hsafe : ∀ k ≤ N, safe k → ‖v k‖ ≤ A)
    (hkeep : ∀ k < N, keep k → safe k ∧ safe (k + 1))
    (hinit : ∀ j < N, |φ j (v 0)| ≤ initial)
    (hinc : ∀ k < N, ∀ j < N, |φ j (v (k + 1) - v k)| ≤ cost k)
    (hstep : ∀ k < N, keep k →
      σ * eta k ≤ φ k (v k - v (k + 1)) + drift k)
    (hgeo : ∀ z : ℕ → V, (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ range N, φ k (z k - z (k + 1))) ≤ G) :
    σ * (∑ k ∈ range N, if keep k then eta k else 0) ≤
      G + (∑ k ∈ range N, if keep k then drift k else 0) + initial +
        ∑ k ∈ range N, if keep k then 0 else cost k := by
  have hpoint : ∀ k < N,
      σ * (if keep k then eta k else 0) ≤
        φ k (auxPath safe v k - auxPath safe v (k + 1)) +
          (if keep k then drift k else 0) +
          (if keep k then 0 else
            |φ k (auxPath safe v (k + 1) - auxPath safe v k)|) := by
    intro k hk
    by_cases hkk : keep k
    · have hz := kept_endpoints safe keep v N hkeep k hk hkk
      simpa [hkk, hz.1, hz.2] using hstep k hk hkk
    · simp only [if_neg hkk, mul_zero, add_zero]
      have h := le_abs_self (φ k (auxPath safe v (k + 1) - auxPath safe v k))
      simp only [map_sub] at h ⊢
      linarith
  have hsum := Finset.sum_le_sum (fun k hk => hpoint k (mem_range.mp hk))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hg := hgeo (auxPath safe v) (auxPath_bounded safe v N A hA hsafe)
  have hp := removed_reset_payment_le safe keep v φ cost initial N hi hc hkeep hinit hinc
  linarith

/-- Scalar aggregation: the same drift charge is used once, whether a step
is kept or removed. This is the algebraic shape of source equation (11). -/
theorem paid_reset_chain_linear_cost (safe keep : ℕ → Prop)
    [DecidablePred safe] [DecidablePred keep]
    (v : ℕ → V) (φ : ℕ → V →ₗ[ℝ] ℝ)
    (eta radius : ℕ → ℝ) (initial σ A G U C : ℝ) (N : ℕ)
    (hi : 0 ≤ initial) (hA : 0 ≤ A)
    (hc : ∀ k < N, 0 ≤ U * σ * eta k + C * (eta k * radius k))
    (hsafe : ∀ k ≤ N, safe k → ‖v k‖ ≤ A)
    (hkeep : ∀ k < N, keep k → safe k ∧ safe (k + 1))
    (hinit : ∀ j < N, |φ j (v 0)| ≤ initial)
    (hinc : ∀ k < N, ∀ j < N,
      |φ j (v (k + 1) - v k)| ≤ U * σ * eta k + C * (eta k * radius k))
    (hstep : ∀ k < N, keep k →
      σ * eta k ≤ φ k (v k - v (k + 1)) + C * (eta k * radius k))
    (hgeo : ∀ z : ℕ → V, (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ range N, φ k (z k - z (k + 1))) ≤ G) :
    σ * (∑ k ∈ range N, if keep k then eta k else 0) ≤
      G + U * σ * (∑ k ∈ range N, if keep k then 0 else eta k) +
        C * (∑ k ∈ range N, eta k * radius k) + initial := by
  have h := paid_reset_chain safe keep v φ
    (fun k => U * σ * eta k + C * (eta k * radius k))
    (fun k => C * (eta k * radius k)) eta initial σ A G N
    hi hc hA hsafe hkeep hinit hinc hstep hgeo
  have halg :
      (∑ k ∈ range N, if keep k then C * (eta k * radius k) else 0) +
        (∑ k ∈ range N, if keep k then 0 else
          U * σ * eta k + C * (eta k * radius k)) =
      U * σ * (∑ k ∈ range N, if keep k then 0 else eta k) +
        C * (∑ k ∈ range N, eta k * radius k) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkk : keep k <;> simp [hkk]
  linarith

end Gate144.PaidReset

#print axioms Gate144.PaidReset.auxPath_bounded
#print axioms Gate144.PaidReset.removed_reset_payment_le
#print axioms Gate144.PaidReset.dual_sum_by_parts
#print axioms Gate144.PaidReset.paid_reset_chain_linear_cost


/-!
Gate134 Sections 2--4: actual affine updates imply the dual charges used in
PaidReset. The noise test bound is 4, not 4*sqrt(number of blocks). The
variable rroot stands for sqrt(number of blocks), separately instantiated.
The actual cone construction, drift bounds, and the dual table that supplies
these test bounds remain separate mathematical interfaces.
-/

namespace Gate144.ActualStep

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem drift_charge (d eta ell rroot R p : ℝ)
    (hd : 0 ≤ d) (heta : 0 ≤ eta) (hdell : 2 * d ≤ ell)
    (hrroot : 0 ≤ rroot) (hR : 0 ≤ R) (hp : |p| ≤ 4 * rroot * R) :
    d * eta * |p| ≤ 2 * ell * rroot * eta * R := by
  have h1 := mul_le_mul_of_nonneg_left hp (mul_nonneg hd heta)
  have h2 := mul_le_mul_of_nonneg_right hdell
    (show 0 ≤ 2 * rroot * eta * R by positivity)
  nlinarith

/-- Apply this with EVERY dual test j, even if the update index is k != j. -/
theorem actual_increment_charge (phi : V →ₗ[ℝ] ℝ) (v xi : V)
    (d eta ell rroot R sigma : ℝ)
    (hd : 0 ≤ d) (heta : 0 ≤ eta) (hdell : 2 * d ≤ ell)
    (hrroot : 0 ≤ rroot) (hR : 0 ≤ R) (hsigma : 0 ≤ sigma)
    (hv : |phi v| ≤ 4 * rroot * R) (hxi : |phi xi| ≤ 4) :
    |phi ((1 - d * eta) • v - (sigma * eta) • xi - v)| ≤
      4 * sigma * eta + 2 * ell * rroot * eta * R := by
  have heq : phi ((1 - d * eta) • v - (sigma * eta) • xi - v) =
      -(d * eta) * phi v - (sigma * eta) * phi xi := by
    simp only [map_sub, map_smul, smul_eq_mul]
    ring
  rw [heq]
  have htri := abs_add_le (-(d * eta) * phi v) (-((sigma * eta) * phi xi))
  simp only [← sub_eq_add_neg, abs_mul, abs_neg, abs_of_nonneg hd,
    abs_of_nonneg heta, abs_of_nonneg hsigma] at htri
  have hnoise := mul_le_mul_of_nonneg_left hxi (mul_nonneg hsigma heta)
  have hdrift := drift_charge d eta ell rroot R (phi v) hd heta hdell hrroot hR hv
  nlinarith

/-- The current table additionally has phi xi = 1. -/
theorem actual_kept_step_charge (phi : V →ₗ[ℝ] ℝ) (v xi : V)
    (d eta ell rroot R sigma : ℝ)
    (hd : 0 ≤ d) (heta : 0 ≤ eta) (hdell : 2 * d ≤ ell)
    (hrroot : 0 ≤ rroot) (hR : 0 ≤ R)
    (hv : |phi v| ≤ 4 * rroot * R) (hxi : phi xi = 1) :
    sigma * eta ≤
      phi (v - ((1 - d * eta) • v - (sigma * eta) • xi)) +
        2 * ell * rroot * eta * R := by
  have heq : phi (v - ((1 - d * eta) • v - (sigma * eta) • xi)) =
      d * eta * phi v + sigma * eta := by
    simp only [map_sub, map_smul, smul_eq_mul, hxi]
    ring
  rw [heq]
  have hp := mul_le_mul_of_nonneg_left (neg_le_abs (phi v)) (mul_nonneg hd heta)
  have hdrift := drift_charge d eta ell rroot R (phi v) hd heta hdell hrroot hR hv
  nlinarith

#print axioms drift_charge
#print axioms actual_increment_charge
#print axioms actual_kept_step_charge

end Gate144.ActualStep


/-!
# Gate144: Section5 interval-charge assembly, with explicit upstream premises

Pinned source: Gate134/weighted-charge/
FULL-ORDER-ALL-PARAMETER-SIMPLEX-BLOCK-LOWER-HAND-PROPOSAL.txt
SHA256 0db4cc4b93f12706e13953358a2117f0e45bfc055d561b3fa3ac729e1cb68685.

SOURCE-ONLY preparation. Root alone may compile.

The N updates below are a reindexing of ANY realized finite interval.
R 0 and R N are its actual state radii, not artificial reset radii.
C = H*D and rootBlocks = sqrt(number of simplex blocks).
No upper bound on h, no confinement hypothesis and no independence or
stopping-time assumption occur.

* kept / large / smallRemoved are the actual Section4--5 partition.
* removed_partition proves it is exact, including equality eta=h.
* small_removed_pre_radius derives the actual pre-state threshold from
  radial growth and the unsafe endpoint definition.
* squared_energy_sum telescopes the explicit ONE-STEP energy premise,
  retaining the signed R_N^2 - R_0^2 endpoint term.
* large_step_charge and small_removed_charge prove (15) and the following
  small-removed charge with the original coefficients.
* interval_charge assembles (11)->(16). Paid-reset estimate (11), actual
  radial growth and the one-step energy inequality remain EXPLICIT PREMISES.
  This file does not establish cone projection, the paid-reset construction,
  positivity/tuning of b0 from parameters, permutation expectations,
  endpoint trimming, probability, objective or minimax consequences.

The radius identity is A=sigma*h+10*C/b0; together with
h=120*C/(b0*sigma) it is the source's A=130*C/b0.
-/

namespace Gate144.IntervalCharge

def stepSum (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, f i

noncomputable def selectedSum (f : ℕ → ℝ) (N : ℕ) (P : ℕ → Prop) : ℝ := by
  classical
  exact stepSum (fun i => if P i then f i else 0) N

def kept (eta R : ℕ → ℝ) (h A : ℝ) (i : ℕ) : Prop :=
  eta i < h ∧ R i ≤ A ∧ R (i + 1) ≤ A

def large (eta : ℕ → ℝ) (h : ℝ) (i : ℕ) : Prop := h ≤ eta i

def smallRemoved (eta R : ℕ → ℝ) (h A : ℝ) (i : ℕ) : Prop :=
  eta i < h ∧ (A < R i ∨ A < R (i + 1))

theorem selected_add_complement (f : ℕ → ℝ) (N : ℕ) (P : ℕ → Prop) :
    selectedSum f N P + selectedSum f N (fun i => ¬ P i) = stepSum f N := by
  classical
  unfold selectedSum stepSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hp : P i <;> simp [hp]

theorem selectedSum_le (f : ℕ → ℝ) (N : ℕ) (P : ℕ → Prop)
    (hf : ∀ i, i < N → 0 ≤ f i) :
    selectedSum f N P ≤ stepSum f N := by
  classical
  unfold selectedSum stepSum
  apply Finset.sum_le_sum
  intro i hi
  have hiN := Finset.mem_range.mp hi
  by_cases hp : P i
  · simp [hp]
  · simpa [hp] using hf i hiN

theorem removed_partition (eta R : ℕ → ℝ) (N : ℕ) (h A : ℝ) :
    selectedSum eta N (fun i => ¬ kept eta R h A i) =
      selectedSum eta N (large eta h) +
        selectedSum eta N (smallRemoved eta R h A) := by
  classical
  unfold selectedSum stepSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hl : h ≤ eta i
  · have hnk : ¬ kept eta R h A i := by
      intro hk
      exact (not_lt_of_ge hl) hk.1
    have hns : ¬ smallRemoved eta R h A i := by
      intro hs
      exact (not_lt_of_ge hl) hs.1
    simp [large, hl, hnk, hns]
  · have hel : eta i < h := lt_of_not_ge hl
    by_cases hk : kept eta R h A i
    · have hns : ¬ smallRemoved eta R h A i := by
        rintro ⟨he, hu | hu⟩
        · exact (not_lt_of_ge hk.2.1) hu
        · exact (not_lt_of_ge hk.2.2) hu
      simp [large, hl, hk, hns]
    · have hu : A < R i ∨ A < R (i + 1) := by
        by_cases hri : R i ≤ A
        · right
          by_contra hn
          exact hk ⟨hel, hri, le_of_not_gt hn⟩
        · exact Or.inl (lt_of_not_ge hri)
      have hs : smallRemoved eta R h A i := ⟨hel, hu⟩
      simp [large, hl, hk, hs]

theorem small_removed_pre_radius (eta R : ℕ → ℝ)
    (h A sigma C b0 : ℝ) (i : ℕ)
    (hsigma : 0 < sigma) (hh : 0 < h) (hb0 : 0 < b0)
    (hA : A = sigma * h + 10 * C / b0)
    (hgrowth : R (i + 1) ≤ R i + sigma * eta i)
    (hsmall : smallRemoved eta R h A i) :
    10 * C / b0 < R i := by
  have hsig : 0 < sigma * h := mul_pos hsigma hh
  have hstep : sigma * eta i < sigma * h :=
    mul_lt_mul_of_pos_left hsmall.1 hsigma
  rcases hsmall.2 with hpre | hpost
  · rw [hA] at hpre
    linarith
  · rw [hA] at hpost
    linarith

/-- The arbitrary-interval energy sum retains both actual endpoint states. -/
theorem squared_energy_sum (eta R : ℕ → ℝ) (sigma : ℝ) :
    ∀ N,
      (∀ i, i < N →
        sigma ^ 2 * (eta i) ^ 2 ≤
          (R (i + 1)) ^ 2 - (R i) ^ 2 + 6 * sigma * (eta i * R i)) →
      sigma ^ 2 * stepSum (fun i => (eta i) ^ 2) N ≤
        (R N) ^ 2 - (R 0) ^ 2 + 6 * sigma * stepSum (fun i => eta i * R i) N := by
  intro N
  induction N with
  | zero =>
      intro he
      simp [stepSum]
  | succ N ih =>
      intro he
      have hp := ih (fun i hi => he i (by omega))
      have hn := he N (by omega)
      simp only [stepSum, Finset.sum_range_succ] at hp ⊢
      nlinarith

theorem large_mass_energy (eta : ℕ → ℝ) (N : ℕ) (h : ℝ)
    (heta : ∀ i, i < N → 0 ≤ eta i) :
    h * selectedSum eta N (large eta h) ≤
      stepSum (fun i => (eta i) ^ 2) N := by
  classical
  unfold selectedSum stepSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have he := heta i (Finset.mem_range.mp hi)
  by_cases hl : large eta h i
  · have hh : h ≤ eta i := hl
    simp only [if_pos hl]
    nlinarith
  · simp only [if_neg hl, mul_zero]
    exact sq_nonneg (eta i)

theorem large_step_charge (eta R : ℕ → ℝ) (N : ℕ)
    (C b0 sigma h : ℝ)
    (hC : 0 < C) (hb0 : 0 < b0) (hsigma : 0 < sigma)
    (hh : h = 120 * C / (b0 * sigma))
    (heta : ∀ i, i < N → 0 ≤ eta i)
    (henergy : ∀ i, i < N →
      sigma ^ 2 * (eta i) ^ 2 ≤
        (R (i + 1)) ^ 2 - (R i) ^ 2 + 6 * sigma * (eta i * R i)) :
    5 * C * selectedSum eta N (large eta h) ≤
      b0 / (24 * sigma) * ((R N) ^ 2 - (R 0) ^ 2) +
        (b0 / 4) * stepSum (fun i => eta i * R i) N := by
  have hm := large_mass_energy eta N h heta
  have he := squared_energy_sum eta R sigma N henergy
  have hk : 0 ≤ b0 / (24 * sigma) :=
    div_nonneg (le_of_lt hb0) (by positivity)
  have hks : 0 ≤ (b0 / (24 * sigma)) * sigma ^ 2 :=
    mul_nonneg hk (sq_nonneg sigma)
  have hcoef : (b0 / (24 * sigma)) * sigma ^ 2 * h = 5 * C := by
    rw [hh]
    field_simp [ne_of_gt hb0, ne_of_gt hsigma]
    <;> ring
  calc
    5 * C * selectedSum eta N (large eta h) =
        ((b0 / (24 * sigma)) * sigma ^ 2) *
          (h * selectedSum eta N (large eta h)) := by rw [← hcoef]; ring
    _ ≤ ((b0 / (24 * sigma)) * sigma ^ 2) *
        stepSum (fun i => (eta i) ^ 2) N :=
      mul_le_mul_of_nonneg_left hm hks
    _ = (b0 / (24 * sigma)) *
        (sigma ^ 2 * stepSum (fun i => (eta i) ^ 2) N) := by ring
    _ ≤ (b0 / (24 * sigma)) *
        ((R N) ^ 2 - (R 0) ^ 2 + 6 * sigma * stepSum (fun i => eta i * R i) N) :=
      mul_le_mul_of_nonneg_left he hk
    _ = b0 / (24 * sigma) * ((R N) ^ 2 - (R 0) ^ 2) +
        (b0 / 4) * stepSum (fun i => eta i * R i) N := by
      field_simp [ne_of_gt hsigma]
      <;> ring

theorem small_removed_charge (eta R : ℕ → ℝ) (N : ℕ)
    (C b0 sigma h A : ℝ)
    (hb0 : 0 < b0) (hsigma : 0 < sigma) (hh : 0 < h)
    (hA : A = sigma * h + 10 * C / b0)
    (heta : ∀ i, i < N → 0 ≤ eta i)
    (hgrowth : ∀ i, i < N → R (i + 1) ≤ R i + sigma * eta i) :
    5 * C * selectedSum eta N (smallRemoved eta R h A) ≤
      (b0 / 2) * selectedSum (fun i => eta i * R i) N (smallRemoved eta R h A) := by
  classical
  unfold selectedSum stepSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hiN := Finset.mem_range.mp hi
  by_cases hs : smallRemoved eta R h A i
  · have hr := small_removed_pre_radius eta R h A sigma C b0 i
      hsigma hh hb0 hA (hgrowth i hiN) hs
    have hr' : 10 * C < R i * b0 := (div_lt_iff₀ hb0).1 hr
    have hbase : 5 * C ≤ (b0 / 2) * R i := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hbase (heta i hiN)
    simp only [if_pos hs]
    nlinarith
  · simp only [if_neg hs, mul_zero, le_refl]

/--
Exact Section5 assembly. The paid-reset premise is (11), with C=H*D and
rootBlocks=sqrt(r). One-step energy and radial growth are separately explicit.
The theorem applies also when h exceeds every allowed step, and to N=0.
-/
theorem interval_charge (eta R : ℕ → ℝ) (N : ℕ)
    (C b b0 sigma ell rootBlocks G h A : ℝ)
    (hC : 0 < C) (hb : 0 < b) (hb0 : 0 < b0) (hsigma : 0 < sigma)
    (hell : 0 ≤ ell) (hroot : 0 ≤ rootBlocks)
    (hb0def : b0 = b - 2 * C * ell * rootBlocks / sigma)
    (hhdef : h = 120 * C / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * C / b0)
    (heta : ∀ i, i < N → 0 < eta i)
    (hR : ∀ i, i ≤ N → 0 ≤ R i)
    (hgrowth : ∀ i, i < N → R (i + 1) ≤ R i + sigma * eta i)
    (henergy : ∀ i, i < N →
      sigma ^ 2 * (eta i) ^ 2 ≤
        (R (i + 1)) ^ 2 - (R i) ^ 2 + 6 * sigma * (eta i * R i))
    (hpaid :
      selectedSum eta N (kept eta R h A) ≤
        G / sigma + 4 * selectedSum eta N (fun i => ¬ kept eta R h A i) +
          (2 * ell * rootBlocks / sigma) * stepSum (fun i => eta i * R i) N +
          4 * rootBlocks * R 0 / sigma) :
    C * stepSum eta N - b * stepSum (fun i => eta i * R i) N ≤
      C * G / sigma + 4 * C * rootBlocks * R 0 / sigma +
        b0 * (R N) ^ 2 / (24 * sigma) := by
  have heta0 : ∀ i, i < N → 0 ≤ eta i :=
    fun i hi => le_of_lt (heta i hi)
  have hh : 0 < h := by
    rw [hhdef]
    exact div_pos (by positivity) (mul_pos hb0 hsigma)
  have hW0 : 0 ≤ stepSum (fun i => eta i * R i) N := by
    apply Finset.sum_nonneg
    intro i hi
    have hiN := Finset.mem_range.mp hi
    exact mul_nonneg (heta0 i hiN) (hR i (le_of_lt hiN))
  have hsplit := selected_add_complement eta N (kept eta R h A)
  have hpart := removed_partition eta R N h A
  have hlarge := large_step_charge eta R N C b0 sigma h
    hC hb0 hsigma hhdef heta0 henergy
  have hsmall := small_removed_charge eta R N C b0 sigma h A
    hb0 hsigma hh hAdef heta0 hgrowth
  have hsmallW := selectedSum_le (fun i => eta i * R i) N
    (smallRemoved eta R h A)
    (fun i hi => mul_nonneg (heta0 i hi) (hR i (le_of_lt hi)))
  have hsmall' :
      5 * C * selectedSum eta N (smallRemoved eta R h A) ≤
        (b0 / 2) * stepSum (fun i => eta i * R i) N := by
    exact hsmall.trans
      (mul_le_mul_of_nonneg_left hsmallW (by positivity))
  have hrem :
      5 * C * selectedSum eta N (fun i => ¬ kept eta R h A i) ≤
        b0 / (24 * sigma) * ((R N) ^ 2 - (R 0) ^ 2) +
          (3 * b0 / 4) * stepSum (fun i => eta i * R i) N := by
    rw [hpart]
    nlinarith
  have hpaidmul := mul_le_mul_of_nonneg_left hpaid (le_of_lt hC)
  have hassembly :
      C * stepSum eta N - b * stepSum (fun i => eta i * R i) N ≤
        C * G / sigma + 4 * C * rootBlocks * R 0 / sigma +
          5 * C * selectedSum eta N (fun i => ¬ kept eta R h A i) -
          b0 * stepSum (fun i => eta i * R i) N := by
    rw [← hsplit]
    rw [hb0def]
    simp only [div_eq_mul_inv] at hpaidmul ⊢
    nlinarith
  have hk : 0 ≤ b0 / (24 * sigma) := by positivity
  have hstart : 0 ≤ (b0 / (24 * sigma)) * (R 0) ^ 2 :=
    mul_nonneg hk (sq_nonneg (R 0))
  have hweighted : 0 ≤ b0 * stepSum (fun i => eta i * R i) N :=
    mul_nonneg (le_of_lt hb0) hW0
  have hend :
      (b0 / (24 * sigma)) * (R N) ^ 2 =
        b0 * (R N) ^ 2 / (24 * sigma) := by ring
  nlinarith

end Gate144.IntervalCharge

#print axioms Gate144.IntervalCharge.removed_partition
#print axioms Gate144.IntervalCharge.small_removed_pre_radius
#print axioms Gate144.IntervalCharge.squared_energy_sum
#print axioms Gate144.IntervalCharge.large_step_charge
#print axioms Gate144.IntervalCharge.small_removed_charge
#print axioms Gate144.IntervalCharge.interval_charge


/-!
This source fragment is compiled in DeterministicCore.lean after PaidReset
and ActualStep. It instantiates the reset lemma with actual affine updates,
including dual tests uniform over all j. The dual table and its variation
bound remain inputs. It is not the complete cone or minimax theorem.
-/

namespace Gate144.ActualPaidResetBridge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem actual_paid_reset (safe keep : ℕ → Prop)
    [DecidablePred safe] [DecidablePred keep]
    (v xi : ℕ → V) (phi : ℕ → V →ₗ[ℝ] ℝ)
    (eta d : ℕ → ℝ) (sigma ell rroot A G : ℝ) (N : ℕ)
    (hsigma : 0 ≤ sigma) (hell : 0 ≤ ell) (hrroot : 0 ≤ rroot)
    (hA : 0 ≤ A)
    (heta : ∀ k < N, 0 ≤ eta k)
    (hd : ∀ k < N, 0 ≤ d k)
    (hdell : ∀ k < N, 2 * d k ≤ ell)
    (hupdate : ∀ k < N,
      v (k + 1) = (1 - d k * eta k) • v k - (sigma * eta k) • xi k)
    (hsafe : ∀ k ≤ N, safe k → ‖v k‖ ≤ A)
    (hkeep : ∀ k < N, keep k → safe k ∧ safe (k + 1))
    (hphiv : ∀ k ≤ N, ∀ j < N, |phi j (v k)| ≤ 4 * rroot * ‖v k‖)
    (hnoise : ∀ k < N, ∀ j < N, |phi j (xi k)| ≤ 4)
    (hcurrent : ∀ k < N, phi k (xi k) = 1)
    (hgeo : ∀ z : ℕ → V, (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ Finset.range N, phi k (z k - z (k + 1))) ≤ G) :
    sigma * (∑ k ∈ Finset.range N, if keep k then eta k else 0) ≤
      G + 4 * sigma * (∑ k ∈ Finset.range N, if keep k then 0 else eta k) +
        (2 * ell * rroot) * (∑ k ∈ Finset.range N, eta k * ‖v k‖) +
        4 * rroot * ‖v 0‖ := by
  apply PaidReset.paid_reset_chain_linear_cost safe keep v phi eta
    (fun k => ‖v k‖) (4 * rroot * ‖v 0‖) sigma A G 4 (2 * ell * rroot) N
  · positivity
  · exact hA
  · intro k hk
    have he := heta k hk
    positivity
  · exact hsafe
  · exact hkeep
  · intro j hj
    exact hphiv 0 (Nat.zero_le N) j hj
  · intro k hk j hj
    rw [hupdate k hk]
    simpa only [mul_assoc] using
      ActualStep.actual_increment_charge (phi j) (v k) (xi k)
        (d k) (eta k) ell rroot ‖v k‖ sigma (hd k hk) (heta k hk)
        (hdell k hk) hrroot (norm_nonneg _) hsigma
        (hphiv k (Nat.le_of_lt hk) j hj) (hnoise k hk j hj)
  · intro k hk hkk
    rw [hupdate k hk]
    simpa only [mul_assoc] using
      ActualStep.actual_kept_step_charge (phi k) (v k) (xi k)
        (d k) (eta k) ell rroot ‖v k‖ sigma (hd k hk) (heta k hk)
        (hdell k hk) hrroot (norm_nonneg _)
        (hphiv k (Nat.le_of_lt hk) k hk) (hcurrent k hk)
  · exact hgeo

#print axioms actual_paid_reset

end Gate144.ActualPaidResetBridge

/-!
Compiled after the standalone modules. This connects actual updates and the
proved reset construction to source (16). Energy, drift/table bounds and
positive parameter relations remain explicit upstream interfaces.
-/

namespace Gate144.ActualIntervalBridge

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem radius_growth (v xi : V) (d eta sigma : ℝ)
    (hd : 0 ≤ d) (heta : 0 ≤ eta) (hsigma : 0 ≤ sigma)
    (hrho : 0 ≤ 1 - d * eta) (hxi : ‖xi‖ = 1) :
    ‖(1 - d * eta) • v - (sigma * eta) • xi‖ ≤ ‖v‖ + sigma * eta := by
  have h := norm_sub_le ((1 - d * eta) • v) ((sigma * eta) • xi)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrho,
    abs_of_nonneg (mul_nonneg hsigma heta), hxi, mul_one] at h
  nlinarith [mul_nonneg (mul_nonneg hd heta) (norm_nonneg v)]

theorem actual_interval_charge
    (v xi : ℕ → V) (phi : ℕ → V →ₗ[ℝ] ℝ) (eta d : ℕ → ℝ)
    (C b b0 sigma ell rroot G h A : ℝ) (N : ℕ)
    (hC : 0 < C) (hb : 0 < b) (hb0 : 0 < b0) (hsigma : 0 < sigma)
    (hell : 0 ≤ ell) (hrroot : 0 ≤ rroot)
    (hb0def : b0 = b - 2 * C * ell * rroot / sigma)
    (hhdef : h = 120 * C / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * C / b0)
    (heta : ∀ k < N, 0 < eta k)
    (hd : ∀ k < N, 0 ≤ d k)
    (hdell : ∀ k < N, 2 * d k ≤ ell)
    (hrho : ∀ k < N, 0 ≤ 1 - d k * eta k)
    (hupdate : ∀ k < N,
      v (k + 1) = (1 - d k * eta k) • v k - (sigma * eta k) • xi k)
    (hxi : ∀ k < N, ‖xi k‖ = 1)
    (hphiv : ∀ k ≤ N, ∀ j < N, |phi j (v k)| ≤ 4 * rroot * ‖v k‖)
    (hnoise : ∀ k < N, ∀ j < N, |phi j (xi k)| ≤ 4)
    (hcurrent : ∀ k < N, phi k (xi k) = 1)
    (hgeo : ∀ z : ℕ → V, (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ Finset.range N, phi k (z k - z (k + 1))) ≤ G)
    (henergy : ∀ k < N, sigma ^ 2 * eta k ^ 2 ≤
      ‖v (k + 1)‖ ^ 2 - ‖v k‖ ^ 2 + 6 * sigma * (eta k * ‖v k‖)) :
    C * IntervalCharge.stepSum eta N -
        b * IntervalCharge.stepSum (fun k => eta k * ‖v k‖) N ≤
      C * G / sigma + 4 * C * rroot * ‖v 0‖ / sigma +
        b0 * ‖v N‖ ^ 2 / (24 * sigma) := by
  classical
  have hh : 0 < h := by rw [hhdef]; positivity
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hp := ActualPaidResetBridge.actual_paid_reset
    (fun k => ‖v k‖ ≤ A) (IntervalCharge.kept eta (fun k => ‖v k‖) h A)
    v xi phi eta d sigma ell rroot A G N (le_of_lt hsigma) hell hrroot hA
    (fun k hk => le_of_lt (heta k hk)) hd hdell hupdate
    (fun k hk hs => hs) (fun k hk hkeep => ⟨hkeep.2.1, hkeep.2.2⟩)
    hphiv hnoise hcurrent hgeo
  have hmass :
      sigma * IntervalCharge.selectedSum eta N
          (IntervalCharge.kept eta (fun k => ‖v k‖) h A) ≤
        G + 4 * sigma * IntervalCharge.selectedSum eta N
          (fun k => ¬ IntervalCharge.kept eta (fun k => ‖v k‖) h A k) +
        (2 * ell * rroot) * IntervalCharge.stepSum (fun k => eta k * ‖v k‖) N +
        4 * rroot * ‖v 0‖ := by
    have hrem : IntervalCharge.selectedSum eta N
        (fun k => ¬ IntervalCharge.kept eta (fun k => ‖v k‖) h A k) =
        ∑ k ∈ Finset.range N,
          if IntervalCharge.kept eta (fun k => ‖v k‖) h A k then 0 else eta k := by
      unfold IntervalCharge.selectedSum IntervalCharge.stepSum
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkeep : IntervalCharge.kept eta (fun k => ‖v k‖) h A k
      · simp [hkeep]
      · simp [hkeep]
    rw [hrem]
    simpa only [IntervalCharge.selectedSum, IntervalCharge.stepSum] using hp
  have hpaid :
      IntervalCharge.selectedSum eta N
          (IntervalCharge.kept eta (fun k => ‖v k‖) h A) ≤
        G / sigma + 4 * IntervalCharge.selectedSum eta N
          (fun k => ¬ IntervalCharge.kept eta (fun k => ‖v k‖) h A k) +
        (2 * ell * rroot / sigma) * IntervalCharge.stepSum (fun k => eta k * ‖v k‖) N +
        4 * rroot * ‖v 0‖ / sigma := by
    apply le_of_mul_le_mul_left (a := sigma) ?_ hsigma
    convert hmass using 1 <;> field_simp [ne_of_gt hsigma] <;> ring
  apply IntervalCharge.interval_charge eta (fun k => ‖v k‖) N
    C b b0 sigma ell rroot G h A hC hb hb0 hsigma hell hrroot hb0def hhdef hAdef
    heta (fun k hk => norm_nonneg _) _ henergy hpaid
  intro k hk
  change ‖v (k + 1)‖ ≤ ‖v k‖ + sigma * eta k
  rw [hupdate k hk]
  exact radius_growth (v k) (xi k) (d k) (eta k) sigma
    (hd k hk) (le_of_lt (heta k hk)) (le_of_lt hsigma) (hrho k hk) (hxi k hk)

#print axioms radius_growth
#print axioms actual_interval_charge

end Gate144.ActualIntervalBridge

/-!
Gate148: instantiate the paid-reset and unrestricted interval estimates
with the ACTUAL same-bank cone trajectory and ACTUAL fixed-label tests.
Compile after accepted ActualBankTrajectory/ActualGradientTrajectory,
ActualAllNModel, and the exact Gate144 charge dependency (without copying
the duplicate ScalarEnergy declarations). Root alone invokes Lean.

No desired reset payment, energy, dual bound, or interval-charge conclusion
is an input. The remaining scalar threshold/parameter relations are shown
explicitly. All statements are pathwise, for every legal realized eta
sequence and every interval of the same bank, without independence.
-/
namespace Gate148.ActualCharge
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
open scoped BigOperators
open Gate146.LabeledBlocks Gate146.FastSpaceOffsets
open Gate146.ActualSequence Gate146.FixedPartitionBank
open Gate147.ActualBankTrajectory

def fastPath {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (t : ℕ) : fastSpace P.size :=
  (trajectory P hn bank ell mu a sigma D eta t).2

def slowPath {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (t : ℕ) : ℝ :=
  (trajectory P hn bank ell mu a sigma D eta t).1

def driftPath {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (t : ℕ) : ℝ :=
  Gate147.ConeTrajectory.drift ell a
    (slowPath P hn bank ell mu a sigma D eta t)
    ‖fastPath P hn bank ell mu a sigma D eta t‖

/-- The recurrence is obtained from the actual defined trajectory. -/
theorem fastPath_update {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (t : ℕ) :
    fastPath P hn bank ell mu a sigma D eta (t + 1) =
      (1 - driftPath P hn bank ell mu a sigma D eta t * eta t) •
        fastPath P hn bank ell mu a sigma D eta t -
      (sigma * eta t) • bankNoise P hn bank t := rfl

/-- Actual q positivity and the original 4 sigma/ell radius invariant. -/
theorem actual_state_bounds {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hcap : mu ≤ ell / 4) (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (t : ℕ) (ht : t ≤ n * K) :
    0 < slowPath P hn bank ell mu a sigma D eta t ∧
      ell * ‖fastPath P hn bank ell mu a sigma D eta t‖ ≤ 4 * sigma := by
  exact trajectory_bounds P hn bank L ell mu a sigma D eta hL hell hellL
    (by linarith) ha hsigma hD heta hetaL t ht

theorem actual_drift_bounds {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hcap : mu ≤ ell / 4) (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (t : ℕ) (ht : t < n * K) :
    0 ≤ driftPath P hn bank ell mu a sigma D eta t ∧
      2 * driftPath P hn bank ell mu a sigma D eta t ≤ ell ∧
      0 ≤ 1 - driftPath P hn bank ell mu a sigma D eta t * eta t := by
  have hb := actual_state_bounds P hn bank L ell mu a sigma D eta hL hell hellL
    hcap ha hsigma hD heta hetaL t (le_of_lt ht)
  have hd := Gate147.ConeTrajectory.drift_bounds ell a
    (slowPath P hn bank ell mu a sigma D eta t)
    ‖fastPath P hn bank ell mu a sigma D eta t‖ (le_of_lt hell) ha
    (le_of_lt hb.1) (norm_nonneg _)
  have hr := Gate147.ConeTrajectory.rho_bounds L ell a
    (slowPath P hn bank ell mu a sigma D eta t)
    ‖fastPath P hn bank ell mu a sigma D eta t‖ (eta t) hL hell hellL ha
    (le_of_lt hb.1) (norm_nonneg _) (le_of_lt (heta t ht)) (hetaL t ht)
  dsimp only [driftPath]
  exact ⟨by linarith [hd.1], by linarith [hd.2], by linarith [hr.1]⟩

/-- One-step energy is a corollary of the accepted actual signed interval
energy at length one. In particular, no energy bound is a new premise. -/
theorem actual_step_energy {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hcap : mu ≤ ell / 4) (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (t : ℕ) (ht : t < n * K) :
    sigma ^ 2 * eta t ^ 2 ≤
      ‖fastPath P hn bank ell mu a sigma D eta (t + 1)‖ ^ 2 -
      ‖fastPath P hn bank ell mu a sigma D eta t‖ ^ 2 +
      6 * sigma * (eta t * ‖fastPath P hn bank ell mu a sigma D eta t‖) := by
  have hh := trajectory_interval_energy P hn bank L ell mu a sigma D eta t 1
    hL hell hellL (by linarith) ha hsigma hD heta hetaL (by omega)
  simpa only [Finset.sum_range_one, Nat.add_zero, fastPath] using hh

/-- Actual (11), before division by sigma, on any interval [s,s+N).
Safe/keep are exactly the real endpoint tests. Auxiliary resets are the
proved Gate144 accounting construction, not changes to this trajectory. -/
theorem actual_paid_reset {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (bank : Fin K → Equiv.Perm (Fin n))
    (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (s N : ℕ) (hN : s + N ≤ n * K) (h A : ℝ) (hA : 0 ≤ A) :
    let v := fastPath P hn bank ell mu a sigma D eta
    let keep := Gate144.IntervalCharge.kept (fun k => eta (s + k))
      (fun k => ‖v (s + k)‖) h A
    sigma * (∑ k ∈ Finset.range N, if keep k then eta (s + k) else 0) ≤
      partitionG P bank A +
      4 * sigma * (∑ k ∈ Finset.range N, if keep k then 0 else eta (s + k)) +
      (2 * ell * Real.sqrt (P.count : ℝ)) *
        (∑ k ∈ Finset.range N, eta (s + k) * ‖v (s + k)‖) +
      4 * Real.sqrt (P.count : ℝ) * ‖v s‖ := by
  classical
  dsimp only
  refine Gate144.ActualPaidResetBridge.actual_paid_reset
    (fun k => ‖fastPath P hn bank ell mu a sigma D eta (s + k)‖ ≤ A)
    (Gate144.IntervalCharge.kept (fun k => eta (s + k))
      (fun k => ‖fastPath P hn bank ell mu a sigma D eta (s + k)‖) h A)
    (fun k => fastPath P hn bank ell mu a sigma D eta (s + k))
    (fun k => bankNoise P hn bank (s + k)) (fun j => fastTest P bank (s + j))
    (fun k => eta (s + k)) (fun k => driftPath P hn bank ell mu a sigma D eta (s + k))
    sigma ell (Real.sqrt (P.count : ℝ)) A (partitionG P bank A) N
    (le_of_lt hsigma) (le_of_lt hell) (Real.sqrt_nonneg _) hA
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    exact le_of_lt (heta (s + k) (by omega))
  · intro k hk
    exact (actual_drift_bounds P hn bank L ell mu a sigma D eta hL hell hellL
      hcap (le_of_lt ha) (le_of_lt hsigma) hD heta hetaL (s + k) (by omega)).1
  · intro k hk
    exact (actual_drift_bounds P hn bank L ell mu a sigma D eta hL hell hellL
      hcap (le_of_lt ha) (le_of_lt hsigma) hD heta hetaL (s + k) (by omega)).2.1
  · intro k hk
    simpa only [Nat.add_assoc] using fastPath_update P hn bank ell mu a sigma D eta (s + k)
  · intro k hk hsafe
    exact hsafe
  · intro k hk hkeep
    exact ⟨hkeep.2.1, hkeep.2.2⟩
  · intro k hk j hj
    exact actual_all_vector_bound P bank (s + j)
      (fastPath P hn bank ell mu a sigma D eta (s + k))
  · intro k hk j hj
    exact actual_all_label_bound P bank (s + j) (currentLabel hn bank (s + k))
  · intro k hk
    exact actual_current_pairing P hn bank (s + k)
  · exact actual_subspace_hgeo P hn2 bank s N A hA hN

/-- Actual (16), with the SAME fixed-bank G used by the exact finite-bank
expectation. All drift, radius, unit-noise, dual, geometry and energy inputs
are supplied by proved statements about this trajectory and labeled model.
Only the still-untuned scalar threshold relations are explicit premises. -/
theorem actual_interval_charge {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (bank : Fin K → Equiv.Perm (Fin n))
    (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (s N : ℕ) (hN : s + N ≤ n * K) (C b b0 h A : ℝ)
    (hC : 0 < C) (hb : 0 < b) (hb0 : 0 < b0)
    (hb0def : b0 = b - 2 * C * ell * Real.sqrt (P.count : ℝ) / sigma)
    (hhdef : h = 120 * C / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * C / b0) :
    C * Gate144.IntervalCharge.stepSum (fun k => eta (s + k)) N -
      b * Gate144.IntervalCharge.stepSum
        (fun k => eta (s + k) * ‖fastPath P hn bank ell mu a sigma D eta (s + k)‖) N ≤
      C * partitionG P bank A / sigma +
      4 * C * Real.sqrt (P.count : ℝ) * ‖fastPath P hn bank ell mu a sigma D eta s‖ / sigma +
      b0 * ‖fastPath P hn bank ell mu a sigma D eta (s + N)‖ ^ 2 / (24 * sigma) := by
  have hh : 0 < h := by rw [hhdef]; positivity
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  refine Gate144.ActualIntervalBridge.actual_interval_charge
    (fun k => fastPath P hn bank ell mu a sigma D eta (s + k))
    (fun k => bankNoise P hn bank (s + k)) (fun j => fastTest P bank (s + j))
    (fun k => eta (s + k)) (fun k => driftPath P hn bank ell mu a sigma D eta (s + k))
    C b b0 sigma ell (Real.sqrt (P.count : ℝ)) (partitionG P bank A) h A N
    hC hb hb0 hsigma (le_of_lt hell) (Real.sqrt_nonneg _) hb0def hhdef hAdef
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    exact heta (s + k) (by omega)
  · intro k hk
    exact (actual_drift_bounds P hn bank L ell mu a sigma D eta hL hell hellL
      hcap (le_of_lt ha) (le_of_lt hsigma) hD heta hetaL (s + k) (by omega)).1
  · intro k hk
    exact (actual_drift_bounds P hn bank L ell mu a sigma D eta hL hell hellL
      hcap (le_of_lt ha) (le_of_lt hsigma) hD heta hetaL (s + k) (by omega)).2.1
  · intro k hk
    exact (actual_drift_bounds P hn bank L ell mu a sigma D eta hL hell hellL
      hcap (le_of_lt ha) (le_of_lt hsigma) hD heta hetaL (s + k) (by omega)).2.2
  · intro k hk
    simpa only [Nat.add_assoc] using fastPath_update P hn bank ell mu a sigma D eta (s + k)
  · intro k hk
    exact bankNoise_unit P hn bank (s + k)
  · intro k hk j hj
    exact actual_all_vector_bound P bank (s + j)
      (fastPath P hn bank ell mu a sigma D eta (s + k))
  · intro k hk j hj
    exact actual_all_label_bound P bank (s + j) (currentLabel hn bank (s + k))
  · intro k hk
    exact actual_current_pairing P hn bank (s + k)
  · exact actual_subspace_hgeo P hn2 bank s N A hA hN
  · intro k hk
    simpa only [Nat.add_assoc] using actual_step_energy P hn bank
      L ell mu a sigma D eta hL hell hellL hcap (le_of_lt ha) (le_of_lt hsigma)
      hD heta hetaL (s + k) (by omega)

/-- The actual envelope in BOTH charge bounds has the already-proved
uniform finite-bank mean. This is not a policy-conditioned expectation. -/
theorem actual_envelope_mean {n : ℕ} (hn : 2 ≤ n) (P : Partition n)
    (K : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    (∑ bank : Fin K → Equiv.Perm (Fin n), partitionG P bank A) /
      (Fintype.card (Fin K → Equiv.Perm (Fin n)) : ℝ) ≤
      16 * A * (K : ℝ) * Real.sqrt (n : ℝ) :=
  partition_G_mean hn P K A hA

#print axioms fastPath_update
#print axioms actual_state_bounds
#print axioms actual_drift_bounds
#print axioms actual_step_energy
#print axioms actual_paid_reset
#print axioms actual_interval_charge
#print axioms actual_envelope_mean
end
end Gate148.ActualCharge