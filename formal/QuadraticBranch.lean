import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Gate148: the identical scalar quadratic branch in Gate134 Section8.
The objective, derivative and trajectory are actual definitions. Every
realized scalar step sequence satisfies the ORIGINAL cap eta<=1/L.
Output weights may depend on the entire realized trajectory. No noise,
order independence, static weights, or product lower bound is assumed.
All divisions involving T or n are explicitly real. Root alone compiles.
-/
namespace Gate148.QuadraticBranch
noncomputable section
open scoped BigOperators

def curvature (T : ℕ) (L : ℝ) : ℝ := L / (2 * (T : ℝ))
def objective (T : ℕ) (L x : ℝ) : ℝ := curvature T L * x ^ 2 / 2
def gradient (T : ℕ) (L x : ℝ) : ℝ := curvature T L * x

def component {n : ℕ} (T : ℕ) (L : ℝ) (_i : Fin n) (x : ℝ) : ℝ :=
  objective T L x

def componentGradient {n : ℕ} (T : ℕ) (L : ℝ) (_i : Fin n) (x : ℝ) : ℝ :=
  gradient T L x

theorem curvature_pos (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L) :
    0 < curvature T L := by
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  unfold curvature
  positivity

theorem curvature_le_L (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L) :
    curvature T L ≤ L := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  unfold curvature
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (T : ℝ))).2
  nlinarith

theorem objective_hasDerivAt (T : ℕ) (L x : ℝ) :
    HasDerivAt (objective T L) (gradient T L x) x := by
  have hh := (((hasDerivAt_id' x).fun_pow 2).const_mul (curvature T L)).div_const 2
  convert hh using 1 <;> simp [objective, gradient] <;> ring

theorem component_hasDerivAt {n : ℕ} (T : ℕ) (L : ℝ) (i : Fin n) (x : ℝ) :
    HasDerivAt (component T L i) (componentGradient T L i x) x :=
  objective_hasDerivAt T L x

theorem objective_convex (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L) :
    ConvexOn ℝ Set.univ (objective T L) := by
  have hlam := (curvature_pos T L hT hL).le
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy c d hc hd hcd
  change objective T L (c * x + d * y) ≤ c * objective T L x + d * objective T L y
  have hc' : c = 1 - d := by linarith
  have hid : c * objective T L x + d * objective T L y -
      objective T L (c * x + d * y) = curvature T L * c * d * (x - y) ^ 2 / 2 := by
    rw [hc']
    unfold objective
    ring
  have hnonneg : 0 ≤ curvature T L * c * d * (x - y) ^ 2 / 2 := by positivity
  linarith

theorem gradient_L_lipschitz (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L) :
    LipschitzWith ⟨L, hL.le⟩ (gradient T L) := by
  have hlam := (curvature_pos T L hT hL).le
  have hcap := curvature_le_L T L hT hL
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |curvature T L * x - curvature T L * y| ≤ L * |x - y|
  rw [← mul_sub, abs_mul, abs_of_nonneg hlam]
  exact mul_le_mul_of_nonneg_right hcap (abs_nonneg _)

theorem component_convex {n : ℕ} (T : ℕ) (L : ℝ) (i : Fin n)
    (hT : 1 ≤ T) (hL : 0 < L) : ConvexOn ℝ Set.univ (component T L i) :=
  objective_convex T L hT hL

theorem componentGradient_L_lipschitz {n : ℕ} (T : ℕ) (L : ℝ) (i : Fin n)
    (hT : 1 ≤ T) (hL : 0 < L) :
    LipschitzWith ⟨L, hL.le⟩ (componentGradient T L i) :=
  gradient_L_lipschitz T L hT hL

@[simp] theorem objective_zero (T : ℕ) (L : ℝ) : objective T L 0 = 0 := by
  simp [objective]

@[simp] theorem gradient_zero (T : ℕ) (L : ℝ) : gradient T L 0 = 0 := by
  simp [gradient]

theorem objective_nonneg (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L) (x : ℝ) :
    0 ≤ objective T L x := by
  have hlam := (curvature_pos T L hT hL).le
  unfold objective
  positivity

theorem minimized_at_zero (T : ℕ) (L : ℝ) (hT : 1 ≤ T) (hL : 0 < L) :
    ∀ x : ℝ, objective T L 0 ≤ objective T L x := by
  intro x
  rw [objective_zero]
  exact objective_nonneg T L hT hL x

theorem component_mean {n : ℕ} (hn : 0 < n) (T : ℕ) (L x : ℝ) :
    (∑ i : Fin n, component T L i x) / (n : ℝ) = objective T L x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [component, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hn0

theorem variance_zero (n T : ℕ) (L : ℝ) :
    (∑ i : Fin n, ‖componentGradient T L i 0‖ ^ 2) / (n : ℝ) = 0 := by
  simp [componentGradient, gradient]

theorem variance_le (n T : ℕ) (L sigma : ℝ) :
    (∑ i : Fin n, ‖componentGradient T L i 0‖ ^ 2) / (n : ℝ) ≤ sigma ^ 2 := by
  rw [variance_zero]
  exact sq_nonneg sigma

theorem initial_distance (D : ℝ) (hD : 0 ≤ D) : dist D (0 : ℝ) = D := by
  simp [Real.dist_eq, abs_of_nonneg hD]

def trajectory (T : ℕ) (L D : ℝ) (eta : ℕ → ℝ) : ℕ → ℝ
  | 0 => D
  | k + 1 => (1 - curvature T L * eta k) * trajectory T L D eta k

/-- This recurrence is exactly the actual scalar component-gradient update. -/
theorem actual_gradient_step {n : ℕ} (T : ℕ) (L D : ℝ) (eta : ℕ → ℝ)
    (k : ℕ) (i : Fin n) :
    trajectory T L D eta (k + 1) = trajectory T L D eta k -
      eta k * componentGradient T L i (trajectory T L D eta k) := by
  simp only [trajectory, componentGradient, gradient]
  ring

theorem step_curvature_bound (T : ℕ) (L eta : ℝ) (hT : 1 ≤ T)
    (hL : 0 < L) (heta : 0 ≤ eta) (hetaL : eta ≤ 1 / L) :
    0 ≤ curvature T L * eta ∧ curvature T L * eta ≤ 1 / (2 * (T : ℝ)) := by
  have hlam := (curvature_pos T L hT hL).le
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  constructor
  · exact mul_nonneg hlam heta
  · calc
      curvature T L * eta ≤ curvature T L * (1 / L) := mul_le_mul_of_nonneg_left hetaL hlam
      _ = 1 / (2 * (T : ℝ)) := by
        unfold curvature
        field_simp [hL.ne', hT0]

theorem reciprocal_cap (T : ℕ) (hT : 1 ≤ T) :
    1 / (2 * (T : ℝ)) ≤ (1 : ℝ) / 2 := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (T : ℝ))).2
  linarith

theorem trajectory_bounds (T : ℕ) (L D : ℝ) (eta : ℕ → ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hD : 0 ≤ D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L) :
    ∀ t, t ≤ T → 0 ≤ trajectory T L D eta t ∧ trajectory T L D eta t ≤ D := by
  intro t
  induction t with
  | zero => intro ht; exact ⟨hD, le_rfl⟩
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hstep := step_curvature_bound T L (eta t) hT hL (heta t (by omega)).le (hetaL t (by omega))
      have hrecip := reciprocal_cap T hT
      have hrho : 0 ≤ 1 - curvature T L * eta t := by linarith
      have hdrop := mul_nonneg hstep.1 hprev.1
      change 0 ≤ (1 - curvature T L * eta t) * trajectory T L D eta t ∧
        (1 - curvature T L * eta t) * trajectory T L D eta t ≤ D
      exact ⟨mul_nonneg hrho hprev.1, by nlinarith [hprev.2]⟩

/-- A direct induction, not an assumed product inequality. -/
theorem trajectory_linear_lower (T : ℕ) (L D : ℝ) (eta : ℕ → ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hD : 0 ≤ D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L) :
    ∀ t, t ≤ T → D - (t : ℝ) * (D / (2 * (T : ℝ))) ≤ trajectory T L D eta t := by
  intro t
  induction t with
  | zero => intro ht; simp [trajectory]
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hx := trajectory_bounds T L D eta hT hL hD heta hetaL t (by omega)
      have hstep := step_curvature_bound T L (eta t) hT hL (heta t (by omega)).le (hetaL t (by omega))
      have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      have hdrop : (curvature T L * eta t) * trajectory T L D eta t ≤ D / (2 * (T : ℝ)) := by
        calc
          _ ≤ (1 / (2 * (T : ℝ))) * D :=
            mul_le_mul hstep.2 hx.2 hx.1 (by positivity)
          _ = _ := by ring
      change D - ((t + 1 : ℕ) : ℝ) * (D / (2 * (T : ℝ))) ≤
        (1 - curvature T L * eta t) * trajectory T L D eta t
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith

theorem all_states_half (T : ℕ) (L D : ℝ) (eta : ℕ → ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hD : 0 ≤ D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L) :
    ∀ t, t ≤ T → D / 2 ≤ trajectory T L D eta t := by
  intro t ht
  have hlin := trajectory_linear_lower T L D eta hT hL hD heta hetaL t ht
  have htR : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hm := mul_le_mul_of_nonneg_right htR (show 0 ≤ D / (2 * (T : ℝ)) by positivity)
  have hid : (T : ℝ) * (D / (2 * (T : ℝ))) = D / 2 := by
    field_simp [hT0.ne']
    <;> ring
  rw [hid] at hm
  linarith

def output (T : ℕ) (L D : ℝ) (eta weight : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (T + 1), weight i * trajectory T L D eta i

theorem output_half (T : ℕ) (L D : ℝ) (eta weight : ℕ → ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hD : 0 ≤ D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L)
    (hw : ∀ i, i ≤ T → 0 ≤ weight i)
    (hsum : ∑ i ∈ Finset.range (T + 1), weight i = 1) :
    D / 2 ≤ output T L D eta weight := by
  have hstates := all_states_half T L D eta hT hL hD heta hetaL
  calc
    D / 2 = (∑ i ∈ Finset.range (T + 1), weight i) * (D / 2) := by rw [hsum]; ring
    _ = ∑ i ∈ Finset.range (T + 1), weight i * (D / 2) := Finset.sum_mul ..
    _ ≤ output T L D eta weight := by
      apply Finset.sum_le_sum
      intro i hi
      have hit : i ≤ T := by have hh := Finset.mem_range.mp hi; omega
      exact mul_le_mul_of_nonneg_left (hstates i hit) (hw i hit)

/-- True objective loss at the actual scalar convex output. -/
theorem output_loss (T : ℕ) (L D : ℝ) (eta weight : ℕ → ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hD : 0 ≤ D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L)
    (hw : ∀ i, i ≤ T → 0 ≤ weight i)
    (hsum : ∑ i ∈ Finset.range (T + 1), weight i = 1) :
    L * D ^ 2 / (16 * (T : ℝ)) ≤
      objective T L (output T L D eta weight) - objective T L 0 := by
  have hout := output_half T L D eta weight hT hL hD heta hetaL hw hsum
  have hlam := (curvature_pos T L hT hL).le
  have hsq : D ^ 2 / 4 ≤ output T L D eta weight ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq hlam
  have hT0 : (T : ℝ) ≠ 0 := by exact_mod_cast (by omega : T ≠ 0)
  have hid : L * D ^ 2 / (16 * (T : ℝ)) = curvature T L * (D ^ 2 / 8) := by
    unfold curvature
    field_simp [hT0]
    <;> ring
  rw [hid, objective_zero, sub_zero]
  unfold objective
  nlinarith

/-- Direct all-n, all-K instance of the same actual branch. -/
theorem epoch_output_loss (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D : ℝ) (eta weight : ℕ → ℝ) (hL : 0 < L) (hD : 0 ≤ D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (hw : ∀ i, i ≤ n * K → 0 ≤ weight i)
    (hsum : ∑ i ∈ Finset.range (n * K + 1), weight i = 1) :
    L * D ^ 2 / (16 * ((n * K : ℕ) : ℝ)) ≤
      objective (n * K) L (output (n * K) L D eta weight) - objective (n * K) L 0 := by
  have hT : 1 ≤ n * K := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact output_loss (n * K) L D eta weight hT hL hD heta hetaL hw hsum

#print axioms objective_hasDerivAt
#print axioms component_hasDerivAt
#print axioms objective_convex
#print axioms gradient_L_lipschitz
#print axioms component_mean
#print axioms variance_zero
#print axioms minimized_at_zero
#print axioms initial_distance
#print axioms actual_gradient_step
#print axioms trajectory_bounds
#print axioms trajectory_linear_lower
#print axioms all_states_half
#print axioms output_loss
#print axioms epoch_output_loss
end
end Gate148.QuadraticBranch
