import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Actual projection onto a nonempty complete convex set. The projection
is chosen from Mathlib's Hilbert projection theorem, not supplied as a
desired gradient. All residual and Taylor estimates are proved from its
variational inequality. Root alone compiles this source. -/
namespace Gate147.ConvexProjection
noncomputable section
open scoped Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def projection (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hc hv x)

theorem projection_mem (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x : E) : projection K hne hc hv x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hc hv x)).1

theorem projection_minimum (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x : E) :
    ‖x - projection K hne hc hv x‖ = ⨅ w : K, ‖x - w‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hc hv x)).2

theorem projection_variational (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x w : E) (hw : w ∈ K) :
    inner ℝ (x - projection K hne hc hv x) (w - projection K hne hc hv x) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hv
    (projection_mem K hne hc hv x)).1 (projection_minimum K hne hc hv x) w hw

theorem projection_minimizes (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x w : E) (hw : w ∈ K) :
    ‖x - projection K hne hc hv x‖ ≤ ‖x - w‖ := by
  rw [projection_minimum K hne hc hv x]
  exact ciInf_le ⟨0, fun y hy => by
    obtain ⟨z, rfl⟩ := hy
    exact norm_nonneg (x - z)⟩ (⟨w, hw⟩ : K)

theorem projection_eq_of_variational (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x y : E) (hy : y ∈ K)
    (hvar : ∀ w ∈ K, inner ℝ (x - y) (w - y) ≤ 0) :
    projection K hne hc hv x = y := by
  let p := projection K hne hc hv x
  have h1 := projection_variational K hne hc hv x y hy
  have h2 := hvar p (projection_mem K hne hc hv x)
  have hid : inner ℝ (x - p) (y - p) + inner ℝ (x - y) (p - y) = ‖p - y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  change inner ℝ (x - p) (y - p) ≤ 0 at h1
  have hn : ‖p - y‖ = 0 := by nlinarith [sq_nonneg ‖p - y‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem projection_eq_self (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x : E) (hx : x ∈ K) :
    projection K hne hc hv x = x := by
  apply projection_eq_of_variational K hne hc hv x x hx
  intro w hw
  simp

def residual (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x : E) : E := x - projection K hne hc hv x

def halfSquaredDistance (K : Set E) (hne : K.Nonempty) (hc : IsComplete K)
    (hv : Convex ℝ K) (x : E) : ℝ := ‖residual K hne hc hv x‖ ^ 2 / 2

section Estimates
variable (K : Set E) (hne : K.Nonempty) (hc : IsComplete K) (hv : Convex ℝ K)
local notation "P" => projection K hne hc hv
local notation "R" => residual K hne hc hv
local notation "D" => halfSquaredDistance K hne hc hv

theorem residual_firm (x y : E) :
    ‖R x - R y‖ ^ 2 ≤ inner ℝ (R x - R y) (x - y) := by
  have h1 := projection_variational K hne hc hv x (P y) (projection_mem K hne hc hv y)
  have h2 := projection_variational K hne hc hv y (P x) (projection_mem K hne hc hv x)
  have hm : 0 ≤ inner ℝ (R x - R y) (P x - P y) := by
    unfold residual
    simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
    linarith
  have hid : x - y = (R x - R y) + (P x - P y) := by
    unfold residual
    abel
  rw [hid, inner_add_right, real_inner_self_eq_norm_sq]
  linarith

theorem residual_nonexpansive (x y : E) : ‖R x - R y‖ ≤ ‖x - y‖ := by
  have h := (residual_firm K hne hc hv x y).trans
    (real_inner_le_norm (R x - R y) (x - y))
  by_contra hnot
  have hlt : ‖x - y‖ < ‖R x - R y‖ := lt_of_not_ge hnot
  have hpos : 0 < ‖R x - R y‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  have hmul := mul_pos hpos (sub_pos.mpr hlt)
  nlinarith

theorem residual_lipschitz : LipschitzWith 1 R := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
    residual_nonexpansive K hne hc hv x y

theorem halfSquaredDistance_nonneg (x : E) : 0 ≤ D x := by
  unfold halfSquaredDistance
  positivity

theorem halfSquaredDistance_zero_of_mem (x : E) (hx : x ∈ K) : D x = 0 := by
  simp [halfSquaredDistance, residual, projection_eq_self K hne hc hv x hx]

theorem taylor_lower (x y : E) :
    0 ≤ D y - D x - inner ℝ (R x) (y - x) := by
  have hvar := projection_variational K hne hc hv x (P y) (projection_mem K hne hc hv y)
  have hid : R y = R x + ((y - x) - (P y - P x)) := by
    unfold residual
    abel
  have hex := norm_add_sq_real (R x) ((y - x) - (P y - P x))
  rw [← hid, inner_sub_right] at hex
  change inner ℝ (R x) (P y - P x) ≤ 0 at hvar
  unfold halfSquaredDistance
  nlinarith [sq_nonneg ‖(y - x) - (P y - P x)‖]

theorem taylor_upper (x y : E) :
    D y - D x - inner ℝ (R x) (y - x) ≤ ‖y - x‖ ^ 2 / 2 := by
  have hmin := projection_minimizes K hne hc hv y (P x) (projection_mem K hne hc hv x)
  have hsq : ‖R y‖ ^ 2 ≤ ‖y - P x‖ ^ 2 := by
    change ‖y - P y‖ ^ 2 ≤ ‖y - P x‖ ^ 2
    have hm := mul_nonneg (sub_nonneg.mpr hmin)
      (add_nonneg (norm_nonneg (y - P x)) (norm_nonneg (y - P y)))
    nlinarith
  have hid : y - P x = R x + (y - x) := by unfold residual; abel
  rw [hid, norm_add_sq_real] at hsq
  unfold halfSquaredDistance
  linarith

theorem taylor_abs (x y : E) :
    |D y - D x - inner ℝ (R x) (y - x)| ≤ ‖y - x‖ ^ 2 / 2 := by
  rw [abs_of_nonneg (taylor_lower K hne hc hv x y)]
  exact taylor_upper K hne hc hv x y

theorem halfSquaredDistance_convex : ConvexOn ℝ Set.univ D := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hx' := mul_nonneg ha (taylor_lower K hne hc hv z x)
  have hy' := mul_nonneg hb (taylor_lower K hne hc hv z y)
  have hvec : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = (a • x + b • y) - (a + b) • z := by
        simp only [smul_sub, add_smul]
        abel
      _ = 0 := by rw [hab, one_smul]; simp [z]
  have hlin : a * inner ℝ (R z) (x - z) + b * inner ℝ (R z) (y - z) = 0 := by
    have hh := congrArg (fun w => inner ℝ (R z) w) hvec
    simpa only [inner_add_right, inner_smul_right, inner_zero_right] using hh
  change D z ≤ a * D x + b * D y
  have hdz : a * D z + b * D z = D z := by
    rw [← add_mul, hab, one_mul]
  nlinarith

/- The exact gradient assertion is stated as a Frechet derivative to avoid
the unnecessary surjective-Riesz/Gradient.Basic import. -/
theorem halfSquaredDistance_hasFDerivAt (x : E) :
    HasFDerivAt D (innerSL ℝ (R x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [innerSL_apply_apply]
  apply Asymptotics.IsLittleO.of_bound
  intro c hcpos
  have hsmall : ∀ᶠ h : E in 𝓝 0, ‖h‖ < 2 * c := by
    have ht : Filter.Tendsto (fun h : E => ‖h‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.continuousAt : ContinuousAt (fun h : E => ‖h‖) 0).tendsto
    exact ht.eventually_lt_const (by linarith)
  filter_upwards [hsmall] with h hh
  have hbnd := taylor_abs K hne hc hv x (x + h)
  simp only [add_sub_cancel_left] at hbnd
  rw [Real.norm_eq_abs]
  have hmul : ‖h‖ ^ 2 / 2 ≤ c * ‖h‖ := by
    have hm := mul_le_mul_of_nonneg_right (le_of_lt hh) (norm_nonneg h)
    nlinarith
  exact hbnd.trans hmul

end Estimates

#print axioms projection_variational
#print axioms projection_eq_of_variational
#print axioms residual_lipschitz
#print axioms taylor_abs
#print axioms halfSquaredDistance_convex
#print axioms halfSquaredDistance_hasFDerivAt
end
end Gate147.ConvexProjection
