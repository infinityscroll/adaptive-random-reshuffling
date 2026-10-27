import RealProduct
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Actual base quadratic on the shared genuine L2 scalar/fast product.
No InnerProductSpace.Calculus/PiL2 import is used. The derivative follows
from an exact Taylor identity and an explicit quadratic remainder bound.
Root alone compiles this source.
-/
namespace Gate147.QuadraticField
noncomputable section
open scoped Topology InnerProductSpace
open Filter
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev State (V : Type*) := WithLp 2 (ℝ × V)

def quadratic (mu ell : ℝ) (x : State V) : ℝ :=
  mu * x.fst ^ 2 / 2 + ell * ‖x.snd‖ ^ 2 / 8

def baseGradient (mu ell : ℝ) (x : State V) : State V :=
  WithLp.toLp 2 (mu * x.fst, (ell / 4) • x.snd)

theorem quadratic_nonneg (mu ell : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell)
    (x : State V) : 0 ≤ quadratic mu ell x := by
  unfold quadratic
  positivity

theorem quadratic_zero (mu ell : ℝ) : quadratic (V := V) mu ell 0 = 0 := by
  simp [quadratic]

theorem product_square (x : State V) :
    ‖x‖ ^ 2 = x.fst ^ 2 + ‖x.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs]

/-- Exact second-order remainder, with no smoothness or convexity premise. -/
theorem quadratic_taylor (mu ell : ℝ) (x y : State V) :
    quadratic mu ell y - quadratic mu ell x -
      inner ℝ (baseGradient mu ell x) (y - x) = quadratic mu ell (y - x) := by
  simp only [quadratic, baseGradient, Gate147.RealProduct.product_inner,
    WithLp.toLp_fst, WithLp.toLp_snd, WithLp.sub_fst, WithLp.sub_snd,
    RCLike.inner_apply, conj_trivial, real_inner_smul_left, inner_sub_right,
    real_inner_self_eq_norm_sq, norm_sub_sq_real,
    real_inner_comm y.snd x.snd]
  ring

theorem quadratic_norm_bound (mu ell : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell)
    (x : State V) :
    quadratic mu ell x ≤ (mu / 2 + ell / 8) * ‖x‖ ^ 2 := by
  have hn := product_square x
  have hm := mul_nonneg hmu (sq_nonneg ‖x.snd‖)
  have he := mul_nonneg hell (sq_nonneg x.fst)
  rw [hn]
  unfold quadratic
  nlinarith

theorem quadratic_taylor_abs (mu ell : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell)
    (x y : State V) :
    |quadratic mu ell y - quadratic mu ell x -
      inner ℝ (baseGradient mu ell x) (y - x)| ≤
      (mu / 2 + ell / 8) * ‖y - x‖ ^ 2 := by
  rw [quadratic_taylor, abs_of_nonneg (quadratic_nonneg mu ell hmu hell _)]
  exact quadratic_norm_bound mu ell hmu hell _

/-- Actual Frechet derivative represented by the shared product inner
product. Positivity is used only for the elementary remainder estimate. -/
theorem quadratic_hasFDerivAt (mu ell : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell)
    (x : State V) :
    HasFDerivAt (quadratic (V := V) mu ell)
      (innerSL ℝ (baseGradient mu ell x)) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [innerSL_apply_apply]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  let C : ℝ := mu / 2 + ell / 8 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcC : 0 < c / C := div_pos hc hC
  have hsmall : ∀ᶠ h : State V in 𝓝 0, ‖h‖ < c / C := by
    have ht : Filter.Tendsto (fun h : State V => ‖h‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa using (continuous_norm.continuousAt :
        ContinuousAt (fun h : State V => ‖h‖) 0).tendsto
    exact ht.eventually_lt_const hcC
  filter_upwards [hsmall] with h hh
  have hb := quadratic_taylor_abs mu ell hmu hell x (x + h)
  simp only [add_sub_cancel_left] at hb
  rw [Real.norm_eq_abs]
  have hhC : ‖h‖ * C ≤ c := (le_div_iff₀ hC).mp (le_of_lt hh)
  have hm := mul_le_mul_of_nonneg_right hhC (norm_nonneg h)
  have hrem : (mu / 2 + ell / 8) * ‖h‖ ^ 2 ≤ c * ‖h‖ := by
    dsimp [C] at hm
    nlinarith [sq_nonneg ‖h‖]
  exact hb.trans hrem

/-- Convexity follows directly from the exact nonnegative remainder. -/
theorem quadratic_convex (mu ell : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell) :
    ConvexOn ℝ Set.univ (quadratic (V := V) mu ell) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hx0 : 0 ≤ quadratic mu ell x - quadratic mu ell z -
      inner ℝ (baseGradient mu ell z) (x - z) := by
    rw [quadratic_taylor]
    exact quadratic_nonneg mu ell hmu hell _
  have hy0 : 0 ≤ quadratic mu ell y - quadratic mu ell z -
      inner ℝ (baseGradient mu ell z) (y - z) := by
    rw [quadratic_taylor]
    exact quadratic_nonneg mu ell hmu hell _
  have hx' := mul_nonneg ha hx0
  have hy' := mul_nonneg hb hy0
  have hvec : a • (x - z) + b • (y - z) = 0 := by
    calc
      _ = (a • x + b • y) - (a + b) • z := by
        simp only [smul_sub, add_smul]
        abel
      _ = 0 := by rw [hab, one_smul]; simp [z]
  have hlin : a * inner ℝ (baseGradient mu ell z) (x - z) +
      b * inner ℝ (baseGradient mu ell z) (y - z) = 0 := by
    have hh := congrArg (fun w => inner ℝ (baseGradient mu ell z) w) hvec
    simpa only [inner_add_right, inner_smul_right, inner_zero_right] using hh
  change quadratic mu ell z ≤ a * quadratic mu ell x + b * quadratic mu ell y
  have hz : a * quadratic mu ell z + b * quadratic mu ell z = quadratic mu ell z := by
    rw [← add_mul, hab, one_mul]
  nlinarith

/-- The correct Euclidean operator norm bound for the diagonal base
Hessian; there is no factor-two loss from a max-product norm. -/
theorem baseGradient_norm_sub_le (mu ell : ℝ) (hmu : 0 ≤ mu)
    (hcap : mu ≤ ell / 4) (x y : State V) :
    ‖baseGradient mu ell x - baseGradient mu ell y‖ ≤ (ell / 4) * ‖x - y‖ := by
  have hell : 0 ≤ ell / 4 := hmu.trans hcap
  have hfst : (baseGradient mu ell x - baseGradient mu ell y).fst =
      mu * (x.fst - y.fst) := by
    simp only [baseGradient, WithLp.sub_fst, WithLp.toLp_fst]
    ring
  have hsnd : (baseGradient mu ell x - baseGradient mu ell y).snd =
      (ell / 4) • (x.snd - y.snd) := by
    simp only [baseGradient, WithLp.sub_snd, WithLp.toLp_snd, smul_sub]
  have hg := WithLp.prod_norm_sq_eq_of_L2 (baseGradient mu ell x - baseGradient mu ell y)
  rw [hfst, hsnd, norm_mul, norm_smul] at hg
  simp only [Real.norm_eq_abs, mul_pow, sq_abs] at hg
  have hd := product_square (x - y)
  simp only [WithLp.sub_fst, WithLp.sub_snd] at hd
  have hmu2 : mu ^ 2 ≤ (ell / 4) ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hmu2 (sq_nonneg (x.fst - y.fst))
  apply le_of_sq_le_sq ?_ (mul_nonneg hell (norm_nonneg _))
  rw [mul_pow]
  rw [hg, hd]
  nlinarith

theorem baseGradient_lipschitz (mu ell : ℝ) (hmu : 0 ≤ mu)
    (hcap : mu ≤ ell / 4) :
    LipschitzWith ⟨ell / 4, hmu.trans hcap⟩ (baseGradient (V := V) mu ell) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using baseGradient_norm_sub_le mu ell hmu hcap x y

#print axioms quadratic_taylor
#print axioms quadratic_hasFDerivAt
#print axioms quadratic_convex
#print axioms baseGradient_norm_sub_le
#print axioms baseGradient_lipschitz
end
end Gate147.QuadraticField
