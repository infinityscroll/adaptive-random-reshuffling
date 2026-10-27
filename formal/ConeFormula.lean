import RealProduct
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! The actual cone on a genuine Euclidean scalar/fast product. The explicit
formula is asserted only for q>0, the reachable region of the construction. -/
namespace Gate147.ConeFormula
noncomputable section
open scoped InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

abbrev State (V : Type*) := WithLp 2 (ℝ × V)
def point (q : ℝ) (v : V) : State V := WithLp.toLp 2 (-q, v)
def cone (a : ℝ) : Set (State V) := {x | ‖x.snd‖ ≤ -a * x.fst}

theorem cone_nonempty (a : ℝ) : (cone (V := V) a).Nonempty := by
  refine ⟨0, ?_⟩
  simp [cone]

theorem cone_closed (a : ℝ) : IsClosed (cone (V := V) a) :=
  isClosed_le ((WithLp.continuous_snd 2 ℝ V).norm)
    (continuous_const.mul (WithLp.continuous_fst 2 ℝ V))

theorem cone_convex (a : ℝ) : Convex ℝ (cone (V := V) a) := by
  intro x hx y hy c d hc hd hcd
  change ‖(c • x + d • y).snd‖ ≤ -a * (c • x + d • y).fst
  simp only [WithLp.add_snd, WithLp.smul_snd, WithLp.add_fst,
    WithLp.smul_fst, smul_eq_mul]
  calc
    ‖c • x.snd + d • y.snd‖ ≤ ‖c • x.snd‖ + ‖d • y.snd‖ := norm_add_le _ _
    _ = c * ‖x.snd‖ + d * ‖y.snd‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hd]
    _ ≤ c * (-a * x.fst) + d * (-a * y.fst) :=
      add_le_add (mul_le_mul_of_nonneg_left hx hc) (mul_le_mul_of_nonneg_left hy hd)
    _ = -a * (c * x.fst + d * y.fst) := by ring

def qproject (a q R : ℝ) : ℝ := (q + a * R) / (1 + a ^ 2)
def radialResidual (a q R : ℝ) : ℝ := (R - a * q) / (1 + a ^ 2)
def outsidePoint (a q : ℝ) (v : V) : State V :=
  point (qproject a q ‖v‖) ((a * qproject a q ‖v‖ / ‖v‖) • v)

theorem denominator_pos (a : ℝ) : 0 < 1 + a ^ 2 := by positivity

theorem outside_radius_pos (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) (hout : a * q < ‖v‖) : 0 < ‖v‖ :=
  (mul_pos ha hq).trans hout

theorem outside_mem (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) (hout : a * q < ‖v‖) :
    outsidePoint a q v ∈ cone a := by
  have hr := outside_radius_pos a q v ha hq hout
  have hQ : 0 < qproject a q ‖v‖ := by unfold qproject; positivity
  have hk : 0 ≤ a * qproject a q ‖v‖ / ‖v‖ := by positivity
  change ‖(a * qproject a q ‖v‖ / ‖v‖) • v‖ ≤ -a * (-qproject a q ‖v‖)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hk, div_mul_cancel₀ _ (ne_of_gt hr)]
  linarith

theorem outside_residual (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) (hout : a * q < ‖v‖) :
    point q v - outsidePoint a q v =
      WithLp.toLp 2 (a * radialResidual a q ‖v‖,
        (radialResidual a q ‖v‖ / ‖v‖) • v) := by
  have hr := ne_of_gt (outside_radius_pos a q v ha hq hout)
  have hd := ne_of_gt (denominator_pos a)
  have hslow : -q - (-qproject a q ‖v‖) = a * radialResidual a q ‖v‖ := by
    unfold qproject radialResidual
    field_simp
    <;> ring
  have hfast : 1 - a * qproject a q ‖v‖ / ‖v‖ = radialResidual a q ‖v‖ / ‖v‖ := by
    unfold qproject radialResidual
    field_simp
    <;> ring
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact hslow
  · change v - (a * qproject a q ‖v‖ / ‖v‖) • v =
      (radialResidual a q ‖v‖ / ‖v‖) • v
    conv_lhs => lhs; rw [← one_smul ℝ v]
    rw [← sub_smul, hfast]

theorem outside_variational (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) (hout : a * q < ‖v‖) :
    ∀ w ∈ cone a, inner ℝ (point q v - outsidePoint a q v)
      (w - outsidePoint a q v) ≤ 0 := by
  intro w hw
  have hr := outside_radius_pos a q v ha hq hout
  have hd := ne_of_gt (denominator_pos a)
  have hc : 0 ≤ radialResidual a q ‖v‖ := by
    unfold radialResidual
    exact le_of_lt (div_pos (sub_pos.mpr hout) (denominator_pos a))
  have hi : inner ℝ v w.snd / ‖v‖ ≤ ‖w.snd‖ := by
    apply (div_le_iff₀ hr).2
    simpa only [mul_comm] using real_inner_le_norm v w.snd
  have hangle : a * w.fst + inner ℝ v w.snd / ‖v‖ ≤ 0 := by
    change ‖w.snd‖ ≤ -a * w.fst at hw
    linarith
  have hvalue : inner ℝ (point q v - outsidePoint a q v)
      (w - outsidePoint a q v) =
      radialResidual a q ‖v‖ * (a * w.fst + inner ℝ v w.snd / ‖v‖) := by
    have hreal (x y : ℝ) : inner ℝ x y = x * y := by
      simp [RCLike.inner_apply', mul_comm]
    rw [outside_residual a q v ha hq hout, Gate147.RealProduct.product_inner]
    change inner ℝ (a * radialResidual a q ‖v‖) (w.fst - (-qproject a q ‖v‖)) +
      inner ℝ ((radialResidual a q ‖v‖ / ‖v‖) • v)
        (w.snd - (a * qproject a q ‖v‖ / ‖v‖) • v) = _
    rw [hreal, real_inner_smul_left, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    field_simp [ne_of_gt hr]
    <;> ring
  rw [hvalue]
  exact mul_nonpos_of_nonneg_of_nonpos hc hangle

theorem outside_minimizes (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) (hout : a * q < ‖v‖) :
    ‖point q v - outsidePoint a q v‖ =
      ⨅ w : cone (V := V) a, ‖point q v - w.val‖ :=
  (norm_eq_iInf_iff_real_inner_le_zero (cone_convex a)
    (outside_mem a q v ha hq hout)).2 (outside_variational a q v ha hq hout)

theorem inside_mem (a q : ℝ) (v : V) (hin : ‖v‖ ≤ a * q) :
    point q v ∈ cone a := by simpa [cone,point] using hin

#print axioms cone_closed
#print axioms cone_convex
#print axioms outside_mem
#print axioms outside_residual
#print axioms outside_variational
#print axioms outside_minimizes
end
end Gate147.ConeFormula
