import ActualObjective

/-!
The actual complete-convex projection is identified with the explicit cone
formula.  The reachable formula is restricted to q > 0, but differentiability,
convexity and nonexpansiveness below are global statements.  In the inside case
(including radius zero and the cone boundary), the residual is exactly zero.
Root alone compiles this source.
-/
namespace Gate147.ConeAnalytic
noncomputable section
open scoped InnerProductSpace
open Gate147.ConeFormula
set_option maxHeartbeats 30000

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

def coneProjection (a : ℝ) (x : State V) : State V :=
  Gate147.ConvexProjection.projection (E := State V) (cone (V := V) a)
    (cone_nonempty (V := V) a) (ActualObjective.coneComplete (V := V) a)
    (cone_convex (V := V) a) x

def coneResidual (a : ℝ) (x : State V) : State V :=
  ActualObjective.coneResidual a x

def coneHalfDistance (a : ℝ) (x : State V) : ℝ :=
  ActualObjective.halfConeDistance a x

theorem coneResidual_eq (a : ℝ) (x : State V) :
    coneResidual a x = x - coneProjection a x := rfl

theorem coneHalfDistance_eq (a : ℝ) (x : State V) :
    coneHalfDistance a x = ‖coneResidual a x‖ ^ 2 / 2 := rfl

/-- This chosen projection really minimizes the distance to the actual cone. -/
theorem coneProjection_minimum (a : ℝ) (x : State V) :
    ‖x - coneProjection a x‖ = ⨅ w : cone (V := V) a, ‖x - w.val‖ :=
  Gate147.ConvexProjection.projection_minimum (E := State V) (cone (V := V) a)
    (cone_nonempty (V := V) a) (ActualObjective.coneComplete (V := V) a)
    (cone_convex (V := V) a) x

#check coneProjection_minimum

theorem coneProjection_outside (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) (hout : a * q < ‖v‖) :
    coneProjection a (point q v) = outsidePoint a q v := by
  exact Gate147.ConvexProjection.projection_eq_of_variational
    (E := State V) (cone (V := V) a) (cone_nonempty (V := V) a)
    (ActualObjective.coneComplete (V := V) a) (cone_convex (V := V) a)
    (point q v) (outsidePoint a q v) (outside_mem a q v ha hq hout)
    (outside_variational a q v ha hq hout)

theorem coneProjection_inside (a q : ℝ) (v : V) (hin : ‖v‖ ≤ a * q) :
    coneProjection a (point q v) = point q v :=
  Gate147.ConvexProjection.projection_eq_self
    (E := State V) (cone (V := V) a) (cone_nonempty (V := V) a)
    (ActualObjective.coneComplete (V := V) a) (cone_convex (V := V) a)
    (point q v) (inside_mem a q v hin)

#check coneProjection_inside

theorem coneResidual_outside (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) (hout : a * q < ‖v‖) :
    coneResidual a (point q v) =
      WithLp.toLp 2 (a * radialResidual a q ‖v‖,
        (radialResidual a q ‖v‖ / ‖v‖) • v) := by
  rw [coneResidual_eq, coneProjection_outside a q v ha hq hout]
  exact outside_residual a q v ha hq hout

theorem coneResidual_inside (a q : ℝ) (v : V) (hin : ‖v‖ ≤ a * q) :
    coneResidual a (point q v) = 0 := by
  rw [coneResidual_eq, coneProjection_inside a q v hin, sub_self]

def clippedResidual (a q R : ℝ) : ℝ := max 0 (R - a * q) / (1 + a ^ 2)

/-- Total real division is harmless at R=0: that entire case is proved using
projection=self, rather than applying the outside formula at zero radius. -/
theorem coneResidual_reachable (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) :
    coneResidual a (point q v) =
      WithLp.toLp 2 (a * clippedResidual a q ‖v‖,
        (clippedResidual a q ‖v‖ / ‖v‖) • v) := by
  by_cases hin : ‖v‖ ≤ a * q
  · rw [coneResidual_inside a q v hin]
    have hh : clippedResidual a q ‖v‖ = 0 := by
      unfold clippedResidual
      rw [max_eq_left (sub_nonpos.mpr hin), zero_div]
    apply WithLp.ofLp_injective
    apply Prod.ext
    · change 0 = a * clippedResidual a q ‖v‖
      rw [hh, mul_zero]
    · change (0 : V) = (clippedResidual a q ‖v‖ / ‖v‖) • v
      rw [hh, zero_div, zero_smul]
  · have hout : a * q < ‖v‖ := lt_of_not_ge hin
    have hh : clippedResidual a q ‖v‖ = radialResidual a q ‖v‖ := by
      unfold clippedResidual radialResidual
      rw [max_eq_right (le_of_lt (sub_pos.mpr hout))]
    rw [hh]
    exact coneResidual_outside a q v ha hq hout

#check coneResidual_reachable

theorem coneResidual_zero (a : ℝ) : coneResidual (V := V) a 0 = 0 := by
  exact ActualObjective.coneResidual_zero (V := V) a

theorem coneHalfDistance_nonneg (a : ℝ) (x : State V) :
    0 ≤ coneHalfDistance a x :=
  ActualObjective.halfConeDistance_nonneg a x

theorem coneHalfDistance_zero (a : ℝ) : coneHalfDistance (V := V) a 0 = 0 := by
  rw [coneHalfDistance_eq, coneResidual_zero]
  simp only [norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]

theorem coneResidual_nonexpansive (a : ℝ) (x y : State V) :
    ‖coneResidual a x - coneResidual a y‖ ≤ ‖x - y‖ :=
  ActualObjective.coneResidual_nonexpansive a x y

/-- Global derivative, represented using the genuine Euclidean inner product. -/
theorem coneHalfDistance_hasFDerivAt (a : ℝ) (x : State V) :
    HasFDerivAt (coneHalfDistance a) (innerSL ℝ (coneResidual a x)) x :=
  ActualObjective.halfConeDistance_hasFDerivAt a x

#print axioms coneProjection_minimum
#print axioms coneProjection_outside
#print axioms coneProjection_inside
#print axioms coneResidual_reachable
#print axioms coneResidual_nonexpansive
#print axioms coneHalfDistance_hasFDerivAt
end
end Gate147.ConeAnalytic
