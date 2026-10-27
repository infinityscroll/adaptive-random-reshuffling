import ConeAnalytic
import ActualObjective
import ActualFieldTrajectory

/-!
Identification, not a new field assumption: the actual global objective's
Frechet gradient is the field used by the existing trajectory source at
every reachable point u=-q with q>0. Both the cone boundary and zero fast
radius are included. The final equality is the original scalar-gradient
update, with no projection or auxiliary state substituted into the algorithm.
Root alone compiles this source.
-/
namespace Gate147.ConeGradientBridge
noncomputable section
open scoped InnerProductSpace
open Gate147.ConeFormula

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

theorem objectiveResidual_reachable (a q : ℝ) (v : V)
    (ha : 0 < a) (hq : 0 < q) :
    ActualObjective.coneResidual a (point q v) =
      WithLp.toLp 2 (a * ConeAnalytic.clippedResidual a q ‖v‖,
        (ConeAnalytic.clippedResidual a q ‖v‖ / ‖v‖) • v) := by
  exact ConeAnalytic.coneResidual_reachable a q v ha hq

theorem fraction_eq_div (a q R : ℝ) :
    ConeTrajectory.fraction a q R = ConeTrajectory.residual a q R / R := by
  by_cases hz : R = 0
  · simp [ConeTrajectory.fraction, hz]
  · simp [ConeTrajectory.fraction, hz]

theorem scaled_clipped (ell a q R : ℝ) :
    (ell / 4) * ConeAnalytic.clippedResidual a q R =
      ConeTrajectory.beta ell a * ConeTrajectory.residual a q R := by
  unfold ConeAnalytic.clippedResidual ConeTrajectory.beta ConeTrajectory.residual
  field_simp [ne_of_gt (denominator_pos a)]
  <;> ring

theorem scaled_clipped_div (ell a q R : ℝ) :
    (ell / 4) * (ConeAnalytic.clippedResidual a q R / R) =
      ConeTrajectory.beta ell a * ConeTrajectory.fraction a q R := by
  calc
    _ = ((ell / 4) * ConeAnalytic.clippedResidual a q R) / R := by ring
    _ = (ConeTrajectory.beta ell a * ConeTrajectory.residual a q R) / R := by
      rw [scaled_clipped]
    _ = _ := by rw [fraction_eq_div]; ring

theorem componentGradient_fst (mu ell a sigma q : ℝ) (v xi : V)
    (ha : 0 < a) (hq : 0 < q) :
    (ActualObjective.componentGradient mu ell a sigma xi (point q v)).fst =
      ConeTrajectory.slowField ell mu a q v := by
  have hs := scaled_clipped ell a q ‖v‖
  simp only [ActualObjective.componentGradient, ActualObjective.phiGradient,
    ActualObjective.offset, WithLp.add_fst, WithLp.smul_fst,
    QuadraticField.baseGradient, WithLp.toLp_fst]
  rw [objectiveResidual_reachable a q v ha hq]
  simp only [WithLp.toLp_fst, point, WithLp.toLp_fst, smul_eq_mul, add_zero]
  unfold ConeTrajectory.slowField
  calc
    _ = -mu * q + a * ((ell / 4) * ConeAnalytic.clippedResidual a q ‖v‖) := by ring
    _ = _ := by rw [hs]; ring

theorem componentGradient_snd (mu ell a sigma q : ℝ) (v xi : V)
    (ha : 0 < a) (hq : 0 < q) :
    (ActualObjective.componentGradient mu ell a sigma xi (point q v)).snd =
      ConeTrajectory.fastField ell a q sigma v xi := by
  simp only [ActualObjective.componentGradient, ActualObjective.phiGradient,
    ActualObjective.offset, WithLp.add_snd, WithLp.smul_snd,
    QuadraticField.baseGradient, WithLp.toLp_snd]
  rw [objectiveResidual_reachable a q v ha hq]
  simp only [WithLp.toLp_snd, point, WithLp.toLp_snd, smul_smul]
  rw [scaled_clipped_div]
  rw [← add_smul]
  rfl

/-- Equality of actual gradients represented in the shared Euclidean space.
The two component formulas above make the all-label noise term explicit. -/
theorem componentGradient_reachable (mu ell a sigma q : ℝ) (v xi : V)
    (ha : 0 < a) (hq : 0 < q) :
    ActualObjective.componentGradient mu ell a sigma xi (point q v) =
      WithLp.toLp 2 (ConeTrajectory.slowField ell mu a q v,
        ConeTrajectory.fastField ell a q sigma v xi) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact componentGradient_fst mu ell a sigma q v xi ha hq
  · exact componentGradient_snd mu ell a sigma q v xi ha hq

theorem component_hasFDerivAt_field (mu ell a sigma q : ℝ) (v xi : V)
    (hmu : 0 ≤ mu) (hell : 0 ≤ ell) (ha : 0 < a) (hq : 0 < q) :
    HasFDerivAt (ActualObjective.component mu ell a sigma xi)
      (innerSL ℝ (WithLp.toLp 2 (ConeTrajectory.slowField ell mu a q v,
        ConeTrajectory.fastField ell a q sigma v xi))) (point q v) := by
  have hh := ActualObjective.component_hasFDerivAt mu ell a sigma xi hmu hell (point q v)
  rw [componentGradient_reachable mu ell a sigma q v xi ha hq] at hh
  exact hh

/-- The actual scalar gradient update equals the trajectory recurrence.
No sign condition on eta is needed for this algebraic identification;
the trajectory module separately enforces the original legal step cap. -/
theorem actual_gradient_update (mu ell a sigma q eta : ℝ) (v xi : V)
    (ha : 0 < a) (hq : 0 < q) :
    point q v - eta • ActualObjective.componentGradient mu ell a sigma xi (point q v) =
      point (ConeTrajectory.slowNext ell mu a q eta v)
        (ConeTrajectory.fastNext ell a q sigma eta v xi) := by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · change -q - eta *
        (ActualObjective.componentGradient mu ell a sigma xi (point q v)).fst =
      -ConeTrajectory.slowNext ell mu a q eta v
    rw [componentGradient_fst mu ell a sigma q v xi ha hq]
    have hh := ConeTrajectory.negative_slow_gradient_update ell mu a q eta v
    linarith
  · change v - eta •
        (ActualObjective.componentGradient mu ell a sigma xi (point q v)).snd =
      ConeTrajectory.fastNext ell a q sigma eta v xi
    rw [componentGradient_snd mu ell a sigma q v xi ha hq]
    exact ConeTrajectory.fast_gradient_update ell a q sigma eta v xi

#print axioms objectiveResidual_reachable
#print axioms scaled_clipped
#print axioms componentGradient_reachable
#print axioms component_hasFDerivAt_field
#print axioms actual_gradient_update
end
end Gate147.ConeGradientBridge
