import ConeFormula
import ConvexProjection
import QuadraticField
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
Gate147: the actual globally defined cone objective and its component
functions on the shared genuine L2 product. The distance is defined using
an actual minimizing projection, not by prescribing a desired gradient.
All gradient assertions below are derived Frechet derivatives represented
by the product inner product. Root alone compiles this source.
-/
namespace Gate147.ActualObjective
noncomputable section
open scoped Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V]

abbrev State (V : Type*) := WithLp 2 (ℝ × V)

def coneComplete (a : ℝ) : IsComplete (ConeFormula.cone (V := V) a) :=
  (ConeFormula.cone_closed a).isComplete

def coneResidual (a : ℝ) (x : State V) : State V :=
  ConvexProjection.residual (ConeFormula.cone a) (ConeFormula.cone_nonempty a)
    (coneComplete a) (ConeFormula.cone_convex a) x

def halfConeDistance (a : ℝ) (x : State V) : ℝ :=
  ConvexProjection.halfSquaredDistance (ConeFormula.cone a) (ConeFormula.cone_nonempty a)
    (coneComplete a) (ConeFormula.cone_convex a) x

/-- This is one half of the squared ACTUAL minimum distance to the cone. -/
theorem halfConeDistance_eq_minimum (a : ℝ) (x : State V) :
    halfConeDistance a x =
      (⨅ w : ConeFormula.cone (V := V) a, ‖x - w.val‖) ^ 2 / 2 := by
  unfold halfConeDistance ConvexProjection.halfSquaredDistance ConvexProjection.residual
  rw [ConvexProjection.projection_minimum]

def Phi (mu ell a : ℝ) (x : State V) : ℝ :=
  QuadraticField.quadratic mu ell x + (ell / 4) * halfConeDistance a x

def phiGradient (mu ell a : ℝ) (x : State V) : State V :=
  QuadraticField.baseGradient mu ell x + (ell / 4) • coneResidual a x

def offset (sigma : ℝ) (xi : V) : State V := WithLp.toLp 2 (0, sigma • xi)

def component (mu ell a sigma : ℝ) (xi : V) (x : State V) : ℝ :=
  Phi mu ell a x + sigma * inner ℝ xi x.snd

def componentGradient (mu ell a sigma : ℝ) (xi : V) (x : State V) : State V :=
  phiGradient mu ell a x + offset sigma xi

theorem offset_pairing (sigma : ℝ) (xi : V) (x : State V) :
    inner ℝ (offset sigma xi) x = sigma * inner ℝ xi x.snd := by
  rw [Gate147.RealProduct.product_inner]
  simp only [offset, WithLp.toLp_fst, WithLp.toLp_snd,
    inner_zero_left, zero_add, real_inner_smul_left]

theorem halfConeDistance_nonneg (a : ℝ) (x : State V) : 0 ≤ halfConeDistance a x :=
  ConvexProjection.halfSquaredDistance_nonneg (ConeFormula.cone a)
    (ConeFormula.cone_nonempty a) (coneComplete a) (ConeFormula.cone_convex a) x

theorem halfConeDistance_hasFDerivAt (a : ℝ) (x : State V) :
    HasFDerivAt (halfConeDistance (V := V) a) (innerSL ℝ (coneResidual a x)) x :=
  ConvexProjection.halfSquaredDistance_hasFDerivAt (ConeFormula.cone a)
    (ConeFormula.cone_nonempty a) (coneComplete a) (ConeFormula.cone_convex a) x

/-- The actual full mean objective, with no gradient identification premise. -/
theorem Phi_hasFDerivAt (mu ell a : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell)
    (x : State V) :
    HasFDerivAt (Phi (V := V) mu ell a) (innerSL ℝ (phiGradient mu ell a x)) x := by
  have hq := QuadraticField.quadratic_hasFDerivAt mu ell hmu hell x
  have hd := (halfConeDistance_hasFDerivAt a x).const_smul (ell / 4)
  have hh := hq.add hd
  have hmap : innerSL ℝ (QuadraticField.baseGradient mu ell x) +
      (ell / 4) • innerSL ℝ (coneResidual a x) = innerSL ℝ (phiGradient mu ell a x) := by
    ext z
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, phiGradient, inner_add_left, real_inner_smul_left, smul_eq_mul]
  rw [hmap] at hh
  exact hh

theorem component_hasFDerivAt (mu ell a sigma : ℝ) (xi : V)
    (hmu : 0 ≤ mu) (hell : 0 ≤ ell) (x : State V) :
    HasFDerivAt (component (V := V) mu ell a sigma xi)
      (innerSL ℝ (componentGradient mu ell a sigma xi x)) x := by
  have hlin : HasFDerivAt (fun y : State V => sigma * inner ℝ xi y.snd)
      (innerSL ℝ (offset sigma xi)) x := by
    have hf : (fun y : State V => sigma * inner ℝ xi y.snd) =
        (fun y : State V => innerSL ℝ (offset sigma xi) y) := by
      funext y
      exact (offset_pairing sigma xi y).symm
    rw [hf]
    exact (innerSL ℝ (offset sigma xi)).hasFDerivAt
  have hh := (Phi_hasFDerivAt mu ell a hmu hell x).add hlin
  have hmap : innerSL ℝ (phiGradient mu ell a x) + innerSL ℝ (offset sigma xi) =
      innerSL ℝ (componentGradient mu ell a sigma xi x) := by
    ext z
    simp only [ContinuousLinearMap.add_apply, innerSL_apply_apply,
      componentGradient, inner_add_left]
  rw [hmap] at hh
  exact hh

theorem Phi_convex (mu ell a : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell) :
    ConvexOn ℝ Set.univ (Phi (V := V) mu ell a) := by
  have hq := QuadraticField.quadratic_convex (V := V) mu ell hmu hell
  have hd := ConvexProjection.halfSquaredDistance_convex (ConeFormula.cone (V := V) a)
    (ConeFormula.cone_nonempty a) (coneComplete a) (ConeFormula.cone_convex a)
  exact hq.add (ConvexOn.smul (show 0 ≤ ell / 4 by positivity) hd)

theorem component_convex (mu ell a sigma : ℝ) (xi : V)
    (hmu : 0 ≤ mu) (hell : 0 ≤ ell) :
    ConvexOn ℝ Set.univ (component (V := V) mu ell a sigma xi) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy c d hc hd hcd
  have hh := (Phi_convex (V := V) mu ell a hmu hell).2 hx hy hc hd hcd
  simp only [smul_eq_mul] at hh
  change component mu ell a sigma xi (c • x + d • y) ≤
    c * component mu ell a sigma xi x + d * component mu ell a sigma xi y
  simp only [component, WithLp.add_snd, WithLp.smul_snd,
    inner_add_right, real_inner_smul_right]
  convert add_le_add_right hh
    (sigma * (c * inner ℝ xi x.snd + d * inner ℝ xi y.snd)) using 1 <;> ring

theorem coneResidual_nonexpansive (a : ℝ) (x y : State V) :
    ‖coneResidual a x - coneResidual a y‖ ≤ ‖x - y‖ :=
  ConvexProjection.residual_nonexpansive (ConeFormula.cone a)
    (ConeFormula.cone_nonempty a) (coneComplete a) (ConeFormula.cone_convex a) x y

theorem phiGradient_norm_sub_le (mu ell a : ℝ) (hmu : 0 ≤ mu)
    (hcap : mu ≤ ell / 4) (x y : State V) :
    ‖phiGradient mu ell a x - phiGradient mu ell a y‖ ≤ (ell / 2) * ‖x - y‖ := by
  have hell : 0 ≤ ell / 4 := hmu.trans hcap
  have hid : phiGradient mu ell a x - phiGradient mu ell a y =
      (QuadraticField.baseGradient mu ell x - QuadraticField.baseGradient mu ell y) +
        (ell / 4) • (coneResidual a x - coneResidual a y) := by
    unfold phiGradient
    rw [smul_sub]
    abel
  rw [hid]
  calc
    _ ≤ ‖QuadraticField.baseGradient mu ell x - QuadraticField.baseGradient mu ell y‖ +
        ‖(ell / 4) • (coneResidual a x - coneResidual a y)‖ := norm_add_le _ _
    _ = ‖QuadraticField.baseGradient mu ell x - QuadraticField.baseGradient mu ell y‖ +
        (ell / 4) * ‖coneResidual a x - coneResidual a y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hell]
    _ ≤ (ell / 4) * ‖x - y‖ + (ell / 4) * ‖x - y‖ :=
      add_le_add (QuadraticField.baseGradient_norm_sub_le mu ell hmu hcap x y)
        (mul_le_mul_of_nonneg_left (coneResidual_nonexpansive a x y) hell)
    _ = _ := by ring

theorem phiGradient_lipschitz (mu ell a : ℝ) (hmu : 0 ≤ mu)
    (hcap : mu ≤ ell / 4) :
    LipschitzWith ⟨ell / 2, by linarith⟩ (phiGradient (V := V) mu ell a) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using phiGradient_norm_sub_le mu ell a hmu hcap x y

theorem componentGradient_norm_sub_le (mu ell a sigma : ℝ) (xi : V)
    (hmu : 0 ≤ mu) (hcap : mu ≤ ell / 4) (x y : State V) :
    ‖componentGradient mu ell a sigma xi x - componentGradient mu ell a sigma xi y‖ ≤
      (ell / 2) * ‖x - y‖ := by
  have hid : componentGradient mu ell a sigma xi x - componentGradient mu ell a sigma xi y =
      phiGradient mu ell a x - phiGradient mu ell a y := by unfold componentGradient; abel
  rw [hid]
  exact phiGradient_norm_sub_le mu ell a hmu hcap x y

theorem componentGradient_lipschitz (mu ell a sigma : ℝ) (xi : V)
    (hmu : 0 ≤ mu) (hcap : mu ≤ ell / 4) :
    LipschitzWith ⟨ell / 2, by linarith⟩ (componentGradient (V := V) mu ell a sigma xi) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using componentGradient_norm_sub_le mu ell a sigma xi hmu hcap x y

/-- The full objective dominates the slow coordinate energy at EVERY state,
not only on a reachable path or an expectation event. -/
theorem Phi_slow_lower (mu ell a : ℝ) (hell : 0 ≤ ell) (x : State V) :
    mu * x.fst ^ 2 / 2 ≤ Phi mu ell a x := by
  have hd := halfConeDistance_nonneg a x
  have hd' := mul_nonneg (show 0 ≤ ell / 4 by positivity) hd
  have hfast := mul_nonneg hell (sq_nonneg ‖x.snd‖)
  unfold Phi QuadraticField.quadratic
  nlinarith

theorem Phi_nonneg (mu ell a : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell)
    (x : State V) : 0 ≤ Phi mu ell a x := by
  have hh := Phi_slow_lower mu ell a hell x
  have hb : 0 ≤ mu * x.fst ^ 2 / 2 := by positivity
  linarith

theorem zero_mem_cone (a : ℝ) : (0 : State V) ∈ ConeFormula.cone a := by
  simp [ConeFormula.cone]

theorem coneResidual_zero (a : ℝ) : coneResidual (V := V) a 0 = 0 := by
  unfold coneResidual ConvexProjection.residual
  rw [ConvexProjection.projection_eq_self _ _ _ _ _ (zero_mem_cone a)]
  simp

theorem Phi_zero (mu ell a : ℝ) : Phi (V := V) mu ell a 0 = 0 := by
  have hd := ConvexProjection.halfSquaredDistance_zero_of_mem (ConeFormula.cone (V := V) a)
    (ConeFormula.cone_nonempty a) (coneComplete a) (ConeFormula.cone_convex a) 0 (zero_mem_cone a)
  change halfConeDistance a 0 = 0 at hd
  simp only [Phi, QuadraticField.quadratic_zero, hd, mul_zero, add_zero]

theorem Phi_minimized_at_zero (mu ell a : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell) :
    ∀ x : State V, Phi (V := V) mu ell a 0 ≤ Phi mu ell a x := by
  intro x
  rw [Phi_zero]
  exact Phi_nonneg mu ell a hmu hell x

#print axioms halfConeDistance_eq_minimum
#print axioms Phi_hasFDerivAt
#print axioms component_hasFDerivAt
#print axioms Phi_convex
#print axioms component_convex
#print axioms phiGradient_lipschitz
#print axioms componentGradient_lipschitz
#print axioms Phi_slow_lower
#print axioms Phi_minimized_at_zero
end
end Gate147.ActualObjective
