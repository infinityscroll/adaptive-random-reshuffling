import RRModel
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Gate149: true linear-isometric transport of the public problem and its
actual gradient trajectory. The map preserves inner products and norms;
no norm is transported through coordinate deletion. The orthonormal-basis
corollary uses standard EuclideanSpace with its genuine L2 norm.
Root alone compiles. No accepted source is changed by this module.
-/
namespace Gate149.IsometricTransport
noncomputable section
open scoped BigOperators InnerProductSpace
open Gate149.RRModel

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {n K : ℕ} {L D sigma : ℝ}

/-- The derivative functional transforms by the actual isometric inverse. -/
theorem innerSL_comp_symm (e : E ≃ₗᵢ[ℝ] F) (v : E) :
    (innerSL ℝ v).comp e.symm.toLinearIsometry.toContinuousLinearMap =
      innerSL ℝ (e v) := by
  ext w
  change inner ℝ v (e.symm w) = inner ℝ (e v) w
  exact (e.inner_map_eq_flip v w).symm

/-- The same component functions in genuine isometric coordinates, with
the SAME L,D,sigma and component count. No extra class assumptions. -/
def transport (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F) :
    Problem F n L D sigma where
  f i y := Q.f i (e.symm y)
  grad i y := e (Q.grad i (e.symm y))
  x0 := e Q.x0
  xstar := e Q.xstar
  hasFDerivAt := by
    intro i y
    have hf := (Q.hasFDerivAt i (e.symm y)).comp y
      (e.symm.toLinearIsometry.toContinuousLinearMap.hasFDerivAt)
    rw [innerSL_comp_symm] at hf
    exact hf
  convex := by
    intro i
    simpa only [Set.preimage_univ, Function.comp_def] using
      (Q.convex i).comp_linearMap e.symm.toLinearEquiv.toLinearMap
  grad_lipschitz := by
    intro i x y
    calc
      ‖e (Q.grad i (e.symm x)) - e (Q.grad i (e.symm y))‖ =
          ‖Q.grad i (e.symm x) - Q.grad i (e.symm y)‖ := by
            rw [← e.map_sub, e.norm_map]
      _ ≤ L * ‖e.symm x - e.symm y‖ := Q.grad_lipschitz i (e.symm x) (e.symm y)
      _ = L * ‖x - y‖ := by rw [← e.symm.map_sub, e.symm.norm_map]
  minimized := by
    intro y
    simpa only [finiteMean, LinearIsometryEquiv.symm_apply_apply] using
      Q.minimized (e.symm y)
  initial_distance := by
    rw [e.dist_map]
    exact Q.initial_distance
  variance := by
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.norm_map] using
      Q.variance

@[simp] theorem transport_x0 (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F) :
    (transport Q e).x0 = e Q.x0 := rfl

@[simp] theorem transport_xstar (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F) :
    (transport Q e).xstar = e Q.xstar := rfl

theorem transport_component (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F)
    (i : Fin n) (x : E) : (transport Q e).f i (e x) = Q.f i x := by
  change Q.f i (e.symm (e x)) = Q.f i x
  rw [e.symm_apply_apply]

theorem transport_gradient (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F)
    (i : Fin n) (x : E) : (transport Q e).grad i (e x) = e (Q.grad i x) := by
  change e (Q.grad i (e.symm (e x))) = e (Q.grad i x)
  rw [e.symm_apply_apply]

theorem transport_mean (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F) (y : F) :
    finiteMean (transport Q e).f y = finiteMean Q.f (e.symm y) := rfl

theorem transport_initial_distance (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F) :
    dist (transport Q e).x0 (transport Q e).xstar = dist Q.x0 Q.xstar :=
  e.dist_map _ _

theorem transport_variance (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F) :
    (∑ i : Fin n, ‖(transport Q e).grad i (transport Q e).xstar‖ ^ 2) / (n : ℝ) =
      (∑ i : Fin n, ‖Q.grad i Q.xstar‖ ^ 2) / (n : ℝ) := by
  simp only [transport_xstar, transport_gradient, LinearIsometryEquiv.norm_map]

/-- Every actual state is preserved for every realized step sequence and
bank, without legality or independence assumptions. -/
theorem transport_trajectory (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F)
    (hn : 0 < n) (bank : Bank n K) (eta : ℕ → ℝ) :
    ∀ t, trajectory (transport Q e) hn bank eta t = e (trajectory Q hn bank eta t) := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [trajectory_succ, ih, transport_gradient, map_sub, map_smul]

theorem transport_output (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F)
    (hn : 0 < n) (bank : Bank n K) (eta weight : ℕ → ℝ) :
    output (transport Q e) hn bank eta weight = e (output Q hn bank eta weight) := by
  simp only [output, transport_trajectory, map_sum, map_smul]

/-- True mean-objective loss at the same actual-state scalar output. -/
theorem transport_loss (Q : Problem E n L D sigma) (e : E ≃ₗᵢ[ℝ] F)
    (hn : 0 < n) (bank : Bank n K) (eta weight : ℕ → ℝ) :
    loss (transport Q e) hn bank eta weight = loss Q hn bank eta weight := by
  simp only [loss, transport_output, transport_mean, transport_xstar,
    LinearIsometryEquiv.symm_apply_apply]

theorem transport_dimension (e : E ≃ₗᵢ[ℝ] F) :
    Module.finrank ℝ F = Module.finrank ℝ E :=
  e.toLinearEquiv.finrank_eq.symm

/-- Standard Euclidean coordinates, obtained only from an orthonormal basis. -/
def standardEquiv (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  (stdOrthonormalBasis ℝ E).repr

def standardProblem (Q : Problem E n L D sigma) :
    Problem (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) n L D sigma :=
  transport Q (standardEquiv E)

theorem standard_loss (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta weight : ℕ → ℝ) :
    loss (standardProblem Q) hn bank eta weight = loss Q hn bank eta weight :=
  transport_loss Q (standardEquiv E) hn bank eta weight

/-- A dimension bound, when proved for a particular witness, survives the
isometry. It is not introduced as a condition on the public Problem class. -/
theorem standard_dimension_le (Q : Problem E n L D sigma)
    (hdim : Module.finrank ℝ E ≤ n) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ≤ n := by
  simpa only [finrank_euclideanSpace_fin] using hdim

#print axioms innerSL_comp_symm
#print axioms transport
#print axioms transport_gradient
#print axioms transport_mean
#print axioms transport_initial_distance
#print axioms transport_variance
#print axioms transport_trajectory
#print axioms transport_output
#print axioms transport_loss
#print axioms transport_dimension
#print axioms standardEquiv
#print axioms standard_loss
#print axioms standard_dimension_le
end
end Gate149.IsometricTransport
