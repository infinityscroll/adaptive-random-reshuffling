import ActualBankTrajectory
import ConeGradientBridge

/-! The actual finite-bank path takes the original scalar gradient steps
of the globally defined component objective on the genuine Euclidean space.
This connects the objective and trajectory modules; it is not the final
probabilistic minimax theorem. -/
namespace Gate147.ActualGradientTrajectory
noncomputable section
open Gate146.LabeledBlocks Gate147.ActualBankTrajectory Gate147.ConeFormula

theorem actual_gradient_step {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L) (hcap : mu ≤ ell / 4)
    (ha : 0 < a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (t : ℕ) (ht : t < n * K) :
    point (trajectory P hn bank ell mu a sigma D eta (t + 1)).1
      (trajectory P hn bank ell mu a sigma D eta (t + 1)).2 =
    point (trajectory P hn bank ell mu a sigma D eta t).1
      (trajectory P hn bank ell mu a sigma D eta t).2 -
    eta t • ActualObjective.componentGradient mu ell a sigma (bankNoise P hn bank t)
      (point (trajectory P hn bank ell mu a sigma D eta t).1
        (trajectory P hn bank ell mu a sigma D eta t).2) := by
  have hmu : mu < ell := by linarith
  have hq := (trajectory_bounds P hn bank L ell mu a sigma D eta
    hL hell hellL hmu (le_of_lt ha) hsigma hD heta hetaL t (le_of_lt ht)).1
  exact (ConeGradientBridge.actual_gradient_update mu ell a sigma
    (trajectory P hn bank ell mu a sigma D eta t).1 (eta t)
    (trajectory P hn bank ell mu a sigma D eta t).2
    (bankNoise P hn bank t) ha hq).symm

#print axioms actual_gradient_step
end
end Gate147.ActualGradientTrajectory
