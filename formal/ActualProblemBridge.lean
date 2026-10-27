import RRModel
import TunedActualRisk
import FiniteLowerBound

/-!
Gate149. Actual instances in the public RR class, and exact identification
of that class's original-label gradient recursion/output/loss with the
accepted hard constructions. Neither a field recurrence nor a surrogate
scalar loss is inserted as the public model's gradient or objective.

Dimension <= n is a WITNESS property, not a restriction of Problem.
The cone uses the existing genuine Euclidean slow/fast space, unchanged.
The scalar quadratic has n identical actual components. All instance
choices are independent of permutation bank, step policy and output.
Root alone compiles; no execution by this source's author.
-/
namespace Gate149.ActualProblemBridge
noncomputable section
open scoped BigOperators InnerProductSpace
open Gate146.LabeledBlocks
open Gate148.HardParameters

/-- The SAME positive-parameter tuned cone, as an actual public-class
problem. The raw variance condition is proved at its actual minimizer. -/
def coneProblem {n K : ℕ} (P : Partition n) (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    RRModel.Problem (Gate148.ActualInstance.Space P) n L D sigma where
  f := Gate148.ActualInstance.component P (mu n K L D sigma)
    (ell n K L D sigma) (a n K L D sigma) sigma
  grad := Gate148.ActualInstance.componentGradient P (mu n K L D sigma)
    (ell n K L D sigma) (a n K L D sigma) sigma
  x0 := Gate148.ActualInstance.initial P D
  xstar := 0
  hasFDerivAt i x := Gate148.ActualInstance.component_hasFDerivAt P _ _ _ _ i
    (mu_pos hn hK hL hD hs).le (ell_pos hn hK hL hD hs).le x
  convex i := Gate148.ActualInstance.component_convex P _ _ _ _ i
    (mu_pos hn hK hL hD hs).le (ell_pos hn hK hL hD hs).le
  grad_lipschitz i x y := by
    have he := ell_pos hn hK hL hD hs
    have heL := ell_le_L n K L D sigma
    have hh := Gate148.ActualInstance.componentGradient_norm_sub_le P
      (mu n K L D sigma) (ell n K L D sigma) (a n K L D sigma) sigma i
      (mu_pos hn hK hL hD hs).le (mu_le_ell_quarter hn hK hL hD hs) x y
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : ell n K L D sigma / 2 ≤ L)
      (norm_nonneg (x - y)))
  minimized := Gate148.ActualInstance.mean_minimized_at_zero P hn _ _ _ _
    (mu_pos hn hK hL hD hs).le (ell_pos hn hK hL hD hs).le
  initial_distance := (Gate148.ActualInstance.initial_distance P D hD.le).le
  variance := (Gate148.ActualInstance.variance_at_zero P hn _ _ _ _).le

/-- Dimension is a fact about this witness, not a public-class axiom. -/
theorem cone_dimension {n : ℕ} (P : Partition n) :
    Module.finrank ℝ (Gate148.ActualInstance.Space P) ≤ n :=
  Gate148.ActualInstance.dimension_le P

/-- The public initial point and the accepted actual trajectory have the
same genuine Euclidean value, including the sign of the slow coordinate. -/
theorem cone_initial_state {n K : ℕ} (P : Partition n) (hn0 : 0 < n)
    (bank : RRModel.Bank n K) (e m aa sigma D : ℝ) (eta : ℕ → ℝ) :
    Gate148.ActualRetention.actualState P hn0 bank e m aa sigma D eta 0 =
      Gate148.ActualInstance.initial P D := rfl

/-- Public recursion equals the actual cone path up to and including nK.
The induction uses the accepted TRUE component-gradient step theorem. -/
theorem cone_trajectory_eq {n K : ℕ} (P : Partition n) (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma)
    (bank : RRModel.Bank n K) (eta : ℕ → ℝ)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L) :
    ∀ t, t ≤ n * K →
      RRModel.trajectory (coneProblem P hn hK L D sigma hL hD hs) hn0 bank eta t =
      Gate148.ActualRetention.actualState P hn0 bank (ell n K L D sigma)
        (mu n K L D sigma) (a n K L D sigma) sigma D eta t := by
  intro t
  induction t with
  | zero =>
      intro ht
      exact (cone_initial_state P hn0 bank _ _ _ sigma D eta).symm
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      rw [RRModel.trajectory, hprev]
      exact (Gate147.ActualGradientTrajectory.actual_gradient_step P hn0 bank
        L (ell n K L D sigma) (mu n K L D sigma) (a n K L D sigma) sigma D eta
        hL (ell_pos hn hK hL hD hs) (ell_le_L n K L D sigma)
        (mu_le_ell_quarter hn hK hL hD hs) (a_pos hn hK hL hD hs) hs.le hD
        heta hetaL t (by omega)).symm

/-- No output restriction is needed for this identity: equality of all
states identifies every real scalar weighted sum. Legality is used only
to establish the preceding cone path equality. -/
theorem cone_output_eq {n K : ℕ} (P : Partition n) (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma)
    (bank : RRModel.Bank n K) (eta weight : ℕ → ℝ)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L) :
    RRModel.output (coneProblem P hn hK L D sigma hL hD hs) hn0 bank eta weight =
      Gate148.ActualRetention.output P hn0 bank (ell n K L D sigma)
        (mu n K L D sigma) (a n K L D sigma) sigma D eta weight := by
  unfold RRModel.output Gate148.ActualRetention.output
  apply Finset.sum_congr rfl
  intro i hi
  rw [cone_trajectory_eq P hn0 hn hK L D sigma hL hD hs bank eta heta hetaL i
    (by have := Finset.mem_range.mp hi; omega)]

/-- Exact public-model loss equals the already checked actual cone loss.
The two selectors can depend arbitrarily on the entire finite bank. -/
theorem cone_loss_eq {n K : ℕ} (P : Partition n) (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma)
    (eta weight : RRModel.Bank n K → ℕ → ℝ)
    (heta : ∀ bank k, k < n * K → 0 < eta bank k)
    (hetaL : ∀ bank k, k < n * K → eta bank k ≤ 1 / L)
    (bank : RRModel.Bank n K) :
    RRModel.loss (coneProblem P hn hK L D sigma hL hD hs) hn0 bank
      (eta bank) (weight bank) =
      Gate148.FiniteLowerBound.coneLoss P hn0 L D sigma eta weight bank := by
  unfold RRModel.loss
  rw [cone_output_eq P hn0 hn hK L D sigma hL hD hs bank
    (eta bank) (weight bank) (heta bank) (hetaL bank)]
  rfl

/-- The actual scalar derivative is converted to the same real Hilbert
gradient convention used in Problem; no independent gradient is declared. -/
theorem quadratic_hasFDerivAt {n : ℕ} (T : ℕ) (L : ℝ) (i : Fin n) (x : ℝ) :
    HasFDerivAt (Gate148.QuadraticBranch.component T L i)
      (innerSL ℝ (Gate148.QuadraticBranch.componentGradient T L i x)) x := by
  apply hasFDerivAt_iff_hasDerivAt.mpr
  simpa only [innerSL_apply_apply, RCLike.inner_apply', conj_trivial, mul_one, one_mul]
    using Gate148.QuadraticBranch.component_hasDerivAt T L i x

theorem quadratic_finiteMean {n : ℕ} (hn0 : 0 < n) (T : ℕ) (L x : ℝ) :
    RRModel.finiteMean (Gate148.QuadraticBranch.component (n := n) T L) x =
      Gate148.QuadraticBranch.objective T L x :=
  Gate148.QuadraticBranch.component_mean hn0 T L x

/-- n identical scalar quadratics, legal even at D=0 or sigma=0. The
variance bound is zero<=sigma^2 and requires no division by D or sigma. -/
def quadraticProblem (n K : ℕ) (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D) :
    RRModel.Problem ℝ n L D sigma where
  f := Gate148.QuadraticBranch.component (n * K) L
  grad := Gate148.QuadraticBranch.componentGradient (n * K) L
  x0 := D
  xstar := 0
  hasFDerivAt := quadratic_hasFDerivAt (n * K) L
  convex i := Gate148.QuadraticBranch.component_convex (n * K) L i
    (by have := Nat.mul_pos (by omega : 0 < n) (by omega : 0 < K); omega) hL
  grad_lipschitz i x y := by
    have hT : 1 ≤ n * K := by
      have := Nat.mul_pos (by omega : 0 < n) (by omega : 0 < K)
      omega
    have hh := (Gate148.QuadraticBranch.componentGradient_L_lipschitz
      (n * K) L i hT hL).dist_le_mul x y
    simpa only [dist_eq_norm] using hh
  minimized x := by
    rw [quadratic_finiteMean (by omega : 0 < n),
      quadratic_finiteMean (by omega : 0 < n)]
    exact Gate148.QuadraticBranch.minimized_at_zero (n * K) L
      (by have := Nat.mul_pos (by omega : 0 < n) (by omega : 0 < K); omega) hL x
  initial_distance := (Gate148.QuadraticBranch.initial_distance D hD).le
  variance := Gate148.QuadraticBranch.variance_le n (n * K) L sigma

theorem quadratic_dimension {n : ℕ} (hn : 2 ≤ n) : Module.finrank ℝ ℝ ≤ n := by
  simpa only [Module.finrank_self] using (show 1 ≤ n by omega)

/-- The public initial state is exactly the scalar construction's initial
state. This equality holds without a positivity restriction on D. -/
theorem quadratic_initial_state (T : ℕ) (L D : ℝ) (eta : ℕ → ℝ) :
    Gate148.QuadraticBranch.trajectory T L D eta 0 = D := rfl

/-- Identical components make this identity valid for every label bank
and all times. No legality or ordering shortcut is used in the induction. -/
theorem quadratic_trajectory_eq {n K : ℕ} (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D)
    (bank : RRModel.Bank n K) (eta : ℕ → ℝ) (t : ℕ) :
    RRModel.trajectory (quadraticProblem n K hn hK L D sigma hL hD) hn0 bank eta t =
      Gate148.QuadraticBranch.trajectory (n * K) L D eta t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [RRModel.trajectory, ih]
      simpa only [smul_eq_mul] using
        (Gate148.QuadraticBranch.actual_gradient_step (n * K) L D eta t
          (Gate146.ActualSequence.currentLabel hn0 bank t)).symm

theorem quadratic_output_eq {n K : ℕ} (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D)
    (bank : RRModel.Bank n K) (eta weight : ℕ → ℝ) :
    RRModel.output (quadraticProblem n K hn hK L D sigma hL hD) hn0 bank eta weight =
      Gate148.QuadraticBranch.output (n * K) L D eta weight := by
  unfold RRModel.output Gate148.QuadraticBranch.output
  apply Finset.sum_congr rfl
  intro i hi
  rw [quadratic_trajectory_eq hn0 hn hK L D sigma hL hD bank eta i]
  rfl

/-- Exact public scalar loss identity, including any bank-dependent
selectors and every zero-noise/zero-distance parameter branch. -/
theorem quadratic_loss_eq {n K : ℕ} (hn0 : 0 < n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D)
    (eta weight : RRModel.Bank n K → ℕ → ℝ) (bank : RRModel.Bank n K) :
    RRModel.loss (quadraticProblem n K hn hK L D sigma hL hD) hn0 bank
      (eta bank) (weight bank) =
      Gate148.FiniteLowerBound.quadraticLoss n K L D eta weight bank := by
  unfold RRModel.loss
  rw [quadratic_output_eq hn0 hn hK L D sigma hL hD bank (eta bank) (weight bank)]
  change RRModel.finiteMean (Gate148.QuadraticBranch.component (n := n) (n * K) L)
      (Gate148.QuadraticBranch.output (n * K) L D (eta bank) (weight bank)) -
      RRModel.finiteMean (Gate148.QuadraticBranch.component (n := n) (n * K) L) 0 = _
  rw [quadratic_finiteMean hn0, quadratic_finiteMean hn0]
  rfl

/-- Actual all-n witness availability; it adds no restriction to Problem. -/
def fixedConeProblem {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    RRModel.Problem (Gate148.ActualInstance.fixedSpace n hn) n L D sigma :=
  coneProblem (fixedPartition n hn) hn hK L D sigma hL hD hs

#print axioms coneProblem
#print axioms cone_initial_state
#print axioms cone_trajectory_eq
#print axioms cone_output_eq
#print axioms cone_loss_eq
#print axioms quadratic_hasFDerivAt
#print axioms quadraticProblem
#print axioms quadratic_trajectory_eq
#print axioms quadratic_output_eq
#print axioms quadratic_loss_eq
#print axioms cone_dimension
#print axioms quadratic_dimension
end
end Gate149.ActualProblemBridge
