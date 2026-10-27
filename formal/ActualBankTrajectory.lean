import ActualFieldTrajectory
import ActualAllNModel

/-! Same original-label finite-bank noise on the actual Euclidean fast
subspace. This module connects the displayed field recurrence to the
coordinate energy proof. Identification with the objective gradient is
a separate analytic bridge, not an assumption hidden in this file. -/
namespace Gate147.ActualBankTrajectory
noncomputable section
open scoped BigOperators
open Gate146.EuclideanCoordinates Gate146.LabeledBlocks
open Gate146.FastSpaceOffsets Gate146.ActualSequence
open Gate147.ConeTrajectory

def bankNoise {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (t : ℕ) : fastSpace P.size :=
  fastXi P (currentLabel hn bank t)

theorem bankNoise_unit {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (t : ℕ) : ‖bankNoise P hn bank t‖ = 1 :=
  fastXi_norm P _

/-- The coercion is the actual norm-preserving subspace inclusion. -/
theorem subtype_trajectory {n : ℕ} (P : Partition n)
    (ell mu a sigma D : ℝ) (eta : ℕ → ℝ) (xi : ℕ → fastSpace P.size) (t : ℕ) :
    (fieldTrajectory ell mu a sigma D eta xi t).1 =
      (fieldTrajectory ell mu a sigma D eta (fun k => (xi k).val) t).1 ∧
    (fieldTrajectory ell mu a sigma D eta xi t).2.val =
      (fieldTrajectory ell mu a sigma D eta (fun k => (xi k).val) t).2 := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
      constructor
      · change slowNext ell mu a
          (fieldTrajectory ell mu a sigma D eta xi t).1 (eta t)
          (fieldTrajectory ell mu a sigma D eta xi t).2 = _
        change (1 - mu * eta t) * (fieldTrajectory ell mu a sigma D eta xi t).1 +
            beta ell a * a * eta t * residual a
              (fieldTrajectory ell mu a sigma D eta xi t).1
              ‖(fieldTrajectory ell mu a sigma D eta xi t).2.val‖ = _
        rw [ih.1, ih.2]
        rfl
      · change (1 - drift ell a (fieldTrajectory ell mu a sigma D eta xi t).1
            ‖(fieldTrajectory ell mu a sigma D eta xi t).2.val‖ * eta t) •
            (fieldTrajectory ell mu a sigma D eta xi t).2.val -
            (sigma * eta t) • (xi t).val = _
        rw [ih.1, ih.2]
        rfl

def trajectory {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ) (eta : ℕ → ℝ) :=
  fieldTrajectory ell mu a sigma D eta (bankNoise P hn bank)

theorem trajectory_bounds {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L) (hmu : mu < ell)
    (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L) :
    ∀ t ≤ n * K, 0 < (trajectory P hn bank ell mu a sigma D eta t).1 ∧
      ell * ‖(trajectory P hn bank ell mu a sigma D eta t).2‖ ≤ 4 * sigma :=
  fieldTrajectory_bounds L ell mu a sigma D eta (bankNoise P hn bank) (n * K)
    hL hell hellL hmu ha hsigma hD heta hetaL (fun k hk => bankNoise_unit P hn bank k)

/-- Every interval of the actual same-bank recurrence, including both
endpoint energies. eta may be any legal realized adaptive sequence. -/
theorem trajectory_interval_energy {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (s N : ℕ) (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L) (hmu : mu < ell)
    (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (hN : s + N ≤ n * K) :
    sigma ^ 2 * (∑ k ∈ Finset.range N, (eta (s + k)) ^ 2) ≤
      ‖(trajectory P hn bank ell mu a sigma D eta (s + N)).2‖ ^ 2 -
      ‖(trajectory P hn bank ell mu a sigma D eta s).2‖ ^ 2 +
      6 * sigma * ∑ k ∈ Finset.range N,
        eta (s + k) * ‖(trajectory P hn bank ell mu a sigma D eta (s + k)).2‖ := by
  have hnrm : ∀ k, ‖(trajectory P hn bank ell mu a sigma D eta k).2‖ =
      ‖(fieldTrajectory ell mu a sigma D eta (fun t => (bankNoise P hn bank t).val) k).2‖ := by
    intro k
    exact congrArg norm (subtype_trajectory P ell mu a sigma D eta (bankNoise P hn bank) k).2
  simp_rw [hnrm]
  exact fieldTrajectory_interval_energy L ell mu a sigma D eta
    (fun t => (bankNoise P hn bank t).val) (n * K) s N
    hL hell hellL hmu ha hsigma hD heta hetaL
    (fun k hk => bankNoise_unit P hn bank k) hN

#print axioms bankNoise_unit
#print axioms subtype_trajectory
#print axioms trajectory_bounds
#print axioms trajectory_interval_energy
end
end Gate147.ActualBankTrajectory
