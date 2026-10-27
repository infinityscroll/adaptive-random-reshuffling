import EuclideanModel
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring




/-!
Gate144: the exact one-step energy estimate in Gate134 Section 2.
The vector lemma uses arbitrary finite Euclidean coordinates to derive the
squared-norm identity from the actual affine fast update. Its dimension is
unrestricted; this covers the finite-dimensional Gate134 model. A previous
general Hilbert-space import exceeded the frozen memory cap and is preserved
under source-history, with no proof acceptance. The finite sum lemma retains
both endpoint energies. Bounds on
the actual cone drift, global radius, and the existence of the legal cone
instance are still separate interfaces, not established by this file.
-/

namespace Gate144.ScalarEnergy

theorem scalar_energy_step (R Rnext sigma eta ell d rho w : ℝ)
    (hR : 0 ≤ R) (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta)
    (hd : 0 ≤ d) (hdell : 2 * d ≤ ell)
    (hrho : rho = 1 - d * eta) (hrho0 : 0 ≤ rho)
    (hradius : ell * R ≤ 4 * sigma) (hw : w ≤ R)
    (hupdate : Rnext ^ 2 = rho ^ 2 * R ^ 2 -
      2 * rho * sigma * eta * w + sigma ^ 2 * eta ^ 2) :
    sigma ^ 2 * eta ^ 2 ≤ Rnext ^ 2 - R ^ 2 + 6 * sigma * eta * R := by
  have hrho1 : rho ≤ 1 := by nlinarith [mul_nonneg hd heta]
  have hangle : rho * w ≤ R :=
    (mul_le_mul_of_nonneg_left hw hrho0).trans
      (by simpa using mul_le_mul_of_nonneg_right hrho1 hR)
  have hcross := mul_le_mul_of_nonneg_left hangle
    (show 0 ≤ 2 * sigma * eta by positivity)
  have hfactor : 1 - ell * eta ≤ rho ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hdell) heta
    nlinarith [sq_nonneg (d * eta)]
  have hbase := mul_le_mul_of_nonneg_right hfactor (sq_nonneg R)
  have hradial := mul_le_mul_of_nonneg_right hradius (mul_nonneg heta hR)
  nlinarith

theorem affine_energy_step (m : ℕ) (v xi : Fin m → ℝ)
    (R Rnext sigma eta ell d : ℝ)
    (hR : 0 ≤ R)
    (hRdef : R ^ 2 = ∑ i, v i ^ 2)
    (hRnext : Rnext ^ 2 = ∑ i, ((1 - d * eta) * v i - sigma * eta * xi i) ^ 2)
    (hsigma : 0 ≤ sigma) (heta : 0 ≤ eta)
    (hd : 0 ≤ d) (hdell : 2 * d ≤ ell)
    (hrho : 0 ≤ 1 - d * eta)
    (hradius : ell * R ≤ 4 * sigma) (hxi : ∑ i, xi i ^ 2 = 1) :
    sigma ^ 2 * eta ^ 2 ≤ Rnext ^ 2 - R ^ 2 + 6 * sigma * eta * R := by
  have hw : (∑ i, v i * xi i) ≤ R := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v xi
    rw [← hRdef, hxi, mul_one] at hcs
    nlinarith
  apply scalar_energy_step R Rnext sigma eta ell d (1 - d * eta)
    (∑ i, v i * xi i) hR hsigma heta hd hdell rfl hrho hradius hw
  rw [hRnext, hRdef, ← mul_one (sigma ^ 2 * eta ^ 2), ← hxi,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Arbitrary finite interval after reindexing its initial state to index 0.
No measurability, independence, or advance selection of the interval is used. -/
theorem energy_sum (R eta : ℕ → ℝ) (sigma : ℝ) (N : ℕ)
    (hstep : ∀ k < N, sigma ^ 2 * eta k ^ 2 ≤
      R (k + 1) ^ 2 - R k ^ 2 + 6 * sigma * eta k * R k) :
    sigma ^ 2 * (∑ k ∈ Finset.range N, eta k ^ 2) ≤
      R N ^ 2 - R 0 ^ 2 +
        6 * sigma * (∑ k ∈ Finset.range N, eta k * R k) := by
  have h := Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
  have ht := Finset.sum_range_sub (fun k => R k ^ 2) N
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [ht] at h
  simpa only [mul_assoc, Finset.mul_sum] using h

#print axioms scalar_energy_step
#print axioms affine_energy_step
#print axioms energy_sum

end Gate144.ScalarEnergy

/-!
Gate147: explicit cone coefficient field, its legal scalar trajectories,
and actual Euclidean signed energy. Compile with the accepted Gate146
EuclideanCoordinates and Gate144 ScalarEnergy declarations available.

IMPORTANT ANALYTIC INTERFACE: this module proves the dynamics of the
explicit field below. It does not claim that the field is the Frechet
(or Riesz) gradient of the globally defined squared-distance objective.
That identification is the separate cone projection/gradient module.
No final radius or energy estimate is assumed by the trajectory theorem.
Root alone runs Lean.
-/
namespace Gate147.ConeTrajectory
open scoped BigOperators
noncomputable section

/-- beta=gamma/(1+a^2), gamma=ell/4. -/
def beta (ell a : ℝ) : ℝ := ell / (4 * (1 + a ^ 2))
def residual (a q R : ℝ) : ℝ := max 0 (R - a * q)
def fraction (a q R : ℝ) : ℝ := if R = 0 then 0 else residual a q R / R
def drift (ell a q R : ℝ) : ℝ := ell / 4 + beta ell a * fraction a q R

theorem residual_nonneg (a q R : ℝ) : 0 ≤ residual a q R := le_max_left _ _

theorem residual_le_radius (a q R : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hR : 0 ≤ R) : residual a q R ≤ R := by
  unfold residual
  exact max_le hR (sub_le_self _ (mul_nonneg ha hq))

theorem fraction_bounds (a q R : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hR : 0 ≤ R) : 0 ≤ fraction a q R ∧ fraction a q R ≤ 1 := by
  by_cases hz : R = 0
  · simp [fraction, hz]
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
    simp only [fraction, if_neg hz]
    exact ⟨div_nonneg (residual_nonneg a q R) hR,
      (div_le_one hp).2 (residual_le_radius a q R ha hq hR)⟩

theorem beta_bounds (ell a : ℝ) (hell : 0 ≤ ell) :
    0 ≤ beta ell a ∧ beta ell a ≤ ell / 4 := by
  have hden : 0 < 4 * (1 + a ^ 2) := by positivity
  constructor
  · exact div_nonneg hell (le_of_lt hden)
  · unfold beta
    apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hell (sq_nonneg a)]

theorem drift_bounds (ell a q R : ℝ) (hell : 0 ≤ ell)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hR : 0 ≤ R) :
    ell / 4 ≤ drift ell a q R ∧ drift ell a q R ≤ ell / 2 := by
  have hb := beta_bounds ell a hell
  have hf := fraction_bounds a q R ha hq hR
  have hp0 := mul_nonneg hb.1 hf.1
  have hp1 := mul_le_mul_of_nonneg_left hf.2 hb.1
  unfold drift
  constructor <;> nlinarith

/-- The original step cap is 1/L; ell<=L is used, never a relaxed cap. -/
theorem ell_step_le_one (L ell eta : ℝ) (hL : 0 < L)
    (hellL : ell ≤ L) (heta : 0 ≤ eta) (hetaL : eta ≤ 1 / L) :
    ell * eta ≤ 1 := by
  have hh : eta * L ≤ 1 := (le_div_iff₀ hL).mp hetaL
  nlinarith [mul_nonneg (sub_nonneg.mpr hellL) heta]

theorem retention_positive (L ell mu eta : ℝ) (hL : 0 < L)
    (hellL : ell ≤ L) (hmu : mu < ell) (heta : 0 < eta)
    (hetaL : eta ≤ 1 / L) : 0 < 1 - mu * eta := by
  have he := ell_step_le_one L ell eta hL hellL (le_of_lt heta) hetaL
  have hm := mul_lt_mul_of_pos_right hmu heta
  linarith

theorem rho_bounds (L ell a q R eta : ℝ) (hL : 0 < L)
    (hell : 0 < ell) (hellL : ell ≤ L) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (hR : 0 ≤ R) (heta : 0 ≤ eta) (hetaL : eta ≤ 1 / L) :
    1 / 2 ≤ 1 - drift ell a q R * eta ∧ 1 - drift ell a q R * eta ≤ 1 := by
  have hd := drift_bounds ell a q R (le_of_lt hell) ha hq hR
  have he := ell_step_le_one L ell eta hL hellL heta hetaL
  have hp := mul_nonneg (show 0 ≤ ell - 2 * drift ell a q R by linarith) heta
  have hd0 : 0 ≤ drift ell a q R := by linarith
  have hp0 := mul_nonneg hd0 heta
  constructor <;> nlinarith

section Normed
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Explicit u-gradient coefficient at u=-q. Analytic gradient
identification, including the cone boundary, is proved elsewhere. -/
def slowField (ell mu a q : ℝ) (v : V) : ℝ :=
  -mu * q + beta ell a * a * residual a q ‖v‖

def fastField (ell a q sigma : ℝ) (v xi : V) : V :=
  drift ell a q ‖v‖ • v + sigma • xi

def slowNext (ell mu a q eta : ℝ) (v : V) : ℝ :=
  (1 - mu * eta) * q + beta ell a * a * eta * residual a q ‖v‖

def fastNext (ell a q sigma eta : ℝ) (v xi : V) : V :=
  (1 - drift ell a q ‖v‖ * eta) • v - (sigma * eta) • xi

/-- If the slow component gradient is the displayed field, the ORIGINAL
u <- u-eta*gradient update, with q=-u, gives exactly slowNext. -/
theorem negative_slow_gradient_update (ell mu a q eta : ℝ) (v : V) :
    -((-q) - eta * slowField ell mu a q v) = slowNext ell mu a q eta v := by
  unfold slowField slowNext
  ring

/-- Exact ordinary scalar gradient update for the explicit fast field. -/
theorem fast_gradient_update (ell a q sigma eta : ℝ) (v xi : V) :
    v - eta • fastField ell a q sigma v xi = fastNext ell a q sigma eta v xi := by
  simp only [fastField, fastNext, smul_add, smul_smul, sub_smul, one_smul,
    sub_add_eq_sub_sub]
  rw [mul_comm eta (drift ell a q ‖v‖), mul_comm eta sigma]

theorem slowNext_positive (L ell mu a q eta : ℝ) (v : V)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : mu < ell) (ha : 0 ≤ a) (hq : 0 < q)
    (heta : 0 < eta) (hetaL : eta ≤ 1 / L) :
    0 < slowNext ell mu a q eta v := by
  have hp := mul_pos (retention_positive L ell mu eta hL hellL hmu heta hetaL) hq
  have hb := (beta_bounds ell a (le_of_lt hell)).1
  have hr := residual_nonneg a q ‖v‖
  unfold slowNext
  positivity

theorem slowNext_retention (ell mu a q eta : ℝ) (v : V)
    (hell : 0 ≤ ell) (ha : 0 ≤ a) (heta : 0 ≤ eta) :
    (1 - mu * eta) * q ≤ slowNext ell mu a q eta v := by
  have hb := (beta_bounds ell a hell).1
  have hr := residual_nonneg a q ‖v‖
  have hn : 0 ≤ beta ell a * a * eta * residual a q ‖v‖ := by positivity
  unfold slowNext
  linarith

theorem fastNext_radius_step (L ell a q sigma eta : ℝ) (v xi : V)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hsigma : 0 ≤ sigma)
    (heta : 0 ≤ eta) (hetaL : eta ≤ 1 / L) (hxi : ‖xi‖ = 1) :
    ‖fastNext ell a q sigma eta v xi‖ ≤ (1 - ell * eta / 4) * ‖v‖ + sigma * eta := by
  have hd := drift_bounds ell a q ‖v‖ (le_of_lt hell) ha hq (norm_nonneg v)
  have hr := rho_bounds L ell a q ‖v‖ eta hL hell hellL ha hq (norm_nonneg v) heta hetaL
  have h := norm_sub_le ((1 - drift ell a q ‖v‖ * eta) • v) ((sigma * eta) • xi)
  have hr0 : 0 ≤ 1 - drift ell a q ‖v‖ * eta := by linarith
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0,
    abs_of_nonneg (mul_nonneg hsigma heta), hxi, mul_one] at h
  have hde := mul_le_mul_of_nonneg_right hd.1 heta
  have hder := mul_le_mul_of_nonneg_right hde (norm_nonneg v)
  unfold fastNext
  nlinarith

theorem fastNext_radius_invariant (L ell a q sigma eta : ℝ) (v xi : V)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hsigma : 0 ≤ sigma)
    (heta : 0 ≤ eta) (hetaL : eta ≤ 1 / L) (hxi : ‖xi‖ = 1)
    (hv : ell * ‖v‖ ≤ 4 * sigma) :
    ell * ‖fastNext ell a q sigma eta v xi‖ ≤ 4 * sigma := by
  have hs := fastNext_radius_step L ell a q sigma eta v xi hL hell hellL ha hq hsigma
    heta hetaL hxi
  have he := ell_step_le_one L ell eta hL hellL heta hetaL
  have hf : 0 ≤ 1 - ell * eta / 4 := by linarith
  have hm := mul_le_mul_of_nonneg_left hv hf
  have hs' := mul_le_mul_of_nonneg_left hs (le_of_lt hell)
  nlinarith

/-- The explicit field trajectory. eta and xi are arbitrary realized
sequences, including sequences determined by the entire revealed bank and
history. No probabilistic independence or predetermined-step premise. -/
def fieldTrajectory (ell mu a sigma D : ℝ) (eta : ℕ → ℝ) (xi : ℕ → V) :
    ℕ → ℝ × V
  | 0 => (D, 0)
  | k + 1 =>
      let x := fieldTrajectory ell mu a sigma D eta xi k
      (slowNext ell mu a x.1 (eta k) x.2,
       fastNext ell a x.1 sigma (eta k) x.2 (xi k))

theorem fieldTrajectory_bounds (L ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (xi : ℕ → V) (T : ℕ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : mu < ell) (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L)
    (hxi : ∀ k < T, ‖xi k‖ = 1) :
    ∀ k ≤ T, 0 < (fieldTrajectory ell mu a sigma D eta xi k).1 ∧
      ell * ‖(fieldTrajectory ell mu a sigma D eta xi k).2‖ ≤ 4 * sigma := by
  intro k
  induction k with
  | zero =>
      intro hk
      simp only [fieldTrajectory, norm_zero, mul_zero]
      exact ⟨hD, by positivity⟩
  | succ k ih =>
      intro hk
      have hkT : k < T := by omega
      have hprev := ih (by omega)
      change 0 < slowNext ell mu a
          (fieldTrajectory ell mu a sigma D eta xi k).1 (eta k)
          (fieldTrajectory ell mu a sigma D eta xi k).2 ∧
        ell * ‖fastNext ell a (fieldTrajectory ell mu a sigma D eta xi k).1 sigma (eta k)
          (fieldTrajectory ell mu a sigma D eta xi k).2 (xi k)‖ ≤ 4 * sigma
      exact ⟨slowNext_positive L ell mu a _ _ _ hL hell hellL hmu ha hprev.1
          (heta k hkT) (hetaL k hkT),
        fastNext_radius_invariant L ell a _ sigma _ _ _ hL hell hellL ha
          (le_of_lt hprev.1) hsigma (le_of_lt (heta k hkT)) (hetaL k hkT)
          (hxi k hkT) hprev.2⟩

theorem fieldTrajectory_radius (L ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (xi : ℕ → V) (T : ℕ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : mu < ell) (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L)
    (hxi : ∀ k < T, ‖xi k‖ = 1) (k : ℕ) (hk : k ≤ T) :
    ‖(fieldTrajectory ell mu a sigma D eta xi k).2‖ ≤ 4 * sigma / ell := by
  apply (le_div_iff₀ hell).2
  have hh := (fieldTrajectory_bounds L ell mu a sigma D eta xi T
    hL hell hellL hmu ha hsigma hD heta hetaL hxi k hk).2
  simpa only [mul_comm] using hh
end Normed

section Euclidean
open Gate146.EuclideanCoordinates
variable {I : Type*} [Fintype I]

/-- Coordinate expansion in the genuine Euclidean wrapper, not the Pi
sup norm. This is the only extra algebra needed to reuse ScalarEnergy. -/
theorem affine_square (v xi : Vec I) (rho sigma eta : ℝ) (hxi : ‖xi‖ = 1) :
    ‖rho • v - (sigma * eta) • xi‖ ^ 2 =
      rho ^ 2 * ‖v‖ ^ 2 - 2 * rho * sigma * eta * dot v xi + sigma ^ 2 * eta ^ 2 := by
  have hunit : square xi = 1 := by rw [← norm_square, hxi]; norm_num
  have hid : square (rho • v - (sigma * eta) • xi) =
      rho ^ 2 * square v - 2 * rho * sigma * eta * dot v xi +
        (sigma ^ 2 * eta ^ 2) * square xi := by
    unfold square dot
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [coord_sub, coord_smul]
    ring
  rw [norm_square, hid, ← norm_square v, hunit, mul_one]

/-- Actual one-step energy for the displayed cone field; radius input is
later supplied by the proved trajectory invariant, never assumed there. -/
theorem fastNext_energy (L ell a q sigma eta : ℝ) (v xi : Vec I)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (ha : 0 ≤ a) (hq : 0 ≤ q) (hsigma : 0 ≤ sigma)
    (heta : 0 ≤ eta) (hetaL : eta ≤ 1 / L) (hxi : ‖xi‖ = 1)
    (hv : ell * ‖v‖ ≤ 4 * sigma) :
    sigma ^ 2 * eta ^ 2 ≤ ‖fastNext ell a q sigma eta v xi‖ ^ 2 - ‖v‖ ^ 2 +
      6 * sigma * eta * ‖v‖ := by
  have hd := drift_bounds ell a q ‖v‖ (le_of_lt hell) ha hq (norm_nonneg v)
  have hr := rho_bounds L ell a q ‖v‖ eta hL hell hellL ha hq (norm_nonneg v) heta hetaL
  have hw : dot v xi ≤ ‖v‖ := by
    have hh := (le_abs_self (dot v xi)).trans (dot_bound v xi)
    simpa only [hxi, mul_one] using hh
  exact Gate144.ScalarEnergy.scalar_energy_step ‖v‖
    ‖fastNext ell a q sigma eta v xi‖ sigma eta ell (drift ell a q ‖v‖)
    (1 - drift ell a q ‖v‖ * eta) (dot v xi)
    (norm_nonneg v) hsigma heta (by linarith) (by linarith) rfl (by linarith)
    hv hw (affine_square v xi _ sigma eta hxi)

/-- Signed interval energy for EVERY interval of the concrete field
trajectory. Both endpoint energies remain, including a negative initial
energy. No stopping-time or action/label independence premise occurs. -/
theorem fieldTrajectory_interval_energy (L ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (xi : ℕ → Vec I) (T s N : ℕ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : mu < ell) (ha : 0 ≤ a) (hsigma : 0 ≤ sigma) (hD : 0 < D)
    (heta : ∀ k < T, 0 < eta k) (hetaL : ∀ k < T, eta k ≤ 1 / L)
    (hxi : ∀ k < T, ‖xi k‖ = 1) (hN : s + N ≤ T) :
    sigma ^ 2 * (∑ k ∈ Finset.range N, (eta (s + k)) ^ 2) ≤
      ‖(fieldTrajectory ell mu a sigma D eta xi (s + N)).2‖ ^ 2 -
        ‖(fieldTrajectory ell mu a sigma D eta xi s).2‖ ^ 2 +
      6 * sigma * ∑ k ∈ Finset.range N,
        eta (s + k) * ‖(fieldTrajectory ell mu a sigma D eta xi (s + k)).2‖ := by
  apply Gate144.ScalarEnergy.energy_sum
    (fun k => ‖(fieldTrajectory ell mu a sigma D eta xi (s + k)).2‖)
    (fun k => eta (s + k)) sigma N
  intro k hk
  have hkt : s + k < T := by omega
  have hstate := fieldTrajectory_bounds L ell mu a sigma D eta xi T hL hell hellL
    hmu ha hsigma hD heta hetaL hxi (s + k) (by omega)
  have hh := fastNext_energy L ell a
    (fieldTrajectory ell mu a sigma D eta xi (s + k)).1 sigma (eta (s + k))
    (fieldTrajectory ell mu a sigma D eta xi (s + k)).2 (xi (s + k))
    hL hell hellL ha (le_of_lt hstate.1) hsigma (le_of_lt (heta _ hkt))
    (hetaL _ hkt) (hxi _ hkt) hstate.2
  simpa only [Nat.add_assoc] using hh
end Euclidean

#print axioms fraction_bounds
#print axioms drift_bounds
#print axioms rho_bounds
#print axioms negative_slow_gradient_update
#print axioms fast_gradient_update
#print axioms fieldTrajectory_bounds
#print axioms fieldTrajectory_radius
#print axioms affine_square
#print axioms fastNext_energy
#print axioms fieldTrajectory_interval_energy
end
end Gate147.ConeTrajectory