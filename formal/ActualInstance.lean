import ActualObjective
import EuclideanModel
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.FieldSimp

/-!
Gate148: actual fixed labeled components on the inherited Euclidean fast
subspace and the genuine L2 slow/fast product. All centering and unit-norm
facts are the proved Gate146 facts for fastXi, not instance hypotheses.
The full derivative and global convexity/smoothness come from the accepted
Gate147 actual projection objective. The drop-last map is used only through
the accepted finrank theorem, never to transport a norm.

This module establishes the actual instance data. It does not assert the
final lower risk, paid-reset estimate, tuned parameter inequalities, or
the identification of an adaptive bank trajectory with the complete model.
Root alone compiles this source; the author performs no compiler execution.
-/
namespace Gate148.ActualInstance
noncomputable section
open scoped BigOperators InnerProductSpace
open Gate146.LabeledBlocks Gate146.FastSpaceOffsets
open Gate147

abbrev Space {n : ℕ} (P : Partition n) := EuclideanModel.State P

def component {n : ℕ} (P : Partition n) (mu ell a sigma : ℝ)
    (i : Fin n) (x : Space P) : ℝ :=
  ActualObjective.component mu ell a sigma (fastXi P i) x

def componentGradient {n : ℕ} (P : Partition n) (mu ell a sigma : ℝ)
    (i : Fin n) (x : Space P) : Space P :=
  ActualObjective.componentGradient mu ell a sigma (fastXi P i) x

def mean {n : ℕ} (P : Partition n) (mu ell a sigma : ℝ) (x : Space P) : ℝ :=
  (∑ i : Fin n, component P mu ell a sigma i x) / (n : ℝ)

def meanGradient {n : ℕ} (P : Partition n) (mu ell a sigma : ℝ)
    (x : Space P) : Space P :=
  (1 / (n : ℝ)) • ∑ i : Fin n, componentGradient P mu ell a sigma i x

def initial {n : ℕ} (P : Partition n) (D : ℝ) : Space P :=
  EuclideanModel.ofSlowFast P (-D) 0

theorem centered_inner {n : ℕ} (P : Partition n) (v : fastSpace P.size) :
    (∑ i : Fin n, inner ℝ (fastXi P i) v) = 0 := by
  rw [← sum_inner, fastXi_centered, inner_zero_left]

theorem centered_offsets {n : ℕ} (P : Partition n) (sigma : ℝ) :
    (∑ i : Fin n, ActualObjective.offset sigma (fastXi P i)) = (0 : Space P) := by
  apply ext_inner_right ℝ
  intro x
  rw [sum_inner]
  simp_rw [ActualObjective.offset_pairing]
  rw [← Finset.mul_sum, centered_inner]
  simp

theorem component_sum {n : ℕ} (P : Partition n) (mu ell a sigma : ℝ)
    (x : Space P) :
    (∑ i : Fin n, component P mu ell a sigma i x) =
      (n : ℝ) * ActualObjective.Phi mu ell a x := by
  unfold component ActualObjective.component
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, centered_inner]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_zero, add_zero]

/-- The actual finite mean, not a prescribed surrogate objective. -/
theorem mean_eq_Phi {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) (x : Space P) :
    mean P mu ell a sigma x = ActualObjective.Phi mu ell a x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold mean
  rw [component_sum]
  exact mul_div_cancel_left₀ _ hn0

theorem componentGradient_sum {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (x : Space P) :
    (∑ i : Fin n, componentGradient P mu ell a sigma i x) =
      (n : ℝ) • ActualObjective.phiGradient mu ell a x := by
  unfold componentGradient ActualObjective.componentGradient
  rw [Finset.sum_add_distrib, centered_offsets]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, add_zero,
    Nat.cast_smul_eq_nsmul]

theorem meanGradient_eq {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) (x : Space P) :
    meanGradient P mu ell a sigma x = ActualObjective.phiGradient mu ell a x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold meanGradient
  rw [componentGradient_sum, smul_smul]
  simp [hn0]

theorem component_hasFDerivAt {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (i : Fin n) (hmu : 0 ≤ mu) (hell : 0 ≤ ell)
    (x : Space P) :
    HasFDerivAt (component P mu ell a sigma i)
      (innerSL ℝ (componentGradient P mu ell a sigma i x)) x :=
  ActualObjective.component_hasFDerivAt mu ell a sigma (fastXi P i) hmu hell x

theorem mean_hasFDerivAt {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell) (x : Space P) :
    HasFDerivAt (mean P mu ell a sigma)
      (innerSL ℝ (meanGradient P mu ell a sigma x)) x := by
  have hf : mean P mu ell a sigma = ActualObjective.Phi mu ell a := by
    funext y
    exact mean_eq_Phi P hn mu ell a sigma y
  rw [hf, meanGradient_eq P hn]
  exact ActualObjective.Phi_hasFDerivAt mu ell a hmu hell x

theorem phiGradient_zero {n : ℕ} (P : Partition n) (mu ell a : ℝ) :
    ActualObjective.phiGradient mu ell a (0 : Space P) = 0 := by
  simp [ActualObjective.phiGradient, QuadraticField.baseGradient,
    ActualObjective.coneResidual_zero]

theorem componentGradient_zero {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (i : Fin n) :
    componentGradient P mu ell a sigma i 0 =
      ActualObjective.offset sigma (fastXi P i) := by
  unfold componentGradient ActualObjective.componentGradient
  rw [phiGradient_zero P, zero_add]

theorem meanGradient_zero {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) : meanGradient P mu ell a sigma 0 = 0 := by
  rw [meanGradient_eq P hn, phiGradient_zero P]

theorem componentGradient_zero_norm_sq {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (i : Fin n) :
    ‖componentGradient P mu ell a sigma i 0‖ ^ 2 = sigma ^ 2 := by
  rw [componentGradient_zero, EuclideanModel.state_norm_square P]
  simp only [ActualObjective.offset, WithLp.toLp_fst, WithLp.toLp_snd,
    zero_pow (by omega : (2 : ℕ) ≠ 0), zero_add, norm_smul, Real.norm_eq_abs]
  change (|sigma| * ‖fastXi P i‖) ^ 2 = sigma ^ 2
  rw [fastXi_norm, mul_one, sq_abs]

/-- Exact variance at the actual minimizer. No desired variance premise. -/
theorem variance_at_zero {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) :
    (∑ i : Fin n, ‖componentGradient P mu ell a sigma i 0‖ ^ 2) / (n : ℝ) =
      sigma ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp_rw [componentGradient_zero_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hn0

theorem centered_variance_at_zero {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) :
    (∑ i : Fin n,
      ‖componentGradient P mu ell a sigma i 0 - meanGradient P mu ell a sigma 0‖ ^ 2) /
      (n : ℝ) = sigma ^ 2 := by
  simp_rw [meanGradient_zero P hn, sub_zero]
  exact variance_at_zero P hn mu ell a sigma

theorem mean_zero {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) : mean P mu ell a sigma 0 = 0 := by
  rw [mean_eq_Phi P hn, ActualObjective.Phi_zero]

theorem mean_minimized_at_zero {n : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (mu ell a sigma : ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell) :
    ∀ x : Space P, mean P mu ell a sigma 0 ≤ mean P mu ell a sigma x := by
  intro x
  rw [mean_eq_Phi P hn, mean_eq_Phi P hn]
  exact ActualObjective.Phi_minimized_at_zero mu ell a hmu hell x

theorem initial_norm {n : ℕ} (P : Partition n) (D : ℝ) (hD : 0 ≤ D) :
    ‖initial P D‖ = D := by
  apply (sq_eq_sq₀ (norm_nonneg _) hD).mp
  rw [EuclideanModel.state_norm_square P]
  simp [initial]

theorem initial_distance {n : ℕ} (P : Partition n) (D : ℝ) (hD : 0 ≤ D) :
    dist (initial P D) (0 : Space P) = D := by
  simpa only [dist_zero_right] using initial_norm P D hD

theorem component_convex {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (i : Fin n) (hmu : 0 ≤ mu) (hell : 0 ≤ ell) :
    ConvexOn ℝ Set.univ (component P mu ell a sigma i) :=
  ActualObjective.component_convex mu ell a sigma (fastXi P i) hmu hell

/-- Original class smoothness L; the actual stronger ell/2 bound is retained. -/
theorem componentGradient_norm_sub_le {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (i : Fin n) (hmu : 0 ≤ mu) (hcap : mu ≤ ell / 4)
    (x y : Space P) :
    ‖componentGradient P mu ell a sigma i x - componentGradient P mu ell a sigma i y‖ ≤
      (ell / 2) * ‖x - y‖ :=
  ActualObjective.componentGradient_norm_sub_le mu ell a sigma (fastXi P i) hmu hcap x y

theorem componentGradient_L_lipschitz {n : ℕ} (P : Partition n)
    (L mu ell a sigma : ℝ) (i : Fin n) (hL : 0 < L)
    (hmu : 0 ≤ mu) (hcap : mu ≤ ell / 4) (hellL : ell ≤ L) :
    LipschitzWith ⟨L, le_of_lt hL⟩ (componentGradient P mu ell a sigma i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := componentGradient_norm_sub_le P mu ell a sigma i hmu hcap x y
  have hEL : ell / 2 ≤ L := by linarith
  simpa only [dist_eq_norm] using
    hh.trans (mul_le_mul_of_nonneg_right hEL (norm_nonneg (x - y)))

/-- The bounded-below assertion in Gate134 Section1 is also actual, even
though it is not an extra premise of the model in its Section0. -/
theorem component_lower_bound {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (i : Fin n) (hmu : 0 ≤ mu) (hell : 0 < ell)
    (x : Space P) : -(2 * sigma ^ 2 / ell) ≤ component P mu ell a sigma i x := by
  have hi : |inner ℝ (fastXi P i) x.snd| ≤ ‖x.snd‖ := by
    simpa only [fastXi_norm, one_mul] using abs_real_inner_le_norm (fastXi P i) x.snd
  have hlinabs : |sigma * inner ℝ (fastXi P i) x.snd| ≤ |sigma| * ‖x.snd‖ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hi (abs_nonneg sigma)
  have hlin : -|sigma| * ‖x.snd‖ ≤ sigma * inner ℝ (fastXi P i) x.snd := by
    have hn := neg_abs_le (sigma * inner ℝ (fastXi P i) x.snd)
    linarith
  have hs := sq_nonneg (ell * ‖x.snd‖ - 4 * |sigma|)
  have habs : |sigma| ^ 2 = sigma ^ 2 := sq_abs sigma
  have hquad : -(2 * sigma ^ 2) / ell ≤ ell * ‖x.snd‖ ^ 2 / 8 - |sigma| * ‖x.snd‖ := by
    apply (div_le_iff₀ hell).2
    nlinarith
  have hd := ActualObjective.halfConeDistance_nonneg a x
  have hdist := mul_nonneg (show 0 ≤ ell / 4 by positivity) hd
  have hslow := mul_nonneg hmu (sq_nonneg x.fst)
  unfold component ActualObjective.component ActualObjective.Phi QuadraticField.quadratic
  rw [neg_div] at hquad
  linarith

theorem component_bddBelow {n : ℕ} (P : Partition n)
    (mu ell a sigma : ℝ) (i : Fin n) (hmu : 0 ≤ mu) (hell : 0 < ell) :
    BddBelow (Set.range (component P mu ell a sigma i)) := by
  refine ⟨-(2 * sigma ^ 2 / ell), ?_⟩
  rintro y ⟨x, rfl⟩
  exact component_lower_bound P mu ell a sigma i hmu hell x

theorem dimension {n : ℕ} (P : Partition n) :
    Module.finrank ℝ (Space P) = n - P.count + 1 :=
  EuclideanModel.state_finrank P

theorem dimension_le {n : ℕ} (P : Partition n) :
    Module.finrank ℝ (Space P) ≤ n := EuclideanModel.state_dimension_bound P

/-- A fixed actual partition is constructed for EVERY n>=2, before a policy
or bank is supplied. All preceding theorems apply to this same choice. -/
abbrev fixedSpace (n : ℕ) (hn : 2 ≤ n) := Space (fixedPartition n hn)

theorem fixed_dimension_le (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank ℝ (fixedSpace n hn) ≤ n := dimension_le (fixedPartition n hn)

#print axioms centered_inner
#print axioms centered_offsets
#print axioms mean_eq_Phi
#print axioms meanGradient_eq
#print axioms component_hasFDerivAt
#print axioms mean_hasFDerivAt
#print axioms meanGradient_zero
#print axioms variance_at_zero
#print axioms centered_variance_at_zero
#print axioms mean_minimized_at_zero
#print axioms initial_distance
#print axioms component_convex
#print axioms componentGradient_L_lipschitz
#print axioms component_lower_bound
#print axioms component_bddBelow
#print axioms fixed_dimension_le

end
end Gate148.ActualInstance
