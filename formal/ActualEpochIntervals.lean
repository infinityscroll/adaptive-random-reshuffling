import GeometryDependency
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals




/-! A fresh wrapper with its explicitly proved Euclidean norm. It does not
reuse the default supremum norm of a function type or change that instance. -/
namespace Gate146.EuclideanCoordinates
noncomputable section
open scoped BigOperators

structure Vec (I : Type*) where
  coord : I → ℝ

def coordEquiv (I : Type*) : Vec I ≃ (I → ℝ) where
  toFun := Vec.coord
  invFun := Vec.mk
  left_inv x := by cases x; rfl
  right_inv x := rfl

instance (I : Type*) : AddCommGroup (Vec I) := (coordEquiv I).addCommGroup
instance (I : Type*) : Module ℝ (Vec I) := (coordEquiv I).module ℝ

@[simp] theorem coord_zero {I : Type*} (i : I) : (0 : Vec I).coord i = 0 := rfl
@[simp] theorem coord_add {I : Type*} (x y : Vec I) (i : I) :
    (x+y).coord i = x.coord i + y.coord i := rfl
@[simp] theorem coord_sub {I : Type*} (x y : Vec I) (i : I) :
    (x-y).coord i = x.coord i - y.coord i := rfl
@[simp] theorem coord_smul {I : Type*} (c : ℝ) (x : Vec I) (i : I) :
    (c • x).coord i = c*x.coord i := rfl

variable {I : Type*} [Fintype I]

def square (x : Vec I) : ℝ := ∑ i, x.coord i ^ 2
def dot (x y : Vec I) : ℝ := ∑ i, x.coord i*y.coord i
instance : Norm (Vec I) := ⟨fun x => Real.sqrt (square x)⟩

theorem square_nonneg (x : Vec I) : 0 ≤ square x :=
  Finset.sum_nonneg (fun i hi => sq_nonneg _)

theorem norm_formula (x : Vec I) : ‖x‖ = Real.sqrt (∑ i, x.coord i^2) := rfl

theorem norm_nonnegative (x : Vec I) : 0 ≤ ‖x‖ := Real.sqrt_nonneg _
theorem norm_square (x : Vec I) : ‖x‖^2 = square x := Real.sq_sqrt (square_nonneg x)

theorem dot_bound (x y : Vec I) : |dot x y| ≤ ‖x‖*‖y‖ := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x.coord y.coord
  have hx := norm_square x
  have hy := norm_square y
  apply abs_le_of_sq_le_sq ?_ (mul_nonneg (norm_nonnegative x) (norm_nonnegative y))
  change (dot x y)^2 ≤ (‖x‖*‖y‖)^2
  change (dot x y)^2 ≤ square x*square y at hc
  nlinarith

theorem norm_smul_euclidean (c : ℝ) (x : Vec I) : ‖c • x‖ = ‖c‖*‖x‖ := by
  have hs : square (c • x) = c^2*square x := by
    unfold square
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coord_smul]
    ring
  change Real.sqrt (square (c • x)) = ‖c‖*Real.sqrt (square x)
  rw [hs, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

theorem norm_triangle_euclidean (x y : Vec I) : ‖x+y‖ ≤ ‖x‖+‖y‖ := by
  have hs : square (x+y) = square x+square y+2*dot x y := by
    unfold square dot
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coord_add]
    ring
  have hc := (le_abs_self (dot x y)).trans (dot_bound x y)
  have hx := norm_square x
  have hy := norm_square y
  have hz := norm_square (x+y)
  have hn := norm_nonnegative (x+y)
  have hnx := norm_nonnegative x
  have hny := norm_nonnegative y
  nlinarith

theorem norm_zero_iff_euclidean (x : Vec I) : ‖x‖=0 ↔ x=0 := by
  constructor
  · intro h
    have hs : square x=0 := by have hh := norm_square x; rw [h] at hh; simpa using hh.symm
    apply (coordEquiv I).injective
    funext i
    change x.coord i=0
    have hi : x.coord i^2 ≤ square x :=
      Finset.single_le_sum (fun j hj => sq_nonneg (x.coord j)) (Finset.mem_univ i)
    rw [hs] at hi
    nlinarith [sq_nonneg (x.coord i)]
  · intro h; subst x; simp [norm_formula]

def euclideanCore : NormedSpace.Core ℝ (Vec I) where
  norm_nonneg := norm_nonnegative
  norm_smul := norm_smul_euclidean
  norm_triangle := norm_triangle_euclidean
  norm_eq_zero_iff := norm_zero_iff_euclidean

instance : NormedAddCommGroup (Vec I) := NormedAddCommGroup.ofCore euclideanCore
instance : NormedSpace ℝ (Vec I) := NormedSpace.ofCore euclideanCore

/-- The test is linear on the same genuine Euclidean normed vector space. -/
def test (phi : Vec I) : Vec I →ₗ[ℝ] ℝ where
  toFun := dot phi
  map_add' x y := by
    simp only [dot, coord_add, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [dot, coord_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem test_bound (phi z : Vec I) : |test phi z| ≤ ‖phi‖*‖z‖ := dot_bound phi z

#print axioms euclideanCore
#print axioms norm_formula
#print axioms norm_square
#print axioms test_bound
end
end Gate146.EuclideanCoordinates



/-!
Gate146: actual fixed-bank, every-interval geometric envelope.
Compile after Gate145 ActualPermutationGeometry and Gate146
EuclideanCoordinates, with Mathlib.Algebra.BigOperators.Intervals available.
The fresh Vec wrapper has its proved Euclidean norm, not a Pi sup norm.
No desired total variation or hgeo bound is assumed by the final theorem.
-/

namespace Gate146.EpochInterval

open scoped BigOperators
open EuclideanCoordinates
open Gate145.PermutationHitBridge Gate145.HitAssembly Gate145.PermutationMarginal

noncomputable section

variable {I : Type*} [Fintype I]

theorem test_sub_apply (u v z : Vec I) :
    test (u - v) z = test u z - test v z := by
  change dot (u - v) z = dot u z - dot v z
  simp only [dot, coord_sub, sub_mul, Finset.sum_sub_distrib]

theorem dual_by_parts (phi z : ℕ → Vec I) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), test (phi k) (z k - z (k + 1))) =
      test (phi 0) (z 0) - test (phi N) (z (N + 1)) +
        ∑ k ∈ Finset.range N, test (phi (k + 1) - phi k) (z (k + 1)) := by
  induction N with
  | zero => simp [map_sub]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp only [map_sub, test_sub_apply]
      ring

theorem shifted_nonnegative_sum_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (l N M : ℕ) (h : l + N ≤ M) :
    (∑ k ∈ Finset.range N, f (l + k)) ≤ ∑ k ∈ Finset.range M, f k := by
  have hp : 0 ≤ ∑ k ∈ Finset.range l, f k :=
    Finset.sum_nonneg (fun k hk => hf k)
  have hpre : (∑ k ∈ Finset.range (l + N), f k) ≤
      ∑ k ∈ Finset.range M, f k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
      (fun k hk hnot => hf k)
  rw [Finset.sum_range_add] at hpre
  linarith

/-- The linear variation estimate is DERIVED from the squared variation. -/
theorem linear_variation_bound (phi : ℕ → Vec I) (n : ℕ) (B : ℝ)
    (hB : 0 ≤ B)
    (hsq : (∑ k ∈ Finset.range (n - 1), ‖phi (k + 1) - phi k‖ ^ 2) ≤ 25 * B) :
    (∑ k ∈ Finset.range (n - 1), ‖phi (k + 1) - phi k‖) ≤
      5 * Real.sqrt ((n - 1 : ℕ) : ℝ) * Real.sqrt B := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n - 1))
    (fun _ => (1 : ℝ)) (fun k => ‖phi (k + 1) - phi k‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at hc
  have hnm : (0 : ℝ) ≤ (n - 1 : ℕ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hsq hnm
  have hroot : (5 * Real.sqrt ((n - 1 : ℕ) : ℝ) * Real.sqrt B) ^ 2 =
      ((n - 1 : ℕ) : ℝ) * (25 * B) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hnm, Real.sq_sqrt hB]
    ring
  apply le_of_sq_le_sq ?_ (by positivity)
  rw [hroot]
  exact hc.trans hm

/-- A contiguous fragment of one epoch. This reusable lemma is conditional
on primitive norm/variation bounds; the actual-table theorem discharges them. -/
theorem epoch_fragment_bound (phi z : ℕ → Vec I) (n l len : ℕ)
    (A R V : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) (hV : 0 ≤ V)
    (hlen : l + len ≤ n)
    (hphi : ∀ j < n, ‖phi j‖ ≤ R)
    (hz : ∀ j, l ≤ j → j ≤ l + len → ‖z j‖ ≤ A)
    (hvar : (∑ j ∈ Finset.range (n - 1), ‖phi (j + 1) - phi j‖) ≤ V) :
    (∑ k ∈ Finset.range len,
      test (phi (l + k)) (z (l + k) - z (l + k + 1))) ≤ A * (2 * R + V) := by
  cases len with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ N =>
      have hstart : test (phi l) (z l) ≤ R * A :=
        (le_abs_self _).trans ((test_bound _ _).trans
          (mul_le_mul (hphi l (by omega)) (hz l (le_refl _) (by omega))
            (norm_nonneg _) hR))
      have hend : -test (phi (l + N)) (z (l + N + 1)) ≤ R * A :=
        (neg_le_abs _).trans ((test_bound _ _).trans
          (mul_le_mul (hphi (l + N) (by omega))
            (hz (l + N + 1) (by omega) (by omega)) (norm_nonneg _) hR))
      have hpoint : ∀ k < N,
          test (phi (l + k + 1) - phi (l + k)) (z (l + k + 1)) ≤
            A * ‖phi (l + k + 1) - phi (l + k)‖ := by
        intro k hk
        have hh := (le_abs_self _).trans
          (test_bound (phi (l + k + 1) - phi (l + k)) (z (l + k + 1)))
        have hz' := hz (l + k + 1) (by omega) (by omega)
        have hm := mul_le_mul_of_nonneg_left hz' (norm_nonneg (phi (l + k + 1) - phi (l + k)))
        nlinarith
      have hsum := Finset.sum_le_sum (s := Finset.range N)
        (fun k hk => hpoint k (Finset.mem_range.mp hk))
      rw [← Finset.mul_sum] at hsum
      have hshift := shifted_nonnegative_sum_le
        (fun j => ‖phi (j + 1) - phi j‖) (fun j => norm_nonneg _)
        l N (n - 1) (by omega)
      have hlast := mul_le_mul_of_nonneg_left (hshift.trans hvar) hA
      have hparts := dual_by_parts (fun k => phi (l + k)) (fun k => z (l + k)) N
      simp only [Nat.add_zero, Nat.add_assoc] at hparts
      simp only [Nat.add_assoc] at hsum hlast
      simp only [Nat.add_assoc] at hend ⊢
      rw [hparts]
      nlinarith

def clip (n base x : ℕ) : ℕ := min n (x - base)

theorem clip_order (n base s t : ℕ) (hst : s ≤ t) :
    clip n base s ≤ clip n base t := by
  unfold clip
  omega

theorem clip_interval (n base s t j : ℕ)
    (h : clip n base s < clip n base t)
    (hlo : clip n base s ≤ j) (hhi : j ≤ clip n base t) :
    s ≤ base + j ∧ base + j ≤ t := by
  unfold clip at *
  omega

theorem clip_sum (f : ℕ → ℝ) (n base s t : ℕ) :
    (∑ j ∈ Finset.Ico (clip n base s) (clip n base t), f j) =
      ∑ j ∈ Finset.range n, if s ≤ base + j ∧ base + j < t then f j else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, clip]
  omega

theorem clipped_epoch_bound (phi z : ℕ → Vec I) (n base s t : ℕ)
    (A R V : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R) (hV : 0 ≤ V)
    (hst : s ≤ t) (hphi : ∀ j < n, ‖phi j‖ ≤ R)
    (hz : ∀ k, s ≤ k → k ≤ t → ‖z k‖ ≤ A)
    (hvar : (∑ j ∈ Finset.range (n - 1), ‖phi (j + 1) - phi j‖) ≤ V) :
    (∑ j ∈ Finset.range n, if s ≤ base + j ∧ base + j < t then
      test (phi j) (z (base + j) - z (base + j + 1)) else 0) ≤ A * (2 * R + V) := by
  rw [← clip_sum (fun j => test (phi j) (z (base + j) - z (base + j + 1))) n base s t]
  have hlohi := clip_order n base s t hst
  by_cases hempty : clip n base s = clip n base t
  · rw [hempty, Finset.Ico_self, Finset.sum_empty]
    positivity
  · have hstrict : clip n base s < clip n base t := by omega
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen : clip n base s + (clip n base t - clip n base s) ≤ n := by
      unfold clip at *
      omega
    have hz' : ∀ j, clip n base s ≤ j →
        j ≤ clip n base s + (clip n base t - clip n base s) →
        ‖z (base + j)‖ ≤ A := by
      intro j hjlo hjhi
      have hjhi' : j ≤ clip n base t := by omega
      have hglobal := clip_interval n base s t j hstrict hjlo hjhi'
      exact hz _ hglobal.1 hglobal.2
    have hh := epoch_fragment_bound phi (fun j => z (base + j)) n
      (clip n base s) (clip n base t - clip n base s) A R V
      hA hR hV hlen hphi hz' hvar
    simpa only [Nat.add_assoc] using hh

/-- Exact decomposition of an arbitrary finite sum into n-step epochs. -/
theorem sum_blocks (f : ℕ → ℝ) (n K : ℕ) :
    (∑ k ∈ Finset.range (n * K), f k) =
      ∑ e ∈ Finset.range K, ∑ j ∈ Finset.range n, f (n * e + j) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem interval_as_mask (f : ℕ → ℝ) (s t T : ℕ) (ht : t ≤ T) :
    (∑ k ∈ Finset.Ico s t, f k) =
      ∑ k ∈ Finset.range T, if s ≤ k ∧ k < t then f k else 0 := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
  omega

/-- The actual finite-coordinate table, wrapped in its genuine Euclidean
norm. Coordinates and fixed labels are exactly those proved in Gate145. -/
def epochVec {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (g : Equiv.Perm (Fin n)) (j : ℕ) :
    Vec (Σ b : Fin r, Fin (size b)) :=
  ⟨globalDualAt size labels hinj g hm j⟩

def gapSum {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (g : Equiv.Perm (Fin n)) : ℝ :=
  ∑ b : Fin r, (1 : ℝ) /
    ((Gate145.ActualGap.selectedGap (g⁻¹ • hitSet (labels b) (hinj b)) (hm b) : ℕ) : ℝ)

theorem gapSum_nonneg {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (g : Equiv.Perm (Fin n)) :
    0 ≤ gapSum size labels hinj hm g := by
  unfold gapSum
  exact Finset.sum_nonneg (fun b hb => by positivity)

theorem actual_epoch_norm {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (g : Equiv.Perm (Fin n)) (j : ℕ) :
    ‖epochVec size labels hinj hm g j‖ ≤ 4 * Real.sqrt (r : ℝ) := by
  have hs : ‖epochVec size labels hinj hm g j‖ ^ 2 ≤ 16 * (r : ℝ) := by
    rw [norm_square]
    exact global_squared_bound size labels hinj g hm hm5 j
  have hr : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt (by positivity)
  apply le_of_sq_le_sq ?_ (by positivity)
  nlinarith

theorem actual_epoch_squared_variation {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (g : Equiv.Perm (Fin n)) :
    (∑ j ∈ Finset.range (n - 1),
      ‖epochVec size labels hinj hm g (j + 1) - epochVec size labels hinj hm g j‖ ^ 2) ≤
      25 * gapSum size labels hinj hm g := by
  have hh := global_variation_bound size labels hinj g hm hm5 (n - 1)
  simpa only [norm_square, square, coord_sub, epochVec, gapSum] using hh

theorem actual_epoch_linear_variation {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (g : Equiv.Perm (Fin n)) :
    (∑ j ∈ Finset.range (n - 1),
      ‖epochVec size labels hinj hm g (j + 1) - epochVec size labels hinj hm g j‖) ≤
      5 * Real.sqrt ((n - 1 : ℕ) : ℝ) * Real.sqrt (gapSum size labels hinj hm g) := by
  exact linear_variation_bound (epochVec size labels hinj hm g) n
    (gapSum size labels hinj hm g) (gapSum_nonneg size labels hinj hm g)
    (actual_epoch_squared_variation size labels hinj hm hm5 g)

/-- Only the first K entries of bank are used on[0,nK). A finite bank can
be extended arbitrarily outside that range without affecting the theorem. -/
def bankTable {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (bank : ℕ → Equiv.Perm (Fin n)) (t : ℕ) :
    Vec (Σ b : Fin r, Fin (size b)) :=
  epochVec size labels hinj hm (bank (t / n)) (t % n)

theorem bankTable_at_epoch {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (bank : ℕ → Equiv.Perm (Fin n))
    (hn : 0 < n) (e j : ℕ) (hj : j < n) :
    bankTable size labels hinj hm bank (n * e + j) =
      epochVec size labels hinj hm (bank e) j := by
  have hd : (n * e + j) / n = e := by
    rw [Nat.add_comm, Nat.add_mul_div_left j e hn, Nat.div_eq_of_lt hj, zero_add]
  have hr : (n * e + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [bankTable, hd, hr]

/-- Same fixed bank, EVERY interval and EVERY bounded auxiliary path.
The8K endpoint budget is paid by at most two endpoints per clipped epoch;
no boundary or final unsafe tail is discarded. -/
theorem actual_bank_interval {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (bank : ℕ → Equiv.Perm (Fin n)) (n2 : 2 ≤ n) (K s t : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (hst : s ≤ t) (ht : t ≤ n * K)
    (z : ℕ → Vec (Σ b : Fin r, Fin (size b)))
    (hz : ∀ k, s ≤ k → k ≤ t → ‖z k‖ ≤ A) :
    (∑ k ∈ Finset.Ico s t,
      test (bankTable size labels hinj hm bank k) (z k - z (k + 1))) ≤
      A * (8 * (K : ℝ) * Real.sqrt (r : ℝ) +
        5 * Real.sqrt ((n - 1 : ℕ) : ℝ) *
          ∑ e ∈ Finset.range K, Real.sqrt (gapSum size labels hinj hm (bank e))) := by
  rw [interval_as_mask _ s t (n * K) ht, sum_blocks]
  have hepoch : ∀ e,
      (∑ j ∈ Finset.range n, if s ≤ n * e + j ∧ n * e + j < t then
        test (bankTable size labels hinj hm bank (n * e + j))
          (z (n * e + j) - z (n * e + j + 1)) else 0) ≤
        A * (2 * (4 * Real.sqrt (r : ℝ)) +
          5 * Real.sqrt ((n - 1 : ℕ) : ℝ) *
            Real.sqrt (gapSum size labels hinj hm (bank e))) := by
    intro e
    have hh := clipped_epoch_bound (epochVec size labels hinj hm (bank e)) z
      n (n * e) s t A (4 * Real.sqrt (r : ℝ))
      (5 * Real.sqrt ((n - 1 : ℕ) : ℝ) * Real.sqrt (gapSum size labels hinj hm (bank e)))
      hA (by positivity) (by positivity) hst
      (fun j hj => actual_epoch_norm size labels hinj hm hm5 (bank e) j) hz
      (actual_epoch_linear_variation size labels hinj hm hm5 (bank e))
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [bankTable_at_epoch size labels hinj hm bank (by omega) e j
      (Finset.mem_range.mp hj)]
  have hsum := Finset.sum_le_sum (s := Finset.range K) (fun e he => hepoch e)
  calc
    _ ≤ ∑ e ∈ Finset.range K,
        A * (2 * (4 * Real.sqrt (r : ℝ)) +
          5 * Real.sqrt ((n - 1 : ℕ) : ℝ) *
            Real.sqrt (gapSum size labels hinj hm (bank e))) := hsum
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The exact shifted-range hgeo interface used by Gate144 paid_reset_chain.
It is derived for actual tables and needs no assumption on when or how the
interval or auxiliary path was selected. -/
theorem actual_interval_hgeo {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (bank : ℕ → Equiv.Perm (Fin n)) (n2 : 2 ≤ n) (K s N : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (hN : s + N ≤ n * K) :
    ∀ z : ℕ → Vec (Σ b : Fin r, Fin (size b)), (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ Finset.range N,
        test (bankTable size labels hinj hm bank (s + k)) (z k - z (k + 1))) ≤
        A * (8 * (K : ℝ) * Real.sqrt (r : ℝ) +
          5 * Real.sqrt ((n - 1 : ℕ) : ℝ) *
            ∑ e ∈ Finset.range K, Real.sqrt (gapSum size labels hinj hm (bank e))) := by
  intro z hz
  have hz' : ∀ k, s ≤ k → k ≤ s + N → ‖z (k - s)‖ ≤ A := by
    intro k hk hkt
    apply hz
    omega
  have hh := actual_bank_interval size labels hinj hm hm5 bank n2 K s (s + N)
    A hA (by omega) hN (fun k => z (k - s)) hz'
  rw [Finset.sum_Ico_eq_sum_range] at hh
  simpa [Nat.add_assoc] using hh

#print axioms dual_by_parts
#print axioms epoch_fragment_bound
#print axioms clipped_epoch_bound
#print axioms actual_epoch_norm
#print axioms actual_epoch_squared_variation
#print axioms actual_bank_interval
#print axioms actual_interval_hgeo

end
end Gate146.EpochInterval