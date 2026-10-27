import ActualStaticModel
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Sqrt




/-!
Gate134(9)->(10), for an exact finite probability space. This does not assume
actions independent of current labels. The input squared-moment bound still
has to be established for actual uniform permutations by the counting proof.
beta(e,w) is intended as sqrt(B_e(w)); its nonnegativity and squared mean
bound are the precise inputs. No claim that an assumed E B<=4 is proved here.
-/

namespace Gate145.EpochExpectation

theorem weighted_root_bound {W : Type*} [Fintype W]
    (p beta : W → ℝ) (hp : ∀ w, 0 ≤ p w)
    (hnorm : ∑ w, p w = 1) (hbeta : ∀ w, 0 ≤ beta w)
    (hsecond : (∑ w, p w * beta w ^ 2) ≤ 4) :
    (∑ w, p w * beta w) ≤ 2 := by
  let m := ∑ w, p w * beta w
  have hm : 0 ≤ m := Finset.sum_nonneg (fun w hw => mul_nonneg (hp w) (hbeta w))
  have hv : 0 ≤ ∑ w, p w * (beta w - m) ^ 2 :=
    Finset.sum_nonneg (fun w hw => mul_nonneg (hp w) (sq_nonneg _))
  have heq : (∑ w, p w * (beta w - m) ^ 2) =
      (∑ w, p w * beta w ^ 2) - m ^ 2 := by
    have he : (∑ w, p w * (beta w - m) ^ 2) =
        (∑ w, p w * beta w ^ 2) - 2 * m * (∑ w, p w * beta w) +
          m ^ 2 * (∑ w, p w) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    rw [he, hnorm]
    change _ - 2 * m * m + m ^ 2 * 1 = _
    ring
  rw [heq] at hv
  change m ≤ 2
  nlinarith

theorem expected_G_bound {W : Type*} [Fintype W]
    (K : ℕ) (p : W → ℝ) (beta : Fin K → W → ℝ)
    (A rootBlocks rootN rootNm1 : ℝ)
    (hp : ∀ w, 0 ≤ p w) (hnorm : ∑ w, p w = 1)
    (hbeta : ∀ e w, 0 ≤ beta e w)
    (hsecond : ∀ e, (∑ w, p w * beta e w ^ 2) ≤ 4)
    (hA : 0 ≤ A) (hr : 0 ≤ rootBlocks) (hn : 0 ≤ rootN)
    (hnm1 : 0 ≤ rootNm1) (hnm1n : rootNm1 ≤ rootN)
    (hratio : 2 * rootBlocks ^ 2 ≤ rootN ^ 2) :
    (∑ w, p w * (A * (8 * (K : ℝ) * rootBlocks +
      5 * rootNm1 * ∑ e, beta e w))) ≤ 16 * A * (K : ℝ) * rootN := by
  have hk : (0 : ℝ) ≤ K := by positivity
  have hroot : 8 * rootBlocks ≤ 6 * rootN := by nlinarith
  have hmeans : ∀ e : Fin K, (∑ w, p w * beta e w) ≤ 2 :=
    fun e => weighted_root_bound p (beta e) hp hnorm (hbeta e) (hsecond e)
  have hall : (∑ e : Fin K, ∑ w, p w * beta e w) ≤ 2 * (K : ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun e he => hmeans e)
    simpa [mul_comm] using hh
  have hid : (∑ w, p w * (A * (8 * (K : ℝ) * rootBlocks +
      5 * rootNm1 * ∑ e, beta e w))) =
      A * (8 * (K : ℝ) * rootBlocks +
        5 * rootNm1 * ∑ e : Fin K, ∑ w, p w * beta e w) := by
    have hpoint : ∀ w, p w * (A * (8 * (K : ℝ) * rootBlocks +
        5 * rootNm1 * ∑ e, beta e w)) =
        (A * 8 * (K : ℝ) * rootBlocks) * p w +
          (A * 5 * rootNm1) * ∑ e, p w * beta e w := by
      intro w
      rw [← Finset.mul_sum]
      ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnorm,
      Finset.sum_comm]
    ring
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left hall (show 0 ≤ 5 * rootNm1 by positivity)
  have hs := mul_le_mul_of_nonneg_right hnm1n (show 0 ≤ 10 * (K : ℝ) by positivity)
  have hb := mul_le_mul_of_nonneg_right hroot hk
  have hinside : 8 * (K : ℝ) * rootBlocks +
      5 * rootNm1 * (∑ e : Fin K, ∑ w, p w * beta e w) ≤
      16 * (K : ℝ) * rootN := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hinside hA
  nlinarith

#print axioms weighted_root_bound
#print axioms expected_G_bound

end Gate145.EpochExpectation

/-!
Compile after ActualGap and EpochExpectation, with additional imports
Mathlib.Algebra.BigOperators.Field and Mathlib.Data.Real.Sqrt.

These are the actual largest gaps of inverse-permutation block positions.
The concrete expectation theorem does not assume E B <= 4. Contained triples
are obtained from each fixed block before the permutation is averaged.
Disjointness/coverage of the labeled blocks is not needed for this upper
bound; connecting the constructed all-n partition is a separate interface.
Only root runs Lean; this source has not been executed by its author.
-/

namespace Gate145.BlockExpectation

open Gate145.PermutationMarginal Gate145.ActualGap
noncomputable section

theorem uniform_fixed_block_le {n m : ℕ} (hn : 3 ≤ n)
    (b : CardSet (Fin n) m) (hm : 2 ≤ m) (hm3 : 3 ≤ m) (hm5 : m ≤ 5) :
    (∑ g : Equiv.Perm (Fin n), (1 : ℝ) / (selectedGap (g⁻¹ • b) hm : ℝ)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ 12 / (n : ℝ) := by
  have hc : 3 ≤ b.val.card := by rw [b.property]; exact hm3
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hc
  exact uniform_actual_gap_le hn b hm hm5 ⟨t, hcard⟩ ht

def blockSum {n r : ℕ} (m : Fin r → ℕ)
    (b : (j : Fin r) → CardSet (Fin n) (m j))
    (hm : ∀ j, 2 ≤ m j) (g : Equiv.Perm (Fin n)) : ℝ :=
  ∑ j : Fin r, (1 : ℝ) / (selectedGap (g⁻¹ • b j) (hm j) : ℝ)

theorem blockSum_nonneg {n r : ℕ} (m : Fin r → ℕ)
    (b : (j : Fin r) → CardSet (Fin n) (m j))
    (hm : ∀ j, 2 ≤ m j) (g : Equiv.Perm (Fin n)) :
    0 ≤ blockSum m b hm g := by
  apply Finset.sum_nonneg
  intro j hj
  positivity

/-- Exact average of the actual reciprocal-largest-gap sum over the full
permutation group. No block independence or learner independence is used. -/
theorem uniform_blocks_le_four {n r : ℕ} (hn : 3 ≤ n)
    (m : Fin r → ℕ) (b : (j : Fin r) → CardSet (Fin n) (m j))
    (hm : ∀ j, 2 ≤ m j) (hm3 : ∀ j, 3 ≤ m j) (hm5 : ∀ j, m j ≤ 5)
    (hr : 3 * r ≤ n) :
    (∑ g : Equiv.Perm (Fin n), blockSum m b hm g) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ 4 := by
  have hEach := fun j : Fin r => uniform_fixed_block_le hn (b j) (hm j) (hm3 j) (hm5 j)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j hj => hEach j)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hrR : (3 : ℝ) * (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hr
  have hlim : (r : ℝ) * (12 / (n : ℝ)) ≤ 4 := by
    rw [show (r : ℝ) * (12 / (n : ℝ)) = (12 * (r : ℝ)) / (n : ℝ) by ring]
    apply (div_le_iff₀ hnR).2
    nlinarith
  calc
    (∑ g : Equiv.Perm (Fin n), blockSum m b hm g) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      ∑ j : Fin r, (∑ g : Equiv.Perm (Fin n),
        (1 : ℝ) / (selectedGap (g⁻¹ • b j) (hm j) : ℝ)) /
          (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
      unfold blockSum
      rw [Finset.sum_comm, Finset.sum_div]
    _ ≤ ∑ _j : Fin r, 12 / (n : ℝ) := hsum
    _ = (r : ℝ) * (12 / (n : ℝ)) := by simp
    _ ≤ 4 := hlim

/-- A reusable finite uniform Jensen step, with no probability-library
assumption. Concrete applications must supply their proved mean bound. -/
theorem uniform_sqrt_le_two {W : Type*} [Fintype W] [Nonempty W]
    (B : W → ℝ) (hB : ∀ w, 0 ≤ B w)
    (hmean : (∑ w : W, B w) / (Fintype.card W : ℝ) ≤ 4) :
    (∑ w : W, Real.sqrt (B w)) / (Fintype.card W : ℝ) ≤ 2 := by
  let c : ℝ := Fintype.card W
  have hc : 0 < c := by dsimp [c]; positivity
  have hnorm : (∑ _w : W, (1 : ℝ) / c) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change c * (1 / c) = 1
    field_simp
  have hsecond : (∑ w : W, (1 / c) * (Real.sqrt (B w)) ^ 2) ≤ 4 := by
    simp_rw [Real.sq_sqrt (hB _)]
    rw [← Finset.mul_sum]
    change (1 / (Fintype.card W : ℝ)) * (∑ w : W, B w) ≤ 4
    convert hmean using 1 <;> ring
  have hh := Gate145.EpochExpectation.weighted_root_bound
    (fun _w : W => (1 : ℝ) / c) (fun w => Real.sqrt (B w))
    (fun _w => le_of_lt (one_div_pos.mpr hc)) hnorm
    (fun w => Real.sqrt_nonneg (B w)) hsecond
  rw [← Finset.mul_sum] at hh
  change (1 / (Fintype.card W : ℝ)) * (∑ w : W, Real.sqrt (B w)) ≤ 2 at hh
  convert hh using 1 <;> ring

theorem uniform_sqrt_blocks_le_two {n r : ℕ} (hn : 3 ≤ n)
    (m : Fin r → ℕ) (b : (j : Fin r) → CardSet (Fin n) (m j))
    (hm : ∀ j, 2 ≤ m j) (hm3 : ∀ j, 3 ≤ m j) (hm5 : ∀ j, m j ≤ 5)
    (hr : 3 * r ≤ n) :
    (∑ g : Equiv.Perm (Fin n), Real.sqrt (blockSum m b hm g)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ 2 :=
  uniform_sqrt_le_two (blockSum m b hm) (blockSum_nonneg m b hm)
    (uniform_blocks_le_four hn m b hm hm3 hm5 hr)

/-- There are exactly two actual positions in Fin 2, so the selected
consecutive gap is one for either permutation. This is not a triple case. -/
theorem two_gap_eq_one (s : CardSet (Fin 2) 2) (hm : 2 ≤ 2) :
    selectedGap s hm = 1 := by
  have hk : index s hm = 0 := by
    have h := (selected_spec s hm).1
    omega
  have hinc : position s 0 < position s 1 := position_inc s 0 (by norm_num)
  have hlast : position s 1 < 2 := by
    simp only [position, dif_pos (show 1 < 2 by norm_num)]
    exact (s.val.orderEmbOfFin s.property ⟨1, by norm_num⟩).isLt
  unfold selectedGap
  rw [hk]
  exact Gate145.GapSelection.two_positions_gap (position s 0) (position s 1) hinc hlast

theorem uniform_two_gap_eq_one (b : CardSet (Fin 2) 2) (hm : 2 ≤ 2) :
    (∑ g : Equiv.Perm (Fin 2), (1 : ℝ) / (selectedGap (g⁻¹ • b) hm : ℝ)) /
      (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) = 1 := by
  have hd : (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) ≠ 0 := by positivity
  simp_rw [two_gap_eq_one]
  simp [hd]

theorem uniform_sqrt_two_gap_eq_one (b : CardSet (Fin 2) 2) (hm : 2 ≤ 2) :
    (∑ g : Equiv.Perm (Fin 2), Real.sqrt ((1 : ℝ) /
      (selectedGap (g⁻¹ • b) hm : ℝ))) /
      (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) = 1 := by
  have hd : (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) ≠ 0 := by positivity
  simp_rw [two_gap_eq_one]
  simp [hd]

#print axioms uniform_fixed_block_le
#print axioms uniform_blocks_le_four
#print axioms uniform_sqrt_le_two
#print axioms uniform_sqrt_blocks_le_two
#print axioms two_gap_eq_one
#print axioms uniform_two_gap_eq_one
#print axioms uniform_sqrt_two_gap_eq_one

end
end Gate145.BlockExpectation

/-! Exact uniform average over the actual K-epoch permutation bank.
Additional import Mathlib.Data.Real.Sqrt. No assumption about
independence of an adaptive policy and a current label is used. -/
namespace Gate145.BankExpectation
open Gate145.PermutationMarginal Gate145.EpochExpectation
noncomputable section

/-- Each coordinate of the uniformly enumerated finite permutation bank has
its actual uniform permutation law, proved by a transitive group action. -/
theorem coordinate_mean (n K : ℕ) (e : Fin K) (F : Equiv.Perm (Fin n) → ℝ) :
    (∑ w : Fin K → Equiv.Perm (Fin n), F (w e)) /
      (Fintype.card (Fin K → Equiv.Perm (Fin n)) : ℝ) =
    (∑ g : Equiv.Perm (Fin n), F g) / (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  letI : MulAction (Fin K → Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) := {
    smul := fun w x => w e * x
    one_smul := fun x => by
      change (1 : Equiv.Perm (Fin n)) * x = x
      exact one_mul x
    mul_smul := fun w v x => by
      change (w e * v e) * x = w e * (v e * x)
      exact mul_assoc _ _ _ }
  have htrans : ∀ x y : Equiv.Perm (Fin n),
      ∃ w : Fin K → Equiv.Perm (Fin n), w • x = y := by
    intro x y
    refine ⟨fun _ => y * x⁻¹, ?_⟩
    change y * x⁻¹ * x = y
    simp [mul_assoc]
  have h := uniform_action_mean (G := Fin K → Equiv.Perm (Fin n)) (1 : Equiv.Perm (Fin n)) F htrans
  change (∑ w : Fin K → Equiv.Perm (Fin n), F (w e * 1)) / _ = _ at h
  simpa only [mul_one] using h

theorem bank_G_from_actual_epoch_mean (n K r : ℕ) (B : Equiv.Perm (Fin n) → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (hr : 2*r ≤ n)
    (hB : ∀ g, 0 ≤ B g)
    (hmean : (∑ g, B g)/(Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ 4) :
    (∑ w : Fin K → Equiv.Perm (Fin n), A*(8*(K:ℝ)*Real.sqrt (r:ℝ) +
      5*Real.sqrt ((n-1:ℕ):ℝ)*∑ e, Real.sqrt (B (w e)))) /
      (Fintype.card (Fin K → Equiv.Perm (Fin n)) : ℝ) ≤
      16*A*(K:ℝ)*Real.sqrt (n:ℝ) := by
  let W := Fin K → Equiv.Perm (Fin n)
  let p : W → ℝ := fun _ => 1/(Fintype.card W : ℝ)
  have hc : (0:ℝ) < Fintype.card W := by positivity
  have hp : ∀ w, 0 ≤ p w := by intro w; dsimp [p]; positivity
  have hnorm : (∑ w, p w) = 1 := by
    simp [p, ne_of_gt hc]
  have hsecond : ∀ e : Fin K, (∑ w : W, p w*(Real.sqrt (B (w e)))^2) ≤ 4 := by
    intro e
    simp_rw [Real.sq_sqrt (hB _)]
    have hid : (∑ w : W, p w*B (w e)) = (∑ w : W, B (w e))/(Fintype.card W : ℝ) := by
      simp only [p, one_div, ← Finset.mul_sum]
      ring
    rw [hid]
    exact (coordinate_mean n K e B).trans_le hmean
  have hratio : 2*(Real.sqrt (r:ℝ))^2 ≤ (Real.sqrt (n:ℝ))^2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg r), Real.sq_sqrt (Nat.cast_nonneg n)]
    exact_mod_cast hr
  have hnm1 : Real.sqrt ((n-1:ℕ):ℝ) ≤ Real.sqrt (n:ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.sub_le n 1
  have h := expected_G_bound K p (fun e w => Real.sqrt (B (w e)))
    A (Real.sqrt (r:ℝ)) (Real.sqrt (n:ℝ)) (Real.sqrt ((n-1:ℕ):ℝ))
    hp hnorm (fun e w => Real.sqrt_nonneg _) hsecond hA
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hnm1 hratio
  have hid : (∑ w : W, p w*(A*(8*(K:ℝ)*Real.sqrt (r:ℝ) +
      5*Real.sqrt ((n-1:ℕ):ℝ)*∑ e, Real.sqrt (B (w e))))) =
    (∑ w : W, A*(8*(K:ℝ)*Real.sqrt (r:ℝ) +
      5*Real.sqrt ((n-1:ℕ):ℝ)*∑ e, Real.sqrt (B (w e)))) / (Fintype.card W : ℝ) := by
    simp only [p, one_div, ← Finset.mul_sum]
    ring
  rw [hid] at h
  exact h

#print axioms coordinate_mean
#print axioms bank_G_from_actual_epoch_mean
end
end Gate145.BankExpectation

namespace Gate145.BankConcrete
open Gate145.PermutationMarginal Gate145.ActualGap Gate145.BlockExpectation Gate145.BankExpectation
noncomputable section

/-- Complete order-only mean bound for the actual largest-gap block sum.
There is no assumed mean, root moment, or independence of learner actions. -/
theorem actual_blocks_bank_G {n r : ℕ} (hn : 3 ≤ n) (K : ℕ)
    (m : Fin r → ℕ) (b : (j : Fin r) → CardSet (Fin n) (m j))
    (hm : ∀ j, 2 ≤ m j) (hm3 : ∀ j, 3 ≤ m j) (hm5 : ∀ j, m j ≤ 5)
    (hr : 3*r ≤ n) (A : ℝ) (hA : 0 ≤ A) :
    (∑ w : Fin K → Equiv.Perm (Fin n), A*(8*(K:ℝ)*Real.sqrt (r:ℝ) +
      5*Real.sqrt ((n-1:ℕ):ℝ)*∑ e, Real.sqrt (blockSum m b hm (w e)))) /
      (Fintype.card (Fin K → Equiv.Perm (Fin n)) : ℝ) ≤
      16*A*(K:ℝ)*Real.sqrt (n:ℝ) := by
  apply bank_G_from_actual_epoch_mean n K r (blockSum m b hm) A hA (by omega)
  · exact blockSum_nonneg m b hm
  · exact uniform_blocks_le_four hn m b hm hm3 hm5 hr

theorem actual_pair_bank_G (K : ℕ) (b : CardSet (Fin 2) 2) (hm : 2 ≤ 2)
    (A : ℝ) (hA : 0 ≤ A) :
    (∑ w : Fin K → Equiv.Perm (Fin 2), A*(8*(K:ℝ)*Real.sqrt (1:ℝ) +
      5*Real.sqrt ((2-1:ℕ):ℝ)*∑ e, Real.sqrt ((1:ℝ)/(selectedGap ((w e)⁻¹ • b) hm : ℝ)))) /
      (Fintype.card (Fin K → Equiv.Perm (Fin 2)) : ℝ) ≤
      16*A*(K:ℝ)*Real.sqrt (2:ℝ) := by
  have hnonneg : ∀ g : Equiv.Perm (Fin 2), 0 ≤ (1:ℝ)/(selectedGap (g⁻¹ • b) hm : ℝ) := by
    intro g; positivity
  have hmean : (∑ g : Equiv.Perm (Fin 2), (1:ℝ)/(selectedGap (g⁻¹ • b) hm : ℝ)) /
      (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) ≤ 4 := by
    rw [uniform_two_gap_eq_one]
    norm_num
  have h := bank_G_from_actual_epoch_mean 2 K 1
    (fun g => (1:ℝ)/(selectedGap (g⁻¹ • b) hm : ℝ)) A hA (by norm_num) hnonneg hmean
  convert h using 1 <;> norm_num

#print axioms actual_blocks_bank_G
#print axioms actual_pair_bank_G
end
end Gate145.BankConcrete

/-!
Gate146: finite permutation-bank interface to the actual every-interval bound.
Compile after EpochInterval and the accepted Gate145 BankConcrete dependencies;
Mathlib.Algebra.BigOperators.Fin supplies Finset.sum_range.
The SAME fixed labels and SAME finite bank occur in hgeo and its expectation.
No disjoint-cover construction, full theorem, or learner-independence premise
is hidden here. Root alone runs Lean.
-/

namespace Gate146.FiniteBankInterval
open scoped BigOperators
open Gate146.EuclideanCoordinates Gate146.EpochInterval
open Gate145.PermutationHitBridge Gate145.HitAssembly Gate145.PermutationMarginal
noncomputable section

/-- Identity outside the supplied bank; no extra random epochs are added. -/
def extendBank {n K : ℕ} (bank : Fin K → Equiv.Perm (Fin n))
    (e : ℕ) : Equiv.Perm (Fin n) :=
  if h : e < K then bank ⟨e, h⟩ else 1

theorem extendBank_on_range {n K : ℕ} (bank : Fin K → Equiv.Perm (Fin n))
    (e : ℕ) (he : e < K) : extendBank bank e = bank ⟨e, he⟩ := by
  simp only [extendBank, dif_pos he]

theorem extendBank_outside {n K : ℕ} (bank : Fin K → Equiv.Perm (Fin n))
    (e : ℕ) (he : K ≤ e) : extendBank bank e = 1 := by
  simp only [extendBank, dif_neg (by omega : ¬ e < K)]

theorem sum_extension {n K : ℕ} (bank : Fin K → Equiv.Perm (Fin n))
    (F : Equiv.Perm (Fin n) → ℝ) :
    (∑ e ∈ Finset.range K, F (extendBank bank e)) =
      ∑ e : Fin K, F (bank e) := by
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro e he
  rw [extendBank_on_range bank e.val e.isLt]

/-- Actual table at every update, now driven by a finite bank. -/
def finiteTable {n r K : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (bank : Fin K → Equiv.Perm (Fin n))
    (t : ℕ) : Vec (Σ b : Fin r, Fin (size b)) :=
  bankTable size labels hinj hm (extendBank bank) t

theorem finiteTable_at_epoch {n r K : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (bank : Fin K → Equiv.Perm (Fin n))
    (hn : 0 < n) (e : Fin K) (j : ℕ) (hj : j < n) :
    finiteTable size labels hinj hm bank (n * e.val + j) =
      epochVec size labels hinj hm (bank e) j := by
  unfold finiteTable
  rw [bankTable_at_epoch size labels hinj hm (extendBank bank) hn e.val j hj,
    extendBank_on_range bank e.val e.isLt]

/-- The actual bank-dependent envelope in the pinned hand proof. -/
def finiteG {n r K : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (bank : Fin K → Equiv.Perm (Fin n)) (A : ℝ) : ℝ :=
  A * (8 * (K : ℝ) * Real.sqrt (r : ℝ) +
    5 * Real.sqrt ((n - 1 : ℕ) : ℝ) *
      ∑ e : Fin K, Real.sqrt (gapSum size labels hinj hm (bank e)))

theorem actual_finite_bank_interval {n r K : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (bank : Fin K → Equiv.Perm (Fin n)) (n2 : 2 ≤ n) (s t : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (hst : s ≤ t) (ht : t ≤ n * K)
    (z : ℕ → Vec (Σ b : Fin r, Fin (size b)))
    (hz : ∀ k, s ≤ k → k ≤ t → ‖z k‖ ≤ A) :
    (∑ k ∈ Finset.Ico s t,
      test (finiteTable size labels hinj hm bank k) (z k - z (k + 1))) ≤
      finiteG size labels hinj hm bank A := by
  have hh := actual_bank_interval size labels hinj hm hm5 (extendBank bank)
    n2 K s t A hA hst ht z hz
  rw [sum_extension bank (fun g => Real.sqrt (gapSum size labels hinj hm g))] at hh
  exact hh

/-- Exact Gate144 shifted hgeo, for each fixed finite bank and every allowed
auxiliary path. The interval/path may be selected after seeing this bank. -/
theorem actual_finite_interval_hgeo {n r K : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (bank : Fin K → Equiv.Perm (Fin n)) (n2 : 2 ≤ n) (s N : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (hN : s + N ≤ n * K) :
    ∀ z : ℕ → Vec (Σ b : Fin r, Fin (size b)), (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ Finset.range N,
        test (finiteTable size labels hinj hm bank (s + k)) (z k - z (k + 1))) ≤
        finiteG size labels hinj hm bank A := by
  intro z hz
  have hh := actual_interval_hgeo size labels hinj hm hm5 (extendBank bank)
    n2 K s N A hA hN z hz
  rw [sum_extension bank (fun g => Real.sqrt (gapSum size labels hinj hm g))] at hh
  exact hh

/-- The coordinate-table gap sum IS the accepted actual blockSum, with the
same inverse permutation applied to the same fixed label sets. -/
theorem gapSum_eq_blockSum {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (g : Equiv.Perm (Fin n)) :
    gapSum size labels hinj hm g =
      Gate145.BlockExpectation.blockSum size (fun b => hitSet (labels b) (hinj b)) hm g := by
  rfl

theorem finiteG_eq_actual_bank_expression {n r K : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (bank : Fin K → Equiv.Perm (Fin n)) (A : ℝ) :
    finiteG size labels hinj hm bank A =
      A * (8 * (K : ℝ) * Real.sqrt (r : ℝ) +
        5 * Real.sqrt ((n - 1 : ℕ) : ℝ) *
          ∑ e : Fin K, Real.sqrt (Gate145.BlockExpectation.blockSum size
            (fun b => hitSet (labels b) (hinj b)) hm (bank e))) := by
  rfl

/-- The precise finite bank envelope used by hgeo has the accepted order-only
mean bound. This is a uniform average over banks, not a conditional average
after any adaptive choice of an interval or auxiliary path. -/
theorem actual_finite_G_mean {n r : ℕ} (hn : 3 ≤ n) (K : ℕ)
    (size : Fin r → ℕ) (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ b, 2 ≤ size b) (hm3 : ∀ b, 3 ≤ size b) (hm5 : ∀ b, size b ≤ 5)
    (hr : 3 * r ≤ n) (A : ℝ) (hA : 0 ≤ A) :
    (∑ bank : Fin K → Equiv.Perm (Fin n), finiteG size labels hinj hm bank A) /
      (Fintype.card (Fin K → Equiv.Perm (Fin n)) : ℝ) ≤
        16 * A * (K : ℝ) * Real.sqrt (n : ℝ) := by
  exact Gate145.BankConcrete.actual_blocks_bank_G hn K size
    (fun b => hitSet (labels b) (hinj b)) hm hm3 hm5 hr A hA

/-- The one-block n=2 case uses its actual selected gap one. It does not
apply a triple-containing-block estimate to a pair. -/
theorem actual_pair_finite_G_mean (K : ℕ)
    (labels : ∀ _b : Fin 1, Fin 2 → Fin 2)
    (hinj : ∀ b, Function.Injective (labels b))
    (hm : ∀ _b : Fin 1, 2 ≤ 2) (A : ℝ) (hA : 0 ≤ A) :
    (∑ bank : Fin K → Equiv.Perm (Fin 2),
        finiteG (fun _ : Fin 1 => 2) labels hinj hm bank A) /
      (Fintype.card (Fin K → Equiv.Perm (Fin 2)) : ℝ) ≤
        16 * A * (K : ℝ) * Real.sqrt (2 : ℝ) := by
  have hh := Gate145.BankConcrete.actual_pair_bank_G K
    (hitSet (labels 0) (hinj 0)) (hm 0) A hA
  simpa only [finiteG, gapSum, Fin.sum_univ_one, Nat.cast_one] using hh

#print axioms sum_extension
#print axioms finiteTable_at_epoch
#print axioms actual_finite_bank_interval
#print axioms actual_finite_interval_hgeo
#print axioms gapSum_eq_blockSum
#print axioms actual_finite_G_mean
#print axioms actual_pair_finite_G_mean

end
end Gate146.FiniteBankInterval

/-! Actual fixed labels and offsets meet the same Euclidean dual tests.
No premise says the tested offset has the desired pairing: it is derived
from the actual bijection and inverse-permutation hit construction. -/
namespace Gate146.LabeledDual
noncomputable section
open scoped BigOperators
open EuclideanCoordinates LabeledBlocks FastSpaceOffsets EpochInterval

theorem epoch_current_pairing {n : ℕ} (P : Partition n)
    (g : Equiv.Perm (Fin n)) (t : Fin n) :
    test (epochVec P.size (labels P) (labels_injective P) P.size_lower g t.val)
      (Xi P (g t)) = 1 := by
  let x : Coordinates P := (labelEquiv P).symm (g t)
  have hx : g t = labels P x.1 x.2 := by
    exact ((labelEquiv P).apply_symm_apply (g t)).symm
  change test (epochVec P.size (labels P) (labels_injective P) P.size_lower g t.val)
    (BlockOffsets.offset P.size x) = 1
  rw [BlockOffsets.global_test_local]
  exact Gate145.PermutationHitBridge.current_pairing (labels P x.1)
    (labels_injective P x.1) g (P.size_lower x.1) (P.size_upper x.1) t x.2 hx

theorem epoch_all_label_pairing {n : ℕ} (P : Partition n)
    (g : Equiv.Perm (Fin n)) (t : ℕ) (a : Fin n) :
    |test (epochVec P.size (labels P) (labels_injective P) P.size_lower g t)
      (Xi P a)| ≤ 4 := by
  unfold Xi
  rw [BlockOffsets.global_test_local]
  exact Gate145.PermutationHitBridge.permuted_all_label_pairing_bound
    (labels P ((labelEquiv P).symm a).1)
    (labels_injective P ((labelEquiv P).symm a).1) g
    (P.size_lower ((labelEquiv P).symm a).1)
    (P.size_upper ((labelEquiv P).symm a).1) t ((labelEquiv P).symm a).2

theorem epoch_all_vector_bound {n : ℕ} (P : Partition n)
    (g : Equiv.Perm (Fin n)) (t : ℕ) (v : Vec (Coordinates P)) :
    |test (epochVec P.size (labels P) (labels_injective P) P.size_lower g t) v| ≤
      4 * Real.sqrt (P.count : ℝ) * ‖v‖ :=
  (test_bound _ _).trans (mul_le_mul_of_nonneg_right
    (actual_epoch_norm P.size (labels P) (labels_injective P)
      P.size_lower P.size_upper g t) (norm_nonneg v))

#print axioms epoch_current_pairing
#print axioms epoch_all_label_pairing
#print axioms epoch_all_vector_bound
end
end Gate146.LabeledDual