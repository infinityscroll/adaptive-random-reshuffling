import ActualEpochIntervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Linarith



/-! Compile after EuclideanCoordinates and Gate145.SimplexDual.
Actual global block-supported offsets in the SAME Euclidean normed space. -/
namespace Gate146.BlockOffsets
open EuclideanCoordinates Gate145.SimplexDual
noncomputable section
open scoped BigOperators

variable {r : ℕ} (size : Fin r → ℕ)
abbrev Coord := Σ b : Fin r, Fin (size b)

def injectBlock (b : Fin r) (u : Fin (size b) → ℝ) : Vec (Coord size) :=
  ⟨fun x => if h : x.1=b then u (h ▸ x.2) else 0⟩

theorem test_injectBlock (phi : Vec (Coord size)) (b : Fin r)
    (u : Fin (size b) → ℝ) :
    test phi (injectBlock size b u) = ∑ j, phi.coord ⟨b,j⟩*u j := by
  classical
  change (∑ x : Coord size, phi.coord x*(injectBlock size b u).coord x) = _
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single b]
  · simp [injectBlock]
  · intro c hc hcb
    simp [injectBlock,hcb]
  · simp

theorem square_injectBlock (b : Fin r) (u : Fin (size b) → ℝ) :
    square (injectBlock size b u) = ∑ j, u j^2 := by
  classical
  unfold square
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single b]
  · simp [injectBlock]
  · intro c hc hcb
    simp [injectBlock,hcb]
  · simp

def offset (x : Coord size) : Vec (Coord size) :=
  injectBlock size x.1 (xi (amplitude (size x.1)) x.2)

theorem offset_norm (hm : ∀ b, 2 ≤ size b) (x : Coord size) :
    ‖offset size x‖ = 1 := by
  have hs : square (offset size x)=1 := by
    unfold offset
    rw [square_injectBlock]
    have h := unit_sqNorm (amplitude (size x.1)) (hm x.1)
      (amplitude_sq (size x.1) (hm x.1)) x.2
    simpa only [Gate145.SimplexDual.sqNorm,Gate145.SimplexDual.dot,pow_two] using h
  have hn := norm_nonnegative (offset size x)
  have hsq := norm_square (offset size x)
  rw [hs] at hsq
  nlinarith

theorem coord_sum {J I : Type*} [Fintype I]
    (s : Finset J) (v : J → Vec I) (i : I) :
    (∑ j ∈ s, v j).coord i = ∑ j ∈ s, (v j).coord i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [Finset.sum_insert,hj,ih]

theorem offset_sum_zero (hm : ∀ b, 2 ≤ size b) :
    (∑ x : Coord size, offset size x) = 0 := by
  classical
  apply (coordEquiv (Coord size)).injective
  funext y
  change (∑ x : Coord size, offset size x).coord y = 0
  rw [coord_sum,Fintype.sum_sigma]
  rw [Finset.sum_eq_single y.1]
  · simp only [offset,injectBlock]
    exact label_sum_zero (amplitude (size y.1)) (hm y.1) y.2
  · intro c hc hcy
    have hyc : y.1 ≠ c := Ne.symm hcy
    simp [offset,injectBlock,hyc]
  · simp

/-- The global dot against an offset uses only that offset's own block. -/
theorem global_test_local (phi : Vec (Coord size)) (x : Coord size) :
    test phi (offset size x) =
      Gate145.SimplexDual.dot (fun j => phi.coord ⟨x.1,j⟩)
        (xi (amplitude (size x.1)) x.2) := by
  exact test_injectBlock size phi x.1 _

#print axioms square_injectBlock
#print axioms offset_norm
#print axioms offset_sum_zero
#print axioms global_test_local
end
end Gate146.BlockOffsets


/-! Gate146: a fixed labeled partition for every n >= 2.
The arithmetic is the constructive realization of Gate145.BlockCounts:
one pair for n=2; otherwise floor(n/3) blocks, with one block of size
3+(n mod 3) and every other block of size 3.  Labels are assigned by the
explicit finSigmaFinEquiv, before any permutation or policy is supplied.
No Euclidean isometry or probability claim is made in this module. -/

namespace Gate146.LabeledBlocks
open scoped BigOperators

structure Partition (n : ℕ) where
  count : ℕ
  size : Fin count → ℕ
  count_pos : 0 < count
  count_le_half : count ≤ n / 2
  total : ∑ j, size j = n
  size_lower : ∀ j, 2 ≤ size j
  size_upper : ∀ j, size j ≤ 5
  pair_iff : ∀ j, size j = 2 ↔ n = 2
  pair_count : n = 2 → count = 1
  large_count : 3 ≤ n → count = n / 3

theorem partition_exists (n : ℕ) (hn : 2 ≤ n) : Nonempty (Partition n) := by
  by_cases htwo : n = 2
  · subst n
    refine ⟨{
      count := 1
      size := fun _ => 2
      count_pos := by omega
      count_le_half := by omega
      total := by simp
      size_lower := by intro j; omega
      size_upper := by intro j; omega
      pair_iff := by intro j; simp
      pair_count := by intro h; rfl
      large_count := by intro h; omega
    }⟩
  · have hthree : 3 ≤ n := by omega
    let k : ℕ := n / 3 - 1
    have hcount : k + 1 = n / 3 := by dsimp [k]; omega
    have hmod : n % 3 < 3 := Nat.mod_lt n (by omega)
    let sizes : Fin (k + 1) → ℕ := Fin.cons (3 + n % 3) (fun _ : Fin k => 3)
    have hlo : ∀ j, 3 ≤ sizes j := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp [sizes]
      · simp [sizes]
    have hhi : ∀ j, sizes j ≤ 5 := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · simp only [sizes, Fin.cons_zero]; omega
      · simp [sizes]
    have hsum : ∑ j, sizes j = n := by
      simp only [sizes, Fin.sum_cons, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul]
      omega
    refine ⟨{
      count := k + 1
      size := sizes
      count_pos := by omega
      count_le_half := by omega
      total := hsum
      size_lower := fun j => by have h := hlo j; omega
      size_upper := hhi
      pair_iff := fun j => by have h := hlo j; omega
      pair_count := by intro h; omega
      large_count := by intro h; exact hcount
    }⟩

noncomputable def fixedPartition (n : ℕ) (hn : 2 ≤ n) : Partition n :=
  Classical.choice (partition_exists n hn)

abbrev Coordinates {n : ℕ} (P : Partition n) := Σ j : Fin P.count, Fin (P.size j)

def labelEquiv {n : ℕ} (P : Partition n) : Coordinates P ≃ Fin n :=
  finSigmaFinEquiv.trans (finCongr P.total)

def labels {n : ℕ} (P : Partition n) (j : Fin P.count) (i : Fin (P.size j)) : Fin n :=
  labelEquiv P ⟨j, i⟩

theorem labels_injective {n : ℕ} (P : Partition n) (j : Fin P.count) :
    Function.Injective (labels P j) := by
  intro i k h
  have he : (⟨j, i⟩ : Coordinates P) = ⟨j, k⟩ := (labelEquiv P).injective h
  cases he
  rfl

theorem different_blocks_disjoint {n : ℕ} (P : Partition n)
    (j k : Fin P.count) (hjk : j ≠ k) (i : Fin (P.size j)) (l : Fin (P.size k)) :
    labels P j i ≠ labels P k l := by
  intro h
  have he : (⟨j, i⟩ : Coordinates P) = ⟨k, l⟩ := (labelEquiv P).injective h
  exact hjk (congrArg Sigma.fst he)

theorem unique_label_preimage {n : ℕ} (P : Partition n) (a : Fin n) :
    ∃! x : Coordinates P, labelEquiv P x = a := by
  refine ⟨(labelEquiv P).symm a, (labelEquiv P).apply_symm_apply a, ?_⟩
  intro x hx
  exact (labelEquiv P).injective (hx.trans ((labelEquiv P).apply_symm_apply a).symm)

def block {n : ℕ} (P : Partition n) (j : Fin P.count) : Finset (Fin n) :=
  Finset.univ.image (labels P j)

theorem card_block {n : ℕ} (P : Partition n) (j : Fin P.count) :
    (block P j).card = P.size j := by
  rw [block, Finset.card_image_of_injective _ (labels_injective P j)]
  simp

theorem blocks_disjoint {n : ℕ} (P : Partition n)
    (j k : Fin P.count) (hjk : j ≠ k) : Disjoint (block P j) (block P k) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i, hi, hei⟩ := Finset.mem_image.mp ha
  obtain ⟨l, hl, hel⟩ := Finset.mem_image.mp hb
  exact different_blocks_disjoint P j k hjk i l (hei.trans hel.symm)

theorem blocks_cover {n : ℕ} (P : Partition n) :
    Finset.univ.biUnion (block P) = Finset.univ := by
  ext a
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨x, hx⟩ := (labelEquiv P).surjective a
  apply Finset.mem_biUnion.mpr
  refine ⟨x.1, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨x.2, Finset.mem_univ _, hx⟩

theorem slow_plus_fast_dimension_bound {n : ℕ} (P : Partition n) :
    n - P.count + 1 ≤ n := by
  have hp := P.count_pos
  have hc := P.count_le_half
  omega

#print axioms partition_exists
#print axioms labelEquiv
#print axioms labels_injective
#print axioms blocks_disjoint
#print axioms blocks_cover
#print axioms unique_label_preimage
#print axioms slow_plus_fast_dimension_bound

end Gate146.LabeledBlocks


/-! An algebraic representation, not an isometry.
The actual coordinate functions with zero sum in each block are linearly
equivalent to n-r real coordinates, whenever the block sizes sum to n.
Each block is represented by dropping its last coordinate and reconstructing
that coordinate as the negative sum.  This usually changes the coordinate
sum-of-squares norm, and no norm equality is asserted here. -/

namespace Gate146.ZeroSumRepresentation
noncomputable section
open scoped BigOperators

def zeroSum (m : ℕ) : Submodule ℝ (Fin m → ℝ) where
  carrier := {v | ∑ i, v i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, (x i + y i) = 0
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change ∑ i, c * x i = 0
    rw [← Finset.mul_sum, hx, mul_zero]

def dropLastEquiv (k : ℕ) : zeroSum (k + 1) ≃ₗ[ℝ] (Fin k → ℝ) where
  toFun v i := v.val i.castSucc
  invFun w := ⟨Fin.snoc w (-∑ i, w i), by
    change ∑ i, Fin.snoc w (-∑ j, w j) i = 0
    simp⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Fin.snoc (α := fun _ : Fin (k + 1) => ℝ) (fun j : Fin k => v.val j.castSucc)
        (-∑ j : Fin k, v.val j.castSucc) (Fin.last k) = v.val (Fin.last k)
      rw [Fin.snoc_last]
      have hv := v.property
      change ∑ j : Fin (k + 1), v.val j = 0 at hv
      rw [Fin.sum_univ_castSucc] at hv
      linarith
    · change Fin.snoc (α := fun _ : Fin (k + 1) => ℝ) (fun i : Fin k => v.val i.castSucc)
        (-∑ i : Fin k, v.val i.castSucc) j.castSucc = v.val j.castSucc
      simp only [Fin.snoc_castSucc]
  right_inv w := by
    funext i
    change Fin.snoc (α := fun _ : Fin (k + 1) => ℝ) w (-∑ j, w j) i.castSucc = w i
    simp only [Fin.snoc_castSucc]
  map_add' x y := rfl
  map_smul' c x := rfl

def zeroSumEquiv (m : ℕ) (hm : 0 < m) : zeroSum m ≃ₗ[ℝ] (Fin (m - 1) → ℝ) := by
  cases m with
  | zero => omega
  | succ k => exact dropLastEquiv k

def blockZeroSum {r : ℕ} (size : Fin r → ℕ) :
    Submodule ℝ ((Σ j : Fin r, Fin (size j)) → ℝ) where
  carrier := {v | ∀ j, ∑ i, v ⟨j, i⟩ = 0}
  zero_mem' := by intro j; simp
  add_mem' := by
    intro x y hx hy j
    change ∑ i, (x ⟨j, i⟩ + y ⟨j, i⟩) = 0
    rw [Finset.sum_add_distrib, hx j, hy j, add_zero]
  smul_mem' := by
    intro c x hx j
    change ∑ i, c * x ⟨j, i⟩ = 0
    rw [← Finset.mul_sum, hx j, mul_zero]

def blockToProduct {r : ℕ} (size : Fin r → ℕ) :
    blockZeroSum size ≃ₗ[ℝ] (∀ j : Fin r, zeroSum (size j)) where
  toFun v j := ⟨fun i => v.val ⟨j, i⟩, v.property j⟩
  invFun w := ⟨fun x => (w x.1).val x.2, fun j => (w j).property⟩
  left_inv v := by
    apply Subtype.ext
    funext x
    rfl
  right_inv w := by
    funext j
    apply Subtype.ext
    rfl
  map_add' x y := rfl
  map_smul' c x := rfl

theorem free_coordinate_count {n r : ℕ} (size : Fin r → ℕ)
    (hpos : ∀ j, 0 < size j) (htotal : ∑ j, size j = n) :
    ∑ j, (size j - 1) = n - r := by
  have hadd : (∑ j, (size j - 1)) + r = n := by
    calc
      (∑ j, (size j - 1)) + r = (∑ j, (size j - 1)) + ∑ _j : Fin r, 1 := by simp
      _ = ∑ j, (size j - 1 + 1) := (Finset.sum_add_distrib).symm
      _ = ∑ j, size j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hp := hpos j
        omega
      _ = n := htotal
  omega

def freeIndexEquiv {n r : ℕ} (size : Fin r → ℕ)
    (hpos : ∀ j, 0 < size j) (htotal : ∑ j, size j = n) :
    (Σ j : Fin r, Fin (size j - 1)) ≃ Fin (n - r) :=
  finSigmaFinEquiv.trans (finCongr (free_coordinate_count size hpos htotal))

def blockRepresentation {n r : ℕ} (size : Fin r → ℕ)
    (hpos : ∀ j, 0 < size j) (htotal : ∑ j, size j = n) :
    blockZeroSum size ≃ₗ[ℝ] (Fin (n - r) → ℝ) :=
  (blockToProduct size).trans
    ((LinearEquiv.piCongrRight (fun j => zeroSumEquiv (size j) (hpos j))).trans
      ((LinearEquiv.piCurry ℝ (fun (j : Fin r) (_ : Fin (size j - 1)) => ℝ)).symm.trans
        (LinearEquiv.piCongrLeft' ℝ
          (fun _ : (Σ j : Fin r, Fin (size j - 1)) => ℝ)
          (freeIndexEquiv size hpos htotal))))

#print axioms dropLastEquiv
#print axioms zeroSumEquiv
#print axioms blockToProduct
#print axioms free_coordinate_count
#print axioms freeIndexEquiv
#print axioms blockRepresentation

end
end Gate146.ZeroSumRepresentation

/-! Append after LabeledBlocks.lean and ZeroSumRepresentation.lean.
This connects the actual Fin n labels to the blockwise zero-sum algebraic
space, then instantiates the all-n representation. No norm on the free
coordinate space is used and no isometry is inferred. -/

namespace Gate146.LabeledZeroSumBridge
noncomputable section
open scoped BigOperators
open Gate146.LabeledBlocks Gate146.ZeroSumRepresentation

def labeledZeroSum {n : ℕ} (P : Partition n) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∀ j, ∑ i, v (labels P j i) = 0}
  zero_mem' := by intro j; simp
  add_mem' := by
    intro x y hx hy j
    change ∑ i, (x (labels P j i) + y (labels P j i)) = 0
    rw [Finset.sum_add_distrib, hx j, hy j, add_zero]
  smul_mem' := by
    intro c x hx j
    change ∑ i, c * x (labels P j i) = 0
    rw [← Finset.mul_sum, hx j, mul_zero]

def labelCoordinateEquiv {n : ℕ} (P : Partition n) :
    labeledZeroSum P ≃ₗ[ℝ] blockZeroSum P.size where
  toFun v := ⟨fun x => v.val (labelEquiv P x), v.property⟩
  invFun w := ⟨fun a => w.val ((labelEquiv P).symm a), by
    intro j
    change ∑ i, w.val ((labelEquiv P).symm (labelEquiv P ⟨j, i⟩)) = 0
    simpa only [Equiv.symm_apply_apply] using w.property j⟩
  left_inv v := by
    apply Subtype.ext
    funext a
    change v.val (labelEquiv P ((labelEquiv P).symm a)) = v.val a
    rw [Equiv.apply_symm_apply]
  right_inv w := by
    apply Subtype.ext
    funext x
    change w.val ((labelEquiv P).symm (labelEquiv P x)) = w.val x
    rw [Equiv.symm_apply_apply]
  map_add' x y := rfl
  map_smul' c x := rfl

def labeledRepresentation {n : ℕ} (P : Partition n) :
    labeledZeroSum P ≃ₗ[ℝ] (Fin (n - P.count) → ℝ) :=
  (labelCoordinateEquiv P).trans
    (blockRepresentation P.size (fun j => by have h := P.size_lower j; omega) P.total)

def fixedFastSpace (n : ℕ) (hn : 2 ≤ n) : Submodule ℝ (Fin n → ℝ) :=
  labeledZeroSum (fixedPartition n hn)

def fixedFastRepresentation (n : ℕ) (hn : 2 ≤ n) :
    fixedFastSpace n hn ≃ₗ[ℝ] (Fin (n - (fixedPartition n hn).count) → ℝ) :=
  labeledRepresentation (fixedPartition n hn)

theorem fixed_total_dimension_bound (n : ℕ) (hn : 2 ≤ n) :
    n - (fixedPartition n hn).count + 1 ≤ n :=
  slow_plus_fast_dimension_bound (fixedPartition n hn)

#print axioms labelCoordinateEquiv
#print axioms labeledRepresentation
#print axioms fixedFastRepresentation
#print axioms fixed_total_dimension_bound

end
end Gate146.LabeledZeroSumBridge

/-! Append after EuclideanCoordinates, BlockOffsets, LabeledBlocks, and
ZeroSumRepresentation.  The norm on fastSpace is the inherited Euclidean
subspace norm. The free-coordinate linear equivalence proves only the
algebraic representation; it is not used to define or transfer that norm. -/

namespace Gate146.FastSpaceOffsets
noncomputable section
open scoped BigOperators
open Gate146.EuclideanCoordinates Gate146.LabeledBlocks

def fastSpace {r : ℕ} (size : Fin r → ℕ) :
    Submodule ℝ (Vec (Σ j : Fin r, Fin (size j))) where
  carrier := {v | ∀ j, ∑ i, v.coord ⟨j, i⟩ = 0}
  zero_mem' := by intro j; simp
  add_mem' := by
    intro x y hx hy j
    simp only [coord_add, Finset.sum_add_distrib, hx j, hy j, add_zero]
  smul_mem' := by
    intro c x hx j
    simp only [coord_smul, ← Finset.mul_sum, hx j, mul_zero]

def fastCoordinateEquiv {r : ℕ} (size : Fin r → ℕ) :
    fastSpace size ≃ₗ[ℝ] Gate146.ZeroSumRepresentation.blockZeroSum size where
  toFun v := ⟨v.val.coord, v.property⟩
  invFun w := ⟨⟨w.val⟩, w.property⟩
  left_inv v := by
    apply Subtype.ext
    apply (coordEquiv _).injective
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def fastRepresentation {n r : ℕ} (size : Fin r → ℕ)
    (hpos : ∀ j, 0 < size j) (htotal : ∑ j, size j = n) :
    fastSpace size ≃ₗ[ℝ] (Fin (n - r) → ℝ) :=
  (fastCoordinateEquiv size).trans
    (Gate146.ZeroSumRepresentation.blockRepresentation size hpos htotal)

def fixedRepresentation (n : ℕ) (hn : 2 ≤ n) :
    fastSpace (fixedPartition n hn).size ≃ₗ[ℝ]
      (Fin (n - (fixedPartition n hn).count) → ℝ) :=
  fastRepresentation (fixedPartition n hn).size
    (fun j => by have h := (fixedPartition n hn).size_lower j; omega)
    (fixedPartition n hn).total

theorem fast_norm_formula {r : ℕ} (size : Fin r → ℕ) (v : fastSpace size) :
    ‖v‖ = Real.sqrt (∑ x, v.val.coord x ^ 2) := by
  change ‖(v : Vec (Σ j : Fin r, Fin (size j)))‖ = _
  exact norm_formula v.val

theorem offset_mem_fastSpace {r : ℕ} (size : Fin r → ℕ)
    (hm : ∀ j, 2 ≤ size j) (x : Σ j : Fin r, Fin (size j)) :
    Gate146.BlockOffsets.offset size x ∈ fastSpace size := by
  rcases x with ⟨c, i⟩
  intro b
  change ∑ j, (Gate146.BlockOffsets.offset size ⟨c, i⟩).coord ⟨b, j⟩ = 0
  by_cases hbc : b = c
  · subst b
    simpa [Gate146.BlockOffsets.offset, Gate146.BlockOffsets.injectBlock] using
      Gate145.SimplexDual.coordinate_sum_zero
        (Gate145.SimplexDual.amplitude (size c)) (hm c) i
  · simp [Gate146.BlockOffsets.offset, Gate146.BlockOffsets.injectBlock, hbc]

/-- Actual original labels are assigned once, independently of the permutation. -/
def Xi {n : ℕ} (P : Partition n) (a : Fin n) : Vec (Coordinates P) :=
  Gate146.BlockOffsets.offset P.size ((labelEquiv P).symm a)

theorem Xi_mem {n : ℕ} (P : Partition n) (a : Fin n) :
    Xi P a ∈ fastSpace P.size :=
  offset_mem_fastSpace P.size P.size_lower ((labelEquiv P).symm a)

theorem Xi_norm {n : ℕ} (P : Partition n) (a : Fin n) : ‖Xi P a‖ = 1 :=
  Gate146.BlockOffsets.offset_norm P.size P.size_lower ((labelEquiv P).symm a)

theorem Xi_centered {n : ℕ} (P : Partition n) : (∑ a : Fin n, Xi P a) = 0 := by
  unfold Xi
  rw [(labelEquiv P).symm.sum_comp]
  exact Gate146.BlockOffsets.offset_sum_zero P.size P.size_lower

def fastXi {n : ℕ} (P : Partition n) (a : Fin n) : fastSpace P.size :=
  ⟨Xi P a, Xi_mem P a⟩

theorem fastXi_norm {n : ℕ} (P : Partition n) (a : Fin n) : ‖fastXi P a‖ = 1 :=
  Xi_norm P a

theorem fastXi_centered {n : ℕ} (P : Partition n) :
    (∑ a : Fin n, fastXi P a) = 0 := by
  apply (fastSpace P.size).injective_subtype
  rw [map_sum, map_zero]
  exact Xi_centered P

theorem fixed_fast_dimension_bound (n : ℕ) (hn : 2 ≤ n) :
    n - (fixedPartition n hn).count + 1 ≤ n :=
  slow_plus_fast_dimension_bound (fixedPartition n hn)

#print axioms fastCoordinateEquiv
#print axioms fastRepresentation
#print axioms fixedRepresentation
#print axioms fast_norm_formula
#print axioms offset_mem_fastSpace
#print axioms Xi_norm
#print axioms Xi_centered
#print axioms fastXi_centered
#print axioms fixed_fast_dimension_bound

end
end Gate146.FastSpaceOffsets