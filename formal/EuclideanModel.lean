import ActualStaticModel
import RealProduct
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Gate147: the accepted Vec norm is NOT replaced. Its actual coordinate
dot product is installed as a compatible inner product. The fast subspace
inherits this norm and inner product. The slow-plus-fast state is the L2
product WithLp 2, never the default max-norm product.

The previous drop-last equivalence is used only to prove finrank. Ambient
Vec completeness comes from a genuine coordinate isometry to PiLp 2;
the fast subspace is complete because its coordinate-sum equations define
a closed subset. No norm is transported through drop-last. A standard
(n-r)-coordinate isometry is deliberately not inferred or constructed.
This module supplies the space, not the cone/projection/objective theorem. -/

namespace Gate147.EuclideanModel
noncomputable section
open scoped BigOperators InnerProductSpace
open Gate146.EuclideanCoordinates Gate146.LabeledBlocks Gate146.FastSpaceOffsets

variable {I : Type*} [Fintype I]

instance vecInnerProductSpace : InnerProductSpace ℝ (Vec I) where
  __ := (inferInstance : NormedSpace ℝ (Vec I))
  inner := Gate146.EuclideanCoordinates.dot
  norm_sq_eq_re_inner x := by
    change ‖x‖ ^ 2 = Gate146.EuclideanCoordinates.dot x x
    simpa only [square, Gate146.EuclideanCoordinates.dot, pow_two] using norm_square x
  conj_inner_symm x y := by
    change Gate146.EuclideanCoordinates.dot y x = Gate146.EuclideanCoordinates.dot x y
    unfold Gate146.EuclideanCoordinates.dot
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  add_left x y z := by
    simp only [Gate146.EuclideanCoordinates.dot, coord_add, add_mul,
      Finset.sum_add_distrib]
  smul_left x y c := by
    change Gate146.EuclideanCoordinates.dot (c • x) y =
      c * Gate146.EuclideanCoordinates.dot x y
    simp only [Gate146.EuclideanCoordinates.dot, coord_smul, mul_assoc, Finset.mul_sum]

theorem vec_inner_formula (x y : Vec I) :
    inner ℝ x y = ∑ i, x.coord i * y.coord i := rfl

def coordLinearEquiv (I : Type*) : Vec I ≃ₗ[ℝ] (I → ℝ) where
  toFun := Vec.coord
  invFun := Vec.mk
  left_inv x := by cases x; rfl
  right_inv x := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

instance vecFiniteDimensional : FiniteDimensional ℝ (Vec I) :=
  (coordLinearEquiv I).symm.finiteDimensional

def vecLpIso (I : Type*) [Fintype I] : Vec I ≃ₗᵢ[ℝ] PiLp 2 (fun _ : I => ℝ) where
  toLinearEquiv := (coordLinearEquiv I).trans (WithLp.linearEquiv 2 ℝ (I → ℝ)).symm
  norm_map' x := by
    change ‖(WithLp.toLp 2 x.coord : PiLp 2 (fun _ : I => ℝ))‖ = ‖x‖
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    change (∑ i, ‖x.coord i‖ ^ 2) = ‖x‖ ^ 2
    simpa only [Real.norm_eq_abs, sq_abs, square] using (norm_square x).symm

instance vecCompleteSpace : CompleteSpace (Vec I) :=
  (vecLpIso I).toIsometryEquiv.completeSpace

theorem continuous_coord (i : I) : Continuous (fun x : Vec I => x.coord i) := by
  change Continuous (fun x : Vec I => (vecLpIso I x) i)
  exact (PiLp.continuous_apply (p := 2) (β := fun _ : I => ℝ) i).comp
    (vecLpIso I).continuous

instance fastInnerProductSpace {r : ℕ} (size : Fin r → ℕ) :
    InnerProductSpace ℝ (fastSpace size) where
  __ := (inferInstance : NormedSpace ℝ (fastSpace size))
  inner x y := inner ℝ (x : Vec (Σ j : Fin r, Fin (size j))) y.val
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner x.val
  conj_inner_symm x y := inner_conj_symm x.val y.val
  add_left x y z := inner_add_left x.val y.val z.val
  smul_left x y c := inner_smul_left x.val y.val c

theorem fastSpace_closed {r : ℕ} (size : Fin r → ℕ) :
    IsClosed (fastSpace size : Set (Vec (Σ j : Fin r, Fin (size j)))) := by
  change IsClosed {x : Vec (Σ j : Fin r, Fin (size j)) | ∀ j, ∑ i, x.coord ⟨j, i⟩ = 0}
  have hj : ∀ j : Fin r,
      IsClosed {x : Vec (Σ j : Fin r, Fin (size j)) | ∑ i, x.coord ⟨j, i⟩ = 0} := by
    intro j
    apply isClosed_eq _ continuous_const
    exact continuous_finset_sum Finset.univ (fun i hi =>
      continuous_coord (I := Σ j : Fin r, Fin (size j)) ⟨j, i⟩)
  simpa only [Set.setOf_forall] using isClosed_iInter hj

instance fastCompleteSpace {r : ℕ} (size : Fin r → ℕ) : CompleteSpace (fastSpace size) :=
  (fastSpace_closed size).isComplete.completeSpace_coe

theorem fast_inner_formula {r : ℕ} (size : Fin r → ℕ) (v w : fastSpace size) :
    inner ℝ v w = ∑ i, v.val.coord i * w.val.coord i := rfl

theorem fast_finrank {n : ℕ} (P : Partition n) :
    Module.finrank ℝ (fastSpace P.size) = n - P.count := by
  have he := (fastRepresentation P.size
    (fun j => by have h := P.size_lower j; omega) P.total).finrank_eq
  simpa only [Module.finrank_fin_fun] using he

/-- The slow coordinate and actual fast subspace have the L2 product norm. -/
abbrev State {n : ℕ} (P : Partition n) := WithLp 2 (ℝ × fastSpace P.size)

def ofSlowFast {n : ℕ} (P : Partition n) (u : ℝ) (v : fastSpace P.size) : State P :=
  WithLp.toLp 2 (u, v)

@[simp] theorem ofSlowFast_fst {n : ℕ} (P : Partition n) (u : ℝ) (v : fastSpace P.size) :
    (ofSlowFast P u v).fst = u := rfl

@[simp] theorem ofSlowFast_snd {n : ℕ} (P : Partition n) (u : ℝ) (v : fastSpace P.size) :
    (ofSlowFast P u v).snd = v := rfl

theorem state_norm_square {n : ℕ} (P : Partition n) (x : State P) :
    ‖x‖ ^ 2 = x.fst ^ 2 + ‖x.snd‖ ^ 2 := by
  simpa only [Real.norm_eq_abs, sq_abs] using WithLp.prod_norm_sq_eq_of_L2 x

theorem state_inner_formula {n : ℕ} (P : Partition n) (x y : State P) :
    inner ℝ x y = x.fst * y.fst + inner ℝ x.snd y.snd := by
  rw [Gate147.RealProduct.product_inner]
  congr 1
  change y.fst * x.fst = x.fst * y.fst
  exact mul_comm _ _

theorem state_finite_dimensional {n : ℕ} (P : Partition n) :
    FiniteDimensional ℝ (State P) := inferInstance

theorem state_complete {n : ℕ} (P : Partition n) : CompleteSpace (State P) := inferInstance

theorem state_finrank {n : ℕ} (P : Partition n) :
    Module.finrank ℝ (State P) = n - P.count + 1 := by
  calc
    Module.finrank ℝ (State P) = Module.finrank ℝ (ℝ × fastSpace P.size) :=
      (WithLp.linearEquiv 2 ℝ (ℝ × fastSpace P.size)).finrank_eq
    _ = 1 + (n - P.count) := by
      rw [Module.finrank_prod, CommSemiring.finrank_self, fast_finrank P]
    _ = n - P.count + 1 := Nat.add_comm _ _

theorem state_dimension_bound {n : ℕ} (P : Partition n) :
    Module.finrank ℝ (State P) ≤ n := by
  rw [state_finrank P]
  exact slow_plus_fast_dimension_bound P

abbrev fixedState (n : ℕ) (hn : 2 ≤ n) := State (fixedPartition n hn)

theorem fixed_state_dimension_bound (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank ℝ (fixedState n hn) ≤ n :=
  state_dimension_bound (fixedPartition n hn)

#print axioms vecInnerProductSpace
#print axioms vecFiniteDimensional
#print axioms vecLpIso
#print axioms vecCompleteSpace
#print axioms continuous_coord
#print axioms fastInnerProductSpace
#print axioms fastSpace_closed
#print axioms fastCompleteSpace
#print axioms fast_finrank
#print axioms state_norm_square
#print axioms state_complete
#print axioms state_finrank
#print axioms fixed_state_dimension_bound

end
end Gate147.EuclideanModel
