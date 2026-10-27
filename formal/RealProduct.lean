import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.Ring

/-! Narrow real L2-product instance. It proves compatibility with the actual
existing L2 norm, without importing the unrelated orthonormal-basis layer. -/
namespace Gate147.RealProduct
noncomputable section
open scoped InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

instance realProductInner : InnerProductSpace ℝ (WithLp 2 (E × F)) where
  inner x y := inner ℝ x.fst y.fst + inner ℝ x.snd y.snd
  norm_sq_eq_re_inner x := by simp [WithLp.prod_norm_sq_eq_of_L2]
  conj_inner_symm x y := by simp [real_inner_comm]
  add_left x y z := by
    simp only [WithLp.add_fst, WithLp.add_snd, inner_add_left]
    ring
  smul_left x y r := by
    simp only [WithLp.smul_fst, WithLp.smul_snd, inner_smul_left]
    ring

theorem product_inner (x y : WithLp 2 (E × F)) :
    inner ℝ x y = inner ℝ x.fst y.fst + inner ℝ x.snd y.snd := rfl

#print axioms realProductInner
#print axioms product_inner
end
end Gate147.RealProduct
