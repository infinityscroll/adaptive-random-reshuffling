import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite uniform averaging of a bank-only nonnegative certificate.
This supplies a probability interface, not the cone's certificate itself.
No independence between the selected loss and the bank is assumed. -/
namespace Gate148.FiniteRisk
noncomputable section
open scoped BigOperators
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def uniformMean (f : Ω → ℝ) : ℝ :=
  (∑ w, f w) / (Fintype.card Ω : ℝ)

theorem uniformMean_const (a : ℝ) : uniformMean (fun _ : Ω => a) = a := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by positivity
  simp [uniformMean, hc]

theorem uniformMean_add (f g : Ω → ℝ) :
    uniformMean (fun w => f w + g w) = uniformMean f + uniformMean g := by
  simp only [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_mul (a : ℝ) (f : Ω → ℝ) :
    uniformMean (fun w => a * f w) = a * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem uniformMean_mono (f g : Ω → ℝ) (hfg : ∀ w, f w ≤ g w) :
    uniformMean f ≤ uniformMean g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum (fun w hw => hfg w))
  positivity

/-- A pathwise penalty yields an expectation bound for any realized loss
array, even one selected after observing the entire finite bank. -/
theorem loss_of_penalty (loss B : Ω → ℝ) (A c E : ℝ)
    (hc : 0 ≤ c) (hB : uniformMean B ≤ E)
    (hpoint : ∀ w, A ≤ loss w + c * B w) :
    A - c * E ≤ uniformMean loss := by
  have hp := uniformMean_mono (fun _ : Ω => A) (fun w => loss w + c * B w) hpoint
  rw [uniformMean_const, uniformMean_add, uniformMean_mul] at hp
  have he := mul_le_mul_of_nonneg_left hB hc
  linarith

/-- Explicit finite Markov-style step for the original constants. B is the
same bank-only upper certificate for every policy/output; a later theorem
must prove its nonnegativity, mean, and the good-bank objective lower. -/
theorem cone_loss_from_bank_certificate (loss B : Ω → ℝ) (mu D : ℝ)
    (hmu : 0 ≤ mu) (hD : 0 < D)
    (hB0 : ∀ w, 0 ≤ B w) (hBmean : uniformMean B ≤ D / 128)
    (hloss0 : ∀ w, 0 ≤ loss w)
    (hgood : ∀ w, B w ≤ D / 4 → mu * D ^ 2 / 8 ≤ loss w) :
    mu * D ^ 2 / 16 ≤ uniformMean loss := by
  have hc : 0 ≤ mu * D / 2 := by positivity
  have hp : ∀ w, mu * D ^ 2 / 8 ≤ loss w + (mu * D / 2) * B w := by
    intro w
    by_cases hg : B w ≤ D / 4
    · have hl := hgood w hg
      have hb := mul_nonneg hc (hB0 w)
      linarith
    · have hb : D / 4 ≤ B w := le_of_lt (lt_of_not_ge hg)
      have hm := mul_le_mul_of_nonneg_left hb hc
      nlinarith [hloss0 w]
  have h := loss_of_penalty loss B (mu * D ^ 2 / 8) (mu * D / 2)
    (D / 128) hc hBmean hp
  nlinarith [mul_nonneg hmu (sq_nonneg D)]

/-- A single bank certificate works uniformly for arbitrary path/output
choices. The selector may depend on the complete bank. This theorem does
not impose a predetermined policy or action/bank independence. -/
theorem cone_loss_for_every_selector {Choices : Ω → Type*}
    (loss : (w : Ω) → Choices w → ℝ) (B : Ω → ℝ) (mu D : ℝ)
    (hmu : 0 ≤ mu) (hD : 0 < D)
    (hB0 : ∀ w, 0 ≤ B w) (hBmean : uniformMean B ≤ D / 128)
    (hloss0 : ∀ w c, 0 ≤ loss w c)
    (hgood : ∀ w, B w ≤ D / 4 → ∀ c, mu * D ^ 2 / 8 ≤ loss w c) :
    ∀ select : (w : Ω) → Choices w,
      mu * D ^ 2 / 16 ≤ uniformMean (fun w => loss w (select w)) := by
  intro select
  exact cone_loss_from_bank_certificate (fun w => loss w (select w)) B mu D
    hmu hD hB0 hBmean (fun w => hloss0 w (select w))
    (fun w hw => hgood w hw (select w))

#print axioms loss_of_penalty
#print axioms cone_loss_from_bank_certificate
#print axioms cone_loss_for_every_selector
end
end Gate148.FiniteRisk
