import FiniteLowerBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Gate149: public finite-sum class and its actual random-reshuffling dynamics.
The class has arbitrary finite dimension. Dimension<=n and individual
component boundedness below are witness properties, NOT class restrictions.
No independence of step/output selectors from the permutation bank occurs.
No measurable-space instance on Bank is installed in this module.
Root alone compiles; no compiler has been run by the author.
-/
namespace Gate149.RRModel
noncomputable section
open scoped BigOperators

universe u v

def finiteMean {E : Type u} {n : ℕ} (f : Fin n → E → ℝ) (x : E) : ℝ :=
  (∑ i : Fin n, f i x) / (n : ℝ)

/-- The full finite-dimensional convex finite-sum class. Parameter signs and
n>=2 are retained by the outer theorem, not silently strengthened here. -/
structure Problem (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (n : ℕ) (L D sigma : ℝ) where
  f : Fin n → E → ℝ
  grad : Fin n → E → E
  x0 : E
  xstar : E
  hasFDerivAt : ∀ i x, HasFDerivAt (f i) (innerSL ℝ (grad i x)) x
  convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  grad_lipschitz : ∀ i x y, ‖grad i x - grad i y‖ ≤ L * ‖x - y‖
  minimized : ∀ x, finiteMean f xstar ≤ finiteMean f x
  initial_distance : dist x0 xstar ≤ D
  variance : (∑ i : Fin n, ‖grad i xstar‖ ^ 2) / (n : ℝ) ≤ sigma ^ 2

abbrev Bank (n K : ℕ) := Gate148.ActualBankRisk.Bank n K
abbrev LegalSelectors := Gate148.FiniteLowerBound.LegalSelectors

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {n K : ℕ} {L D sigma : ℝ}

theorem Problem.component_continuous (Q : Problem E n L D sigma) (i : Fin n) :
    Continuous (Q.f i) := by
  exact continuous_iff_continuousAt.2 (fun x => (Q.hasFDerivAt i x).continuousAt)

/-- The actual derivative field is continuous by the specified global
gradient inequality. Absolute L is used only to avoid an extraneous sign
premise in this helper; legal problems retain their original L. -/
theorem Problem.gradient_lipschitzWith (Q : Problem E n L D sigma) (i : Fin n) :
    LipschitzWith ⟨|L|, abs_nonneg L⟩ (Q.grad i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [dist_eq_norm]
  exact (Q.grad_lipschitz i x y).trans
    (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))

theorem Problem.gradient_continuous (Q : Problem E n L D sigma) (i : Fin n) :
    Continuous (Q.grad i) :=
  (Q.gradient_lipschitzWith i).continuous

theorem Problem.mean_continuous (Q : Problem E n L D sigma) :
    Continuous (finiteMean Q.f) := by
  exact (continuous_finset_sum Finset.univ
    (fun i _ => Q.component_continuous i)).div_const (n : ℝ)

/-- Literal component-gradient recursion, using the original fixed-label
accessor. The bank is not resampled at a step or conditioned on its selector. -/
def trajectory (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta : ℕ → ℝ) : ℕ → E
  | 0 => Q.x0
  | t + 1 => trajectory Q hn bank eta t - eta t •
      Q.grad (Gate146.ActualSequence.currentLabel hn bank t) (trajectory Q hn bank eta t)

@[simp] theorem trajectory_zero (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta : ℕ → ℝ) : trajectory Q hn bank eta 0 = Q.x0 := rfl

theorem trajectory_succ (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta : ℕ → ℝ) (t : ℕ) :
    trajectory Q hn bank eta (t + 1) = trajectory Q hn bank eta t - eta t •
      Q.grad (Gate146.ActualSequence.currentLabel hn bank t) (trajectory Q hn bank eta t) := rfl

/-- All actual states, including the initial and final state. -/
def output (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta weight : ℕ → ℝ) : E :=
  ∑ i ∈ Finset.range (n * K + 1), weight i • trajectory Q hn bank eta i

def loss (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta weight : ℕ → ℝ) : ℝ :=
  finiteMean Q.f (output Q hn bank eta weight) - finiteMean Q.f Q.xstar

/-- Nonnegativity follows from the actual global minimum. No selector
legality or desired risk bound is needed for this pointwise fact. -/
theorem loss_nonneg (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta weight : ℕ → ℝ) :
    0 ≤ loss Q hn bank eta weight :=
  sub_nonneg.mpr (Q.minimized (output Q hn bank eta weight))

section SeedMeasurability
variable {Seed : Type v} [MeasurableSpace Seed]
variable [MeasurableSpace E] [BorelSpace E]

/-- Seedwise measurability at a fixed bank, with assumptions only on the
finite update prefix used. Actual gradient continuity is proved above. -/
theorem trajectory_measurable (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta : Seed → ℕ → ℝ) (N : ℕ)
    (heta : ∀ k < N, Measurable (fun seed => eta seed k)) :
    ∀ t, t ≤ N → Measurable (fun seed => trajectory Q hn bank (eta seed) t) := by
  intro t
  induction t with
  | zero =>
      intro ht
      exact measurable_const
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hg := (Q.gradient_continuous
        (Gate146.ActualSequence.currentLabel hn bank t)).measurable.comp hprev
      simpa only [trajectory_succ] using
        hprev.sub ((heta t (by omega)).smul hg)

theorem output_measurable (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta weight : Seed → ℕ → ℝ)
    (heta : ∀ k < n * K, Measurable (fun seed => eta seed k))
    (hweight : ∀ i, i ≤ n * K → Measurable (fun seed => weight seed i)) :
    Measurable (fun seed => output Q hn bank (eta seed) (weight seed)) := by
  apply Finset.measurable_sum
  intro i hi
  have hiT : i ≤ n * K := by have hh := Finset.mem_range.mp hi; omega
  exact (hweight i hiT).smul (trajectory_measurable Q hn bank eta (n * K) heta i hiT)

theorem loss_measurable (Q : Problem E n L D sigma) (hn : 0 < n)
    (bank : Bank n K) (eta weight : Seed → ℕ → ℝ)
    (heta : ∀ k < n * K, Measurable (fun seed => eta seed k))
    (hweight : ∀ i, i ≤ n * K → Measurable (fun seed => weight seed i)) :
    Measurable (fun seed => loss Q hn bank (eta seed) (weight seed)) := by
  exact (Q.mean_continuous.measurable.comp
    (output_measurable Q hn bank eta weight heta hweight)).sub measurable_const

end SeedMeasurability

#print axioms Problem.component_continuous
#print axioms Problem.gradient_lipschitzWith
#print axioms Problem.gradient_continuous
#print axioms Problem.mean_continuous
#print axioms trajectory_succ
#print axioms loss_nonneg
#print axioms trajectory_measurable
#print axioms output_measurable
#print axioms loss_measurable
end
end Gate149.RRModel
