import ActualProblemBridge
import IsometricTransport
import PublicRisk

/-! One parameter-only actual Euclidean instance, selected before every
seed law and selector, with the full all-parameter randomized RR lower.
The rate is unchanged from Gate134. The upper is published prior work,
not an axiom or a theorem manufactured in this file. -/
namespace Gate149.LowerWitness
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory RRModel PublicRisk ActualProblemBridge IsometricTransport
open Gate148.RateLoss Gate148.FiniteLowerBound

theorem rate_nonneg (n K : ℕ) (L D sigma : ℝ)
    (hL : 0 ≤ L) (hD : 0 ≤ D) (hs : 0 ≤ sigma) :
    0 ≤ Psi n K L D sigma / 524288 := by
  dsimp only [Psi, A0, B0, N1, N2]
  positivity

/-- A single actual problem in standard Euclidean dimension at most n
works for EVERY full-bank-dependent legal scalar step/output selector.
The class itself still allows arbitrary finite dimension. -/
theorem one_fixed_euclidean_instance {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D) (hs : 0 ≤ sigma) :
    ∃ d : ℕ, d ≤ n ∧ ∃ Q : Problem (EuclideanSpace ℝ (Fin d)) n L D sigma,
      UniformLower Q (by omega) K (Psi n K L D sigma / 524288) := by
  let P := Gate146.LabeledBlocks.fixedPartition n hn
  have hn0 : 0 < n := by omega
  obtain ⟨chooseCone, hpos, hb⟩ := one_fixed_branch_uniform_lower P hn0 hn hK
    L D sigma hL hD hs
  cases chooseCone with
  | false =>
      let Q := quadraticProblem n K hn hK L D sigma hL hD
      refine ⟨Module.finrank ℝ ℝ, quadratic_dimension hn, standardProblem Q, ?_⟩
      intro eta weight hlegal
      calc
        Psi n K L D sigma / 524288 ≤
            Gate148.FiniteRisk.uniformMean (quadraticLoss n K L D eta weight) := by
          simpa using hb eta weight hlegal
        _ = Gate148.FiniteRisk.uniformMean
            (fun bank => loss (standardProblem Q) hn0 bank (eta bank) (weight bank)) := by
          congr 1
          funext bank
          rw [standard_loss]
          exact (quadratic_loss_eq hn0 hn hK L D sigma hL hD eta weight bank).symm
  | true =>
      obtain ⟨hDp, hsp⟩ := hpos rfl
      let Q := coneProblem P hn hK L D sigma hL hDp hsp
      refine ⟨Module.finrank ℝ (Gate148.ActualInstance.Space P), cone_dimension P,
        standardProblem Q, ?_⟩
      intro eta weight hlegal
      calc
        Psi n K L D sigma / 524288 ≤
            Gate148.FiniteRisk.uniformMean (coneLoss P hn0 L D sigma eta weight) := by
          simpa using hb eta weight hlegal
        _ = Gate148.FiniteRisk.uniformMean
            (fun bank => loss (standardProblem Q) hn0 bank (eta bank) (weight bank)) := by
          congr 1
          funext bank
          rw [standard_loss]
          exact (cone_loss_eq P hn0 hn hK L D sigma hL hDp hsp eta weight
            hlegal.1 hlegal.2.1 bank).symm

/-- Actual joint expectation, with a single instance preceding the private
seed space, its probability law, and all measurable adaptive selectors.
The permitted selectors are stronger than causal current-epoch policies:
they may inspect the entire epoch bank. Legality is only product-a.e.
The witness dimension cap is not a restriction on the optimization class. -/
theorem one_fixed_instance_joint_lower {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D) (hs : 0 ≤ sigma) :
    ∃ d : ℕ, d ≤ n ∧ ∃ Q : Problem (EuclideanSpace ℝ (Fin d)) n L D sigma,
      ∀ (Seed : Type*) [MeasurableSpace Seed] (nu : Measure Seed) [IsProbabilityMeasure nu]
        (eta weight : Seed → Bank n K → ℕ → ℝ),
        (∀ bank k, k < n * K → Measurable (fun seed => eta seed bank k)) →
        (∀ bank i, i ≤ n * K → Measurable (fun seed => weight seed bank i)) →
        (∀ᵐ pair ∂nu.prod (JointBankLaw.bankLaw n K),
          LegalAt n K L (eta pair.1 pair.2) (weight pair.1 pair.2)) →
        ENNReal.ofReal (Psi n K L D sigma / 524288) ≤
          risk nu Q (by omega) eta weight := by
  obtain ⟨d, hd, Q, hQ⟩ := one_fixed_euclidean_instance hn hK L D sigma hL hD hs
  refine ⟨d, hd, Q, ?_⟩
  intro Seed inst nu instProb eta weight heta hweight hlegal
  borelize (EuclideanSpace ℝ (Fin d))
  exact risk_lower Q (by omega) _ (rate_nonneg n K L D sigma hL.le hD hs)
    hQ nu eta weight heta hweight hlegal

#print axioms rate_nonneg
#print axioms one_fixed_euclidean_instance
#print axioms one_fixed_instance_joint_lower
end
end Gate149.LowerWitness
