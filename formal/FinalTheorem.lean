import LowerWitness
import EpochProductLaw
import PublicMinimax

/-! Public entrypoint: the exact lower under fresh independent uniform
epoch permutations and an arbitrary independent private seed. Class
membership and gradient recursion are contained in RRModel.Problem/loss.
No published upper guarantee is a premise of this lower theorem. -/
namespace Gate149.FinalTheorem
noncomputable section
open scoped ENNReal
open MeasureTheory RRModel PublicRisk Gate148.RateLoss

theorem one_fixed_instance_fresh_epoch_lower {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D) (hs : 0 ≤ sigma) :
    ∃ d : ℕ, d ≤ n ∧ ∃ Q : Problem (EuclideanSpace ℝ (Fin d)) n L D sigma,
      ∀ (Seed : Type*) [MeasurableSpace Seed] (nu : Measure Seed) [IsProbabilityMeasure nu]
        (eta weight : Seed → Bank n K → ℕ → ℝ),
        (∀ bank k, k < n * K → Measurable (fun seed => eta seed bank k)) →
        (∀ bank i, i ≤ n * K → Measurable (fun seed => weight seed bank i)) →
        (∀ᵐ pair ∂nu.prod (EpochProductLaw.independentEpochLaw n K),
          LegalAt n K L (eta pair.1 pair.2) (weight pair.1 pair.2)) →
        ENNReal.ofReal (Psi n K L D sigma / 524288) ≤
          ∫⁻ pair, ENNReal.ofReal
            (loss Q (by omega) pair.2 (eta pair.1 pair.2) (weight pair.1 pair.2))
            ∂nu.prod (EpochProductLaw.independentEpochLaw n K) := by
  obtain ⟨d, hd, Q, hQ⟩ := LowerWitness.one_fixed_instance_joint_lower hn hK
    L D sigma hL hD hs
  refine ⟨d, hd, Q, ?_⟩
  intro Seed inst nu instProb eta weight heta hweight hlegal
  rw [← EpochProductLaw.bankLaw_eq_independentEpochLaw] at hlegal ⊢
  exact hQ Seed nu eta weight heta hweight hlegal

#print axioms one_fixed_instance_fresh_epoch_lower
#print axioms PublicMinimax.both_minimax_lower
#print axioms PublicMinimax.sandwich_given_upper_strategy
end
end Gate149.FinalTheorem
