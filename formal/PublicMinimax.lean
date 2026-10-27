import LowerWitness
import MinimaxOrder

/-! Actual instance-indexed strategies and the two minimax orders.
The lower is proved. The upper-sandwich theorem is EXPLICITLY conditional
on a class-uniform upper strategy, supplied mathematically by published
prior work; this file does not formally reprove that published theorem. -/
namespace Gate149.PublicMinimax
noncomputable section
open scoped ENNReal
open MeasureTheory RRModel PublicRisk LowerWitness Gate148.RateLoss

abbrev Instance (n : ℕ) (L D sigma : ℝ) :=
  Σ d : ℕ, Problem (EuclideanSpace ℝ (Fin d)) n L D sigma

/-- Full-bank informed strategy, with arbitrary instance dependence.
Thus this class contains measurable gradient/history/current-epoch
adaptive scalar strategies; it does not force predetermined schedules. -/
structure Strategy (n K : ℕ) (L D sigma : ℝ) (Seed : Type*)
    [MeasurableSpace Seed] (nu : Measure Seed) where
  eta : Instance n L D sigma → Seed → Bank n K → ℕ → ℝ
  weight : Instance n L D sigma → Seed → Bank n K → ℕ → ℝ
  eta_measurable : ∀ I bank k, k < n * K → Measurable (fun seed => eta I seed bank k)
  weight_measurable : ∀ I bank i, i ≤ n * K → Measurable (fun seed => weight I seed bank i)
  legal : ∀ I, ∀ᵐ pair ∂nu.prod (JointBankLaw.bankLaw n K),
    LegalAt n K L (eta I pair.1 pair.2) (weight I pair.1 pair.2)

def modelRisk {n K : ℕ} {L D sigma : ℝ} {Seed : Type*} [MeasurableSpace Seed]
    (nu : Measure Seed) (hn : 0 < n) (I : Instance n L D sigma)
    (a : Strategy n K L D sigma Seed nu) : ℝ≥0∞ :=
  risk nu I.2 hn (a.eta I) (a.weight I)

/-- An explicit legal strategy makes the minimax policy class nonempty.
It takes legal positive steps and returns the allowed initial state. -/
def initialStrategy (n K : ℕ) (L D sigma : ℝ) (hL : 0 < L)
    (Seed : Type*) [MeasurableSpace Seed] (nu : Measure Seed) :
    Strategy n K L D sigma Seed nu where
  eta := fun _ _ _ _ => 1 / (2 * L)
  weight := fun _ _ _ i => if i = 0 then 1 else 0
  eta_measurable := fun _ _ _ _ => measurable_const
  weight_measurable := fun _ _ _ _ => measurable_const
  legal := by
    intro I
    apply Filter.Eventually.of_forall
    intro pair
    refine ⟨fun k hk => by positivity, fun k hk => ?_, fun i hi => ?_, ?_⟩
    · exact div_le_div_of_nonneg_left (by norm_num) hL (by linarith)
    · dsimp only
      split_ifs <;> norm_num
    · simp

theorem strategy_nonempty (n K : ℕ) (L D sigma : ℝ) (hL : 0 < L)
    (Seed : Type*) [MeasurableSpace Seed] (nu : Measure Seed) :
    Nonempty (Strategy n K L D sigma Seed nu) :=
  ⟨initialStrategy n K L D sigma hL Seed nu⟩

/-- A single problem precedes every instance-responsive strategy. The
strategy seed law is arbitrary; its independence concerns only the bank. -/
theorem one_instance_all_strategies {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D) (hs : 0 ≤ sigma)
    {Seed : Type*} [MeasurableSpace Seed] (nu : Measure Seed) [IsProbabilityMeasure nu] :
    ∃ I : Instance n L D sigma, I.1 ≤ n ∧
      ∀ a : Strategy n K L D sigma Seed nu,
        ENNReal.ofReal (Psi n K L D sigma / 524288) ≤ modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I a := by
  obtain ⟨d, hd, Q, hQ⟩ := one_fixed_euclidean_instance hn hK L D sigma hL hD hs
  refine ⟨⟨d, Q⟩, hd, ?_⟩
  intro a
  borelize (EuclideanSpace ℝ (Fin d))
  exact risk_lower Q (by omega) _ (rate_nonneg n K L D sigma hL.le hD hs) hQ
    nu (a.eta ⟨d, Q⟩) (a.weight ⟨d, Q⟩) (a.eta_measurable ⟨d, Q⟩)
    (a.weight_measurable ⟨d, Q⟩) (a.legal ⟨d, Q⟩)

theorem both_minimax_lower {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D) (hs : 0 ≤ sigma)
    {Seed : Type*} [MeasurableSpace Seed] (nu : Measure Seed) [IsProbabilityMeasure nu] :
    ENNReal.ofReal (Psi n K L D sigma / 524288) ≤
      (⨆ I, ⨅ a, modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I a) ∧
    ENNReal.ofReal (Psi n K L D sigma / 524288) ≤
      (⨅ a, ⨆ I, modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I a) := by
  obtain ⟨I, hd, hI⟩ := one_instance_all_strategies hn hK L D sigma hL hD hs nu
  exact MinimaxOrder.fixed_witness_both_lower (modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega)) _ I hI

/-- The complete rate sandwich CONDITIONAL on the separately supplied
published upper guarantee. Neither exact minimax equality nor an upper
for every legal strategy is claimed. No axiom is declared. -/
theorem sandwich_given_upper_strategy {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K)
    (L D sigma : ℝ) (hL : 0 < L) (hD : 0 ≤ D) (hs : 0 ≤ sigma)
    {Seed : Type*} [MeasurableSpace Seed] (nu : Measure Seed) [IsProbabilityMeasure nu]
    (aUpper : Strategy n K L D sigma Seed nu)
    (hUpper : ∀ I, modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I aUpper ≤
      ENNReal.ofReal (57 * Psi n K L D sigma)) :
    ENNReal.ofReal (Psi n K L D sigma / 524288) ≤
      (⨆ I, ⨅ a, modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I a) ∧
    (⨆ I, ⨅ a, modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I a) ≤
      ENNReal.ofReal (57 * Psi n K L D sigma) ∧
    ENNReal.ofReal (Psi n K L D sigma / 524288) ≤
      (⨅ a, ⨆ I, modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I a) ∧
    (⨅ a, ⨆ I, modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega) I a) ≤
      ENNReal.ofReal (57 * Psi n K L D sigma) := by
  obtain ⟨I, hd, hI⟩ := one_instance_all_strategies hn hK L D sigma hL hD hs nu
  exact MinimaxOrder.conditional_sandwich (modelRisk (n := n) (K := K) (L := L) (D := D) (sigma := sigma) nu (by omega)) _ _ I aUpper hI hUpper

#print axioms one_instance_all_strategies
#print axioms initialStrategy
#print axioms strategy_nonempty
#print axioms both_minimax_lower
#print axioms sandwich_given_upper_strategy
end
end Gate149.PublicMinimax
