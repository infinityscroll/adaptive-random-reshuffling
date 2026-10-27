import RRModel
import JointBankLaw

/-! The actual public-model loss under an independent private seed and
fresh uniform permutation bank. Selectors may depend on the entire bank;
legality is required only almost everywhere under that actual joint law.
No integrability assumption and no selector/bank independence is imposed. -/
namespace Gate149.PublicRisk
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory RRModel

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n K : ℕ} {L D sigma : ℝ}

def LegalAt (n K : ℕ) (L : ℝ) (eta weight : ℕ → ℝ) : Prop :=
  (∀ k < n * K, 0 < eta k) ∧ (∀ k < n * K, eta k ≤ 1 / L) ∧
  (∀ i, i ≤ n * K → 0 ≤ weight i) ∧
  (∑ i ∈ Finset.range (n * K + 1), weight i = 1)

theorem legalSelectors_iff (eta weight : Bank n K → ℕ → ℝ) :
    LegalSelectors n K L eta weight ↔ ∀ bank, LegalAt n K L (eta bank) (weight bank) := by
  constructor
  · intro h bank
    exact ⟨h.1 bank, h.2.1 bank, h.2.2.1 bank, h.2.2.2 bank⟩
  · intro h
    exact ⟨fun bank => (h bank).1, fun bank => (h bank).2.1,
      fun bank => (h bank).2.2.1, fun bank => (h bank).2.2.2⟩

def UniformLower (Q : Problem E n L D sigma) (hn : 0 < n) (K : ℕ) (c : ℝ) : Prop :=
  ∀ eta weight : Bank n K → ℕ → ℝ, LegalSelectors n K L eta weight →
    c ≤ Gate148.FiniteRisk.uniformMean
      (fun bank => loss Q hn bank (eta bank) (weight bank))

def risk {Seed : Type v} [MeasurableSpace Seed] (nu : Measure Seed)
    (Q : Problem E n L D sigma) (hn : 0 < n)
    (eta weight : Seed → Bank n K → ℕ → ℝ) : ℝ≥0∞ :=
  ∫⁻ pair, ENNReal.ofReal (loss Q hn pair.2 (eta pair.1 pair.2) (weight pair.1 pair.2))
    ∂nu.prod (JointBankLaw.bankLaw n K)

section Measurable
variable [MeasurableSpace E] [BorelSpace E]
variable {Seed : Type v} [MeasurableSpace Seed]

theorem joint_loss_measurable (Q : Problem E n L D sigma) (hn : 0 < n)
    (eta weight : Seed → Bank n K → ℕ → ℝ)
    (heta : ∀ bank k, k < n * K → Measurable (fun seed => eta seed bank k))
    (hweight : ∀ bank i, i ≤ n * K → Measurable (fun seed => weight seed bank i)) :
    Measurable (fun pair : Seed × Bank n K =>
      loss Q hn pair.2 (eta pair.1 pair.2) (weight pair.1 pair.2)) := by
  apply JointBankLaw.measurable_from_seed_sections
    (fun seed bank => loss Q hn bank (eta seed bank) (weight seed bank))
  intro bank
  exact loss_measurable Q hn bank (fun seed => eta seed bank)
    (fun seed => weight seed bank) (heta bank) (hweight bank)

/-- The fixed actual problem is chosen before the seed space, probability
law and all selectors. Legal actions may depend on both random inputs. -/
theorem risk_lower (Q : Problem E n L D sigma) (hn : 0 < n) (c : ℝ) (hc : 0 ≤ c)
    (hQ : UniformLower Q hn K c)
    (nu : Measure Seed) [IsProbabilityMeasure nu]
    (eta weight : Seed → Bank n K → ℕ → ℝ)
    (heta : ∀ bank k, k < n * K → Measurable (fun seed => eta seed bank k))
    (hweight : ∀ bank i, i ≤ n * K → Measurable (fun seed => weight seed bank i))
    (hlegal : ∀ᵐ pair ∂nu.prod (JointBankLaw.bankLaw n K),
      LegalAt n K L (eta pair.1 pair.2) (weight pair.1 pair.2)) :
    ENNReal.ofReal c ≤ risk nu Q hn eta weight := by
  have hs := JointBankLaw.ae_seed_forall_bank_of_ae_joint n K nu
    (fun pair => LegalAt n K L (eta pair.1 pair.2) (weight pair.1 pair.2)) hlegal
  apply JointBankLaw.joint_lower_of_ae_seed nu
    (fun pair => loss Q hn pair.2 (eta pair.1 pair.2) (weight pair.1 pair.2))
    (joint_loss_measurable Q hn eta weight heta hweight)
    (fun pair => loss_nonneg Q hn pair.2 _ _) c hc
  exact hs.mono (fun seed h => hQ (eta seed) (weight seed)
    ((legalSelectors_iff (eta seed) (weight seed)).mpr h))
end Measurable

#print axioms legalSelectors_iff
#print axioms joint_loss_measurable
#print axioms risk_lower
end
end Gate149.PublicRisk
