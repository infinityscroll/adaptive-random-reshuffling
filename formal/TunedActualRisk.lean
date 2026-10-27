import ActualBankRisk
import TunedThresholds

/-!
Gate148. Tuned positive-parameter ACTUAL finite-bank expected loss and
actual legal-instance facts. The deficit, threshold, geometric-envelope
mean and Markov conditions are all discharged by the parameter-only
construction. No desired certificate, good-bank probability, retention,
or risk inequality is an input to the final theorem.

The scalar steps and scalar convex weights may depend on the ENTIRE bank.
The fixed partition and objective are chosen before these selectors. Thus
no policy/bank independence or online-revelation restriction is introduced.
Private-seed integration, the zero-parameter branches, the deterministic
bias witness and the final Psi/minimax/rate assembly remain separate.
Root alone compiles this source.
-/
namespace Gate148.TunedActualRisk
noncomputable section
open scoped BigOperators InnerProductSpace
open Gate146.LabeledBlocks
open Gate148.ActualBankRisk Gate148.FiniteRisk

theorem positive_n {n : ℕ} (hn : 2 ≤ n) : 0 < n := by omega

/-- The block-count input is obtained from the ACTUAL partition. -/
theorem partition_count_real {n : ℕ} (P : Partition n) :
    2 * (P.count : ℝ) ≤ (n : ℝ) := by
  have hc := P.count_le_half
  have hnat : 2 * P.count ≤ n := by omega
  exact_mod_cast hnat

theorem retention_b_eq (ell a : ℝ) :
    ActualRetention.b ell a = HardParameters.b ell a := rfl

theorem retention_C_eq (mu ell a D : ℝ) :
    ActualRetention.C mu ell a D = HardParameters.H mu ell a * D := rfl

/-- The exact concrete expected-loss theorem. There is no scalar
certificate premise: every tuning condition is proved from the original
n,K,L,D,sigma parameters and the actual partition bound. -/
theorem actual_tuned_expected_output_loss {n K : ℕ} (P : Partition n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hsigma : 0 < sigma)
    (eta weight : Bank n K → ℕ → ℝ)
    (heta : ∀ bank k, k < n * K → 0 < eta bank k)
    (hetaL : ∀ bank k, k < n * K → eta bank k ≤ 1 / L)
    (hw : ∀ bank i, i ≤ n * K → 0 ≤ weight bank i)
    (hsum : ∀ bank, ∑ i ∈ Finset.range (n * K + 1), weight bank i = 1) :
    let ell := HardParameters.ell n K L D sigma
    let mu := HardParameters.mu n K L D sigma
    let a := HardParameters.a n K L D sigma
    mu * D ^ 2 / 16 ≤ uniformMean
      (selectedLoss P (positive_n hn) ell mu a sigma D eta weight) := by
  let e := HardParameters.ell n K L D sigma
  let m := HardParameters.mu n K L D sigma
  let aa := HardParameters.a n K L D sigma
  let r : ℝ := (P.count : ℝ)
  let bb := HardParameters.b0 m e aa D sigma r
  let h := HardParameters.stepThreshold m e aa D sigma r
  let A := HardParameters.radiusThreshold m e aa D sigma r
  change m * D ^ 2 / 16 ≤ uniformMean
    (selectedLoss P (positive_n hn) e m aa sigma D eta weight)
  have he : 0 < e := HardParameters.ell_pos hn hK hL hD hsigma
  have hm : 0 < m := HardParameters.mu_pos hn hK hL hD hsigma
  have ha : 0 < aa := HardParameters.a_pos hn hK hL hD hsigma
  have heL : e ≤ L := HardParameters.ell_le_L n K L D sigma
  have hcap : m ≤ e / 4 := HardParameters.mu_le_ell_quarter hn hK hL hD hsigma
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrn : 2 * r ≤ (n : ℝ) := partition_count_real P
  have hth := HardParameters.actual_thresholds hn hK hL hD hsigma hr hrn
  dsimp only at hth
  have hbb : 0 < bb := hth.2.2.1
  have hbbdef : bb = ActualRetention.b e aa -
      2 * ActualRetention.C m e aa D * e * Real.sqrt (P.count : ℝ) / sigma := by
    rw [retention_b_eq, retention_C_eq]
    dsimp only [bb, r, HardParameters.b0]
    ring
  have hhdef : h = 120 * ActualRetention.C m e aa D / (bb * sigma) := by
    rw [retention_C_eq]
    dsimp only [h, HardParameters.stepThreshold]
    ring
  have hAdata := TunedThresholds.actual_threshold_bounds hn hK hL hD hsigma hr hrn
  dsimp only at hAdata
  have hAdef : A = sigma * h + 10 * ActualRetention.C m e aa D / bb := by
    rw [retention_C_eq]
    exact hAdata.1
  have hraw := TunedThresholds.actual_bank_mean_certificate hn hK hL hD hsigma hr hrn
  dsimp only at hraw
  have hscalar : certificateMeanBound P K L (ActualRetention.C m e aa D)
      (ActualRetention.b e aa) sigma A ≤ D / 128 := by
    rw [retention_C_eq, retention_b_eq]
    exact hraw.2.le
  exact actual_expected_output_loss P (positive_n hn) hn L e m aa sigma D
    eta weight hL he heL hm hcap ha hsigma hD heta hetaL hw hsum
    bb h A hbb hbbdef hhdef hAdef hscalar

/-- The fixed partition exists for every n>=2 and is selected independently
of bank, policy and output. This specialization is the actual parameter-only
instance used by the construction. -/
theorem fixed_tuned_expected_output_loss {n K : ℕ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hsigma : 0 < sigma)
    (eta weight : Bank n K → ℕ → ℝ)
    (heta : ∀ bank k, k < n * K → 0 < eta bank k)
    (hetaL : ∀ bank k, k < n * K → eta bank k ≤ 1 / L)
    (hw : ∀ bank i, i ≤ n * K → 0 ≤ weight bank i)
    (hsum : ∀ bank, ∑ i ∈ Finset.range (n * K + 1), weight bank i = 1) :
    let ell := HardParameters.ell n K L D sigma
    let mu := HardParameters.mu n K L D sigma
    let a := HardParameters.a n K L D sigma
    mu * D ^ 2 / 16 ≤ uniformMean
      (selectedLoss (fixedPartition n hn) (positive_n hn)
        ell mu a sigma D eta weight) :=
  actual_tuned_expected_output_loss (fixedPartition n hn) hn hK L D sigma
    hL hD hsigma eta weight heta hetaL hw hsum

/-- Actual instance membership: the gradient is identified by HasFDerivAt;
the variance is the actual centered variance at the actual minimizer;
distance and dimension use the inherited Euclidean model. These facts are
proved for the SAME parameter choices as the preceding risk theorem. -/
theorem actual_tuned_legal_instance {n K : ℕ} (P : Partition n)
    (hn : 2 ≤ n) (hK : 1 ≤ K) (L D sigma : ℝ)
    (hL : 0 < L) (hD : 0 < D) (hsigma : 0 < sigma) :
    let ell := HardParameters.ell n K L D sigma
    let mu := HardParameters.mu n K L D sigma
    let a := HardParameters.a n K L D sigma
    (∀ i, ConvexOn ℝ Set.univ (ActualInstance.component P mu ell a sigma i)) ∧
    (∀ i x, HasFDerivAt (ActualInstance.component P mu ell a sigma i)
      (innerSL ℝ (ActualInstance.componentGradient P mu ell a sigma i x)) x) ∧
    (∀ i, LipschitzWith ⟨L, hL.le⟩
      (ActualInstance.componentGradient P mu ell a sigma i)) ∧
    (∀ x : ActualInstance.Space P,
      ActualInstance.mean P mu ell a sigma 0 ≤ ActualInstance.mean P mu ell a sigma x) ∧
    ((∑ i : Fin n,
      ‖ActualInstance.componentGradient P mu ell a sigma i 0 -
        ActualInstance.meanGradient P mu ell a sigma 0‖ ^ 2) / (n : ℝ) = sigma ^ 2) ∧
    dist (ActualInstance.initial P D) (0 : ActualInstance.Space P) = D ∧
    Module.finrank ℝ (ActualInstance.Space P) ≤ n ∧
    (∀ i, BddBelow (Set.range (ActualInstance.component P mu ell a sigma i))) := by
  dsimp only
  have he := HardParameters.ell_pos hn hK hL hD hsigma
  have hm := HardParameters.mu_pos hn hK hL hD hsigma
  have hcap := HardParameters.mu_le_ell_quarter hn hK hL hD hsigma
  have heL := HardParameters.ell_le_L n K L D sigma
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ActualInstance.component_convex P _ _ _ _ i hm.le he.le
  · intro i x
    exact ActualInstance.component_hasFDerivAt P _ _ _ _ i hm.le he.le x
  · intro i
    exact ActualInstance.componentGradient_L_lipschitz P L _ _ _ _ i hL hm.le hcap heL
  · exact ActualInstance.mean_minimized_at_zero P hn _ _ _ _ hm.le he.le
  · exact ActualInstance.centered_variance_at_zero P hn _ _ _ _
  · exact ActualInstance.initial_distance P D hD.le
  · exact ActualInstance.dimension_le P
  · intro i
    exact ActualInstance.component_bddBelow P _ _ _ _ i hm.le he

#print axioms partition_count_real
#print axioms actual_tuned_expected_output_loss
#print axioms fixed_tuned_expected_output_loss
#print axioms actual_tuned_legal_instance
end
end Gate148.TunedActualRisk
