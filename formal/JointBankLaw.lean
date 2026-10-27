import RandomizedRisk
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
Gate149. Actual finite uniform permutation-bank measure and its product with
an arbitrary private-seed probability measure. All nonnegative expectations
are ENNReal integrals, permitting infinite loss without an integrability
restriction. The loss and all selectors may depend on both coordinates.
Only the input law is the independent product of seed and uniform bank.

The product-a.e. to seed-a.e./every-bank step is proved from the actual
strictly positive singleton masses, not assumed as a policy restriction.
No compiler, Lake or package modification is performed by the author.
-/
namespace Gate149.JointBankLaw
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Gate148.RandomizedRisk

section FiniteLaw
variable (B : Type*) [Fintype B] [Nonempty B] [MeasurableSpace B]
  [MeasurableSingletonClass B]

/-- Actual uniformly weighted sum of Dirac probability measures. -/
def finiteUniformLaw : Measure B :=
  (Fintype.card B : ℝ≥0∞)⁻¹ • ∑ bank : B, Measure.dirac bank

instance finiteUniformLaw_probability : IsProbabilityMeasure (finiteUniformLaw B) := by
  classical
  have hc : (Fintype.card B : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card B ≠ 0)
  refine ⟨?_⟩
  unfold finiteUniformLaw
  rw [Measure.smul_apply, Measure.finset_sum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hc (by simp)

theorem finiteUniformLaw_singleton (bank : B) :
    finiteUniformLaw B {bank} = (Fintype.card B : ℝ≥0∞)⁻¹ := by
  classical
  unfold finiteUniformLaw
  rw [Measure.smul_apply, Measure.finset_sum_apply]
  simp [Measure.dirac_apply, Set.indicator, smul_eq_mul]

theorem finiteUniformLaw_singleton_pos (bank : B) :
    0 < finiteUniformLaw B {bank} := by
  rw [finiteUniformLaw_singleton]
  exact ENNReal.inv_pos.2 (by simp)

/-- Exact equality with the previously accepted finite-uniform ENNReal sum. -/
theorem lintegral_finiteUniformLaw (f : B → ℝ≥0∞) :
    (∫⁻ bank, f bank ∂finiteUniformLaw B) = uniformENNMean f := by
  classical
  unfold finiteUniformLaw uniformENNMean
  rw [lintegral_smul_measure, lintegral_finset_sum_measure]
  simp only [lintegral_dirac, smul_eq_mul, Finset.mul_sum]

/-- There are no nonempty null subsets of the finite uniform bank. -/
theorem ae_finiteUniformLaw_iff (P : B → Prop) :
    (∀ᵐ bank ∂finiteUniformLaw B, P bank) ↔ ∀ bank, P bank := by
  constructor
  · intro h bank
    exact (ae_iff_of_countable.mp h) bank (ne_of_gt (finiteUniformLaw_singleton_pos B bank))
  · intro h
    exact Filter.Eventually.of_forall h
end FiniteLaw

/-- The original bank type, including empty epoch index sets when K=0. -/
abbrev Bank (n K : ℕ) := Fin K → Equiv.Perm (Fin n)

instance bankMeasurableSpace (n K : ℕ) : MeasurableSpace (Bank n K) := ⊤

instance bankNonempty (n K : ℕ) : Nonempty (Bank n K) :=
  ⟨fun _ => Equiv.refl _⟩

theorem bank_all_sets_measurable (n K : ℕ) (s : Set (Bank n K)) : MeasurableSet s := by
  exact MeasurableSpace.measurableSet_top

/-- The concrete, nonempty, finite, uniformly distributed permutation bank. -/
abbrev bankLaw (n K : ℕ) : Measure (Bank n K) := finiteUniformLaw (Bank n K)

instance bankLaw_probability (n K : ℕ) : IsProbabilityMeasure (bankLaw n K) :=
  finiteUniformLaw_probability (Bank n K)

theorem bankLaw_singleton_pos (n K : ℕ) (bank : Bank n K) :
    0 < bankLaw n K {bank} := finiteUniformLaw_singleton_pos (Bank n K) bank

section JointLaw
variable {Seed B : Type*} [MeasurableSpace Seed]
  [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

/-- A finite discrete bank lets seedwise measurable sections assemble into
an actual jointly measurable selector or loss. -/
theorem measurable_from_seed_sections {Y : Type*} [MeasurableSpace Y]
    (f : Seed → B → Y) (hf : ∀ bank, Measurable (fun seed => f seed bank)) :
    Measurable (fun pair : Seed × B => f pair.1 pair.2) :=
  measurable_from_prod_countable_left hf

/-- Tonelli for the actual uniform-bank measure, with the finite inner
integral identified exactly. This remains valid for infinite ENNReal loss. -/
theorem joint_lintegral_eq_uniform (nu : Measure Seed)
    (f : Seed × B → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ pair, f pair ∂nu.prod (finiteUniformLaw B)) =
      ∫⁻ seed, uniformENNMean (fun bank => f (seed, bank)) ∂nu := by
  rw [lintegral_prod f hf.aemeasurable]
  apply lintegral_congr
  intro seed
  exact lintegral_finiteUniformLaw B (fun bank => f (seed, bank))

/-- The previous iterated real-loss wrapper equals the ACTUAL joint product
expectation for measurable nonnegative losses, not just a formal surrogate. -/
theorem joint_real_loss_eq_randomizedLoss (nu : Measure Seed)
    (loss : Seed × B → ℝ) (hloss : Measurable loss)
    (h0 : ∀ pair, 0 ≤ loss pair) :
    (∫⁻ pair, ENNReal.ofReal (loss pair) ∂nu.prod (finiteUniformLaw B)) =
      randomizedLoss nu (fun seed bank => loss (seed, bank)) := by
  rw [joint_lintegral_eq_uniform nu (fun pair => ENNReal.ofReal (loss pair))
    hloss.ennreal_ofReal]
  exact (randomizedLoss_eq_uniformENNMean nu
    (fun seed bank => loss (seed, bank)) (fun seed bank => h0 (seed, bank))).symm

/-- Product-a.e. legality gives legality at EVERY bank for almost every
seed, because every finite bank has strictly positive mass. No independence
of Legal or of its selected actions from either coordinate is assumed. -/
theorem ae_seed_forall_of_ae_joint (nu : Measure Seed) (Legal : Seed × B → Prop)
    (hlegal : ∀ᵐ pair ∂nu.prod (finiteUniformLaw B), Legal pair) :
    ∀ᵐ seed ∂nu, ∀ bank, Legal (seed, bank) := by
  have h := Measure.ae_ae_of_ae_prod hlegal
  exact h.mono (fun seed hs => (ae_finiteUniformLaw_iff B (fun bank => Legal (seed, bank))).mp hs)

/-- The full equivalence when the joint legality event is measurable. -/
theorem ae_joint_iff_seed_forall (nu : Measure Seed) (Legal : Seed × B → Prop)
    (hLegal : MeasurableSet {pair | Legal pair}) :
    (∀ᵐ pair ∂nu.prod (finiteUniformLaw B), Legal pair) ↔
      ∀ᵐ seed ∂nu, ∀ bank, Legal (seed, bank) := by
  rw [Measure.ae_prod_iff_ae_ae hLegal]
  apply Filter.eventually_congr
  exact Filter.Eventually.of_forall
    (fun seed => ae_finiteUniformLaw_iff B (fun bank => Legal (seed, bank)))

/-- A.e.-seed finite-bank lower bounds imply a joint-product lower without
requiring finite expected loss. This is the generic actual-law wrapper. -/
theorem joint_lower_of_ae_seed (nu : Measure Seed) [IsProbabilityMeasure nu]
    (loss : Seed × B → ℝ) (hloss : Measurable loss)
    (h0 : ∀ pair, 0 ≤ loss pair) (c : ℝ) (hc : 0 ≤ c)
    (hlower : ∀ᵐ seed ∂nu, c ≤ Gate148.FiniteRisk.uniformMean (fun bank => loss (seed, bank))) :
    ENNReal.ofReal c ≤ ∫⁻ pair, ENNReal.ofReal (loss pair) ∂nu.prod (finiteUniformLaw B) := by
  rw [joint_real_loss_eq_randomizedLoss nu loss hloss h0]
  unfold randomizedLoss
  have hcast : ∀ᵐ seed ∂nu, ENNReal.ofReal c ≤
      ENNReal.ofReal (Gate148.FiniteRisk.uniformMean (fun bank => loss (seed, bank))) :=
    hlower.mono (fun seed hs => ENNReal.ofReal_le_ofReal hs)
  calc
    ENNReal.ofReal c = ∫⁻ _seed : Seed, ENNReal.ofReal c ∂nu := by simp
    _ ≤ _ := lintegral_mono_ae hcast
end JointLaw

/-- Concrete bank specialization for the policy-model interface. -/
theorem joint_bank_expectation {Seed : Type*} [MeasurableSpace Seed]
    (n K : ℕ) (nu : Measure Seed) (f : Seed × Bank n K → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ pair, f pair ∂nu.prod (bankLaw n K)) =
      ∫⁻ seed, uniformENNMean (fun bank => f (seed, bank)) ∂nu :=
  joint_lintegral_eq_uniform nu f hf

theorem ae_seed_forall_bank_of_ae_joint {Seed : Type*} [MeasurableSpace Seed]
    (n K : ℕ) (nu : Measure Seed) (Legal : Seed × Bank n K → Prop)
    (hlegal : ∀ᵐ pair ∂nu.prod (bankLaw n K), Legal pair) :
    ∀ᵐ seed ∂nu, ∀ bank, Legal (seed, bank) :=
  ae_seed_forall_of_ae_joint nu Legal hlegal

#print axioms finiteUniformLaw_probability
#print axioms finiteUniformLaw_singleton_pos
#print axioms lintegral_finiteUniformLaw
#print axioms bankLaw_probability
#print axioms measurable_from_seed_sections
#print axioms joint_real_loss_eq_randomizedLoss
#print axioms ae_seed_forall_of_ae_joint
#print axioms ae_joint_iff_seed_forall
#print axioms joint_lower_of_ae_seed
#print axioms joint_bank_expectation
#print axioms ae_seed_forall_bank_of_ae_joint

end
end Gate149.JointBankLaw
