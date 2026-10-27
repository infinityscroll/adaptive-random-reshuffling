import ActualTrim
import ActualInstance

/-!
Gate148: actual slow retention and actual vector-output objective lower.
The pointwise inequalities are derived from the accepted slowNext/max
formula. The final good-bank theorem uses ActualTrim's same-bank interval
certificate. No desired retention, objective lower, or interval cap is
assumed in that final theorem. Threshold scalars remain explicit upstream
parameter inputs. Root alone compiles this source.
-/
namespace Gate148.ActualRetention
noncomputable section
open scoped BigOperators InnerProductSpace
open Gate146.LabeledBlocks Gate146.FastSpaceOffsets
open Gate147 Gate148.ActualCharge

def b (ell a : ℝ) : ℝ := ConeTrajectory.beta ell a * a
def C (mu ell a D : ℝ) : ℝ := (mu + b ell a * a) * D

theorem b_pos (ell a : ℝ) (hell : 0 < ell) (ha : 0 < a) : 0 < b ell a := by
  unfold b ConeTrajectory.beta
  positivity

theorem C_pos (mu ell a D : ℝ) (hmu : 0 < mu) (hell : 0 < ell)
    (ha : 0 < a) (hD : 0 < D) : 0 < C mu ell a D := by
  have hb := b_pos ell a hell ha
  unfold C
  positivity

section Step
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Original 1/L cap, not the looser 1/ell cap. -/
theorem slowNext_retention_cap (L ell mu a q eta : ℝ) (v : V)
    (hell : 0 ≤ ell) (hmu : 0 ≤ mu) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (heta : 0 ≤ eta) (hetaL : eta ≤ 1 / L) :
    (1 - mu / L) * q ≤ ConeTrajectory.slowNext ell mu a q eta v := by
  have hs := ConeTrajectory.slowNext_retention ell mu a q eta v hell ha heta
  have hm : mu * eta ≤ mu / L := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hetaL hmu
  have hmq := mul_le_mul_of_nonneg_right hm hq
  nlinarith

/-- Actual max-residual formula gives the below-D deficit bound. -/
theorem slowNext_drop (ell mu a D q eta : ℝ) (v : V)
    (hell : 0 ≤ ell) (hmu : 0 ≤ mu) (ha : 0 ≤ a)
    (heta : 0 ≤ eta) (hqD : q ≤ D) :
    q - ConeTrajectory.slowNext ell mu a q eta v ≤
      eta * (C mu ell a D - b ell a * ‖v‖) := by
  have hbeta := (ConeTrajectory.beta_bounds ell a hell).1
  have hb : 0 ≤ b ell a := mul_nonneg hbeta ha
  have hH : 0 ≤ mu + b ell a * a := by positivity
  have hr : ‖v‖ - a * q ≤ ConeTrajectory.residual a q ‖v‖ :=
    le_max_right _ _
  have hrmul := mul_le_mul_of_nonneg_left hr (mul_nonneg hb heta)
  have hqmul := mul_le_mul_of_nonneg_left hqD (mul_nonneg heta hH)
  unfold ConeTrajectory.slowNext
  change q - ((1 - mu * eta) * q + b ell a * eta * ConeTrajectory.residual a q ‖v‖) ≤ _
  unfold C
  nlinarith
end Step

theorem mu_div_L_le_quarter (L ell mu : ℝ) (hL : 0 < L)
    (hcap : mu ≤ ell / 4) (hellL : ell ≤ L) : mu / L ≤ 1 / 4 := by
  apply (div_le_iff₀ hL).2
  linarith

theorem slowPath_update {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (t : ℕ) :
    slowPath P hn bank ell mu a sigma D eta (t + 1) =
      ConeTrajectory.slowNext ell mu a (slowPath P hn bank ell mu a sigma D eta t)
        (eta t) (fastPath P hn bank ell mu a sigma D eta t) := rfl

/-- Intermediate scalar interface. Its interval premise is discharged by
actual_all_interval_cap in the final good-bank theorem below. -/
theorem half_retention_with_interval_cap {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L ell mu a sigma D Z : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (hZ : 0 ≤ Z) (hZ4 : Z ≤ D / 4)
    (hinterval : ∀ s t, s ≤ t → t ≤ n * K →
      Gate144.EndpointTrim.intervalSum
        (fun i => eta i * (C mu ell a D - b ell a *
          ‖fastPath P hn bank ell mu a sigma D eta i‖)) s t ≤ Z) :
    ∀ t, t ≤ n * K → D / 2 ≤ slowPath P hn bank ell mu a sigma D eta t := by
  refine Gate144.EndpointTrim.half_retention_from_interval_cap
    (slowPath P hn bank ell mu a sigma D eta)
    (fun i => eta i * (C mu ell a D - b ell a *
      ‖fastPath P hn bank ell mu a sigma D eta i‖))
    (n * K) D (mu / L) Z hD.le (div_nonneg hmu.le hL.le)
    (mu_div_L_le_quarter L ell mu hL hcap hellL) hZ hZ4 rfl ?_ ?_ hinterval
  · intro i hi
    have hstate := actual_state_bounds P hn bank L ell mu a sigma D eta
      hL hell hellL hcap ha.le hsigma.le hD heta hetaL i (le_of_lt hi)
    rw [slowPath_update]
    exact slowNext_retention_cap L ell mu a _ _ _ hell.le hmu.le ha.le
      hstate.1.le (heta i hi).le (hetaL i hi)
  · intro i hi hq
    rw [slowPath_update]
    exact slowNext_drop ell mu a D _ _ _ hell.le hmu.le ha.le (heta i hi).le hq

def actualState {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta : ℕ → ℝ) (t : ℕ) : ActualInstance.Space P :=
  ConeFormula.point (slowPath P hn bank ell mu a sigma D eta t)
    (fastPath P hn bank ell mu a sigma D eta t)

/-- A scalar convex combination of ALL actual states, including state nK. -/
def output {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta weight : ℕ → ℝ) : ActualInstance.Space P :=
  ∑ i ∈ Finset.range (n * K + 1), weight i • actualState P hn bank ell mu a sigma D eta i

theorem fst_sum {n : ℕ} (P : Partition n) (s : Finset ℕ)
    (x : ℕ → ActualInstance.Space P) : (∑ i ∈ s, x i).fst = ∑ i ∈ s, (x i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, WithLp.add_fst, ih]

theorem output_fst {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta weight : ℕ → ℝ) :
    (output P hn bank ell mu a sigma D eta weight).fst =
      -(∑ i ∈ Finset.range (n * K + 1),
        weight i * slowPath P hn bank ell mu a sigma D eta i) := by
  unfold output
  rw [fst_sum]
  simp only [WithLp.smul_fst, actualState, ConeFormula.point, WithLp.toLp_fst,
    smul_eq_mul, mul_neg, Finset.sum_neg_distrib]

theorem output_loss_from_half_retention {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (bank : Fin K → Equiv.Perm (Fin n)) (ell mu a sigma D : ℝ)
    (eta weight : ℕ → ℝ) (hmu : 0 ≤ mu) (hell : 0 ≤ ell) (hD : 0 ≤ D)
    (hq : ∀ i, i ≤ n * K → D / 2 ≤ slowPath P hn bank ell mu a sigma D eta i)
    (hw : ∀ i, i ≤ n * K → 0 ≤ weight i)
    (hsum : ∑ i ∈ Finset.range (n * K + 1), weight i = 1) :
    mu * D ^ 2 / 8 ≤
      ActualInstance.mean P mu ell a sigma (output P hn bank ell mu a sigma D eta weight) -
        ActualInstance.mean P mu ell a sigma 0 := by
  have hqbar := Gate144.EndpointTrim.convex_output_lower
    (slowPath P hn bank ell mu a sigma D eta) weight (n * K) (D / 2) hq hw hsum
  have hslow := ActualObjective.Phi_slow_lower mu ell a hell
    (output P hn bank ell mu a sigma D eta weight)
  rw [output_fst, neg_sq] at hslow
  have hprod : 0 ≤
      ((∑ i ∈ Finset.range (n * K + 1), weight i * slowPath P hn bank ell mu a sigma D eta i) - D / 2) *
      ((∑ i ∈ Finset.range (n * K + 1), weight i * slowPath P hn bank ell mu a sigma D eta i) + D / 2) := by
    apply mul_nonneg <;> linarith
  have hmul := mul_nonneg hmu hprod
  rw [ActualInstance.mean_eq_Phi P hn2, ActualInstance.mean_zero P hn2, sub_zero]
  nlinarith

/-- Actual same-bank certificate, with the deficit coefficients derived
from slowNext. There is no assumed all-interval cap in this statement. -/
theorem good_bank_half_retention {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (bank : Fin K → Equiv.Perm (Fin n))
    (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (b0 h A : ℝ) (hb0 : 0 < b0)
    (hb0def : b0 = b ell a - 2 * C mu ell a D * ell * Real.sqrt (P.count : ℝ) / sigma)
    (hhdef : h = 120 * C mu ell a D / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * C mu ell a D / b0)
    (hgood : ActualTrim.certificate P bank L (C mu ell a D) (b ell a) sigma A ≤ D / 4) :
    ∀ t, t ≤ n * K → D / 2 ≤ slowPath P hn bank ell mu a sigma D eta t := by
  have hb := b_pos ell a hell ha
  have hC := C_pos mu ell a D hmu hell ha hD
  have hh : 0 < h := by rw [hhdef]; positivity
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  have hZ := ActualTrim.certificate_nonneg P bank L (C mu ell a D) (b ell a) sigma A
    hL hC.le hb hsigma hA
  have hinterval := ActualTrim.actual_all_interval_cap P hn hn2 bank
    L ell mu a sigma D eta hL hell hellL hmu hcap ha hsigma hD heta hetaL
    (C mu ell a D) (b ell a) b0 h A hC hb hb0 hb0def hhdef hAdef
  exact half_retention_with_interval_cap P hn bank L ell mu a sigma D
    (ActualTrim.certificate P bank L (C mu ell a D) (b ell a) sigma A) eta
    hL hell hellL hmu hcap ha hsigma hD heta hetaL hZ hgood hinterval

/-- Every scalar convex output of the ACTUAL states has the true mean-loss
lower on a good bank. The weights can be chosen after the entire path.
No expectation or action/bank/output independence is used here. -/
theorem good_bank_output_loss {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (bank : Fin K → Equiv.Perm (Fin n))
    (L ell mu a sigma D : ℝ) (eta weight : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (b0 h A : ℝ) (hb0 : 0 < b0)
    (hb0def : b0 = b ell a - 2 * C mu ell a D * ell * Real.sqrt (P.count : ℝ) / sigma)
    (hhdef : h = 120 * C mu ell a D / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * C mu ell a D / b0)
    (hgood : ActualTrim.certificate P bank L (C mu ell a D) (b ell a) sigma A ≤ D / 4)
    (hw : ∀ i, i ≤ n * K → 0 ≤ weight i)
    (hsum : ∑ i ∈ Finset.range (n * K + 1), weight i = 1) :
    mu * D ^ 2 / 8 ≤
      ActualInstance.mean P mu ell a sigma (output P hn bank ell mu a sigma D eta weight) -
        ActualInstance.mean P mu ell a sigma 0 := by
  have hq := good_bank_half_retention P hn hn2 bank L ell mu a sigma D eta
    hL hell hellL hmu hcap ha hsigma hD heta hetaL b0 h A hb0 hb0def hhdef hAdef hgood
  exact output_loss_from_half_retention P hn hn2 bank ell mu a sigma D eta weight
    hmu.le hell.le hD.le hq hw hsum

#print axioms slowNext_retention_cap
#print axioms slowNext_drop
#print axioms mu_div_L_le_quarter
#print axioms half_retention_with_interval_cap
#print axioms output_fst
#print axioms output_loss_from_half_retention
#print axioms good_bank_half_retention
#print axioms good_bank_output_loss
end
end Gate148.ActualRetention
