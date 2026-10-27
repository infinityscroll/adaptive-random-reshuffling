import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Gate148. Actual positive-parameter construction in Gate134 Sections 1,5,6,8.
All functions below are the specified parameter-only choices. No desired
risk, charge, or probability statement is assumed by the construction.
D=0 and sigma=0 are separate branches, not inputs to these divisions.
Root alone compiles this file. No compilation has been performed by its author.
-/
namespace Gate148.HardParameters
noncomputable section

/-- Exactly 2^(-14), written rationally for the finite constant checks. -/
def theta : ℝ := 1 / 16384

def ell (n K : ℕ) (L D sigma : ℝ) : ℝ :=
  min L (sigma * Real.sqrt (K : ℝ) / (D * Real.sqrt (n : ℝ)))

def linearCap (n K : ℕ) (D sigma : ℝ) : ℝ :=
  sigma / (D * Real.sqrt ((n : ℝ) * (K : ℝ)))

def cubicCap (n K : ℕ) (ell D sigma : ℝ) : ℝ :=
  (ell * sigma ^ 2 / ((n : ℝ) * (K : ℝ) ^ 2 * D ^ 2)) ^ ((3 : ℝ)⁻¹)

def mu (n K : ℕ) (L D sigma : ℝ) : ℝ :=
  theta * min (ell n K L D sigma)
    (min (linearCap n K D sigma) (cubicCap n K (ell n K L D sigma) D sigma))

def a (n K : ℕ) (L D sigma : ℝ) : ℝ :=
  Real.sqrt (mu n K L D sigma / ell n K L D sigma)

def beta (ell a : ℝ) : ℝ := ell / (4 * (1 + a ^ 2))
def b (ell a : ℝ) : ℝ := beta ell a * a
def H (mu ell a : ℝ) : ℝ := mu + b ell a * a

def b0 (mu ell a D sigma r : ℝ) : ℝ :=
  b ell a - 2 * H mu ell a * D * ell * Real.sqrt r / sigma

def stepThreshold (mu ell a D sigma r : ℝ) : ℝ :=
  120 * H mu ell a * D / (b0 mu ell a D sigma r * sigma)

def radiusThreshold (mu ell a D sigma r : ℝ) : ℝ :=
  130 * H mu ell a * D / b0 mu ell a D sigma r

@[simp] theorem theta_eq_pow : theta = (2 : ℝ) ^ (-14 : ℤ) := by
  norm_num [theta]

theorem theta_pos : 0 < theta := by norm_num [theta]
theorem theta_le_quarter : theta ≤ (1 : ℝ) / 4 := by norm_num [theta]
theorem theta_lt_one : theta < 1 := by norm_num [theta]

theorem cast_pos {n K : ℕ} (hn : 2 ≤ n) (hK : 1 ≤ K) :
    (0 : ℝ) < n ∧ (0 : ℝ) < K := by
  constructor
  · exact_mod_cast (show 0 < n by omega)
  · exact_mod_cast (show 0 < K by omega)

theorem ell_pos {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    0 < ell n K L D sigma := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  unfold ell
  exact lt_min hL (div_pos (mul_pos hs (Real.sqrt_pos.2 hK0))
    (mul_pos hD (Real.sqrt_pos.2 hn0)))

theorem ell_le_L (n K : ℕ) (L D sigma : ℝ) : ell n K L D sigma ≤ L :=
  min_le_left _ _

theorem ell_le_scale (n K : ℕ) (L D sigma : ℝ) :
    ell n K L D sigma ≤ sigma * Real.sqrt (K : ℝ) / (D * Real.sqrt (n : ℝ)) :=
  min_le_right _ _

theorem linearCap_pos {n K : ℕ} {D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hD : 0 < D) (hs : 0 < sigma) :
    0 < linearCap n K D sigma := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  exact div_pos hs (mul_pos hD (Real.sqrt_pos.2 (mul_pos hn0 hK0)))

theorem cubicCap_pos {n K : ℕ} {ell D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (he : 0 < ell) (hD : 0 < D) (hs : 0 < sigma) :
    0 < cubicCap n K ell D sigma := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  unfold cubicCap
  apply Real.rpow_pos_of_pos
  exact div_pos (mul_pos he (sq_pos_of_pos hs))
    (mul_pos (mul_pos hn0 (sq_pos_of_pos hK0)) (sq_pos_of_pos hD))

theorem cubicCap_cube {n K : ℕ} {ell D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (he : 0 < ell) (hD : 0 < D) (hs : 0 < sigma) :
    cubicCap n K ell D sigma ^ 3 = ell * sigma ^ 2 / ((n : ℝ) * (K : ℝ) ^ 2 * D ^ 2) := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  unfold cubicCap
  apply Real.rpow_inv_natCast_pow
  · positivity
  · norm_num

theorem mu_pos {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    0 < mu n K L D sigma := by
  have he := ell_pos hn hK hL hD hs
  exact mul_pos theta_pos (lt_min he
    (lt_min (linearCap_pos hn hK hD hs) (cubicCap_pos hn hK he hD hs)))

theorem mu_le_ell (n K : ℕ) (L D sigma : ℝ) :
    mu n K L D sigma ≤ theta * ell n K L D sigma := by
  exact mul_le_mul_of_nonneg_left (min_le_left _ _) theta_pos.le

theorem mu_le_linear (n K : ℕ) (L D sigma : ℝ) :
    mu n K L D sigma ≤ theta * linearCap n K D sigma := by
  exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) theta_pos.le

theorem mu_le_cubic (n K : ℕ) (L D sigma : ℝ) :
    mu n K L D sigma ≤ theta * cubicCap n K (ell n K L D sigma) D sigma := by
  exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) theta_pos.le

theorem mu_le_ell_quarter {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    mu n K L D sigma ≤ ell n K L D sigma / 4 := by
  have he := (ell_pos hn hK hL hD hs).le
  have ht := mul_le_mul_of_nonneg_right theta_le_quarter he
  have hm := mu_le_ell n K L D sigma
  nlinarith

/-- The auxiliary scale is admissible for the ORIGINAL input parameters. -/
theorem ell_regime {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    ell n K L D sigma ^ 2 * D ^ 2 * (n : ℝ) ≤ sigma ^ 2 * (K : ℝ) := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have he := ell_pos hn hK hL hD hs
  have hsn := Real.sq_sqrt hn0.le
  have hsk := Real.sq_sqrt hK0.le
  have hc := (le_div_iff₀ (mul_pos hD (Real.sqrt_pos.2 hn0))).mp
    (ell_le_scale n K L D sigma)
  have hsq := mul_self_le_mul_self
    (show 0 ≤ ell n K L D sigma * (D * Real.sqrt (n : ℝ)) by positivity) hc
  have hsq2 : (ell n K L D sigma * (D * Real.sqrt (n : ℝ))) ^ 2 ≤
      (sigma * Real.sqrt (K : ℝ)) ^ 2 := by nlinarith [hsq]
  simpa only [mul_pow, hsn, hsk, mul_assoc] using hsq2

theorem a_pos {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    0 < a n K L D sigma :=
  Real.sqrt_pos.2 (div_pos (mu_pos hn hK hL hD hs) (ell_pos hn hK hL hD hs))

theorem a_sq_mul_ell {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    a n K L D sigma ^ 2 * ell n K L D sigma = mu n K L D sigma := by
  have he := ell_pos hn hK hL hD hs
  have hm := mu_pos hn hK hL hD hs
  unfold a
  rw [Real.sq_sqrt (div_nonneg hm.le he.le)]
  exact div_mul_cancel₀ _ he.ne'

theorem a_sq_le_theta {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    a n K L D sigma ^ 2 ≤ theta := by
  have he := ell_pos hn hK hL hD hs
  have hid := a_sq_mul_ell hn hK hL hD hs
  have hm := mu_le_ell n K L D sigma
  nlinarith

/-- Product of the two ACTUAL linear caps, not an extra parameter hypothesis. -/
theorem mixed_cap {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    mu n K L D sigma * ell n K L D sigma * D ^ 2 * (n : ℝ) ≤ theta * sigma ^ 2 := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have he := ell_pos hn hK hL hD hs
  have hm := mu_pos hn hK hL hD hs
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsk : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.2 hK0
  have hprod : Real.sqrt ((n : ℝ) * (K : ℝ)) =
      Real.sqrt (n : ℝ) * Real.sqrt (K : ℝ) := Real.sqrt_mul hn0.le _
  have h1 := (le_div_iff₀ (mul_pos hD hsn)).mp (ell_le_scale n K L D sigma)
  have h2 : mu n K L D sigma * (D * Real.sqrt ((n : ℝ) * (K : ℝ))) ≤ theta * sigma := by
    have hx := mu_le_linear n K L D sigma
    unfold linearCap at hx
    have hden : 0 < D * Real.sqrt ((n : ℝ) * (K : ℝ)) :=
      mul_pos hD (Real.sqrt_pos.2 (mul_pos hn0 hK0))
    have hz := mul_le_mul_of_nonneg_right hx hden.le
    simpa only [mul_assoc, div_mul_cancel₀ sigma hden.ne'] using hz
  rw [hprod] at h2
  have hp := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hid : (ell n K L D sigma * (D * Real.sqrt (n : ℝ))) *
      (mu n K L D sigma * (D * (Real.sqrt (n : ℝ) * Real.sqrt (K : ℝ)))) =
      (mu n K L D sigma * ell n K L D sigma * D ^ 2 * (n : ℝ)) * Real.sqrt (K : ℝ) := by
    calc
      _ = (mu n K L D sigma * ell n K L D sigma * D ^ 2 * Real.sqrt (n : ℝ) ^ 2) *
          Real.sqrt (K : ℝ) := by ring
      _ = _ := by rw [Real.sq_sqrt hn0.le]
  have hrhs : (sigma * Real.sqrt (K : ℝ)) * (theta * sigma) =
      (theta * sigma ^ 2) * Real.sqrt (K : ℝ) := by ring
  rw [hid, hrhs] at hp
  exact le_of_mul_le_mul_right hp hsk

theorem cubic_budget {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    mu n K L D sigma ^ 3 * ((n : ℝ) * (K : ℝ) ^ 2 * D ^ 2) ≤
      theta ^ 3 * ell n K L D sigma * sigma ^ 2 := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have he := ell_pos hn hK hL hD hs
  have hm := mu_pos hn hK hL hD hs
  have hcube := cubicCap_cube hn hK he hD hs
  have hh := pow_le_pow_left₀ hm.le (mu_le_cubic n K L D sigma) 3
  rw [mul_pow, hcube] at hh
  have hd : 0 < (n : ℝ) * (K : ℝ) ^ 2 * D ^ 2 := by positivity
  have h := mul_le_mul_of_nonneg_right hh hd.le
  have cancel : (theta ^ 3 *
      (ell n K L D sigma * sigma ^ 2 / ((n : ℝ) * (K : ℝ) ^ 2 * D ^ 2))) *
      ((n : ℝ) * (K : ℝ) ^ 2 * D ^ 2) = theta ^ 3 * ell n K L D sigma * sigma ^ 2 := by
    rw [mul_assoc, div_mul_cancel₀ _ hd.ne']
    ring
  rwa [cancel] at h

/-- Small coefficient identities used to instantiate the paid-reset thresholds. -/
theorem coefficient_identities {mu ell a : ℝ} (hm : 0 < mu) (he : 0 < ell)
    (ha : 0 < a) (hid : a ^ 2 * ell = mu) (hsmall : a ^ 2 ≤ theta) :
    0 < b ell a ∧ 0 < H mu ell a ∧
    H mu ell a ≤ 5 * mu / 4 ∧
    H mu ell a = b ell a * (a * (5 + 4 * a ^ 2)) := by
  have hd : 0 < 4 * (1 + a ^ 2) := by positivity
  have hb : 0 < b ell a := mul_pos (div_pos he hd) ha
  have hh : 0 < H mu ell a := by unfold H; positivity
  have hbase : beta ell a * a ^ 2 ≤ mu / 4 := by
    unfold beta
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg hm.le (sq_nonneg a)]
  have hupper : H mu ell a ≤ 5 * mu / 4 := by
    unfold H b
    nlinarith
  refine ⟨hb, hh, hupper, ?_⟩
  rw [← hid]
  unfold H b beta
  field_simp <;> ring


/-- The charge loss is derived from the two parameter caps and 2r <= n.
No final b0 bound is included among the hypotheses. -/
theorem coefficient_charge {mu ell a D sigma n r : ℝ}
    (hm : 0 < mu) (he : 0 < ell) (ha : 0 < a) (hD : 0 < D) (hs : 0 < sigma)
    (hr : 0 ≤ r) (hrn : 2 * r ≤ n)
    (hid : a ^ 2 * ell = mu) (hsmall : a ^ 2 ≤ theta)
    (hcap : mu * ell * D ^ 2 * n ≤ theta * sigma ^ 2) :
    15 * b ell a / 16 ≤ b0 mu ell a D sigma r ∧
    b0 mu ell a D sigma r ≤ b ell a ∧ 0 < b0 mu ell a D sigma r := by
  obtain ⟨hb, hh, hupper, hidentity⟩ := coefficient_identities hm he ha hid hsmall
  let X : ℝ := a * D * ell * Real.sqrt r
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hXid : X ^ 2 = mu * ell * D ^ 2 * r := by
    calc
      X ^ 2 = (a ^ 2 * ell) * ell * D ^ 2 * Real.sqrt r ^ 2 := by dsimp [X]; ring
      _ = mu * ell * D ^ 2 * r := by rw [hid, Real.sq_sqrt hr]
  have hmul := mul_le_mul_of_nonneg_left hrn
    (show 0 ≤ mu * ell * D ^ 2 by positivity)
  have hXsq : 2 * X ^ 2 ≤ theta * sigma ^ 2 := by
    rw [hXid]
    nlinarith
  have hXbound : X ≤ sigma / 168 := by
    by_contra hx
    have hlt : sigma / 168 < X := lt_of_not_ge hx
    have hp := mul_pos (sub_pos.mpr hlt) (show 0 < X + sigma / 168 by positivity)
    norm_num [theta] at hXsq
    nlinarith
  have hcoef : 2 * (5 + 4 * a ^ 2) ≤ (21 : ℝ) / 2 := by
    norm_num [theta] at hsmall
    linarith
  have hv : 2 * (5 + 4 * a ^ 2) * X ≤ sigma / 16 := by
    calc
      _ ≤ ((21 : ℝ) / 2) * (sigma / 168) :=
        mul_le_mul hcoef hXbound hX (by norm_num)
      _ = _ := by ring
  have hnum : 2 * H mu ell a * D * ell * Real.sqrt r =
      b ell a * (2 * (5 + 4 * a ^ 2) * X) := by
    rw [hidentity]
    dsimp [X]
    ring
  have hcharge : 2 * H mu ell a * D * ell * Real.sqrt r / sigma ≤ b ell a / 16 := by
    apply (div_le_iff₀ hs).2
    rw [hnum]
    have ht := mul_le_mul_of_nonneg_left hv hb.le
    nlinarith
  have hcharge0 : 0 ≤ 2 * H mu ell a * D * ell * Real.sqrt r / sigma := by positivity
  unfold b0
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- The actual constructed b0 and thresholds satisfy the interval-chain inputs. -/
theorem actual_thresholds {n K : ℕ} {L D sigma r : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma)
    (hr : 0 ≤ r) (hrn : 2 * r ≤ (n : ℝ)) :
    let e := ell n K L D sigma
    let m := mu n K L D sigma
    let aa := a n K L D sigma
    15 * b e aa / 16 ≤ b0 m e aa D sigma r ∧ b0 m e aa D sigma r ≤ b e aa ∧
    0 < b0 m e aa D sigma r ∧ 0 < stepThreshold m e aa D sigma r ∧
    0 < radiusThreshold m e aa D sigma r ∧
    radiusThreshold m e aa D sigma r - sigma * stepThreshold m e aa D sigma r =
      10 * H m e aa * D / b0 m e aa D sigma r := by
  dsimp only
  have hm := mu_pos hn hK hL hD hs
  have he := ell_pos hn hK hL hD hs
  have ha := a_pos hn hK hL hD hs
  have hid := a_sq_mul_ell hn hK hL hD hs
  have hsmall := a_sq_le_theta hn hK hL hD hs
  have hcap := mixed_cap hn hK hL hD hs
  obtain ⟨hlower, hupper, hb0⟩ := coefficient_charge hm he ha hD hs hr hrn hid hsmall hcap
  obtain ⟨hb, hh, _, _⟩ := coefficient_identities hm he ha hid hsmall
  refine ⟨hlower, hupper, hb0, ?_, ?_, ?_⟩
  · unfold stepThreshold
    positivity
  · unfold radiusThreshold
    positivity
  · unfold radiusThreshold stepThreshold
    field_simp <;> ring

/-- A convenient exact finite arithmetic check for the eventual expectation
bound. It contains no probabilistic hypothesis and no risk conclusion. -/
theorem deficit_constant :
    (5 : ℝ) / 4 * theta + 7 * (theta / 128) * (53345 / 24) < 1 / 128 := by
  norm_num [theta]

#print axioms theta_eq_pow
#print axioms ell_pos
#print axioms mu_pos
#print axioms mu_le_ell_quarter
#print axioms ell_regime
#print axioms a_sq_mul_ell
#print axioms a_sq_le_theta
#print axioms mixed_cap
#print axioms cubic_budget
#print axioms coefficient_identities
#print axioms coefficient_charge
#print axioms actual_thresholds
#print axioms deficit_constant

end
end Gate148.HardParameters
