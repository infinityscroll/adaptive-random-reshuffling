import HardParameterCertificate

/-!
Gate148. Exact threshold and bank-envelope arithmetic for the unchanged
Gate134 construction. The generic algebra lemma is discharged by the
actual n,K,L,D,sigma parameters below. No probability law, expectation,
retention event or final risk is supplied as a premise. Root alone compiles.
-/
namespace Gate148.TunedThresholds
noncomputable section
open Gate148.HardParameters Gate148.HardParameterCertificate

/-- The actual denominator lower bound controls the actual radius threshold. -/
theorem radius_le {C b b0 : ℝ} (hC : 0 ≤ C) (hb : 0 < b)
    (hlower : 15 * b / 16 ≤ b0) :
    130 * C / b0 ≤ 2080 * C / (15 * b) := by
  have hd : 0 < 15 * b / 16 := by positivity
  have h := div_le_div_of_nonneg_left (show 0 ≤ 130 * C by positivity) hd hlower
  calc
    130 * C / b0 ≤ 130 * C / (15 * b / 16) := h
    _ = 2080 * C / (15 * b) := by field_simp; ring

/-- Algebra of the EXACT geometric and endpoint terms. The clock bounds
will be proved from n>=2,K>=1 and 0<=r<=n for the actual parameters. -/
theorem mean_bound {L D sigma C H b A n K r : ℝ}
    (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) (hb : 0 < b)
    (hC : 0 ≤ C) (hCD : C = H * D)
    (hA : A ≤ 2080 * C / (15 * b))
    (hclock : 1 ≤ K * Real.sqrt n) (hrclock : Real.sqrt r ≤ K * Real.sqrt n) :
    C / L + 16 * C * A * K * Real.sqrt n / sigma +
      4 * C ^ 2 * Real.sqrt r / (sigma * b) + C ^ 2 / (24 * sigma * b) ≤
    D * (H / L + (53345 : ℝ) / 24 *
      (H ^ 2 * D * K * Real.sqrt n / (sigma * b))) := by
  let X : ℝ := K * Real.sqrt n
  let t : ℝ := C ^ 2 * X / (sigma * b)
  have hX : 0 ≤ X := by dsimp [X]; linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hgeom : 16 * C * A * K * Real.sqrt n / sigma ≤ (33280 : ℝ) / 15 * t := by
    have hp := mul_le_mul_of_nonneg_left hA (show 0 ≤ 16 * C * X / sigma by positivity)
    have hleft : (16 * C * X / sigma) * A =
        16 * C * A * K * Real.sqrt n / sigma := by dsimp [X]; ring
    have hright : (16 * C * X / sigma) * (2080 * C / (15 * b)) =
        (33280 : ℝ) / 15 * t := by
      dsimp [t]
      field_simp
      <;> ring
    rwa [hleft, hright] at hp
  have hstart : 4 * C ^ 2 * Real.sqrt r / (sigma * b) ≤ 4 * t := by
    have hp := mul_le_mul_of_nonneg_left hrclock
      (show 0 ≤ 4 * C ^ 2 / (sigma * b) by positivity)
    dsimp [t, X]
    convert hp using 1 <;> ring
  have hend : C ^ 2 / (24 * sigma * b) ≤ t / 24 := by
    have hp := mul_le_mul_of_nonneg_left hclock
      (show 0 ≤ C ^ 2 / (24 * sigma * b) by positivity)
    dsimp [t, X]
    convert hp using 1 <;> ring
  have hsum : C / L + 16 * C * A * K * Real.sqrt n / sigma +
      4 * C ^ 2 * Real.sqrt r / (sigma * b) + C ^ 2 / (24 * sigma * b) ≤
      C / L + (53345 : ℝ) / 24 * t := by
    linarith
  have hid : C / L + (53345 : ℝ) / 24 * t =
      D * (H / L + (53345 : ℝ) / 24 *
        (H ^ 2 * D * K * Real.sqrt n / (sigma * b))) := by
    dsimp [t, X]
    rw [hCD]
    ring
  exact hsum.trans_eq hid

/-- The actual square-root clock comparisons, with no n=2 exception. -/
theorem actual_clock_bounds {n K : ℕ} {r : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hr : 0 ≤ r) (hrn : 2 * r ≤ (n : ℝ)) :
    1 ≤ (K : ℝ) * Real.sqrt (n : ℝ) ∧
    Real.sqrt r ≤ (K : ℝ) * Real.sqrt (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hk1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hsqrt1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.2 hn1
  have hsqrtK : Real.sqrt (n : ℝ) ≤ (K : ℝ) * Real.sqrt (n : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hk1 (Real.sqrt_nonneg (n : ℝ))
  have hrle : r ≤ (n : ℝ) := by linarith
  exact ⟨hsqrt1.trans hsqrtK, (Real.sqrt_le_sqrt hrle).trans hsqrtK⟩

/-- Exact threshold identity and actual radius upper bound. -/
theorem actual_threshold_bounds {n K : ℕ} {L D sigma r : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma)
    (hr : 0 ≤ r) (hrn : 2 * r ≤ (n : ℝ)) :
    let e := ell n K L D sigma
    let m := mu n K L D sigma
    let aa := a n K L D sigma
    let C := H m e aa * D
    radiusThreshold m e aa D sigma r = sigma * stepThreshold m e aa D sigma r +
      10 * C / b0 m e aa D sigma r ∧
    radiusThreshold m e aa D sigma r ≤ 2080 * C / (15 * b e aa) := by
  dsimp only
  have he := ell_pos hn hK hL hD hs
  have hm := mu_pos hn hK hL hD hs
  have ha := a_pos hn hK hL hD hs
  obtain ⟨hb, hh, _, _⟩ := coefficient_identities hm he ha
    (a_sq_mul_ell hn hK hL hD hs) (a_sq_le_theta hn hK hL hD hs)
  have hth := actual_thresholds hn hK hL hD hs hr hrn
  dsimp only at hth
  obtain ⟨hb0, _, _, _, _, hidentity⟩ := hth
  constructor
  · simp only [mul_assoc] at hidentity
    linarith
  · have hrad := radius_le (C := H (mu n K L D sigma) (ell n K L D sigma)
      (a n K L D sigma) * D) (by positivity) hb hb0
    simpa only [radiusThreshold, mul_assoc] using hrad

/-- Exact actual envelope domination and strict tuned certificate.
For an actual block partition, r is instantiated with its real block count;
its established 2r<=n bound discharges the only block-count premise. -/
theorem actual_bank_mean_certificate {n K : ℕ} {L D sigma r : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma)
    (hr : 0 ≤ r) (hrn : 2 * r ≤ (n : ℝ)) :
    let e := ell n K L D sigma
    let m := mu n K L D sigma
    let aa := a n K L D sigma
    let C := H m e aa * D
    let A := radiusThreshold m e aa D sigma r
    let raw := C / L + 16 * C * A * (K : ℝ) * Real.sqrt (n : ℝ) / sigma +
      4 * C ^ 2 * Real.sqrt r / (sigma * b e aa) + C ^ 2 / (24 * sigma * b e aa)
    raw ≤ D * (H m e aa / L + (53345 : ℝ) / 24 *
      (H m e aa ^ 2 * D * (K : ℝ) * Real.sqrt (n : ℝ) / (sigma * b e aa))) ∧
    raw < D / 128 := by
  dsimp only
  have he := ell_pos hn hK hL hD hs
  have hm := mu_pos hn hK hL hD hs
  have ha := a_pos hn hK hL hD hs
  obtain ⟨hb, hh, _, _⟩ := coefficient_identities hm he ha
    (a_sq_mul_ell hn hK hL hD hs) (a_sq_le_theta hn hK hL hD hs)
  have hth := actual_threshold_bounds hn hK hL hD hs hr hrn
  dsimp only at hth
  obtain ⟨_, hA⟩ := hth
  obtain ⟨hclock, hrclock⟩ := actual_clock_bounds hn hK hr hrn
  have hmean := mean_bound hL hD hs hb
    (show 0 ≤ H (mu n K L D sigma) (ell n K L D sigma) (a n K L D sigma) * D by positivity)
    rfl hA hclock hrclock
  have hnum := actual_deficit_numerical_bound hn hK hL hD hs
  dsimp only at hnum
  refine ⟨hmean, hmean.trans_lt ?_⟩
  have hmul := mul_lt_mul_of_pos_left hnum hD
  simpa only [mul_one_div] using hmul

#print axioms radius_le
#print axioms mean_bound
#print axioms actual_clock_bounds
#print axioms actual_threshold_bounds
#print axioms actual_bank_mean_certificate

end
end Gate148.TunedThresholds
