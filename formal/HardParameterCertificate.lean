import HardParameters

/-!
Gate148. Numerical certificate for the ACTUAL Gate134 parameter choices.
This companion imports, but does not modify, accepted HardParameters.
It proves the remaining coefficient and cubic-budget conversions and then
the explicit scalar upper bound < 1/128. No expectation, deficit, event,
trajectory, output or final risk is postulated. Connecting the scalar
certificate to the actual bank-only estimate is a separate assembly step.
Root alone compiles this source.
-/
namespace Gate148.HardParameterCertificate
noncomputable section
open Gate148.HardParameters

/-- Exact useful coefficient estimate, without fractional powers of mu. -/
theorem H_sq_div_b_le {mu ell a : ℝ} (hm : 0 < mu) (he : 0 < ell)
    (ha : 0 < a) (hid : a ^ 2 * ell = mu) (hsmall : a ^ 2 ≤ theta) :
    H mu ell a ^ 2 / b ell a ≤ 7 * mu * a := by
  obtain ⟨hb, hh, hupper, _⟩ := coefficient_identities hm he ha hid hsmall
  have hmu2 : 4 * (1 + a ^ 2) * b ell a * mu * a = mu ^ 2 := by
    rw [← hid]
    unfold b beta
    field_simp <;> ring
  have hsq : H mu ell a ^ 2 ≤ (5 * mu / 4) ^ 2 :=
    (sq_le_sq₀ hh.le (by positivity)).2 hupper
  have hc : (25 : ℝ) / 4 * (1 + a ^ 2) ≤ 7 := by
    norm_num [theta] at hsmall
    linarith
  have hp := mul_le_mul_of_nonneg_right hc (show 0 ≤ b ell a * mu * a by positivity)
  have htotal : H mu ell a ^ 2 ≤ 7 * mu * a * b ell a := by
    nlinarith [hmu2]
  exact (div_le_iff₀ hb).2 htotal

/-- Converting the exact cubic budget to its square-root scale. This is a
pure real lemma; the actual construction discharges its hypotheses below. -/
theorem cubic_scale_le {mu ell a D sigma n K : ℝ}
    (hm : 0 < mu) (he : 0 < ell) (ha : 0 < a)
    (hD : 0 < D) (hs : 0 < sigma) (hn : 0 ≤ n) (hK : 0 ≤ K)
    (hid : a ^ 2 * ell = mu)
    (hbudget : mu ^ 3 * (n * K ^ 2 * D ^ 2) ≤ theta ^ 3 * ell * sigma ^ 2) :
    mu * a * D * K * Real.sqrt n / sigma ≤ theta / 128 := by
  let y : ℝ := mu * a * D * K * Real.sqrt n
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have hyid : ell * y ^ 2 = mu ^ 3 * (n * K ^ 2 * D ^ 2) := by
    calc
      ell * y ^ 2 = (a ^ 2 * ell) * mu ^ 2 * D ^ 2 * K ^ 2 * Real.sqrt n ^ 2 := by
        dsimp [y]
        ring
      _ = mu ^ 3 * (n * K ^ 2 * D ^ 2) := by
        rw [hid, Real.sq_sqrt hn]
        ring
  have hsquare : y ^ 2 ≤ theta ^ 3 * sigma ^ 2 := by
    apply le_of_mul_le_mul_left (a := ell)
    · rw [hyid]
      nlinarith [hbudget]
    · exact he
  have ht : theta ^ 3 = (theta / 128) ^ 2 := by norm_num [theta]
  rw [ht, ← mul_pow] at hsquare
  have hbound : y ≤ theta / 128 * sigma :=
    (sq_le_sq₀ hy0 (by have := theta_pos; positivity)).mp hsquare
  apply (div_le_iff₀ hs).2
  exact hbound

/-- The actual cubic budget yields the required small dimension/epoch scale. -/
theorem actual_cubic_scale_le {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    mu n K L D sigma * a n K L D sigma * D * (K : ℝ) * Real.sqrt (n : ℝ) / sigma ≤
      theta / 128 := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  exact cubic_scale_le (mu_pos hn hK hL hD hs) (ell_pos hn hK hL hD hs)
    (a_pos hn hK hL hD hs) hD hs hn0.le hK0.le
    (a_sq_mul_ell hn hK hL hD hs) (cubic_budget hn hK hL hD hs)

theorem actual_H_over_L_le {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    H (mu n K L D sigma) (ell n K L D sigma) (a n K L D sigma) / L ≤
      (5 : ℝ) / 4 * theta := by
  have he := ell_pos hn hK hL hD hs
  have hm := mu_pos hn hK hL hD hs
  have ha := a_pos hn hK hL hD hs
  obtain ⟨_, _, hu, _⟩ := coefficient_identities hm he ha
    (a_sq_mul_ell hn hK hL hD hs) (a_sq_le_theta hn hK hL hD hs)
  have hmL : mu n K L D sigma ≤ theta * L :=
    (mu_le_ell n K L D sigma).trans
      (mul_le_mul_of_nonneg_left (ell_le_L n K L D sigma) theta_pos.le)
  apply (div_le_iff₀ hL).2
  nlinarith

/-- Actual coefficient plus actual cubic cap. No final deficit estimate is an input. -/
theorem actual_charge_scale_le {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    let e := ell n K L D sigma
    let m := mu n K L D sigma
    let aa := a n K L D sigma
    H m e aa ^ 2 * D * (K : ℝ) * Real.sqrt (n : ℝ) / (sigma * b e aa) ≤
      7 * (theta / 128) := by
  dsimp only
  have he := ell_pos hn hK hL hD hs
  have hm := mu_pos hn hK hL hD hs
  have ha := a_pos hn hK hL hD hs
  have hid := a_sq_mul_ell hn hK hL hD hs
  have hsmall := a_sq_le_theta hn hK hL hD hs
  obtain ⟨hb, hh, _, _⟩ := coefficient_identities hm he ha hid hsmall
  have hr := H_sq_div_b_le hm he ha hid hsmall
  have hscale := actual_cubic_scale_le hn hK hL hD hs
  have hf : 0 ≤ D * (K : ℝ) * Real.sqrt (n : ℝ) / sigma := by positivity
  have hp := mul_le_mul_of_nonneg_right hr hf
  have hidleft :
      (H (mu n K L D sigma) (ell n K L D sigma) (a n K L D sigma) ^ 2 /
        b (ell n K L D sigma) (a n K L D sigma)) *
        (D * (K : ℝ) * Real.sqrt (n : ℝ) / sigma) =
      H (mu n K L D sigma) (ell n K L D sigma) (a n K L D sigma) ^ 2 *
        D * (K : ℝ) * Real.sqrt (n : ℝ) /
        (sigma * b (ell n K L D sigma) (a n K L D sigma)) := by
    field_simp
    <;> ring
  have hidright :
      (7 * mu n K L D sigma * a n K L D sigma) *
        (D * (K : ℝ) * Real.sqrt (n : ℝ) / sigma) =
      7 * (mu n K L D sigma * a n K L D sigma * D * (K : ℝ) *
        Real.sqrt (n : ℝ) / sigma) := by ring
  rw [hidleft, hidright] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left hscale (by norm_num))

/-- The complete tuned numerical expression in Gate134(18), for every
positive original parameter tuple. This is the scalar certificate to be
combined with the actual bank expectation, not an assumption on that bank. -/
theorem actual_deficit_numerical_bound {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    let e := ell n K L D sigma
    let m := mu n K L D sigma
    let aa := a n K L D sigma
    H m e aa / L + (53345 : ℝ) / 24 *
      (H m e aa ^ 2 * D * (K : ℝ) * Real.sqrt (n : ℝ) / (sigma * b e aa)) < 1 / 128 := by
  dsimp only
  have hfirst := actual_H_over_L_le hn hK hL hD hs
  have hsecond := actual_charge_scale_le hn hK hL hD hs
  dsimp only at hsecond
  have hc := mul_le_mul_of_nonneg_left hsecond
    (show (0 : ℝ) ≤ 53345 / 24 by norm_num)
  have hsum := add_le_add hfirst hc
  have hstrict :
      (5 : ℝ) / 4 * theta + (53345 : ℝ) / 24 * (7 * (theta / 128)) < 1 / 128 := by
    nlinarith [deficit_constant]
  exact hsum.trans_lt hstrict

#print axioms H_sq_div_b_le
#print axioms cubic_scale_le
#print axioms actual_cubic_scale_le
#print axioms actual_H_over_L_le
#print axioms actual_charge_scale_le
#print axioms actual_deficit_numerical_bound

end
end Gate148.HardParameterCertificate
