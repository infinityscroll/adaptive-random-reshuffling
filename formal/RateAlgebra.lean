import HardParameters

/-! Gate148: exact positive-parameter rate reduction for the unchanged
Gate134 construction. The auxiliary ell is eliminated, not fixed to a
favorable regime. These algebraic lemmas do not assert a risk theorem. -/
namespace Gate148.RateAlgebra
noncomputable section
open Gate148.HardParameters

theorem scale_algebra (D sigma x y : ℝ) (hD : D ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    sigma * y / (D * x) = y ^ 2 * (sigma / (D * (x * y))) := by
  field_simp
  <;> ring

theorem cube_algebra (D sigma x y : ℝ) (hD : D ≠ 0) (hx : x ≠ 0)
    (hy : y ≠ 0) :
    (sigma / (D * (x * y))) ^ 3 =
      (sigma * y / (D * x)) * sigma ^ 2 / (x ^ 2 * (y ^ 2) ^ 2 * D ^ 2) := by
  field_simp
  <;> ring

theorem scale_eq_K_linear {n K : ℕ} {D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hD : 0 < D) :
    sigma * Real.sqrt (K : ℝ) / (D * Real.sqrt (n : ℝ)) =
      (K : ℝ) * linearCap n K D sigma := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have h := scale_algebra D sigma (Real.sqrt (n : ℝ)) (Real.sqrt (K : ℝ))
    hD.ne' (Real.sqrt_pos.2 hn0).ne' (Real.sqrt_pos.2 hK0).ne'
  simpa only [Real.sq_sqrt hK0.le, linearCap, Real.sqrt_mul hn0.le] using h

theorem cubic_scale_eq_linear {n K : ℕ} {D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hD : 0 < D) (hs : 0 < sigma) :
    cubicCap n K (sigma * Real.sqrt (K : ℝ) / (D * Real.sqrt (n : ℝ))) D sigma =
      linearCap n K D sigma := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have hsn := Real.sqrt_pos.2 hn0
  have hsk := Real.sqrt_pos.2 hK0
  have he : 0 < sigma * Real.sqrt (K : ℝ) / (D * Real.sqrt (n : ℝ)) := by positivity
  apply (pow_left_inj₀ (cubicCap_pos hn hK he hD hs).le
    (linearCap_pos hn hK hD hs).le (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [cubicCap_cube hn hK he hD hs]
  have h := cube_algebra D sigma (Real.sqrt (n : ℝ)) (Real.sqrt (K : ℝ))
    hD.ne' hsn.ne' hsk.ne'
  simpa only [Real.sq_sqrt hn0.le, Real.sq_sqrt hK0.le,
    linearCap, Real.sqrt_mul hn0.le] using h.symm

theorem cubicCap_mono {n K : ℕ} {e f D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (he : 0 < e) (hef : e ≤ f)
    (hD : 0 < D) (hs : 0 < sigma) :
    cubicCap n K e D sigma ≤ cubicCap n K f D sigma := by
  have hf := he.trans_le hef
  apply (pow_le_pow_iff_left₀ (cubicCap_pos hn hK he hD hs).le
    (cubicCap_pos hn hK hf hD hs).le (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [cubicCap_cube hn hK he hD hs, cubicCap_cube hn hK hf hD hs]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hef (sq_nonneg sigma)) (by positivity)

/-- The actual tuned mu agrees exactly with the original-L cap minimum,
including the regime in which the auxiliary smoothness ell is smaller. -/
theorem mu_original_caps {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    mu n K L D sigma = theta *
      min L (min (linearCap n K D sigma) (cubicCap n K L D sigma)) := by
  let S := sigma * Real.sqrt (K : ℝ) / (D * Real.sqrt (n : ℝ))
  have hS : 0 < S := by
    obtain ⟨hn0, hK0⟩ := cast_pos hn hK
    dsimp [S]
    positivity
  have hlin := linearCap_pos hn hK hD hs
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlinS : linearCap n K D sigma ≤ S := by
    have hprod := mul_le_mul_of_nonneg_right hK1 hlin.le
    dsimp [S]
    rw [scale_eq_K_linear hn hK hD]
    simpa only [one_mul] using hprod
  by_cases hSL : S ≤ L
  · have hell : ell n K L D sigma = S := min_eq_right hSL
    have hcS : cubicCap n K S D sigma = linearCap n K D sigma :=
      cubic_scale_eq_linear hn hK hD hs
    have hlinC : linearCap n K D sigma ≤ cubicCap n K L D sigma := by
      rw [← hcS]
      exact cubicCap_mono hn hK hS hSL hD hs
    unfold mu
    rw [hell, hcS, min_self, min_eq_right hlinS,
      min_eq_left hlinC, min_eq_right (hlinS.trans hSL)]
  · have hell : ell n K L D sigma = L := min_eq_left (le_of_not_ge hSL)
    unfold mu
    rw [hell]

#print axioms scale_eq_K_linear
#print axioms cubic_scale_eq_linear
#print axioms cubicCap_mono
#print axioms mu_original_caps
end
end Gate148.RateAlgebra
