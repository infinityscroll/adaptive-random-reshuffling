import RateAlgebra

/-! Gate148: original-parameter loss scales and the unchanged final
constant comparison. Risk/instance selection is a separate interface. -/
namespace Gate148.RateLoss
noncomputable section
open Gate148.HardParameters Gate148.RateAlgebra

def A0 (L D : ℝ) : ℝ := L * D ^ 2
def B0 (n K : ℕ) (L D : ℝ) : ℝ := A0 L D / ((n : ℝ) * (K : ℝ))
def N1 (n K : ℕ) (D sigma : ℝ) : ℝ :=
  sigma * D / Real.sqrt ((n : ℝ) * (K : ℝ))
def N2 (n K : ℕ) (L D sigma : ℝ) : ℝ :=
  (L * sigma ^ 2 * D ^ 4 / ((n : ℝ) * (K : ℝ) ^ 2)) ^ ((3 : ℝ)⁻¹)
def M (n K : ℕ) (L D sigma : ℝ) : ℝ :=
  min (A0 L D) (min (N1 n K D sigma) (N2 n K L D sigma))
def Psi (n K : ℕ) (L D sigma : ℝ) : ℝ :=
  min (A0 L D) (B0 n K L D + min (N1 n K D sigma) (N2 n K L D sigma))

theorem linear_scaled {n K : ℕ} {D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hD : 0 < D) :
    linearCap n K D sigma * D ^ 2 = N1 n K D sigma := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have hroot : Real.sqrt ((n : ℝ) * (K : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos hn0 hK0)).ne'
  unfold linearCap N1
  field_simp
  <;> ring

theorem cubic_scaled {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    cubicCap n K L D sigma * D ^ 2 = N2 n K L D sigma := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have hc := cubicCap_pos hn hK hL hD hs
  have hN : 0 ≤ N2 n K L D sigma := Real.rpow_nonneg (by positivity) _
  apply (pow_left_inj₀ (mul_nonneg hc.le (sq_nonneg D)) hN
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hcube : N2 n K L D sigma ^ 3 =
      L * sigma ^ 2 * D ^ 4 / ((n : ℝ) * (K : ℝ) ^ 2) := by
    unfold N2
    apply Real.rpow_inv_natCast_pow
    · positivity
    · norm_num
  rw [mul_pow, cubicCap_cube hn hK hL hD hs, hcube]
  field_simp
  <;> ring

/-- Exactly mu*D²=theta*M, uniformly across both auxiliary-scale regimes. -/
theorem mu_loss_scale {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    mu n K L D sigma * D ^ 2 = theta * M n K L D sigma := by
  rw [mu_original_caps hn hK hL hD hs, mul_assoc,
    min_mul_of_nonneg _ _ (sq_nonneg D), min_mul_of_nonneg _ _ (sq_nonneg D),
    linear_scaled hn hK hD, cubic_scaled hn hK hL hD hs]
  rfl

theorem cone_constant {n K : ℕ} {L D sigma : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 < L) (hD : 0 < D) (hs : 0 < sigma) :
    mu n K L D sigma * D ^ 2 / 16 = M n K L D sigma / 262144 := by
  rw [mu_loss_scale hn hK hL hD hs]
  unfold theta
  ring

theorem min_sum_le (A B N : ℝ) (hB : 0 ≤ B) :
    min A (B + N) ≤ B + min A N := by
  by_cases hAN : A ≤ N
  · rw [min_eq_left hAN]
    exact (min_le_left A (B + N)).trans (by linarith)
  · rw [min_eq_right (le_of_not_ge hAN)]
    exact min_le_right A (B + N)

theorem psi_le_B_plus_M (n K : ℕ) (L D sigma : ℝ) (hL : 0 ≤ L) :
    Psi n K L D sigma ≤ B0 n K L D + M n K L D sigma := by
  exact min_sum_le _ _ _ (by unfold B0 A0; positivity)

/-- The parameter-only better-of-two choice, before actual instances are
assembled. The supplied A/B/N are scalar rates, never risk hypotheses. -/
theorem final_constant_comparison (A B N : ℝ) (hB : 0 ≤ B) :
    min A (B + N) / 524288 ≤ max (B / 16) (min A N / 262144) := by
  have hp := min_sum_le A B N hB
  have hleft := le_max_left (B / 16) (min A N / 262144)
  have hright := le_max_right (B / 16) (min A N / 262144)
  linarith

theorem zero_distance (n K : ℕ) (L sigma : ℝ) : Psi n K L 0 sigma = 0 := by
  simp [Psi, A0, B0, N1, N2]

theorem zero_noise {n K : ℕ} {L D : ℝ}
    (hn : 2 ≤ n) (hK : 1 ≤ K) (hL : 0 ≤ L) :
    Psi n K L D 0 = B0 n K L D := by
  obtain ⟨hn0, hK0⟩ := cast_pos hn hK
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hprod : (1 : ℝ) ≤ (n : ℝ) * (K : ℝ) := by nlinarith
  have hB : B0 n K L D ≤ A0 L D := by
    unfold B0
    apply (div_le_iff₀ (mul_pos hn0 hK0)).2
    have hA : 0 ≤ A0 L D := by unfold A0; positivity
    nlinarith
  simpa only [Psi, N1, N2, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, mul_zero, zero_div,
    Real.zero_rpow (by norm_num : (3 : ℝ)⁻¹ ≠ 0), min_self, add_zero,
    min_eq_right hB]

#print axioms mu_loss_scale
#print axioms cone_constant
#print axioms final_constant_comparison
#print axioms zero_distance
#print axioms zero_noise
end
end Gate148.RateLoss
