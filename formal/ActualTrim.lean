import ActualCharge
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring




/-!
# Gate144: exact endpoint trimming and deterministic retention

Pinned hand source:
Gate134/weighted-charge/FULL-ORDER-ALL-PARAMETER-SIMPLEX-BLOCK-LOWER-HAND-PROPOSAL.txt
SHA256 0db4cc4b93f12706e13953358a2117f0e45bfc055d561b3fa3ac729e1cb68685.

SOURCE-ONLY preparation by vi_release_math_audit. Only root may compile.

Mapping:
* `exists_shortest_max_interval` implements the finite retrospective choice
  in Section6. Empty intervals are included, so the maximum is at least zero.
* `shortest_max_positive_endpoints` implements strict positivity of its first
  and last update when the maximum is positive.
* `endpoint_trim_bound` deletes the last UPDATE. The remaining final STATE
  is t-1; the singleton case is handled separately.
* `cone_endpoint_trim_bound` specializes w_i = eta_i (C - b R_i), C = H D.
  Its small-endpoint interval bound is an EXPLICIT UNVERIFIED DEPENDENCY:
  it must be connected to the paid-reset/dynamics estimate (16), with its
  constants and nonnegativity checks, before asserting (17) for the cone.
* `retention_from_interval_cap` formalizes the last-above-D deterministic
  selection in Section7, using pointwise retention/drop and simultaneous
  interval caps as premises. Those premises are NOT proved cone dynamics here.
* `convex_output_lower` permits arbitrary nonnegative normalized weights on
  ALL actual states 0,...,T, including trajectory-selected weights pathwise.

No independence, stopping-time, fixed-schedule, bounded-radius or static-output
assumption is introduced. The sequences may be chosen retrospectively.
This file does not formalize paid resets, cone projection, permutation
expectations, Markov's inequality, parameter tuning, objective domination,
the minimax assembly or the imported upper theorem.
-/

namespace Gate144.EndpointTrim

/-- Half-open interval sum, using prefixes to make endpoint identities exact. -/
def intervalSum (w : ℕ → ℝ) (s t : ℕ) : ℝ :=
  (∑ i ∈ Finset.range t, w i) - ∑ i ∈ Finset.range s, w i

@[simp] theorem intervalSum_self (w : ℕ → ℝ) (s : ℕ) :
    intervalSum w s s = 0 := by
  simp [intervalSum]

theorem intervalSum_succ_right (w : ℕ → ℝ) (s t : ℕ) :
    intervalSum w s (t + 1) = intervalSum w s t + w t := by
  simp only [intervalSum, Finset.sum_range_succ]
  ring

theorem intervalSum_succ_left (w : ℕ → ℝ) (s t : ℕ) :
    intervalSum w (s + 1) t = intervalSum w s t - w s := by
  simp only [intervalSum, Finset.sum_range_succ]
  ring

/-- A maximizing interval, with the shortest-length tie rule. -/
structure ShortestMax (w : ℕ → ℝ) (T s t : ℕ) : Prop where
  left_le_right : s ≤ t
  right_le_horizon : t ≤ T
  maximal : ∀ a b, a ≤ b → b ≤ T →
    intervalSum w a b ≤ intervalSum w s t
  shortest : ∀ a b, a ≤ b → b ≤ T →
    intervalSum w a b = intervalSum w s t → t - s ≤ b - a

theorem exists_shortest_max_interval (w : ℕ → ℝ) (T : ℕ) :
    ∃ s t, ShortestMax w T s t := by
  classical
  let S : Finset (ℕ × ℕ) :=
    ((Finset.range (T + 1)).product (Finset.range (T + 1))).filter
      (fun st => st.1 ≤ st.2)
  have hmem : ∀ a b, (a, b) ∈ S ↔ a ≤ b ∧ b ≤ T := by
    intro a b
    constructor
    · intro hab
      have hf := Finset.mem_filter.mp hab
      have hp := Finset.mem_product.mp hf.1
      have hb := Finset.mem_range.mp hp.2
      exact ⟨hf.2, by omega⟩
    · intro hab
      apply Finset.mem_filter.mpr
      refine ⟨?_, hab.1⟩
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hS : S.Nonempty := ⟨(0, 0), (hmem 0 0).2 (by omega)⟩
  obtain ⟨u, hu, hmax⟩ :=
    S.exists_max_image (fun st => intervalSum w st.1 st.2) hS
  let M : Finset (ℕ × ℕ) :=
    S.filter (fun st => intervalSum w st.1 st.2 = intervalSum w u.1 u.2)
  have hM : M.Nonempty := by
    refine ⟨u, ?_⟩
    exact Finset.mem_filter.mpr ⟨hu, rfl⟩
  obtain ⟨v, hv, hmin⟩ := M.exists_min_image (fun st => st.2 - st.1) hM
  have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
  have hvval : intervalSum w v.1 v.2 = intervalSum w u.1 u.2 :=
    (Finset.mem_filter.mp hv).2
  have hvbounds : v.1 ≤ v.2 ∧ v.2 ≤ T := (hmem v.1 v.2).1 hvS
  refine ⟨v.1, v.2, ⟨hvbounds.1, hvbounds.2, ?_, ?_⟩⟩
  · intro a b hab hb
    have h := hmax (a, b) ((hmem a b).2 ⟨hab, hb⟩)
    simpa only [hvval] using h
  · intro a b hab hb heq
    apply hmin (a, b)
    apply Finset.mem_filter.mpr
    exact ⟨(hmem a b).2 ⟨hab, hb⟩, heq.trans hvval⟩

theorem shortest_max_nonneg {w : ℕ → ℝ} {T s t : ℕ}
    (h : ShortestMax w T s t) :
    0 ≤ intervalSum w s t := by
  simpa using h.maximal 0 0 (by omega) (by omega)

theorem shortest_max_positive_endpoints {w : ℕ → ℝ} {T s t : ℕ}
    (h : ShortestMax w T s t) (hpos : 0 < intervalSum w s t) :
    s < t ∧ 0 < w s ∧ 0 < w (t - 1) := by
  have htT := h.right_le_horizon
  have hst : s < t := by
    have hle := h.left_le_right
    by_contra hn
    have heq : s = t := by omega
    simp [heq] at hpos
  have hfirst : 0 < w s := by
    by_contra hn
    have hw : w s ≤ 0 := le_of_not_gt hn
    have hm := h.maximal (s + 1) t (by omega) h.right_le_horizon
    have hi := intervalSum_succ_left w s t
    have heq : intervalSum w (s + 1) t = intervalSum w s t := by
      linarith
    have hl := h.shortest (s + 1) t (by omega) h.right_le_horizon heq
    omega
  have hlast : 0 < w (t - 1) := by
    have hpred : t - 1 + 1 = t := by omega
    have hi : intervalSum w s t =
        intervalSum w s (t - 1) + w (t - 1) := by
      simpa only [hpred] using intervalSum_succ_right w s (t - 1)
    by_contra hn
    have hw : w (t - 1) ≤ 0 := le_of_not_gt hn
    have hm := h.maximal s (t - 1) (by omega) (by omega)
    have heq : intervalSum w s (t - 1) = intervalSum w s t := by
      linarith
    have hl := h.shortest s (t - 1) (by omega) (by omega) heq
    omega
  exact ⟨hst, hfirst, hlast⟩

/--
Abstract Section6 trim. The bound `hsmall` is a premise, not a proved paid-reset
estimate. Both of its radii are actual STATE indices.
-/
theorem endpoint_trim_bound (w R : ℕ → ℝ) (T : ℕ)
    (cap B radius : ℝ)
    (hcap0 : 0 ≤ cap) (hB0 : 0 ≤ B)
    (hcap : ∀ i, i < T → w i ≤ cap)
    (hpositive : ∀ i, i < T → 0 < w i → R i < radius)
    (hsmall : ∀ s t, s < t → t ≤ T →
      R s < radius → R t < radius → intervalSum w s t ≤ B) :
    ∀ u v, u ≤ v → v ≤ T → intervalSum w u v ≤ cap + B := by
  obtain ⟨s, t, h⟩ := exists_shortest_max_interval w T
  have hbound : intervalSum w s t ≤ cap + B := by
    by_cases hpos : 0 < intervalSum w s t
    · obtain ⟨hst, hfirst, hlast⟩ := shortest_max_positive_endpoints h hpos
      have htT := h.right_le_horizon
      have hsT : s < T := by omega
      have hlastT : t - 1 < T := by omega
      have hrs := hpositive s hsT hfirst
      have hrt := hpositive (t - 1) hlastT hlast
      have hpred : t - 1 + 1 = t := by omega
      have hsplit : intervalSum w s t =
          intervalSum w s (t - 1) + w (t - 1) := by
        simpa only [hpred] using intervalSum_succ_right w s (t - 1)
      have hlastcap := hcap (t - 1) hlastT
      by_cases hempty : s = t - 1
      · have hzero : intervalSum w s (t - 1) = 0 := by simp [hempty]
        linarith
      · have hrem : s < t - 1 := by omega
        have hrembound := hsmall s (t - 1) hrem (by omega) hrs hrt
        linarith
    · have hz : intervalSum w s t ≤ 0 := le_of_not_gt hpos
      linarith
  intro u v huv hv
  exact (h.maximal u v huv hv).trans hbound

/--
Cone-form increments. C denotes H*D. Strict positivity of every actual step
is retained, although the implication from a positive increment also follows
from nonnegative steps. No probabilistic restriction is present.
-/
theorem cone_endpoint_trim_bound (eta R : ℕ → ℝ) (T : ℕ)
    (C b L B : ℝ)
    (hC : 0 ≤ C) (hb : 0 < b) (hL : 0 < L) (hB : 0 ≤ B)
    (heta : ∀ i, i < T → 0 < eta i)
    (heta_cap : ∀ i, i < T → eta i ≤ 1 / L)
    (hR : ∀ i, i ≤ T → 0 ≤ R i)
    (hsmall : ∀ s t, s < t → t ≤ T →
      R s < C / b → R t < C / b →
      intervalSum (fun i => eta i * (C - b * R i)) s t ≤ B) :
    ∀ s t, s ≤ t → t ≤ T →
      intervalSum (fun i => eta i * (C - b * R i)) s t ≤ C / L + B := by
  apply endpoint_trim_bound
      (fun i => eta i * (C - b * R i)) R T (C / L) B (C / b)
  · exact div_nonneg hC (le_of_lt hL)
  · exact hB
  · intro i hi
    have he : 0 ≤ eta i := le_of_lt (heta i hi)
    have hri : 0 ≤ R i := hR i (le_of_lt hi)
    have hfactor : C - b * R i ≤ C := by
      nlinarith
    calc
      eta i * (C - b * R i) ≤ eta i * C :=
        mul_le_mul_of_nonneg_left hfactor he
      _ ≤ (1 / L) * C :=
        mul_le_mul_of_nonneg_right (heta_cap i hi) hC
      _ = C / L := by ring
  · intro i hi hw
    have hfactor : 0 < C - b * R i := by
      by_contra hn
      have hh : C - b * R i ≤ 0 := le_of_not_gt hn
      have hm := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (heta i hi)) hh
      linarith
    apply (lt_div_iff₀ hb).2
    nlinarith
  · exact hsmall

/-- Telescoping a pointwise loss bound, including the empty interval. -/
theorem loss_le_intervalSum (q w : ℕ → ℝ) :
    ∀ s t, s ≤ t →
      (∀ i, s ≤ i → i < t → q i - q (i + 1) ≤ w i) →
      q s - q t ≤ intervalSum w s t := by
  intro s t
  induction t with
  | zero =>
      intro hst hstep
      have hs : s = 0 := by omega
      simp [hs]
  | succ t ih =>
      intro hst hstep
      by_cases hle : s ≤ t
      · have hp := ih hle (fun i hsi hit => hstep i hsi (by omega))
        have ht := hstep t hle (by omega)
        rw [intervalSum_succ_right]
        linarith
      · have hs : s = t + 1 := by omega
        simp [hs]

/--
Deterministic Section7 retention from simultaneous interval control.
The chosen last-above-D index may depend on the whole realized path.
The dynamics and the interval cap remain explicit upstream premises.
-/
theorem retention_from_interval_cap (q w : ℕ → ℝ) (T : ℕ)
    (D eps Z : ℝ)
    (hD : 0 ≤ D) (heps : 0 ≤ eps) (heps1 : eps < 1) (hZ : 0 ≤ Z)
    (hq0 : q 0 = D)
    (hret : ∀ i, i < T → (1 - eps) * q i ≤ q (i + 1))
    (hdrop : ∀ i, i < T → q i ≤ D → q i - q (i + 1) ≤ w i)
    (hinterval : ∀ s t, s ≤ t → t ≤ T → intervalSum w s t ≤ Z) :
    ∀ t, t ≤ T → (1 - eps) * D - Z ≤ q t := by
  classical
  intro t ht
  by_cases hqt : D ≤ q t
  · have hprod : 0 ≤ eps * D := mul_nonneg heps hD
    nlinarith
  · let E : Finset ℕ := (Finset.range t).filter (fun j => D < q j)
    by_cases hE : E.Nonempty
    · obtain ⟨j, hj, hmax⟩ := E.exists_max_image (fun j => j) hE
      have hjlt : j < t := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      have hjq : D < q j := (Finset.mem_filter.mp hj).2
      have hpath : ∀ i, j + 1 ≤ i → i < t → q i ≤ D := by
        intro i hji hit
        by_contra hn
        have hqi : D < q i := lt_of_not_ge hn
        have hiE : i ∈ E :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hit, hqi⟩
        have hij := hmax i hiE
        omega
      have htel := loss_le_intervalSum q w (j + 1) t (by omega)
        (fun i hji hit => hdrop i (lt_of_lt_of_le hit ht) (hpath i hji hit))
      have hcap := hinterval (j + 1) t (by omega) ht
      have hretain := hret j (lt_of_lt_of_le hjlt ht)
      have hmul : (1 - eps) * D ≤ (1 - eps) * q j :=
        mul_le_mul_of_nonneg_left (le_of_lt hjq) (by linarith)
      linarith
    · have hpath : ∀ i, i < t → q i ≤ D := by
        intro i hit
        by_contra hn
        have hqi : D < q i := lt_of_not_ge hn
        apply hE
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hit, hqi⟩⟩
      have htel := loss_le_intervalSum q w 0 t (by omega)
        (fun i _ hit => hdrop i (lt_of_lt_of_le hit ht) (hpath i hit))
      have hcap := hinterval 0 t (by omega) ht
      have hprod : 0 ≤ eps * D := mul_nonneg heps hD
      rw [hq0] at htel
      nlinarith

/-- The pathwise good-event constants used in Section7. -/
theorem half_retention_from_interval_cap (q w : ℕ → ℝ) (T : ℕ)
    (D eps Z : ℝ)
    (hD : 0 ≤ D) (heps : 0 ≤ eps) (heps4 : eps ≤ 1 / 4)
    (hZ : 0 ≤ Z) (hZ4 : Z ≤ D / 4)
    (hq0 : q 0 = D)
    (hret : ∀ i, i < T → (1 - eps) * q i ≤ q (i + 1))
    (hdrop : ∀ i, i < T → q i ≤ D → q i - q (i + 1) ≤ w i)
    (hinterval : ∀ s t, s ≤ t → t ≤ T → intervalSum w s t ≤ Z) :
    ∀ t, t ≤ T → D / 2 ≤ q t := by
  intro t ht
  have h := retention_from_interval_cap q w T D eps Z hD heps
    (by linarith) hZ hq0 hret hdrop hinterval t ht
  have hprod : eps * D ≤ (1 / 4) * D :=
    mul_le_mul_of_nonneg_right heps4 hD
  nlinarith

/-- Arbitrary scalar convex weights on all actual states, including x_T. -/
theorem convex_output_lower (q alpha : ℕ → ℝ) (T : ℕ) (lower : ℝ)
    (hq : ∀ i, i ≤ T → lower ≤ q i)
    (ha : ∀ i, i ≤ T → 0 ≤ alpha i)
    (hsum : ∑ i ∈ Finset.range (T + 1), alpha i = 1) :
    lower ≤ ∑ i ∈ Finset.range (T + 1), alpha i * q i := by
  calc
    lower = (∑ i ∈ Finset.range (T + 1), alpha i) * lower := by
      rw [hsum]
      ring
    _ = ∑ i ∈ Finset.range (T + 1), alpha i * lower := by
      rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ Finset.range (T + 1), alpha i * q i := by
      apply Finset.sum_le_sum
      intro i hi
      have hit : i ≤ T := by
        have hh := Finset.mem_range.mp hi
        omega
      exact mul_le_mul_of_nonneg_left (hq i hit) (ha i hit)

end Gate144.EndpointTrim

-- Root's bounded compilation should retain these dependency reports.
#print axioms Gate144.EndpointTrim.exists_shortest_max_interval
#print axioms Gate144.EndpointTrim.shortest_max_positive_endpoints
#print axioms Gate144.EndpointTrim.endpoint_trim_bound
#print axioms Gate144.EndpointTrim.cone_endpoint_trim_bound
#print axioms Gate144.EndpointTrim.retention_from_interval_cap
#print axioms Gate144.EndpointTrim.half_retention_from_interval_cap
#print axioms Gate144.EndpointTrim.convex_output_lower


/-!
Gate148: the shortest-maximizer endpoint trim for the ACTUAL trajectory.
Compile after ActualCharge and the accepted Gate144 EndpointTrim module.
No EndpointTrim declarations are copied here. Root alone invokes Lean.

The endpoint bounds used below are R_s,R_t<C/b. The global radius 4sigma/ell
is deliberately NOT substituted into the interval remainder. The resulting
certificate depends on the fixed bank and parameters, not on eta, states,
or the interval selected by the shortest-maximizer proof.
-/
namespace Gate148.ActualTrim
noncomputable section
open scoped BigOperators
open Gate146.LabeledBlocks Gate146.ActualSequence Gate146.FixedPartitionBank
open Gate144.EndpointTrim Gate144.IntervalCharge Gate148.ActualCharge

theorem intervalSum_add_eq_stepSum (w : ℕ → ℝ) (s N : ℕ) :
    intervalSum w s (s + N) = stepSum (fun k => w (s + k)) N := by
  unfold intervalSum stepSum
  rw [Finset.sum_range_add]
  ring

theorem intervalSum_weighted (eta R : ℕ → ℝ) (C b : ℝ) (s N : ℕ) :
    intervalSum (fun i => eta i * (C - b * R i)) s (s + N) =
      C * stepSum (fun k => eta (s + k)) N -
      b * stepSum (fun k => eta (s + k) * R (s + k)) N := by
  rw [intervalSum_add_eq_stepSum]
  unfold stepSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

def endpointBudget {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (C b sigma A : ℝ) : ℝ :=
  C * partitionG P bank A / sigma +
    4 * C ^ 2 * Real.sqrt (P.count : ℝ) / (sigma * b) +
    C ^ 2 / (24 * sigma * b)

def certificate {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L C b sigma A : ℝ) : ℝ :=
  C / L + endpointBudget P bank C b sigma A

theorem certificate_expanded {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L C b sigma A : ℝ) :
    certificate P bank L C b sigma A = C / L + C * partitionG P bank A / sigma +
      4 * C ^ 2 * Real.sqrt (P.count : ℝ) / (sigma * b) +
      C ^ 2 / (24 * sigma * b) := by
  unfold certificate endpointBudget
  ring

theorem endpointBudget_nonneg {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (C b sigma A : ℝ)
    (hC : 0 ≤ C) (hb : 0 < b) (hsigma : 0 < sigma) (hA : 0 ≤ A) :
    0 ≤ endpointBudget P bank C b sigma A := by
  have hG : 0 ≤ partitionG P bank A := actual_G_nonneg P bank A hA
  unfold endpointBudget
  positivity

theorem certificate_nonneg {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (L C b sigma A : ℝ)
    (hL : 0 < L) (hC : 0 ≤ C) (hb : 0 < b) (hsigma : 0 < sigma) (hA : 0 ≤ A) :
    0 ≤ certificate P bank L C b sigma A :=
  add_nonneg (div_nonneg hC (le_of_lt hL))
    (endpointBudget_nonneg P bank C b sigma A hC hb hsigma hA)

/-- Elementary endpoint conversion, retaining the two actual small-radius
hypotheses separately. b0<=b will be derived from its exact definition. -/
theorem endpoint_terms_le (C b b0 sigma rroot Rs Rt : ℝ)
    (hC : 0 ≤ C) (hb : 0 < b) (hb0 : 0 ≤ b0) (hb0b : b0 ≤ b)
    (hsigma : 0 < sigma) (hrroot : 0 ≤ rroot)
    (hRs : 0 ≤ Rs) (hRt : 0 ≤ Rt) (hs : Rs ≤ C / b) (ht : Rt ≤ C / b) :
    4 * C * rroot * Rs / sigma + b0 * Rt ^ 2 / (24 * sigma) ≤
      4 * C ^ 2 * rroot / (sigma * b) + C ^ 2 / (24 * sigma * b) := by
  have hs1 : 4 * C * rroot * Rs / sigma ≤
      4 * C * rroot * (C / b) / sigma :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by positivity)) (le_of_lt hsigma)
  have hs2 : 4 * C * rroot * (C / b) / sigma =
      4 * C ^ 2 * rroot / (sigma * b) := by
    field_simp [ne_of_gt hb, ne_of_gt hsigma]
    <;> ring
  have ht2 : Rt ^ 2 ≤ (C / b) ^ 2 :=
    (sq_le_sq₀ hRt (div_nonneg hC (le_of_lt hb))).2 ht
  have ht1 : b0 * Rt ^ 2 / (24 * sigma) ≤ b * (C / b) ^ 2 / (24 * sigma) :=
    div_le_div_of_nonneg_right
      (mul_le_mul hb0b ht2 (sq_nonneg Rt) (le_of_lt hb)) (by positivity)
  have ht3 : b * (C / b) ^ 2 / (24 * sigma) = C ^ 2 / (24 * sigma * b) := by
    field_simp [ne_of_gt hb, ne_of_gt hsigma]
    <;> ring
  rw [hs2] at hs1
  rw [ht3] at ht1
  exact add_le_add hs1 ht1

/-- The hsmall premise of the accepted endpoint-trim theorem is proved
from actual_interval_charge, including the ACTUAL final state radius. -/
theorem actual_small_endpoint_bound {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (bank : Fin K → Equiv.Perm (Fin n))
    (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (C b b0 h A : ℝ) (hC : 0 < C) (hb : 0 < b) (hb0 : 0 < b0)
    (hb0def : b0 = b - 2 * C * ell * Real.sqrt (P.count : ℝ) / sigma)
    (hhdef : h = 120 * C / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * C / b0)
    (s t : ℕ) (hst : s < t) (ht : t ≤ n * K)
    (hsR : ‖fastPath P hn bank ell mu a sigma D eta s‖ < C / b)
    (htR : ‖fastPath P hn bank ell mu a sigma D eta t‖ < C / b) :
    intervalSum (fun i => eta i * (C - b * ‖fastPath P hn bank ell mu a sigma D eta i‖)) s t ≤
      endpointBudget P bank C b sigma A := by
  have hstN : s + (t - s) = t := by omega
  have hcharge := actual_interval_charge P hn hn2 bank L ell mu a sigma D eta
    hL hell hellL hmu hcap ha hsigma hD heta hetaL s (t - s) (by omega)
    C b b0 h A hC hb hb0 hb0def hhdef hAdef
  rw [hstN] at hcharge
  have hsum := intervalSum_weighted eta
    (fun i => ‖fastPath P hn bank ell mu a sigma D eta i‖) C b s (t - s)
  rw [hstN] at hsum
  rw [hsum]
  have hb0b : b0 ≤ b := by
    have hp : 0 ≤ 2 * C * ell * Real.sqrt (P.count : ℝ) / sigma := by positivity
    rw [hb0def]
    linarith
  have he := endpoint_terms_le C b b0 sigma (Real.sqrt (P.count : ℝ))
    ‖fastPath P hn bank ell mu a sigma D eta s‖
    ‖fastPath P hn bank ell mu a sigma D eta t‖
    (le_of_lt hC) hb (le_of_lt hb0) hb0b hsigma (Real.sqrt_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (le_of_lt hsR) (le_of_lt htR)
  unfold endpointBudget
  linarith

/-- The bank-only certificate bounds every actual interval deficit. The
single-update and empty-remainder cases are supplied by the accepted
shortest-maximizer theorem; no unjustified terminal-radius substitution. -/
theorem actual_all_interval_cap {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (hn2 : 2 ≤ n) (bank : Fin K → Equiv.Perm (Fin n))
    (L ell mu a sigma D : ℝ) (eta : ℕ → ℝ)
    (hL : 0 < L) (hell : 0 < ell) (hellL : ell ≤ L)
    (hmu : 0 < mu) (hcap : mu ≤ ell / 4) (ha : 0 < a)
    (hsigma : 0 < sigma) (hD : 0 < D)
    (heta : ∀ k < n * K, 0 < eta k) (hetaL : ∀ k < n * K, eta k ≤ 1 / L)
    (C b b0 h A : ℝ) (hC : 0 < C) (hb : 0 < b) (hb0 : 0 < b0)
    (hb0def : b0 = b - 2 * C * ell * Real.sqrt (P.count : ℝ) / sigma)
    (hhdef : h = 120 * C / (b0 * sigma))
    (hAdef : A = sigma * h + 10 * C / b0) :
    ∀ s t, s ≤ t → t ≤ n * K →
      intervalSum (fun i => eta i * (C - b * ‖fastPath P hn bank ell mu a sigma D eta i‖)) s t ≤
        certificate P bank L C b sigma A := by
  have hh : 0 < h := by rw [hhdef]; positivity
  have hA : 0 ≤ A := by rw [hAdef]; positivity
  refine cone_endpoint_trim_bound eta
    (fun i => ‖fastPath P hn bank ell mu a sigma D eta i‖) (n * K)
    C b L (endpointBudget P bank C b sigma A) (le_of_lt hC) hb hL
    (endpointBudget_nonneg P bank C b sigma A (le_of_lt hC) hb hsigma hA)
    heta hetaL (fun i hi => norm_nonneg _) ?_
  intro s t hst ht hsR htR
  exact actual_small_endpoint_bound P hn hn2 bank L ell mu a sigma D eta
    hL hell hellL hmu hcap ha hsigma hD heta hetaL C b b0 h A
    hC hb hb0 hb0def hhdef hAdef s t hst ht hsR htR

#print axioms intervalSum_weighted
#print axioms certificate_nonneg
#print axioms endpoint_terms_le
#print axioms actual_small_endpoint_bound
#print axioms actual_all_interval_cap
end
end Gate148.ActualTrim