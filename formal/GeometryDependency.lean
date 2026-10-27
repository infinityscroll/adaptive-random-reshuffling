import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Sort


/-!
# Gate145: exact finite counting of the reciprocal span of three positions

Pinned source: Gate134 Section 3, SHA256
0db4cc4b93f12706e13953358a2117f0e45bfc055d561b3fa3ac729e1cb68685.

`OrderedTriple n` contains exactly the increasing triples i < j < k < n,
stored in reverse order (k,j,i). `SpanCoordinates n` stores span r+2,
starting position i, and interior offset j-i-1. The explicit bijection
proves the grouped distribution; it is not an assumed expectation formula.

All reciprocals, sums being normalized, and averages below are REAL.
The finite counting theorem does not yet prove that three prescribed
labels in a uniformly sampled full permutation induce the uniform law on
this sample space. That marginal-law bridge, and the simplex/gap/Jensen
assembly, remain separate obligations. No policy-step independence is used.
-/

open Finset
open scoped BigOperators

namespace Gate145.SpanCounting

/-- A strictly increasing triple, represented as (last, middle, first). -/
abbrev OrderedTriple (n : ℕ) := Σ k : Fin n, Σ j : Fin k.val, Fin j.val

/-- A triple represented by span minus two, start, and interior offset. -/
abbrev SpanCoordinates (n : ℕ) :=
  Σ r : Fin (n - 2), Fin (n - (r.val + 2)) × Fin (r.val + 1)

theorem orderedTriple_ext {n : ℕ} {x y : OrderedTriple n}
    (hk : x.1.val = y.1.val) (hj : x.2.1.val = y.2.1.val)
    (hi : x.2.2.val = y.2.2.val) : x = y := by
  rcases x with ⟨⟨k, hk'⟩, ⟨j, hj'⟩, ⟨i, hi'⟩⟩
  rcases y with ⟨⟨l, hl'⟩, ⟨v, hv'⟩, ⟨u, hu'⟩⟩
  dsimp only at hk hj hi
  subst l
  subst v
  subst u
  rfl

def spanToOrdered {n : ℕ} (x : SpanCoordinates n) : OrderedTriple n :=
  ⟨⟨x.2.1.val + (x.1.val + 2), by
      have h := x.2.1.isLt
      omega⟩,
   ⟨⟨x.2.1.val + x.2.2.val + 1, by
        have h := x.2.2.isLt
        dsimp
        omega⟩,
    ⟨x.2.1.val, by dsimp; omega⟩⟩⟩

theorem spanToOrdered_injective (n : ℕ) :
    Function.Injective (@spanToOrdered n) := by
  intro x y h
  rcases x with ⟨⟨r, hr⟩, ⟨i, hi⟩, ⟨j, hj⟩⟩
  rcases y with ⟨⟨r', hr'⟩, ⟨i', hi'⟩, ⟨j', hj'⟩⟩
  have hiEq : i = i' := congrArg (fun t : OrderedTriple n => t.2.2.val) h
  have hkEq : i + (r + 2) = i' + (r' + 2) :=
    congrArg (fun t : OrderedTriple n => t.1.val) h
  have hjEq : i + j + 1 = i' + j' + 1 :=
    congrArg (fun t : OrderedTriple n => t.2.1.val) h
  have hrEq : r = r' := by omega
  have hjEq' : j = j' := by omega
  subst i'
  subst r'
  subst j'
  rfl

theorem spanToOrdered_surjective (n : ℕ) :
    Function.Surjective (@spanToOrdered n) := by
  intro t
  rcases t with ⟨⟨k, hk⟩, ⟨j, hj⟩, ⟨i, hi⟩⟩
  change j < k at hj
  change i < j at hi
  refine ⟨⟨⟨k - i - 2, by omega⟩,
    ⟨⟨i, by dsimp; omega⟩, ⟨j - i - 1, by dsimp; omega⟩⟩⟩, ?_⟩
  apply orderedTriple_ext
  · dsimp [spanToOrdered]
    omega
  · dsimp [spanToOrdered]
    omega
  · rfl

noncomputable def spanEquiv (n : ℕ) : SpanCoordinates n ≃ OrderedTriple n :=
  Equiv.ofBijective spanToOrdered
    ⟨spanToOrdered_injective n, spanToOrdered_surjective n⟩

/-- Actual position span, always at least two on this finite type. -/
def span {n : ℕ} (t : OrderedTriple n) : ℕ := t.1.val - t.2.2.val

theorem span_ge_two {n : ℕ} (t : OrderedTriple n) : 2 ≤ span t := by
  have h₁ := t.2.2.isLt
  have h₂ := t.2.1.isLt
  dsimp [span]
  omega

theorem span_spanToOrdered {n : ℕ} (x : SpanCoordinates n) :
    span (spanToOrdered x) = x.1.val + 2 := by
  dsimp [span, spanToOrdered]
  omega

/-- Elementary hockey-stick identity, including empty ranges. -/
theorem sum_range_choose (n k : ℕ) :
    (∑ i ∈ range n, i.choose k) = n.choose (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih, Nat.choose_succ_succ]
      change n.choose (k + 1) + n.choose k = n.choose k + n.choose (k + 1)
      omega

theorem sum_fin_choose (n k : ℕ) :
    (∑ i : Fin n, i.val.choose k) = n.choose (k + 1) := by
  calc
    (∑ i : Fin n, i.val.choose k) = (∑ i ∈ range n, i.choose k) :=
      (Finset.sum_range (n := n) (fun i : ℕ => i.choose k)).symm
    _ = n.choose (k + 1) := sum_range_choose n k

/-- Actual increasing triples, not merely a postulated distribution, have choose(n,3) elements. -/
theorem card_orderedTriple (n : ℕ) :
    Fintype.card (OrderedTriple n) = n.choose 3 := by
  simp only [OrderedTriple, Fintype.card_sigma, Fintype.card_fin]
  have hinner (k : Fin n) : (∑ j : Fin k.val, j.val) = k.val.choose 2 := by
    simpa using sum_fin_choose k.val 1
  simp_rw [hinner]
  exact sum_fin_choose n 2

/-- Exact span multiplicities. The r-th term is (n-(r+2))*((r+2)-1). -/
theorem card_spanCoordinates (n : ℕ) :
    Fintype.card (SpanCoordinates n) =
      ∑ r ∈ range (n - 2), (n - (r + 2)) * (r + 1) := by
  simp only [SpanCoordinates, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [Finset.sum_range]

theorem span_multiplicities_sum (n : ℕ) :
    (∑ r ∈ range (n - 2), (n - (r + 2)) * (r + 1)) = n.choose 3 := by
  rw [← card_spanCoordinates, ← card_orderedTriple]
  exact Fintype.card_congr (spanEquiv n)

/-- The manuscript's grouped sum, reindexed by r=l-2. -/
noncomputable def groupedReciprocalSum (n : ℕ) : ℝ :=
  ∑ r ∈ range (n - 2),
    (((n - (r + 2) : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ)) / ((r + 2 : ℕ) : ℝ)

/-- Exact equality between the actual uniform sample sum and its span grouping. -/
theorem reciprocal_sum_grouped (n : ℕ) :
    (∑ t : OrderedTriple n, (1 : ℝ) / (span t : ℝ)) =
      groupedReciprocalSum n := by
  have h := Fintype.sum_equiv (spanEquiv n)
    (fun x : SpanCoordinates n => (1 : ℝ) / ((x.1.val + 2 : ℕ) : ℝ))
    (fun t : OrderedTriple n => (1 : ℝ) / (span t : ℝ)) (by
      intro x
      change (1 : ℝ) / ((x.1.val + 2 : ℕ) : ℝ) =
        (1 : ℝ) / (span (spanToOrdered x) : ℝ)
      rw [span_spanToOrdered])
  rw [← h]
  unfold groupedReciprocalSum
  rw [Finset.sum_range]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  ring

theorem sum_cast_range (n : ℕ) :
    (∑ i ∈ range n, (i : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem sum_starts (n : ℕ) (hn : 2 ≤ n) :
    (∑ r ∈ range (n - 2), ((n - (r + 2) : ℕ) : ℝ)) =
      ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 := by
  have hterm : (∑ r ∈ range (n - 2), ((n - (r + 2) : ℕ) : ℝ)) =
      ∑ r ∈ range (n - 2), ((n : ℝ) - (r : ℝ) - 2) := by
    apply sum_congr rfl
    intro r hr
    have hrn : r + 2 ≤ n := by have := mem_range.mp hr; omega
    rw [Nat.cast_sub hrn]
    push_cast
    ring
  rw [hterm, sum_sub_distrib, sum_sub_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [sum_cast_range, Nat.cast_sub hn]
  norm_num only [Nat.cast_ofNat]
  ring

/-- The numerator bound, uniform in n and with no fixed-parameter computation. -/
theorem grouped_reciprocal_sum_le (n : ℕ) (hn : 2 ≤ n) :
    groupedReciprocalSum n ≤ ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 := by
  rw [← sum_starts n hn]
  unfold groupedReciprocalSum
  apply sum_le_sum
  intro r hr
  have hden : (0 : ℝ) < ((r + 2 : ℕ) : ℝ) := by positivity
  have hcount : (0 : ℝ) ≤ ((n - (r + 2) : ℕ) : ℝ) := by positivity
  apply (div_le_iff₀ hden).2
  push_cast
  nlinarith

/-- The real-valued choose-three identity, valid even for n=0,1,2. -/
theorem cast_choose_three (n : ℕ) :
    (n.choose 3 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ' n 2, Nat.cast_add, ih, Nat.cast_choose_two]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Finite uniform average over the genuine increasing-triple sample space. -/
noncomputable def uniformReciprocalSpan (n : ℕ) : ℝ :=
  (∑ t : OrderedTriple n, (1 : ℝ) / (span t : ℝ)) /
    (Fintype.card (OrderedTriple n) : ℝ)

theorem uniform_reciprocal_span_le (n : ℕ) (hn : 3 ≤ n) :
    uniformReciprocalSpan n ≤ (3 : ℝ) / (n : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcpos : (0 : ℝ) < (n.choose 3 : ℝ) := by
    exact_mod_cast (Nat.choose_pos hn)
  unfold uniformReciprocalSpan
  rw [reciprocal_sum_grouped, card_orderedTriple]
  apply (div_le_iff₀ hcpos).2
  have hnum := grouped_reciprocal_sum_le n (by omega)
  rw [cast_choose_three]
  have hid : (3 : ℝ) / (n : ℝ) *
      ((n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6) =
      ((n : ℝ) - 1) * ((n : ℝ) - 2) / 2 := by
    field_simp [ne_of_gt hnpos]
    <;> ring
  rw [hid]
  exact hnum

end Gate145.SpanCounting

#print axioms Gate145.SpanCounting.spanEquiv
#print axioms Gate145.SpanCounting.card_orderedTriple
#print axioms Gate145.SpanCounting.span_multiplicities_sum
#print axioms Gate145.SpanCounting.reciprocal_sum_grouped
#print axioms Gate145.SpanCounting.grouped_reciprocal_sum_le
#print axioms Gate145.SpanCounting.uniform_reciprocal_span_le


/-!
Exact finite counting for a transitive action. Uniformity of the image is
PROVED from fiber equivalences, not a probability assumption.
The actual action on three-subsets, its transitivity and the inverse-position
instantiation are separate interfaces pending the next source extension.
Only root runs the compiler. This source has not been run by its author.
-/

noncomputable section

open Finset

namespace Gate145.PermutationMarginal

variable {G X : Type*} [Group G] [MulAction G X]

def actionFiberEquiv (x y z : X) (h : G) (hh : h • y = z) :
    {g : G // g • x = y} ≃ {g : G // g • x = z} where
  toFun g := ⟨h * g, by rw [mul_smul, g.property, hh]⟩
  invFun g := ⟨h⁻¹ * g, by rw [mul_smul, g.property, ← hh, inv_smul_smul]⟩
  left_inv g := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv g := by
    apply Subtype.ext
    simp [mul_assoc]

variable [Fintype G] [Fintype X] [DecidableEq X]

theorem fiber_card_eq (x y z : X)
    (htrans : ∀ y z : X, ∃ h : G, h • y = z) :
    Fintype.card {g : G // g • x = y} =
      Fintype.card {g : G // g • x = z} := by
  obtain ⟨h, hh⟩ := htrans y z
  exact Fintype.card_congr (actionFiberEquiv x y z h hh)

theorem group_card_eq (x : X)
    (htrans : ∀ y z : X, ∃ h : G, h • y = z) :
    Fintype.card G =
      Fintype.card X * Fintype.card {g : G // g • x = x} := by
  classical
  calc
    Fintype.card G =
        Fintype.card (Σ y : X, {g : G // g • x = y}) :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv (fun g : G => g • x))).symm
    _ = ∑ y : X, Fintype.card {g : G // g • x = y} := Fintype.card_sigma
    _ = ∑ _y : X, Fintype.card {g : G // g • x = x} := by
      apply Finset.sum_congr rfl
      intro y hy
      exact fiber_card_eq x y x htrans
    _ = Fintype.card X * Fintype.card {g : G // g • x = x} := by simp

theorem group_sum_eq (x : X) (F : X → ℝ) :
    (∑ g : G, F (g • x)) =
      ∑ y : X, (Fintype.card {g : G // g • x = y} : ℝ) * F y := by
  classical
  have he := Fintype.sum_equiv
    (Equiv.sigmaFiberEquiv (fun g : G => g • x))
    (fun u : Σ y : X, {g : G // g • x = y} => F u.1)
    (fun g : G => F (g • x))
    (by
      intro u
      exact congrArg F u.2.property.symm)
  calc
    (∑ g : G, F (g • x)) =
        ∑ u : Σ y : X, {g : G // g • x = y}, F u.1 := he.symm
    _ = ∑ y : X, (Fintype.card {g : G // g • x = y} : ℝ) * F y := by
      rw [Fintype.sum_sigma]
      simp

/-- Exact pushforward of the normalized finite sum on the ACTUAL group.
No equal-fiber or uniform-image premise appears in this statement. -/
theorem uniform_action_mean (x : X) (F : X → ℝ)
    (htrans : ∀ y z : X, ∃ h : G, h • y = z) :
    (∑ g : G, F (g • x)) / (Fintype.card G : ℝ) =
      (∑ y : X, F y) / (Fintype.card X : ℝ) := by
  classical
  letI : Nonempty X := ⟨x⟩
  letI : Nonempty {g : G // g • x = x} := ⟨⟨1, one_smul G x⟩⟩
  have hx : (Fintype.card X : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := X))
  have hf : (Fintype.card {g : G // g • x = x} : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := {g : G // g • x = x}))
  have hc : (Fintype.card G : ℝ) =
      (Fintype.card X : ℝ) * (Fintype.card {g : G // g • x = x} : ℝ) := by
    exact_mod_cast group_card_eq x htrans
  rw [group_sum_eq]
  simp_rw [fiber_card_eq x _ x htrans]
  rw [← Finset.mul_sum, hc]
  field_simp
  <;> ring

#print axioms actionFiberEquiv
#print axioms fiber_card_eq
#print axioms group_card_eq
#print axioms group_sum_eq
#print axioms uniform_action_mean

end Gate145.PermutationMarginal

end

/-!
Compile this fragment after PermutationMarginal.lean, additionally importing:
  Mathlib.Data.Fintype.Powerset
  Mathlib.Data.Fintype.Perm
  Mathlib.Logic.Equiv.Fintype
  Mathlib.Algebra.Group.Equiv.Basic
The group acts on ACTUAL cardinality-k subsets. Transitivity is proved by
extending a finite-subset bijection, not assumed. Inversion converts a
position-to-label permutation into positions of fixed labels.
The sorted-triple/span-statistic equivalence remains a separate interface.
No compiler was run by this source's author.
-/

namespace Gate145.PermutationMarginal

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev CardSet (α : Type*) (k : ℕ) := {s : Finset α // s.card = k}

instance cardSetMulAction (k : ℕ) : MulAction (Equiv.Perm α) (CardSet α k) where
  smul g s := ⟨s.val.map g.toEmbedding, by simpa using s.property⟩
  one_smul s := by
    apply Subtype.ext
    change s.val.map (1 : Equiv.Perm α).toEmbedding = s.val
    exact Finset.map_refl
  mul_smul g h s := by
    apply Subtype.ext
    change s.val.map (g * h).toEmbedding =
      (s.val.map h.toEmbedding).map g.toEmbedding
    rw [Finset.map_map]
    rfl

theorem cardset_transitive (k : ℕ) (s t : CardSet α k) :
    ∃ g : Equiv.Perm α, g • s = t := by
  classical
  have hc : Fintype.card {a : α // a ∈ s.val} =
      Fintype.card {a : α // a ∈ t.val} := by
    simpa only [Fintype.card_coe] using s.property.trans t.property.symm
  let e : {a : α // a ∈ s.val} ≃ {a : α // a ∈ t.val} :=
    Classical.choice (Fintype.card_eq.mp hc)
  refine ⟨e.extendSubtype, ?_⟩
  apply Subtype.ext
  change s.val.map e.extendSubtype.toEmbedding = t.val
  ext a
  constructor
  · intro ha
    obtain ⟨x, hx, hxa⟩ := Finset.mem_map.mp ha
    have he : e.extendSubtype x = (e ⟨x, hx⟩).val :=
      e.extendSubtype_apply_of_mem x hx
    rw [← hxa]
    change e.extendSubtype x ∈ t.val
    rw [he]
    exact (e ⟨x, hx⟩).property
  · intro ha
    let y : {a : α // a ∈ t.val} := ⟨a, ha⟩
    refine Finset.mem_map.mpr ⟨(e.symm y).val, (e.symm y).property, ?_⟩
    change e.extendSubtype (e.symm y).val = a
    rw [e.extendSubtype_apply_of_mem _ (e.symm y).property]
    exact congrArg Subtype.val (e.apply_symm_apply y)

theorem uniform_cardset_mean (k : ℕ) (s : CardSet α k)
    (F : CardSet α k → ℝ) :
    (∑ g : Equiv.Perm α, F (g • s)) /
        (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ t : CardSet α k, F t) / (Fintype.card (CardSet α k) : ℝ) :=
  uniform_action_mean s F (cardset_transitive k)

theorem uniform_inverse_cardset_mean (k : ℕ) (s : CardSet α k)
    (F : CardSet α k → ℝ) :
    (∑ g : Equiv.Perm α, F (g⁻¹ • s)) /
        (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ t : CardSet α k, F t) / (Fintype.card (CardSet α k) : ℝ) := by
  have hi := Equiv.sum_comp (Equiv.inv (Equiv.Perm α))
    (fun g : Equiv.Perm α => F (g • s))
  calc
    (∑ g : Equiv.Perm α, F (g⁻¹ • s)) /
        (Fintype.card (Equiv.Perm α) : ℝ) =
      (∑ g : Equiv.Perm α, F (g • s)) /
        (Fintype.card (Equiv.Perm α) : ℝ) := by
      exact congrArg (fun v : ℝ => v / (Fintype.card (Equiv.Perm α) : ℝ)) hi
    _ = (∑ t : CardSet α k, F t) /
        (Fintype.card (CardSet α k) : ℝ) := uniform_cardset_mean k s F

/-- If g maps positions to labels, g^{-1} applied to the fixed label set is
exactly its set of actual update positions. -/
theorem mem_inverse_positions (k : ℕ) (s : CardSet α k)
    (g : Equiv.Perm α) (a : α) :
    a ∈ (g⁻¹ • s).val ↔ g a ∈ s.val := by
  change a ∈ s.val.map (g⁻¹).toEmbedding ↔ g a ∈ s.val
  rw [Finset.mem_map_equiv]
  change g a ∈ s.val ↔ g a ∈ s.val
  rfl

def threeLabels {n : ℕ} (a b c : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CardSet (Fin n) 3 :=
  ⟨{a, b, c}, by simp [hab, hac, hbc]⟩

/-- For every statistic of an unordered three-position set, averaging over
the actual uniform permutation is exactly the uniform three-subset average.
A fixed triple is an input chosen independently of the summation variable. -/
theorem uniform_three_positions {n : ℕ} (s : CardSet (Fin n) 3)
    (F : CardSet (Fin n) 3 → ℝ) :
    (∑ g : Equiv.Perm (Fin n), F (g⁻¹ • s)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) =
      (∑ t : CardSet (Fin n) 3, F t) / (Nat.choose n 3 : ℝ) := by
  simpa only [CardSet, Fintype.card_finset_len, Fintype.card_fin] using
    uniform_inverse_cardset_mean 3 s F

#print axioms cardset_transitive
#print axioms uniform_cardset_mean
#print axioms uniform_inverse_cardset_mean
#print axioms mem_inverse_positions
#print axioms threeLabels
#print axioms uniform_three_positions

end Gate145.PermutationMarginal


/-!
Compile after PermutationMarginal.lean, ThreeSubsetMarginal.inc and
SpanCounting.lean, additionally importing Mathlib.Data.Finset.Max and
Mathlib.Data.Fintype.EquivFin.

The map below sends an increasing triple to its ACTUAL three-position set.
Injectivity is proved from the ordered coordinates. The known cardinality
identity then proves surjectivity of this particular map. The statistic is
the actual maximum position minus the actual minimum position; its
preservation is proved explicitly, not inferred from equal cardinalities.
No compiler was run by this source's author.
-/

namespace Gate145.PermutationMarginal

open Gate145.SpanCounting

def firstPosition {n : ℕ} (t : OrderedTriple n) : Fin n :=
  ⟨t.2.2.val, lt_trans t.2.2.isLt (lt_trans t.2.1.isLt t.1.isLt)⟩

def middlePosition {n : ℕ} (t : OrderedTriple n) : Fin n :=
  ⟨t.2.1.val, lt_trans t.2.1.isLt t.1.isLt⟩

def tripleToSet {n : ℕ} (t : OrderedTriple n) : CardSet (Fin n) 3 :=
  threeLabels (firstPosition t) (middlePosition t) t.1
    (by
      intro h
      have hv := congrArg Fin.val h
      have hi := t.2.2.isLt
      dsimp [firstPosition, middlePosition] at hv
      omega)
    (by
      intro h
      have hv := congrArg Fin.val h
      have hi := t.2.2.isLt
      have hj := t.2.1.isLt
      dsimp [firstPosition] at hv
      omega)
    (by
      intro h
      have hv := congrArg Fin.val h
      have hj := t.2.1.isLt
      dsimp [middlePosition] at hv
      omega)

theorem mem_tripleToSet {n : ℕ} (t : OrderedTriple n) (a : Fin n) :
    a ∈ (tripleToSet t).val ↔
      a.val = t.2.2.val ∨ a.val = t.2.1.val ∨ a.val = t.1.val := by
  simp [tripleToSet, threeLabels, firstPosition, middlePosition, Fin.ext_iff]

theorem tripleToSet_injective (n : ℕ) :
    Function.Injective (@tripleToSet n) := by
  intro x y h
  have hs := congrArg Subtype.val h
  have hxk : x.1 ∈ (tripleToSet x).val :=
    (mem_tripleToSet x x.1).2 (Or.inr (Or.inr rfl))
  have hyk : y.1 ∈ (tripleToSet y).val :=
    (mem_tripleToSet y y.1).2 (Or.inr (Or.inr rfl))
  have hxi : firstPosition x ∈ (tripleToSet x).val :=
    (mem_tripleToSet x (firstPosition x)).2 (Or.inl rfl)
  have hyi : firstPosition y ∈ (tripleToSet y).val :=
    (mem_tripleToSet y (firstPosition y)).2 (Or.inl rfl)
  have hxj : middlePosition x ∈ (tripleToSet x).val :=
    (mem_tripleToSet x (middlePosition x)).2 (Or.inr (Or.inl rfl))
  rw [hs] at hxk hxi hxj
  rw [← hs] at hyk hyi
  have hxkv := (mem_tripleToSet y x.1).1 hxk
  have hykv := (mem_tripleToSet x y.1).1 hyk
  have hxiv := (mem_tripleToSet y (firstPosition x)).1 hxi
  have hyiv := (mem_tripleToSet x (firstPosition y)).1 hyi
  have hxjv := (mem_tripleToSet y (middlePosition x)).1 hxj
  have hxi_lt := x.2.2.isLt
  have hxj_lt := x.2.1.isLt
  have hyi_lt := y.2.2.isLt
  have hyj_lt := y.2.1.isLt
  dsimp [firstPosition, middlePosition] at hxiv hyiv hxjv
  apply orderedTriple_ext <;> omega

theorem tripleToSet_bijective (n : ℕ) :
    Function.Bijective (@tripleToSet n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨tripleToSet_injective n, ?_⟩
  rw [card_orderedTriple]
  simp [CardSet, Fintype.card_finset_len]

noncomputable def tripleSetEquiv (n : ℕ) :
    OrderedTriple n ≃ CardSet (Fin n) 3 :=
  Equiv.ofBijective tripleToSet (tripleToSet_bijective n)

theorem three_nonempty {n : ℕ} (s : CardSet (Fin n) 3) : s.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [s.property]
  norm_num

/-- The actual outer span of an unordered three-position set. -/
def subsetSpan {n : ℕ} (s : CardSet (Fin n) 3) : ℕ :=
  (s.val.max' (three_nonempty s)).val - (s.val.min' (three_nonempty s)).val

theorem max_tripleToSet {n : ℕ} (t : OrderedTriple n) :
    (tripleToSet t).val.max' (three_nonempty (tripleToSet t)) = t.1 := by
  apply (Finset.max'_eq_iff _ _ _).2
  refine ⟨(mem_tripleToSet t t.1).2 (Or.inr (Or.inr rfl)), ?_⟩
  intro a ha
  have hm := (mem_tripleToSet t a).1 ha
  have hi := t.2.2.isLt
  have hj := t.2.1.isLt
  change a.val ≤ t.1.val
  omega

theorem min_tripleToSet {n : ℕ} (t : OrderedTriple n) :
    (tripleToSet t).val.min' (three_nonempty (tripleToSet t)) = firstPosition t := by
  apply (Finset.min'_eq_iff _ _ _).2
  refine ⟨(mem_tripleToSet t (firstPosition t)).2 (Or.inl rfl), ?_⟩
  intro a ha
  have hm := (mem_tripleToSet t a).1 ha
  have hi := t.2.2.isLt
  have hj := t.2.1.isLt
  change t.2.2.val ≤ a.val
  omega

theorem subsetSpan_tripleToSet {n : ℕ} (t : OrderedTriple n) :
    subsetSpan (tripleToSet t) = span t := by
  unfold subsetSpan
  rw [max_tripleToSet, min_tripleToSet]
  rfl

theorem subset_reciprocal_mean (n : ℕ) :
    (∑ s : CardSet (Fin n) 3, (1 : ℝ) / (subsetSpan s : ℝ)) /
        (Nat.choose n 3 : ℝ) = uniformReciprocalSpan n := by
  have hs := (tripleSetEquiv n).sum_comp
    (fun s : CardSet (Fin n) 3 => (1 : ℝ) / (subsetSpan s : ℝ))
  change (∑ t : OrderedTriple n, (1 : ℝ) / (subsetSpan (tripleToSet t) : ℝ)) =
    (∑ s : CardSet (Fin n) 3, (1 : ℝ) / (subsetSpan s : ℝ)) at hs
  simp_rw [subsetSpan_tripleToSet] at hs
  unfold uniformReciprocalSpan
  rw [card_orderedTriple, hs]

/-- Exact uniform-permutation reciprocal-span bound for ANY fixed triple
of distinct labels, with positions taken from the inverse permutation.
No independence between the policy and permutation is an input: no policy
appears in the statistic. This is a genuine finite population expectation. -/
theorem uniform_actual_three_span_le (n : ℕ) (hn : 3 ≤ n)
    (s : CardSet (Fin n) 3) :
    (∑ g : Equiv.Perm (Fin n), (1 : ℝ) / (subsetSpan (g⁻¹ • s) : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ (3 : ℝ) / (n : ℝ) := by
  rw [uniform_three_positions s (fun t => (1 : ℝ) / (subsetSpan t : ℝ)),
    subset_reciprocal_mean]
  exact uniform_reciprocal_span_le n hn

#print axioms tripleToSet_injective
#print axioms tripleToSet_bijective
#print axioms subsetSpan_tripleToSet
#print axioms subset_reciprocal_mean
#print axioms uniform_actual_three_span_le

end Gate145.PermutationMarginal


/-! Actual largest-gap selection for an arbitrary sorted position list.
The sorted enumeration of an actual block's permutation positions is a
separate interface. No gap lower bound is assumed in the selection theorem. -/

namespace Gate145.GapSelection

def gap (position : ℕ → ℕ) (i : ℕ) : ℕ := position (i + 1) - position i

theorem telescoping_gaps (position : ℕ → ℕ) (M : ℕ)
    (hinc : ∀ i < M, position i < position (i + 1)) :
    ∀ N ≤ M, position N = position 0 + ∑ i ∈ Finset.range N, gap position i := by
  intro N
  induction N with
  | zero => intro hN; simp
  | succ N ih =>
      intro hN
      have hprev := ih (by omega)
      have hstep := hinc N (by omega)
      rw [Finset.sum_range_succ]
      dsimp [gap] at hprev ⊢
      omega

theorem exists_largest_gap (position : ℕ → ℕ) (m : ℕ) (hm : 2 ≤ m)
    (hinc : ∀ i < m - 1, position i < position (i + 1)) :
    ∃ k, k < m - 1 ∧ 0 < gap position k ∧
      (∀ i < m - 1, gap position i ≤ gap position k) ∧
      position (m - 1) - position 0 ≤ (m - 1) * gap position k := by
  have hne : (Finset.range (m - 1)).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨k, hk, hmax⟩ :=
    (Finset.range (m - 1)).exists_max_image (gap position) hne
  have hklt := Finset.mem_range.mp hk
  have hmax' : ∀ i < m - 1, gap position i ≤ gap position k :=
    fun i hi => hmax i (Finset.mem_range.mpr hi)
  have hsum := Finset.sum_le_sum (s := Finset.range (m - 1))
    (fun i hi => hmax' i (Finset.mem_range.mp hi))
  have htel := telescoping_gaps position (m - 1) hinc (m - 1) (le_refl _)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  refine ⟨k, hklt, ?_, hmax', ?_⟩
  · have hs := hinc k hklt
    dsimp [gap]
    omega
  · calc
      position (m - 1) - position 0 = ∑ i ∈ Finset.range (m - 1), gap position i := by omega
      _ ≤ (m - 1) * gap position k := by simpa using hsum

theorem exists_four_span_gap (position : ℕ → ℕ) (m : ℕ)
    (hm : 2 ≤ m) (hm5 : m ≤ 5)
    (hinc : ∀ i < m - 1, position i < position (i + 1)) :
    ∃ k, k < m - 1 ∧ 0 < gap position k ∧
      (∀ i < m - 1, gap position i ≤ gap position k) ∧
      position (m - 1) - position 0 ≤ 4 * gap position k := by
  obtain ⟨k, hk, hg, hmax, hspan⟩ := exists_largest_gap position m hm hinc
  refine ⟨k, hk, hg, hmax, hspan.trans ?_⟩
  exact Nat.mul_le_mul_right (gap position k) (by omega)

theorem reciprocal_gap_le (g span : ℕ) (hg : 0 < g) (hs : 0 < span)
    (hspan : span ≤ 4 * g) : (1 : ℝ) / (g : ℝ) ≤ 4 / (span : ℝ) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hsR : (0 : ℝ) < span := by exact_mod_cast hs
  apply (div_le_div_iff₀ hgR hsR).2
  have hh : (span : ℝ) ≤ 4 * (g : ℝ) := by exact_mod_cast hspan
  simpa using hh

theorem two_positions_gap (p q : ℕ) (hpq : p < q) (hq : q < 2) : q - p = 1 := by
  omega

#print axioms telescoping_gaps
#print axioms exists_largest_gap
#print axioms exists_four_span_gap
#print axioms reciprocal_gap_le
#print axioms two_positions_gap

end Gate145.GapSelection

/-! Actual largest consecutive gap of the sorted positions of a fixed block.
Additional import: Mathlib.Data.Finset.Sort. No uniform-gap expectation input. -/
namespace Gate145.ActualGap
open Gate145.PermutationMarginal Gate145.GapSelection
noncomputable section

def position {n m : ℕ} (s : CardSet (Fin n) m) (i : ℕ) : ℕ :=
  if h : i < m then (s.val.orderEmbOfFin s.property ⟨i,h⟩).val else 0

theorem position_inc {n m : ℕ} (s : CardSet (Fin n) m) :
    ∀ i < m-1, position s i < position s (i+1) := by
  intro i hi
  have hi0 : i < m := by omega
  have hi1 : i+1 < m := by omega
  simp only [position, dif_pos hi0, dif_pos hi1]
  exact (s.val.orderEmbOfFin s.property).strictMono (show (⟨i,hi0⟩ : Fin m) < ⟨i+1,hi1⟩ by change i < i+1; omega)

def index {n m : ℕ} (s : CardSet (Fin n) m) (hm : 2 ≤ m) : ℕ :=
  Classical.choose (exists_largest_gap (position s) m hm (position_inc s))

def selectedGap {n m : ℕ} (s : CardSet (Fin n) m) (hm : 2 ≤ m) : ℕ :=
  gap (position s) (index s hm)

theorem selected_spec {n m : ℕ} (s : CardSet (Fin n) m) (hm : 2 ≤ m) :
    index s hm < m-1 ∧ 0 < selectedGap s hm ∧
    (∀ i < m-1, gap (position s) i ≤ selectedGap s hm) ∧
    position s (m-1) - position s 0 ≤ (m-1)*selectedGap s hm := by
  exact Classical.choose_spec (exists_largest_gap (position s) m hm (position_inc s))

theorem position_zero {n m : ℕ} (s : CardSet (Fin n) m) (hm : 0 < m) :
    position s 0 = (s.val.min' (Finset.card_pos.mp (by omega))).val := by
  simp only [position, dif_pos hm]
  exact congrArg Fin.val (Finset.orderEmbOfFin_zero s.property hm)

theorem position_last {n m : ℕ} (s : CardSet (Fin n) m) (hm : 0 < m) :
    position s (m-1) = (s.val.max' (Finset.card_pos.mp (by omega))).val := by
  have hlast : m-1 < m := by omega
  simp only [position, dif_pos hlast]
  exact congrArg Fin.val (Finset.orderEmbOfFin_last s.property hm)

theorem three_span_positive {n : ℕ} (t : CardSet (Fin n) 3) : 0 < subsetSpan t := by
  obtain ⟨x,hx⟩ := (tripleSetEquiv n).surjective t
  rw [← hx]
  change 0 < subsetSpan (tripleToSet x)
  rw [subsetSpan_tripleToSet]
  have h := Gate145.SpanCounting.span_ge_two x
  omega

theorem contained_span_bound {n m : ℕ} (s : CardSet (Fin n) m)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (t : CardSet (Fin n) 3)
    (ht : t.val ⊆ s.val) : subsetSpan t ≤ 4*selectedGap s hm := by
  have hm0 : 0 < m := by omega
  have hs := (selected_spec s hm).2.2.2
  have hs4 : position s (m-1) - position s 0 ≤ 4*selectedGap s hm :=
    hs.trans (Nat.mul_le_mul_right _ (by omega))
  have hmax := Finset.le_max' s.val (t.val.max' (three_nonempty t))
    (ht (Finset.max'_mem t.val (three_nonempty t)))
  have hmin := Finset.min'_le s.val (t.val.min' (three_nonempty t))
    (ht (Finset.min'_mem t.val (three_nonempty t)))
  rw [position_zero s hm0, position_last s hm0] at hs4
  change (t.val.max' (three_nonempty t)).val ≤ _ at hmax
  change _ ≤ (t.val.min' (three_nonempty t)).val at hmin
  unfold subsetSpan
  omega

theorem reciprocal_selected_le {n m : ℕ} (s : CardSet (Fin n) m)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (t : CardSet (Fin n) 3)
    (ht : t.val ⊆ s.val) :
    (1:ℝ)/(selectedGap s hm : ℝ) ≤ 4/(subsetSpan t : ℝ) :=
  reciprocal_gap_le _ _ (selected_spec s hm).2.1
    (three_span_positive t) (contained_span_bound s hm hm5 t ht)

theorem map_subset {n m : ℕ} (b : CardSet (Fin n) m) (t : CardSet (Fin n) 3)
    (ht : t.val ⊆ b.val) (g : Equiv.Perm (Fin n)) :
    (g⁻¹ • t).val ⊆ (g⁻¹ • b).val := by
  intro a ha
  exact (mem_inverse_positions m b g a).2 (ht ((mem_inverse_positions 3 t g a).1 ha))

/-- The fixed triple t is inside the fixed block b before the permutation
is drawn. The left side uses the actual largest consecutive gap. -/
theorem uniform_actual_gap_le {n m : ℕ} (hn : 3 ≤ n)
    (b : CardSet (Fin n) m) (hm : 2 ≤ m) (hm5 : m ≤ 5)
    (t : CardSet (Fin n) 3) (ht : t.val ⊆ b.val) :
    (∑ g : Equiv.Perm (Fin n), (1:ℝ)/(selectedGap (g⁻¹ • b) hm : ℝ)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) ≤ 12/(n:ℝ) := by
  have hd : (0:ℝ) < Fintype.card (Equiv.Perm (Fin n)) := by positivity
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun g hg =>
    reciprocal_selected_le (g⁻¹ • b) hm hm5 (g⁻¹ • t) (map_subset b t ht g))
  have hmean := div_le_div_of_nonneg_right hsum (le_of_lt hd)
  have htrip := uniform_actual_three_span_le n hn t
  calc
    _ ≤ (∑ g : Equiv.Perm (Fin n), 4/(subsetSpan (g⁻¹ • t) : ℝ)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := hmean
    _ = 4*((∑ g : Equiv.Perm (Fin n), (1:ℝ)/(subsetSpan (g⁻¹ • t) : ℝ)) /
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)) := by
        simp_rw [show ∀ x : ℝ, 4/x = 4*(1/x) by intro x; ring]
        rw [← Finset.mul_sum]
        ring
    _ ≤ 4*(3/(n:ℝ)) := mul_le_mul_of_nonneg_left htrip (by norm_num)
    _ = 12/(n:ℝ) := by ring

#print axioms position_inc
#print axioms selected_spec
#print axioms contained_span_bound
#print axioms uniform_actual_gap_le
end
end Gate145.ActualGap


/-!
Gate145: actual finite-coordinate regular simplexes and the two dual endpoints
from Gate134 Sections 1 and 3. `dot` and `sqNorm` are explicitly Euclidean:
we do not use the supremum norm on a function type. No final Gram or norm
bound is assumed. The scale is constructed using the nonnegative real square
root; the parametric statements are connected to this actual scale below.

Every simplex vector and both dual endpoints have coordinate sum zero. The
identification of this subspace with Euclidean space of dimension m-1, and
the all-block dimension n-r+1 <= n, are separate interfaces: this file does
not silently count its ambient m coordinates as an (m-1)-dimensional block.
Interpolation, permutations, probability, cone dynamics, and the complete
minimax theorem are outside the statements in this file.
-/

namespace Gate145.SimplexDual

open scoped BigOperators
noncomputable section

def dot {m : ℕ} (u v : Fin m → ℝ) : ℝ := ∑ j, u j * v j

def sqNorm {m : ℕ} (u : Fin m → ℝ) : ℝ := dot u u

def basis {m : ℕ} (i : Fin m) : Fin m → ℝ :=
  fun j => if j = i then 1 else 0

def xi {m : ℕ} (a : ℝ) (i : Fin m) : Fin m → ℝ :=
  fun j => a * (basis i j - 1 / (m : ℝ))

def amplitude (m : ℕ) : ℝ := Real.sqrt ((m : ℝ) / ((m : ℝ) - 1))

def blockSum {m : ℕ} (a : ℝ) (E : Finset (Fin m)) : Fin m → ℝ :=
  fun j => ∑ i ∈ E, xi a i j

def before {m : ℕ} (a : ℝ) (E : Finset (Fin m)) : Fin m → ℝ :=
  fun j => ((m : ℝ) - 1) / ((m : ℝ) - E.card) * blockSum a E j

def after {m : ℕ} (a : ℝ) (E : Finset (Fin m)) : Fin m → ℝ :=
  fun j => -(((m : ℝ) - 1) / E.card) * blockSum a E j

theorem dot_comm {m : ℕ} (u v : Fin m → ℝ) : dot u v = dot v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem dot_scale_left {m : ℕ} (c : ℝ) (u v : Fin m → ℝ) :
    dot (fun j => c * u j) v = c * dot u v := by
  simp only [dot, mul_assoc, Finset.mul_sum]

theorem dot_scale_right {m : ℕ} (c : ℝ) (u v : Fin m → ℝ) :
    dot u (fun j => c * v j) = c * dot u v := by
  rw [dot_comm, dot_scale_left, dot_comm v u]

theorem dot_sub_left {m : ℕ} (u v w : Fin m → ℝ) :
    dot (fun j => u j - v j) w = dot u w - dot v w := by
  simp only [dot, sub_mul, Finset.sum_sub_distrib]

theorem dot_sub_right {m : ℕ} (u v w : Fin m → ℝ) :
    dot u (fun j => v j - w j) = dot u v - dot u w := by
  simp only [dot, mul_sub, Finset.sum_sub_distrib]

theorem dot_basis_left {m : ℕ} (i : Fin m) (v : Fin m → ℝ) :
    dot (basis i) v = v i := by
  simp [dot, basis]

theorem dot_basis_right {m : ℕ} (i : Fin m) (v : Fin m → ℝ) :
    dot v (basis i) = v i := by
  rw [dot_comm, dot_basis_left]

theorem dot_constants (m : ℕ) (c d : ℝ) :
    dot (fun _ : Fin m => c) (fun _ => d) = (m : ℝ) * c * d := by
  simp [dot, mul_assoc]

theorem dot_sum_left {m : ℕ} (E : Finset (Fin m))
    (u : Fin m → Fin m → ℝ) (v : Fin m → ℝ) :
    dot (fun j => ∑ i ∈ E, u i j) v = ∑ i ∈ E, dot (u i) v := by
  simp only [dot, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sqNorm_scale {m : ℕ} (c : ℝ) (u : Fin m → ℝ) :
    sqNorm (fun j => c * u j) = c ^ 2 * sqNorm u := by
  unfold sqNorm
  rw [dot_scale_left, dot_scale_right]
  ring

theorem amplitude_pos (m : ℕ) (hm : 2 ≤ m) : 0 < amplitude m := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  apply Real.sqrt_pos.mpr
  apply div_pos <;> linarith

theorem amplitude_sq (m : ℕ) (hm : 2 ≤ m) :
    amplitude m ^ 2 = (m : ℝ) / ((m : ℝ) - 1) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  apply Real.sq_sqrt
  apply div_nonneg <;> linarith

/-- Label sum: the actual offsets are exactly centered in each coordinate. -/
theorem label_sum_zero {m : ℕ} (a : ℝ) (hm : 2 ≤ m) (j : Fin m) :
    (∑ i, xi a i j) = 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [xi, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hb : (∑ i : Fin m, basis i j) = 1 := by
    simp [basis]
  rw [hb]
  simp [hmR]

/-- Each actual offset lies in the coordinate-sum-zero subspace. -/
theorem coordinate_sum_zero {m : ℕ} (a : ℝ) (hm : 2 ≤ m) (i : Fin m) :
    (∑ j, xi a i j) = 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  simp only [xi, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hb : (∑ j : Fin m, basis i j) = 1 := by simp [basis]
  rw [hb]
  simp [hmR]

theorem gram_raw {m : ℕ} (a : ℝ) (hm : 2 ≤ m) (i l : Fin m) :
    dot (xi a i) (xi a l) =
      a ^ 2 * ((if i = l then 1 else 0) - 1 / (m : ℝ)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  change dot (fun j => a * (basis i j - 1 / (m : ℝ)))
    (fun j => a * (basis l j - 1 / (m : ℝ))) = _
  rw [dot_scale_left, dot_scale_right, dot_sub_left,
    dot_sub_right, dot_sub_right, dot_basis_left, dot_basis_left,
    dot_basis_right, dot_constants]
  unfold basis
  by_cases hil : i = l
  · simp only [hil, if_true]
    field_simp
    <;> ring
  · simp only [hil, if_false]
    field_simp
    <;> ring

/-- Normalized Gram identity, derived from the actual coordinates. -/
theorem gram {m : ℕ} (a : ℝ) (hm : 2 ≤ m)
    (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1)) (i l : Fin m) :
    dot (xi a i) (xi a l) =
      ((m : ℝ) * (if i = l then 1 else 0) - 1) / ((m : ℝ) - 1) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (m : ℝ) ≠ 0 := by linarith
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  rw [gram_raw a hm i l, ha]
  field_simp
  <;> ring

theorem unit_sqNorm {m : ℕ} (a : ℝ) (hm : 2 ≤ m)
    (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1)) (i : Fin m) :
    sqNorm (xi a i) = 1 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  simp only [sqNorm, gram a hm ha, if_true, mul_one]
  exact div_self hm1

theorem off_diagonal {m : ℕ} (a : ℝ) (hm : 2 ≤ m)
    (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (i l : Fin m) (hil : i ≠ l) :
    dot (xi a i) (xi a l) = -1 / ((m : ℝ) - 1) := by
  simp [gram a hm ha, hil]

theorem block_pairing {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1)) (l : Fin m) :
    dot (blockSum a E) (xi a l) =
      ((m : ℝ) * (if l ∈ E then 1 else 0) - E.card) / ((m : ℝ) - 1) := by
  have hid : (∑ i ∈ E, (if i = l then (1 : ℝ) else 0)) =
      (if l ∈ E then 1 else 0) := by simp
  calc
    dot (blockSum a E) (xi a l) = ∑ i ∈ E, dot (xi a i) (xi a l) :=
      dot_sum_left E (xi a) (xi a l)
    _ = ∑ i ∈ E, ((m : ℝ) * (if i = l then 1 else 0) - 1) /
        ((m : ℝ) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact gram a hm ha i l
    _ = ((m : ℝ) * (∑ i ∈ E, (if i = l then (1 : ℝ) else 0)) - E.card) /
        ((m : ℝ) - 1) := by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = _ := by rw [hid]

theorem block_pairing_inside {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (l : Fin m) (hl : l ∈ E) :
    dot (blockSum a E) (xi a l) = ((m : ℝ) - E.card) / ((m : ℝ) - 1) := by
  simpa [hl] using block_pairing a E hm ha l

theorem block_pairing_outside {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (l : Fin m) (hl : l ∉ E) :
    dot (blockSum a E) (xi a l) = -(E.card : ℝ) / ((m : ℝ) - 1) := by
  simpa [hl] using block_pairing a E hm ha l

theorem block_sqNorm {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1)) :
    sqNorm (blockSum a E) =
      (E.card : ℝ) * ((m : ℝ) - E.card) / ((m : ℝ) - 1) := by
  calc
    sqNorm (blockSum a E) = ∑ i ∈ E, dot (xi a i) (blockSum a E) :=
      dot_sum_left E (xi a) (blockSum a E)
    _ = ∑ _i ∈ E, ((m : ℝ) - E.card) / ((m : ℝ) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [dot_comm, block_pairing_inside a E hm ha i hi]
    _ = _ := by simp [div_eq_mul_inv, mul_assoc]

theorem block_coordinate_sum_zero {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) : (∑ j, blockSum a E j) = 0 := by
  unfold blockSum
  rw [Finset.sum_comm]
  simp [coordinate_sum_zero a hm]

theorem before_coordinate_sum_zero {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) : (∑ j, before a E j) = 0 := by
  simp only [before, ← Finset.mul_sum, block_coordinate_sum_zero a E hm, mul_zero]

theorem after_coordinate_sum_zero {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) : (∑ j, after a E j) = 0 := by
  simp only [after, ← Finset.mul_sum, block_coordinate_sum_zero a E hm, mul_zero]

theorem before_pairing {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (hkm : E.card < m) (l : Fin m) (hl : l ∈ E) :
    dot (before a E) (xi a l) = 1 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkmR : (E.card : ℝ) < (m : ℝ) := by exact_mod_cast hkm
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hmk : (m : ℝ) - E.card ≠ 0 := by linarith
  unfold before
  rw [dot_scale_left, block_pairing_inside a E hm ha l hl]
  field_simp

theorem after_pairing {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (hk : 0 < E.card) (l : Fin m) (hl : l ∉ E) :
    dot (after a E) (xi a l) = 1 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < E.card := by exact_mod_cast hk
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hk0 : (E.card : ℝ) ≠ 0 := ne_of_gt hkR
  unfold after
  rw [dot_scale_left, block_pairing_outside a E hm ha l hl]
  field_simp
  <;> ring

theorem before_sqNorm {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (hkm : E.card < m) :
    sqNorm (before a E) = (E.card : ℝ) * ((m : ℝ) - 1) / ((m : ℝ) - E.card) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkmR : (E.card : ℝ) < (m : ℝ) := by exact_mod_cast hkm
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hmk : (m : ℝ) - E.card ≠ 0 := by linarith
  unfold before
  rw [sqNorm_scale, block_sqNorm a E hm ha]
  field_simp
  <;> ring

theorem after_sqNorm {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (hk : 0 < E.card) :
    sqNorm (after a E) = ((m : ℝ) - E.card) * ((m : ℝ) - 1) / E.card := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < E.card := by exact_mod_cast hk
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hk0 : (E.card : ℝ) ≠ 0 := ne_of_gt hkR
  unfold after
  rw [sqNorm_scale, block_sqNorm a E hm ha]
  field_simp
  <;> ring

theorem change_sqNorm {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (hk : 0 < E.card) (hkm : E.card < m) :
    sqNorm (fun j => after a E j - before a E j) =
      (m : ℝ) ^ 2 * ((m : ℝ) - 1) / ((E.card : ℝ) * ((m : ℝ) - E.card)) := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkR : (0 : ℝ) < E.card := by exact_mod_cast hk
  have hkmR : (E.card : ℝ) < (m : ℝ) := by exact_mod_cast hkm
  have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
  have hk0 : (E.card : ℝ) ≠ 0 := ne_of_gt hkR
  have hmk : (m : ℝ) - E.card ≠ 0 := by linarith
  have hfun : (fun j => after a E j - before a E j) =
      (fun j => (-(((m : ℝ) - 1) / E.card) -
        ((m : ℝ) - 1) / ((m : ℝ) - E.card)) * blockSum a E j) := by
    funext j
    unfold before after
    ring
  rw [hfun, sqNorm_scale, block_sqNorm a E hm ha]
  field_simp
  <;> ring

/-- Algebraic endpoint bounds for every nonempty proper subset, sizes 2--5. -/
theorem dual_bounds {m : ℕ} (a : ℝ) (E : Finset (Fin m))
    (hm : 2 ≤ m) (hm5 : m ≤ 5)
    (ha : a ^ 2 = (m : ℝ) / ((m : ℝ) - 1))
    (hk : 0 < E.card) (hkm : E.card < m) :
    sqNorm (before a E) ≤ 16 ∧ sqNorm (after a E) ≤ 16 ∧
      sqNorm (fun j => after a E j - before a E j) ≤ 25 := by
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm5R : (m : ℝ) ≤ 5 := by exact_mod_cast hm5
  have hkR : (1 : ℝ) ≤ E.card := by exact_mod_cast (Nat.succ_le_of_lt hk)
  have hkmR : (E.card : ℝ) + 1 ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hkm)
  have hkpos : (0 : ℝ) < E.card := by linarith
  have hmkpos : (0 : ℝ) < (m : ℝ) - E.card := by linarith
  have hmul : (m : ℝ) - 1 ≤ (E.card : ℝ) * ((m : ℝ) - E.card) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hkR)
      (show 0 ≤ (m : ℝ) - E.card - 1 by linarith)]
  rw [before_sqNorm a E hm ha hkm, after_sqNorm a E hm ha hk,
    change_sqNorm a E hm ha hk hkm]
  constructor
  · apply (div_le_iff₀ hmkpos).mpr
    have h1 : (E.card : ℝ) * ((m : ℝ) - 1) ≤ ((m : ℝ) - 1) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) - 1 by linarith)
        (show 0 ≤ (m : ℝ) - 1 - E.card by linarith)]
    have h2 : ((m : ℝ) - 1) ^ 2 ≤ 16 := by nlinarith
    nlinarith
  constructor
  · apply (div_le_iff₀ hkpos).mpr
    have h1 : ((m : ℝ) - E.card) * ((m : ℝ) - 1) ≤ ((m : ℝ) - 1) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ (m : ℝ) - 1 by linarith)
        (sub_nonneg.mpr hkR)]
    have h2 : ((m : ℝ) - 1) ^ 2 ≤ 16 := by nlinarith
    nlinarith
  · apply (div_le_iff₀ (mul_pos hkpos hmkpos)).mpr
    have hs : (m : ℝ) ^ 2 ≤ 25 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hmul (sq_nonneg (m : ℝ))
    have h2 := mul_le_mul_of_nonneg_right hs
      (le_of_lt (mul_pos hkpos hmkpos))
    exact h1.trans h2

/-- The actual square-root coordinate construction supplies all endpoint
identities and bounds; no existential Gram-model assumption remains. -/
theorem actual_dual {m : ℕ} (E : Finset (Fin m))
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (hk : 0 < E.card) (hkm : E.card < m) :
    (∀ i ∈ E, dot (before (amplitude m) E) (xi (amplitude m) i) = 1) ∧
    (∀ i, i ∉ E → dot (after (amplitude m) E) (xi (amplitude m) i) = 1) ∧
    sqNorm (before (amplitude m) E) ≤ 16 ∧
    sqNorm (after (amplitude m) E) ≤ 16 ∧
    sqNorm (fun j => after (amplitude m) E j - before (amplitude m) E j) ≤ 25 := by
  constructor
  · intro i hi
    exact before_pairing (amplitude m) E hm (amplitude_sq m hm) hkm i hi
  constructor
  · intro i hi
    exact after_pairing (amplitude m) E hm (amplitude_sq m hm) hk i hi
  exact dual_bounds (amplitude m) E hm hm5 (amplitude_sq m hm) hk hkm

#print axioms amplitude_sq
#print axioms label_sum_zero
#print axioms coordinate_sum_zero
#print axioms gram
#print axioms block_sqNorm
#print axioms actual_dual

end
end Gate145.SimplexDual


/-!
Gate134 Section3: the discrete largest-gap interpolation clock.
The chosen endpoints are update positions p<q; there are q-p differences,
not q-p-1. All finite horizons and arbitrary finite coordinate dimensions
are retained. The actual simplex endpoints and largest-gap selection are
separate interfaces; this file does not assume the desired clock energy.
-/

namespace Gate145.ClockVariation

noncomputable def clock (p q t : ℕ) : ℝ :=
  ((min (t - p) (q - p) : ℕ) : ℝ) / ((q - p : ℕ) : ℝ)

theorem gap_pos (p q : ℕ) (hpq : p < q) : (0 : ℝ) < ((q - p : ℕ) : ℝ) := by
  exact_mod_cast (show 0 < q - p by omega)

theorem clock_bounds (p q t : ℕ) (hpq : p < q) :
    0 ≤ clock p q t ∧ clock p q t ≤ 1 := by
  have hg := gap_pos p q hpq
  constructor
  · unfold clock
    positivity
  · unfold clock
    apply (div_le_one hg).2
    exact_mod_cast Nat.min_le_right (t - p) (q - p)

theorem clock_before (p q t : ℕ) (ht : t ≤ p) : clock p q t = 0 := by
  simp [clock, Nat.sub_eq_zero_of_le ht]

theorem clock_after (p q t : ℕ) (hpq : p < q) (ht : q ≤ t) :
    clock p q t = 1 := by
  have hmin : q - p ≤ t - p := Nat.sub_le_sub_right ht p
  have hg := gap_pos p q hpq
  simp [clock, min_eq_right hmin, ne_of_gt hg]

theorem clock_increment (p q t : ℕ) (hpq : p < q) :
    clock p q (t + 1) - clock p q t =
      if p ≤ t ∧ t < q then 1 / ((q - p : ℕ) : ℝ) else 0 := by
  by_cases h : p ≤ t ∧ t < q
  · have hn : min (t + 1 - p) (q - p) = min (t - p) (q - p) + 1 := by omega
    have hr : ((min (t + 1 - p) (q - p) : ℕ) : ℝ) =
        ((min (t - p) (q - p) : ℕ) : ℝ) + 1 := by exact_mod_cast hn
    simp only [if_pos h, clock]
    rw [hr]
    ring
  · have hn : min (t + 1 - p) (q - p) = min (t - p) (q - p) := by omega
    simp [clock, hn, h]

theorem increment_square (p q t : ℕ) (hpq : p < q) :
    (clock p q (t + 1) - clock p q t) ^ 2 =
      (clock p q (t + 1) - clock p q t) / ((q - p : ℕ) : ℝ) := by
  rw [clock_increment p q t hpq]
  split_ifs <;> ring

theorem clock_energy (p q N : ℕ) (hpq : p < q) :
    (∑ t ∈ Finset.range N, (clock p q (t + 1) - clock p q t) ^ 2) ≤
      1 / ((q - p : ℕ) : ℝ) := by
  have hid : (∑ t ∈ Finset.range N, (clock p q (t + 1) - clock p q t) ^ 2) =
      (clock p q N - clock p q 0) / ((q - p : ℕ) : ℝ) := by
    simp_rw [increment_square p q _ hpq]
    rw [← Finset.sum_div, Finset.sum_range_sub]
  rw [hid]
  have hN := (clock_bounds p q N hpq).2
  have h0 := (clock_bounds p q 0 hpq).1
  have hd : clock p q N - clock p q 0 ≤ 1 := by linarith
  have hg := gap_pos p q hpq
  exact div_le_div_of_nonneg_right hd (le_of_lt hg)

noncomputable def linePoint {m : ℕ} (u w : Fin m → ℝ) (alpha : ℝ) : Fin m → ℝ :=
  fun i => (1 - alpha) * u i + alpha * w i

theorem linePoint_square_bound {m : ℕ} (u w : Fin m → ℝ) (alpha B : ℝ)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hu : (∑ i, u i ^ 2) ≤ B) (hw : (∑ i, w i ^ 2) ≤ B) :
    (∑ i, linePoint u w alpha i ^ 2) ≤ B := by
  have heq : (∑ i, linePoint u w alpha i ^ 2) =
      (1 - alpha) * (∑ i, u i ^ 2) + alpha * (∑ i, w i ^ 2) -
        alpha * (1 - alpha) * (∑ i, (u i - w i) ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [linePoint]
    ring
  have hs : 0 ≤ ∑ i : Fin m, (u i - w i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hc := mul_nonneg (mul_nonneg ha0 (sub_nonneg.mpr ha1)) hs
  have hu' := mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr ha1)
  have hw' := mul_le_mul_of_nonneg_left hw ha0
  linarith

theorem linePoint_difference_square {m : ℕ} (u w : Fin m → ℝ) (alpha beta : ℝ) :
    (∑ i, (linePoint u w beta i - linePoint u w alpha i) ^ 2) =
      (beta - alpha) ^ 2 * (∑ i, (w i - u i) ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [linePoint]
  ring

theorem block_variation_energy {m : ℕ} (u w : Fin m → ℝ) (p q N : ℕ)
    (hpq : p < q) (hdiff : (∑ i, (w i - u i) ^ 2) ≤ 25) :
    (∑ t ∈ Finset.range N,
      ∑ i, (linePoint u w (clock p q (t + 1)) i -
        linePoint u w (clock p q t) i) ^ 2) ≤ 25 / ((q - p : ℕ) : ℝ) := by
  simp_rw [linePoint_difference_square]
  rw [← Finset.sum_mul]
  have hd0 : 0 ≤ ∑ i : Fin m, (w i - u i) ^ 2 :=
    Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have he := mul_le_mul_of_nonneg_right (clock_energy p q N hpq) hd0
  have hg := gap_pos p q hpq
  have hh := mul_le_mul_of_nonneg_left hdiff
    (show 0 ≤ 1 / ((q - p : ℕ) : ℝ) by positivity)
  calc
    _ ≤ (1 / ((q - p : ℕ) : ℝ)) * (∑ i, (w i - u i) ^ 2) := he
    _ ≤ (1 / ((q - p : ℕ) : ℝ)) * 25 := hh
    _ = 25 / ((q - p : ℕ) : ℝ) := by ring

#print axioms clock_bounds
#print axioms clock_before
#print axioms clock_after
#print axioms clock_increment
#print axioms clock_energy
#print axioms linePoint_square_bound
#print axioms linePoint_difference_square
#print axioms block_variation_energy

end Gate145.ClockVariation

/-!
Gate145: connection of the ACTUAL fixed simplex offsets and dual endpoints
to the proved discrete interpolation clock. Compile after SimplexDual.lean
and ClockVariation.lean. No final endpoint, change, or table norm bound is
assumed here: those are discharged by the actual square-root construction.

The offsets xi(amplitude m)i are fixed before choosing E or the time map.
Only the analytical dual depends on the early subset and chosen gap. This
file does not relabel or change an instance in response to its permutation.
The actual sorted-permutation-position construction, largest-gap selection
connection, block direct sum, and zero-sum subspace dimension/isometry remain
separate interfaces. Fin m coordinates use the explicit Euclidean dot and
squared norm, not the default function-space norm.
-/

namespace Gate145.SimplexClock

open scoped BigOperators
open SimplexDual ClockVariation

noncomputable section

def dualAt {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ) : Fin m → ℝ :=
  linePoint (before (amplitude m) E) (after (amplitude m) E) (clock p q t)

theorem sqNorm_eq_sum_sq {m : ℕ} (u : Fin m → ℝ) :
    sqNorm u = ∑ j, u j ^ 2 := by
  simp only [sqNorm, dot, pow_two]

/-- Pointwise bound at EVERY time, including the interior interpolation. -/
theorem dualAt_sqNorm {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (hk : 0 < E.card) (hkm : E.card < m)
    (hpq : p < q) : sqNorm (dualAt E p q t) ≤ 16 := by
  obtain ⟨hearly, hlate, hu, hw, hchange⟩ := actual_dual E hm hm5 hk hkm
  have hu' : (∑ j, before (amplitude m) E j ^ 2) ≤ 16 := by
    simpa only [sqNorm_eq_sum_sq] using hu
  have hw' : (∑ j, after (amplitude m) E j ^ 2) ≤ 16 := by
    simpa only [sqNorm_eq_sum_sq] using hw
  have hc := clock_bounds p q t hpq
  rw [sqNorm_eq_sum_sq]
  exact linePoint_square_bound (before (amplitude m) E) (after (amplitude m) E)
    (clock p q t) 16 hc.1 hc.2 hu' hw'

/-- Finite-horizon variation, with a REAL reciprocal gap. No endpoint-change
bound is an input; the actual simplex construction supplies it. -/
theorem dualAt_variation {m : ℕ} (E : Finset (Fin m)) (p q N : ℕ)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (hk : 0 < E.card) (hkm : E.card < m)
    (hpq : p < q) :
    (∑ t ∈ Finset.range N,
      sqNorm (fun j => dualAt E p q (t + 1) j - dualAt E p q t j)) ≤
      25 / ((q - p : ℕ) : ℝ) := by
  obtain ⟨hearly, hlate, hu, hw, hchange⟩ := actual_dual E hm hm5 hk hkm
  have hchange' : (∑ j,
      (after (amplitude m) E j - before (amplitude m) E j) ^ 2) ≤ 25 := by
    simpa only [sqNorm_eq_sum_sq] using hchange
  simpa only [sqNorm_eq_sum_sq, dualAt] using
    block_variation_energy (before (amplitude m) E) (after (amplitude m) E)
      p q N hpq hchange'

theorem dualAt_before {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ)
    (ht : t ≤ p) : dualAt E p q t = before (amplitude m) E := by
  funext j
  simp [dualAt, clock_before p q t ht, linePoint]

theorem dualAt_after {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ)
    (hpq : p < q) (ht : q ≤ t) :
    dualAt E p q t = after (amplitude m) E := by
  funext j
  simp [dualAt, clock_after p q t hpq ht, linePoint]

theorem early_pairing {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (hk : 0 < E.card) (hkm : E.card < m)
    (i : Fin m) (hi : i ∈ E) (ht : t ≤ p) :
    dot (dualAt E p q t) (xi (amplitude m) i) = 1 := by
  rw [dualAt_before E p q t ht]
  exact (actual_dual E hm hm5 hk hkm).1 i hi

theorem late_pairing {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (hk : 0 < E.card) (hkm : E.card < m)
    (hpq : p < q) (i : Fin m) (hi : i ∉ E) (ht : q ≤ t) :
    dot (dualAt E p q t) (xi (amplitude m) i) = 1 := by
  rw [dualAt_after E p q t hpq ht]
  exact (actual_dual E hm hm5 hk hkm).2.1 i hi

/-- Every fixed label has pairing1 at its specified hit time. The hypotheses
are precisely the temporal separation furnished by a chosen empty gap. -/
theorem hit_pairing {m : ℕ} (E : Finset (Fin m)) (p q : ℕ)
    (hit : Fin m → ℕ)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (hk : 0 < E.card) (hkm : E.card < m)
    (hpq : p < q)
    (hearly : ∀ i ∈ E, hit i ≤ p)
    (hlate : ∀ i, i ∉ E → q ≤ hit i) :
    ∀ i, dot (dualAt E p q (hit i)) (xi (amplitude m) i) = 1 := by
  intro i
  by_cases hi : i ∈ E
  · exact early_pairing E p q (hit i) hm hm5 hk hkm i hi (hearly i hi)
  · exact late_pairing E p q (hit i) hm hm5 hk hkm hpq i hi (hlate i hi)

/-- Uniform pairing bound against ANY fixed offset, not just the label whose
hit occurs at the current time. This is needed by the paid-reset interface. -/
theorem all_label_pairing_bound {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ)
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (hk : 0 < E.card) (hkm : E.card < m)
    (hpq : p < q) (i : Fin m) :
    |dot (dualAt E p q t) (xi (amplitude m) i)| ≤ 4 := by
  have hd : (∑ j, dualAt E p q t j ^ 2) ≤ 16 := by
    simpa only [sqNorm_eq_sum_sq] using dualAt_sqNorm E p q t hm hm5 hk hkm hpq
  have hx : (∑ j, xi (amplitude m) i j ^ 2) = 1 := by
    simpa only [sqNorm_eq_sum_sq] using
      unit_sqNorm (amplitude m) hm (amplitude_sq m hm) i
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (dualAt E p q t) (xi (amplitude m) i)
  rw [hx, mul_one] at hc
  have hs : dot (dualAt E p q t) (xi (amplitude m) i) ^ 2 ≤ (4 : ℝ) ^ 2 := by
    change (∑ j, dualAt E p q t j * xi (amplitude m) i j) ^ 2 ≤ (4 : ℝ) ^ 2
    nlinarith
  exact abs_le_of_sq_le_sq hs (by norm_num)

/-- Interpolation remains in the actual coordinate-zero-sum subspace. This
does not by itself prove the subspace dimension or an isometric model. -/
theorem dualAt_coordinate_sum_zero {m : ℕ} (E : Finset (Fin m)) (p q t : ℕ)
    (hm : 2 ≤ m) : (∑ j, dualAt E p q t j) = 0 := by
  change (∑ j, ((1 - clock p q t) * before (amplitude m) E j +
    clock p q t * after (amplitude m) E j)) = 0
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    before_coordinate_sum_zero (amplitude m) E hm,
    after_coordinate_sum_zero (amplitude m) E hm]
  ring

#print axioms dualAt_sqNorm
#print axioms dualAt_variation
#print axioms hit_pairing
#print axioms all_label_pairing_bound
#print axioms dualAt_coordinate_sum_zero

end
end Gate145.SimplexClock

/-!
Gate145: actual fixed-label hit-map assembly. Compile after ActualGap.inc
and SimplexClock.inc (and their unchanged dependencies).

The hit map is injective but need not be monotone in label order. Its actual
image is sorted; the selected largest consecutive gap determines the early
subset of the ORIGINAL labels. Every temporal-separation premise used by
SimplexClock.hit_pairing is proved below. The fixed simplex vectors are never
reordered or replaced when the hit map changes. No probabilistic assumption
or final pairing/norm/variation bound is supplied as a hypothesis.

Remaining interfaces include an actual all-n labeled block partition, its
orthogonal direct sum and zero-sum subspace dimension/isometry, and the
connection of each block's inverse-permutation hit map to the global table.
-/

namespace Gate145.HitAssembly

open scoped BigOperators
open PermutationMarginal SimplexDual SimplexClock

noncomputable section

def hitSet {n m : ℕ} (hit : Fin m → Fin n) (hinj : Function.Injective hit) :
    CardSet (Fin n) m :=
  ⟨Finset.univ.image hit, by
    rw [Finset.card_image_of_injective _ hinj]
    simp⟩

theorem hit_mem {n m : ℕ} (hit : Fin m → Fin n) (hinj : Function.Injective hit)
    (i : Fin m) : hit i ∈ (hitSet hit hinj).val := by
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem position_at_fin {n m : ℕ} (s : CardSet (Fin n) m) (j : Fin m) :
    ActualGap.position s j.val = (s.val.orderEmbOfFin s.property j).val := by
  simp only [ActualGap.position, dif_pos j.isLt]

theorem position_mono {n m : ℕ} (s : CardSet (Fin n) m) (i j : Fin m)
    (hij : i ≤ j) : ActualGap.position s i.val ≤ ActualGap.position s j.val := by
  rw [position_at_fin, position_at_fin]
  exact (s.val.orderEmbOfFin s.property).monotone hij

theorem every_member_has_rank {n m : ℕ} (s : CardSet (Fin n) m)
    (x : Fin n) (hx : x ∈ s.val) :
    ∃ j : Fin m, ActualGap.position s j.val = x.val := by
  obtain ⟨j, hj⟩ := (s.val.orderIsoOfFin s.property).surjective ⟨x, hx⟩
  refine ⟨j, ?_⟩
  rw [position_at_fin]
  change ((s.val.orderIsoOfFin s.property) j).val.val = x.val
  rw [hj]

/-- No member of the actual position set lies strictly between consecutive
sorted positions. This is proved from the sorted enumeration, not assumed. -/
theorem consecutive_no_interior {n m : ℕ} (s : CardSet (Fin n) m)
    (k : ℕ) (hk : k < m - 1) (x : Fin n) (hx : x ∈ s.val)
    (hleft : ActualGap.position s k < x.val) :
    ActualGap.position s (k + 1) ≤ x.val := by
  have hk0 : k < m := by omega
  have hk1 : k + 1 < m := by omega
  obtain ⟨j, hj⟩ := every_member_has_rank s x hx
  have hjgt : k < j.val := by
    by_contra h
    have hle : j ≤ (⟨k, hk0⟩ : Fin m) := by
      change j.val ≤ k
      omega
    have hp := position_mono s j ⟨k, hk0⟩ hle
    change ActualGap.position s j.val ≤ ActualGap.position s k at hp
    rw [hj] at hp
    omega
  have hle : (⟨k + 1, hk1⟩ : Fin m) ≤ j := by
    change k + 1 ≤ j.val
    omega
  have hp := position_mono s ⟨k + 1, hk1⟩ j hle
  change ActualGap.position s (k + 1) ≤ ActualGap.position s j.val at hp
  rwa [hj] at hp

theorem position_is_hit {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (j : Fin m) :
    ∃ i : Fin m, (hit i).val = ActualGap.position (hitSet hit hinj) j.val := by
  let s := hitSet hit hinj
  have hmem : s.val.orderEmbOfFin s.property j ∈ Finset.univ.image hit :=
    Finset.orderEmbOfFin_mem s.val s.property j
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  rw [position_at_fin]
  exact congrArg Fin.val heq

def leftTime {n m : ℕ} (hit : Fin m → Fin n) (hinj : Function.Injective hit)
    (hm : 2 ≤ m) : ℕ :=
  ActualGap.position (hitSet hit hinj) (ActualGap.index (hitSet hit hinj) hm)

def rightTime {n m : ℕ} (hit : Fin m → Fin n) (hinj : Function.Injective hit)
    (hm : 2 ≤ m) : ℕ :=
  ActualGap.position (hitSet hit hinj) (ActualGap.index (hitSet hit hinj) hm + 1)

def earlySubset {n m : ℕ} (hit : Fin m → Fin n) (hinj : Function.Injective hit)
    (hm : 2 ≤ m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => (hit i).val ≤ leftTime hit hinj hm)

theorem selected_times_strict {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) :
    leftTime hit hinj hm < rightTime hit hinj hm := by
  exact ActualGap.position_inc (hitSet hit hinj)
    (ActualGap.index (hitSet hit hinj) hm) (ActualGap.selected_spec _ hm).1

theorem early_time {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) (i : Fin m)
    (hi : i ∈ earlySubset hit hinj hm) :
    (hit i).val ≤ leftTime hit hinj hm := by
  exact (Finset.mem_filter.mp hi).2

theorem late_time {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) (i : Fin m)
    (hi : i ∉ earlySubset hit hinj hm) :
    rightTime hit hinj hm ≤ (hit i).val := by
  have hnot : ¬ (hit i).val ≤ leftTime hit hinj hm := by
    intro h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
  have hleft : leftTime hit hinj hm < (hit i).val := by omega
  exact consecutive_no_interior (hitSet hit hinj)
    (ActualGap.index (hitSet hit hinj) hm) (ActualGap.selected_spec _ hm).1
    (hit i) (hit_mem hit hinj i) hleft

theorem early_nonempty {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) :
    0 < (earlySubset hit hinj hm).card := by
  have hk : ActualGap.index (hitSet hit hinj) hm < m := by
    have h := (ActualGap.selected_spec (hitSet hit hinj) hm).1
    omega
  obtain ⟨i, hi⟩ := position_is_hit hit hinj ⟨ActualGap.index (hitSet hit hinj) hm, hk⟩
  apply Finset.card_pos.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩⟩
  exact le_of_eq hi

theorem early_proper {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) :
    (earlySubset hit hinj hm).card < m := by
  have hk1 : ActualGap.index (hitSet hit hinj) hm + 1 < m := by
    have h := (ActualGap.selected_spec (hitSet hit hinj) hm).1
    omega
  obtain ⟨i, hi⟩ := position_is_hit hit hinj
    ⟨ActualGap.index (hitSet hit hinj) hm + 1, hk1⟩
  have hiq : (hit i).val = rightTime hit hinj hm := hi
  have hiout : i ∉ earlySubset hit hinj hm := by
    intro hin
    have hle := early_time hit hinj hm i hin
    have hpq := selected_times_strict hit hinj hm
    omega
  have hsub : earlySubset hit hinj hm ⊂ (Finset.univ : Finset (Fin m)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    apply hiout
    rw [heq]
    exact Finset.mem_univ i
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hsub

def actualDualAt {n m : ℕ} (hit : Fin m → Fin n) (hinj : Function.Injective hit)
    (hm : 2 ≤ m) (t : ℕ) : Fin m → ℝ :=
  dualAt (earlySubset hit hinj hm) (leftTime hit hinj hm) (rightTime hit hinj hm) t

/-- Every fixed label has pairing1 at its ACTUAL injective hit time. No
separation, early-subset cardinality, endpoint, or current-pairing assumption
remains. The subset is derived from the actual selected consecutive gap. -/
theorem actual_hit_pairing {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) (hm5 : m ≤ 5) :
    ∀ i, dot (actualDualAt hit hinj hm (hit i).val) (xi (amplitude m) i) = 1 := by
  exact hit_pairing (earlySubset hit hinj hm) (leftTime hit hinj hm)
    (rightTime hit hinj hm) (fun i => (hit i).val) hm hm5
    (early_nonempty hit hinj hm) (early_proper hit hinj hm)
    (selected_times_strict hit hinj hm) (early_time hit hinj hm) (late_time hit hinj hm)

theorem actual_sqNorm {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) (hm5 : m ≤ 5) (t : ℕ) :
    sqNorm (actualDualAt hit hinj hm t) ≤ 16 := by
  exact dualAt_sqNorm (earlySubset hit hinj hm) (leftTime hit hinj hm)
    (rightTime hit hinj hm) t hm hm5 (early_nonempty hit hinj hm)
    (early_proper hit hinj hm) (selected_times_strict hit hinj hm)

theorem actual_all_label_pairing_bound {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) (hm5 : m ≤ 5)
    (t : ℕ) (i : Fin m) :
    |dot (actualDualAt hit hinj hm t) (xi (amplitude m) i)| ≤ 4 := by
  exact all_label_pairing_bound (earlySubset hit hinj hm) (leftTime hit hinj hm)
    (rightTime hit hinj hm) t hm hm5 (early_nonempty hit hinj hm)
    (early_proper hit hinj hm) (selected_times_strict hit hinj hm) i

theorem actual_variation {n m : ℕ} (hit : Fin m → Fin n)
    (hinj : Function.Injective hit) (hm : 2 ≤ m) (hm5 : m ≤ 5) (N : ℕ) :
    (∑ t ∈ Finset.range N, sqNorm (fun j =>
      actualDualAt hit hinj hm (t + 1) j - actualDualAt hit hinj hm t j)) ≤
      25 / ((ActualGap.selectedGap (hitSet hit hinj) hm : ℕ) : ℝ) := by
  exact dualAt_variation (earlySubset hit hinj hm) (leftTime hit hinj hm)
    (rightTime hit hinj hm) N hm hm5 (early_nonempty hit hinj hm)
    (early_proper hit hinj hm) (selected_times_strict hit hinj hm)

#print axioms consecutive_no_interior
#print axioms early_nonempty
#print axioms early_proper
#print axioms actual_hit_pairing
#print axioms actual_sqNorm
#print axioms actual_all_label_pairing_bound
#print axioms actual_variation

end
end Gate145.HitAssembly

/-!
Gate145: fixed label embeddings and actual inverse-permutation positions.
Compile after ActualHitGeometry.lean. No original instance label or simplex
offset depends on the permutation: only the dual table does.

The optional block assembly uses an explicit dependent coordinate set and
finite sums of squares. It does not assume a global Euclidean norm or an
isometry, and does not claim that block embeddings form a partition merely
because each embedding is injective. Those interfaces remain separate.
-/

namespace Gate145.PermutationHitBridge

open scoped BigOperators
open PermutationMarginal SimplexDual SimplexClock HitAssembly

noncomputable section

def permHit {n m : ℕ} (labels : Fin m → Fin n) (g : Equiv.Perm (Fin n)) :
    Fin m → Fin n := fun i => g.symm (labels i)

theorem permHit_injective {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n)) :
    Function.Injective (permHit labels g) :=
  g.symm.injective.comp hinj

theorem hit_has_fixed_label {n m : ℕ} (labels : Fin m → Fin n)
    (g : Equiv.Perm (Fin n)) (i : Fin m) :
    g (permHit labels g i) = labels i := by
  exact g.apply_symm_apply (labels i)

/-- Exact identification of the constructed hit-set with the inverse action
on the fixed original block. This is equality of actual cardinality-m sets. -/
theorem hitSet_inverse {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n)) :
    hitSet (permHit labels g) (permHit_injective labels hinj g) =
      g⁻¹ • hitSet labels hinj := by
  apply Subtype.ext
  ext x
  rw [mem_inverse_positions m (hitSet labels hinj) g x]
  change x ∈ Finset.univ.image (permHit labels g) ↔
    g x ∈ Finset.univ.image labels
  constructor
  · intro hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
    have hh := congrArg g heq
    simpa only [hit_has_fixed_label] using hh
  · intro hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
    have hh := congrArg g.symm heq
    simpa only [Equiv.symm_apply_apply, permHit] using hh

def permutedDualAt {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n))
    (hm : 2 ≤ m) (t : ℕ) : Fin m → ℝ :=
  actualDualAt (permHit labels g) (permHit_injective labels hinj g) hm t

theorem permuted_hit_pairing {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n))
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (i : Fin m) :
    dot (permutedDualAt labels hinj g hm (g.symm (labels i)).val)
      (xi (amplitude m) i) = 1 := by
  exact actual_hit_pairing (permHit labels g) (permHit_injective labels hinj g)
    hm hm5 i

/-- Position-to-label orientation is explicit: if g(t)=labels(i), the
unchanged offset xi_i has pairing1 with the table at position t. -/
theorem current_pairing {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n))
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (t : Fin n) (i : Fin m)
    (hcurrent : g t = labels i) :
    dot (permutedDualAt labels hinj g hm t.val) (xi (amplitude m) i) = 1 := by
  have ht : g.symm (labels i) = t := by
    rw [← hcurrent, g.symm_apply_apply]
  simpa only [ht] using permuted_hit_pairing labels hinj g hm hm5 i

theorem permuted_sqNorm {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n))
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (t : ℕ) :
    sqNorm (permutedDualAt labels hinj g hm t) ≤ 16 := by
  exact actual_sqNorm (permHit labels g) (permHit_injective labels hinj g) hm hm5 t

theorem permuted_all_label_pairing_bound {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n))
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (t : ℕ) (i : Fin m) :
    |dot (permutedDualAt labels hinj g hm t) (xi (amplitude m) i)| ≤ 4 := by
  exact actual_all_label_pairing_bound (permHit labels g)
    (permHit_injective labels hinj g) hm hm5 t i

/-- The variation denominator is now exactly the selected gap of the
inverse-permuted fixed block, matching the actual gap-expectation source. -/
theorem permuted_variation {n m : ℕ} (labels : Fin m → Fin n)
    (hinj : Function.Injective labels) (g : Equiv.Perm (Fin n))
    (hm : 2 ≤ m) (hm5 : m ≤ 5) (N : ℕ) :
    (∑ t ∈ Finset.range N, sqNorm (fun j =>
      permutedDualAt labels hinj g hm (t + 1) j -
        permutedDualAt labels hinj g hm t j)) ≤
      25 / ((ActualGap.selectedGap (g⁻¹ • hitSet labels hinj) hm : ℕ) : ℝ) := by
  have hv := actual_variation (permHit labels g)
    (permHit_injective labels hinj g) hm hm5 N
  rw [hitSet_inverse labels hinj g] at hv
  exact hv

/-- Actual finite dependent coordinates for a family of possibly different
block sizes. No ambient norm or isometry is introduced by this definition. -/
def globalDualAt {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (g : Equiv.Perm (Fin n)) (hm : ∀ b, 2 ≤ size b) (t : ℕ) :
    (Σ b : Fin r, Fin (size b)) → ℝ :=
  fun x => permutedDualAt (labels x.1) (hinj x.1) g (hm x.1) t x.2

theorem global_squared_bound {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (g : Equiv.Perm (Fin n)) (hm : ∀ b, 2 ≤ size b)
    (hm5 : ∀ b, size b ≤ 5) (t : ℕ) :
    (∑ x : (Σ b : Fin r, Fin (size b)), globalDualAt size labels hinj g hm t x ^ 2) ≤
      16 * (r : ℝ) := by
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun b hb =>
    permuted_sqNorm (labels b) (hinj b) g (hm b) (hm5 b) t)
  rw [Fintype.sum_sigma]
  simpa only [globalDualAt, sqNorm_eq_sum_sq, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using hb

theorem global_variation_bound {n r : ℕ} (size : Fin r → ℕ)
    (labels : ∀ b, Fin (size b) → Fin n)
    (hinj : ∀ b, Function.Injective (labels b))
    (g : Equiv.Perm (Fin n)) (hm : ∀ b, 2 ≤ size b)
    (hm5 : ∀ b, size b ≤ 5) (N : ℕ) :
    (∑ t ∈ Finset.range N, ∑ x : (Σ b : Fin r, Fin (size b)),
      (globalDualAt size labels hinj g hm (t + 1) x -
        globalDualAt size labels hinj g hm t x) ^ 2) ≤
      25 * ∑ b : Fin r,
        (1 : ℝ) / ((ActualGap.selectedGap (g⁻¹ • hitSet (labels b) (hinj b))
          (hm b) : ℕ) : ℝ) := by
  calc
    _ = ∑ b : Fin r, ∑ t ∈ Finset.range N,
        sqNorm (fun j => permutedDualAt (labels b) (hinj b) g (hm b) (t + 1) j -
          permutedDualAt (labels b) (hinj b) g (hm b) t j) := by
      simp only [Fintype.sum_sigma, globalDualAt, sqNorm_eq_sum_sq]
      rw [Finset.sum_comm]
    _ ≤ ∑ b : Fin r,
        25 / ((ActualGap.selectedGap (g⁻¹ • hitSet (labels b) (hinj b))
          (hm b) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      exact permuted_variation (labels b) (hinj b) g (hm b) (hm5 b) N
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring

#print axioms hitSet_inverse
#print axioms current_pairing
#print axioms permuted_sqNorm
#print axioms permuted_all_label_pairing_bound
#print axioms permuted_variation
#print axioms global_squared_bound
#print axioms global_variation_bound

end
end Gate145.PermutationHitBridge