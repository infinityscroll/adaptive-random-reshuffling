import ActualFiniteBankModel



/-!
Gate146: instantiate the SAME finite-bank hgeo and expectation using the
constructed all-n fixed labeled partition. Compile after LabeledBlocks,
FiniteBankInterval, and accepted Gate145 BankConcrete dependencies.
Root alone runs Lean; no new target mean bound is assumed.
-/
namespace Gate146.FixedPartitionBank
open scoped BigOperators
open EuclideanCoordinates LabeledBlocks EpochInterval FiniteBankInterval
open Gate145.PermutationMarginal Gate145.HitAssembly
noncomputable section

theorem partition_size_three {n : ℕ} (P : Partition n) (hn : 3 ≤ n)
    (j : Fin P.count) : 3 ≤ P.size j := by
  have hlo := P.size_lower j
  have hne : P.size j ≠ 2 := by
    intro h
    have he := (P.pair_iff j).1 h
    omega
  omega

theorem partition_three_count {n : ℕ} (P : Partition n) (hn : 3 ≤ n) :
    3 * P.count ≤ n := by
  have hc := P.large_count hn
  have hd := Nat.mod_add_div n 3
  omega

theorem pair_selected_gap {m : ℕ} (s : CardSet (Fin 2) m)
    (hm : 2 ≤ m) (he : m = 2) :
    Gate145.ActualGap.selectedGap s hm = 1 := by
  subst m
  exact Gate145.BlockExpectation.two_gap_eq_one s hm

/-- A Partition 2 has exactly one actual pair, and its actual selected gap
is one under every permutation. No dependent transport of the partition
or relabeling of the instance is performed. -/
theorem partition_pair_gapSum (P : Partition 2) (g : Equiv.Perm (Fin 2)) :
    gapSum P.size (labels P) (labels_injective P) P.size_lower g = 1 := by
  have hg : ∀ j : Fin P.count,
      Gate145.ActualGap.selectedGap
        (g⁻¹ • hitSet (labels P j) (labels_injective P j)) (P.size_lower j) = 1 := by
    intro j
    exact pair_selected_gap _ (P.size_lower j) ((P.pair_iff j).2 rfl)
  unfold gapSum
  simp_rw [hg]
  simp [P.pair_count rfl]

/-- Exact actual finite bank envelope, with all fixed labels supplied by
one constructed labeled partition before any bank or policy is chosen. -/
def partitionG {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (A : ℝ) : ℝ :=
  finiteG P.size (labels P) (labels_injective P) P.size_lower bank A

theorem partition_G_mean {n : ℕ} (hn : 2 ≤ n) (P : Partition n)
    (K : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    (∑ bank : Fin K → Equiv.Perm (Fin n), partitionG P bank A) /
      (Fintype.card (Fin K → Equiv.Perm (Fin n)) : ℝ) ≤
      16 * A * (K : ℝ) * Real.sqrt (n : ℝ) := by
  by_cases htwo : n = 2
  · subst n
    let B : Equiv.Perm (Fin 2) → ℝ :=
      gapSum P.size (labels P) (labels_injective P) P.size_lower
    have hB : ∀ g, B g = 1 := fun g => partition_pair_gapSum P g
    have hnonneg : ∀ g, 0 ≤ B g := by intro g; rw [hB]; norm_num
    have hcard : (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) ≠ 0 := by positivity
    have hmean : (∑ g : Equiv.Perm (Fin 2), B g) /
        (Fintype.card (Equiv.Perm (Fin 2)) : ℝ) ≤ 4 := by
      simp_rw [hB]
      simp [hcard]
    have hr : 2 * P.count ≤ 2 := by
      have hp := P.pair_count rfl
      omega
    exact Gate145.BankExpectation.bank_G_from_actual_epoch_mean 2 K P.count B
      A hA hr hnonneg hmean
  · have hthree : 3 ≤ n := by omega
    exact actual_finite_G_mean hthree K P.size (labels P) (labels_injective P)
      P.size_lower (partition_size_three P hthree) P.size_upper
      (partition_three_count P hthree) A hA

/-- No generic size/count hypothesis remains: fixedPartition supplies the
actual all-n construction, its injective disjoint covering labels, and all
arithmetic constraints. The bank is still exactly Fin K -> Perm(Fin n). -/
theorem fixed_partition_G_mean (n : ℕ) (hn : 2 ≤ n)
    (K : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    (∑ bank : Fin K → Equiv.Perm (Fin n),
        partitionG (fixedPartition n hn) bank A) /
      (Fintype.card (Fin K → Equiv.Perm (Fin n)) : ℝ) ≤
      16 * A * (K : ℝ) * Real.sqrt (n : ℝ) :=
  partition_G_mean hn (fixedPartition n hn) K A hA

/-- The corresponding hgeo uses the identical fixed partition, table and
bank-dependent partitionG whose unconditional mean was just proved. -/
theorem fixed_partition_interval_hgeo (n : ℕ) (hn : 2 ≤ n) (K : ℕ)
    (bank : Fin K → Equiv.Perm (Fin n)) (s N : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (hN : s + N ≤ n * K) :
    let P := fixedPartition n hn
    ∀ z : ℕ → Vec (Coordinates P), (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ Finset.range N,
        test (finiteTable P.size (labels P) (labels_injective P)
          P.size_lower bank (s + k)) (z k - z (k + 1))) ≤ partitionG P bank A := by
  dsimp only
  exact actual_finite_interval_hgeo (fixedPartition n hn).size
    (labels (fixedPartition n hn)) (labels_injective (fixedPartition n hn))
    (fixedPartition n hn).size_lower (fixedPartition n hn).size_upper bank
    hn s N A hA hN

#print axioms partition_size_three
#print axioms partition_three_count
#print axioms partition_pair_gapSum
#print axioms partition_G_mean
#print axioms fixed_partition_G_mean
#print axioms fixed_partition_interval_hgeo
end
end Gate146.FixedPartitionBank

/-! The actual finite-bank sequence, on the true Euclidean fast subspace.
The generic paid-reset geometry hypotheses are derived for these fixed
offsets and tests; affine dynamics and parameter hypotheses remain separate. -/
namespace Gate146.ActualSequence
noncomputable section
open scoped BigOperators
open EuclideanCoordinates LabeledBlocks FastSpaceOffsets EpochInterval
open FiniteBankInterval LabeledDual

def currentLabel {n K : ℕ} (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (t : ℕ) : Fin n :=
  (extendBank bank (t / n)) ⟨t % n, Nat.mod_lt t hn⟩

def fastTest {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (t : ℕ) : fastSpace P.size →ₗ[ℝ] ℝ :=
  (test (finiteTable P.size (labels P) (labels_injective P)
    P.size_lower bank t)).comp (fastSpace P.size).subtype

theorem actual_current_pairing {n K : ℕ} (P : Partition n) (hn : 0 < n)
    (bank : Fin K → Equiv.Perm (Fin n)) (t : ℕ) :
    fastTest P bank t (fastXi P (currentLabel hn bank t)) = 1 := by
  exact epoch_current_pairing P (extendBank bank (t / n))
    ⟨t % n, Nat.mod_lt t hn⟩

theorem actual_all_label_bound {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (t : ℕ) (a : Fin n) :
    |fastTest P bank t (fastXi P a)| ≤ 4 :=
  epoch_all_label_pairing P (extendBank bank (t / n)) (t % n) a

theorem actual_all_vector_bound {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (t : ℕ) (v : fastSpace P.size) :
    |fastTest P bank t v| ≤ 4 * Real.sqrt (P.count : ℝ) * ‖v‖ :=
  epoch_all_vector_bound P (extendBank bank (t / n)) (t % n) v.val

/-- Every interval and every bounded auxiliary path in the actual n-r
dimensional subspace, with the SAME G used by the finite-bank expectation. -/
theorem actual_subspace_hgeo {n K : ℕ} (P : Partition n) (hn : 2 ≤ n)
    (bank : Fin K → Equiv.Perm (Fin n)) (s N : ℕ)
    (A : ℝ) (hA : 0 ≤ A) (hN : s + N ≤ n * K) :
    ∀ z : ℕ → fastSpace P.size, (∀ k ≤ N, ‖z k‖ ≤ A) →
      (∑ k ∈ Finset.range N, fastTest P bank (s + k) (z k - z (k + 1))) ≤
        finiteG P.size (labels P) (labels_injective P) P.size_lower bank A := by
  intro z hz
  have hh := actual_finite_interval_hgeo P.size (labels P) (labels_injective P)
    P.size_lower P.size_upper bank hn s N A hA hN (fun k => (z k).val) hz
  exact hh

theorem actual_G_nonneg {n K : ℕ} (P : Partition n)
    (bank : Fin K → Equiv.Perm (Fin n)) (A : ℝ) (hA : 0 ≤ A) :
    0 ≤ finiteG P.size (labels P) (labels_injective P) P.size_lower bank A := by
  unfold finiteG
  positivity

#print axioms actual_current_pairing
#print axioms actual_all_label_bound
#print axioms actual_all_vector_bound
#print axioms actual_subspace_hgeo
#print axioms actual_G_nonneg
end
end Gate146.ActualSequence