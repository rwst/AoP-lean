/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

import Mathlib.MeasureTheory.Measure.Basic

/-!
# Disjoint sequences of sets of finite positive measure

A measure `μ` *has a disjoint sequence* if there are pairwise disjoint measurable sets `Aₙ`,
`n ∈ ℕ`, with `0 < μ Aₙ < ∞`. This is the measure-theoretic form of `L¹(μ)` being
infinite-dimensional. Without a disjoint sequence, the finite part of `μ` is small: one set of
finite measure contains almost all of every set of finite measure, and the positive values of
`μ` are bounded away from `0`.

## Main definitions

* `MeasureTheory.Measure.HasDisjointSeq`: `μ` has a disjoint sequence.
* `MeasureTheory.Measure.IsAtomSet`: a measurable set of finite positive measure all of whose
  measurable subsets have measure `0` or full measure.

## Main statements

* `MeasureTheory.Measure.hasDisjointSeq_of_forall_exists`: a construction that can always be
  continued by a new disjoint set of finite positive measure gives a disjoint sequence.
* `MeasureTheory.Measure.exists_isAtomSet_subset`: without a disjoint sequence, every set of
  finite positive measure contains an atom set.
* `MeasureTheory.Measure.exists_measure_sdiff_eq_zero`: without a disjoint sequence, there is a
  set `U` of finite measure with `μ (E \ U) = 0` for every `E` of finite measure.
* `MeasureTheory.Measure.exists_le_measure`: without a disjoint sequence, the positive values of
  `μ` are bounded below by some `c ≠ 0`.
* `MeasureTheory.Measure.hasDisjointSeq_iff`: `μ` has a disjoint sequence iff it has sets of
  arbitrarily large finite measure or sets of arbitrarily small positive measure.
-/

@[expose] public section

open Set Function
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable (μ) in
/-- `μ` has a disjoint sequence: pairwise disjoint measurable sets `Aₙ`, `n ∈ ℕ`, with
`0 < μ Aₙ < ∞`. -/
def HasDisjointSeq : Prop :=
  ∃ A : ℕ → Set α, Pairwise (Disjoint on A) ∧ ∀ n, MeasurableSet (A n) ∧ μ (A n) ≠ 0 ∧ μ (A n) ≠ ∞

variable (μ) in
/-- An atom set of `μ`: a measurable set of finite positive measure whose measurable subsets
have measure `0` or `μ A`. -/
def IsAtomSet (A : Set α) : Prop :=
  MeasurableSet A ∧ μ A ≠ 0 ∧ μ A ≠ ∞ ∧ ∀ B ⊆ A, MeasurableSet B → μ B = 0 ∨ μ B = μ A

/-- If, starting from `∅`, every stage `U` of a construction can be continued by a measurable
set `D` of finite positive measure disjoint from `U`, then `μ` has a disjoint sequence. -/
theorem hasDisjointSeq_of_forall_exists {P : Set α → Prop} (h0 : P ∅)
    (h : ∀ U, P U → ∃ D, MeasurableSet D ∧ μ D ≠ 0 ∧ μ D ≠ ∞ ∧ Disjoint D U ∧ P (U ∪ D)) :
    HasDisjointSeq μ := by
  choose! D hDm hD0 hDtop hDU hP using h
  let U : ℕ → Set α := fun n => Nat.rec (motive := fun _ => Set α) ∅ (fun _ V => V ∪ D V) n
  have hU : ∀ n, P (U n) := fun n => Nat.rec h0 (fun n ih => hP _ ih) n
  have hmono : Monotone U := monotone_nat_of_le_succ fun n => subset_union_left
  refine ⟨fun n => D (U n), fun i j hij => ?_,
    fun n => ⟨hDm _ (hU n), hD0 _ (hU n), hDtop _ (hU n)⟩⟩
  wlog hlt : i < j generalizing i j
  · exact (this j i hij.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)).symm
  exact (hDU _ (hU j)).symm.mono_left (subset_union_right.trans (hmono (Nat.succ_le_of_lt hlt)))

/-- Without a disjoint sequence, every set of finite positive measure contains an atom set. -/
theorem exists_isAtomSet_subset (h : ¬ HasDisjointSeq μ) {E : Set α} (hE : MeasurableSet E)
    (h0 : μ E ≠ 0) (htop : μ E ≠ ∞) : ∃ A ⊆ E, IsAtomSet μ A := by
  by_contra! hno
  refine h (hasDisjointSeq_of_forall_exists
    (P := fun U => MeasurableSet U ∧ U ⊆ E ∧ μ (E \ U) ≠ 0) ⟨.empty, empty_subset _, by simpa⟩ ?_)
  rintro U ⟨hUm, hUE, hU0⟩
  have hFtop : μ (E \ U) ≠ ∞ := ne_top_of_le_ne_top htop (measure_mono sdiff_subset)
  have hna := hno (E \ U) sdiff_subset
  simp only [IsAtomSet, not_and, not_forall, not_or] at hna
  obtain ⟨B, hBF, hBm, hB0, hBF'⟩ := hna (hE.diff hUm) hU0 hFtop
  have hBtop : μ B ≠ ∞ := ne_top_of_le_ne_top hFtop (measure_mono hBF)
  have hlt : μ B < μ (E \ U) := lt_of_le_of_ne (measure_mono hBF) hBF'
  refine ⟨B, hBm, hB0, hBtop, disjoint_sdiff_left.mono_left hBF,
    hUm.union hBm, union_subset hUE (hBF.trans sdiff_subset), ?_⟩
  rw [← sdiff_sdiff, measure_sdiff hBF hBm.nullMeasurableSet hBtop]
  exact (tsub_pos_of_lt hlt).ne'

/-- Without a disjoint sequence, one set `U` of finite measure contains almost all of every set
of finite measure. -/
theorem exists_measure_sdiff_eq_zero (h : ¬ HasDisjointSeq μ) :
    ∃ U, MeasurableSet U ∧ μ U ≠ ∞ ∧ ∀ E, MeasurableSet E → μ E ≠ ∞ → μ (E \ U) = 0 := by
  by_contra! hno
  refine h (hasDisjointSeq_of_forall_exists (P := fun U => MeasurableSet U ∧ μ U ≠ ∞)
    ⟨.empty, by simp⟩ ?_)
  rintro U ⟨hUm, hUtop⟩
  obtain ⟨E, hEm, hEtop, hE0⟩ := hno U hUm hUtop
  have hDtop : μ (E \ U) ≠ ∞ := ne_top_of_le_ne_top hEtop (measure_mono sdiff_subset)
  exact ⟨E \ U, hEm.diff hUm, hE0, hDtop, disjoint_sdiff_left, hUm.union (hEm.diff hUm),
    (measure_union_lt_top hUtop.lt_top hDtop.lt_top).ne⟩

/-- Two atom sets of different measures meet in a null set. -/
lemma IsAtomSet.measure_inter_eq_zero {A B : Set α} (hA : IsAtomSet μ A) (hB : IsAtomSet μ B)
    (hne : μ A ≠ μ B) : μ (A ∩ B) = 0 := by
  rcases hA.2.2.2 _ inter_subset_left (hA.1.inter hB.1) with h | h
  · exact h
  rcases hB.2.2.2 _ inter_subset_right (hA.1.inter hB.1) with h' | h'
  · exact h'
  exact absurd (h.symm.trans h') hne

/-- Without a disjoint sequence, the positive values of `μ` are bounded below. Otherwise there
are atom sets `Aₙ` of strictly decreasing measures; they meet in null sets, and
`Aₙ \ ⋃_{k<n} Aₖ` is a disjoint sequence. -/
theorem exists_le_measure (h : ¬ HasDisjointSeq μ) :
    ∃ c ≠ 0, ∀ A, MeasurableSet A → μ A ≠ 0 → c ≤ μ A := by
  by_contra! hno
  have hat : ∀ c : ℝ≥0∞, c ≠ 0 → ∃ A, IsAtomSet μ A ∧ μ A < c := by
    intro c hc
    obtain ⟨S, hSm, hS0, hSc⟩ := hno c hc
    obtain ⟨A, hAS, hA⟩ := exists_isAtomSet_subset h hSm hS0 (ne_top_of_lt hSc)
    exact ⟨A, hA, (measure_mono hAS).trans_lt hSc⟩
  choose! f hf hfc using hat
  let A : ℕ → Set α := fun n => Nat.rec (motive := fun _ => Set α) (f 1) (fun _ B => f (μ B)) n
  have hA : ∀ n, IsAtomSet μ (A n) := fun n =>
    Nat.rec (hf 1 one_ne_zero) (fun n ih => hf _ ih.2.1) n
  have hanti : StrictAnti fun n => μ (A n) :=
    strictAnti_nat_of_succ_lt fun n => hfc _ (hA n).2.1
  refine h ⟨fun n => A n \ ⋃ k ∈ Finset.range n, A k, fun i j hij => ?_, fun n => ⟨?_, ?_, ?_⟩⟩
  · wlog hlt : i < j generalizing i j
    · exact (this j i hij.symm (lt_of_le_of_ne (not_lt.1 hlt) hij.symm)).symm
    refine disjoint_sdiff_left.symm.mono_left ?_
    exact sdiff_subset.trans (subset_biUnion_of_mem (u := A) (Finset.mem_coe.2
      (Finset.mem_range.2 hlt)))
  · exact (hA n).1.diff (Finset.measurableSet_biUnion _ fun k _ => (hA k).1)
  · rw [measure_sdiff_null']
    · exact (hA n).2.1
    rw [inter_iUnion₂]
    refine (measure_biUnion_null_iff (Finset.range n).countable_toSet).2 fun k hk => ?_
    exact (hA n).measure_inter_eq_zero (hA k)
      (hanti (Finset.mem_range.1 (Finset.mem_coe.1 hk))).ne
  · exact ne_top_of_le_ne_top (hA n).2.2.1 (measure_mono sdiff_subset)

/-- A disjoint sequence gives sets of arbitrarily large finite measure (finite unions of its
sets) or sets of arbitrarily small positive measure (its sets themselves). -/
theorem HasDisjointSeq.large_or_small (h : HasDisjointSeq μ) :
    (∀ M ≠ ∞, ∃ V, MeasurableSet V ∧ M < μ V ∧ μ V ≠ ∞) ∨
      ∀ c ≠ 0, ∃ V, MeasurableSet V ∧ μ V ≠ 0 ∧ μ V < c := by
  obtain ⟨A, hdisj, hA⟩ := h
  by_cases hs : ∀ c ≠ 0, ∃ n, μ (A n) < c
  · exact Or.inr fun c hc => by
      obtain ⟨n, hn⟩ := hs c hc
      exact ⟨A n, (hA n).1, (hA n).2.1, hn⟩
  push Not at hs
  obtain ⟨c, hc, hle⟩ := hs
  refine Or.inl fun M hM => ?_
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hc hM
  have hm : ∀ k ∈ Finset.range N, MeasurableSet (A k) := fun k _ => (hA k).1
  have hμ : μ (⋃ k ∈ Finset.range N, A k) = ∑ k ∈ Finset.range N, μ (A k) :=
    measure_biUnion_finset (fun i _ j _ hij => hdisj hij) hm
  refine ⟨⋃ k ∈ Finset.range N, A k, Finset.measurableSet_biUnion _ hm, ?_, ?_⟩
  · rw [hμ]
    refine hN.trans_le ?_
    simpa using Finset.card_nsmul_le_sum (Finset.range N) (fun k => μ (A k)) c
      fun k _ => hle k
  · rw [hμ]
    exact ENNReal.sum_ne_top.2 fun k _ => (hA k).2.2

/-- `μ` has a disjoint sequence iff it has sets of arbitrarily large finite measure or sets of
arbitrarily small positive measure. -/
theorem hasDisjointSeq_iff :
    HasDisjointSeq μ ↔ (∀ M ≠ ∞, ∃ V, MeasurableSet V ∧ M < μ V ∧ μ V ≠ ∞) ∨
      ∀ c ≠ 0, ∃ V, MeasurableSet V ∧ μ V ≠ 0 ∧ μ V < c := by
  refine ⟨HasDisjointSeq.large_or_small, fun hls => ?_⟩
  by_contra h
  rcases hls with hl | hs
  · obtain ⟨U, hUm, hUtop, hU⟩ := exists_measure_sdiff_eq_zero h
    obtain ⟨V, hVm, hlt, hVtop⟩ := hl _ hUtop
    have := measure_inter_add_sdiff V hUm (μ := μ)
    rw [hU V hVm hVtop, add_zero] at this
    exact (this ▸ hlt).not_ge (measure_mono inter_subset_right)
  · obtain ⟨c, hc, hle⟩ := exists_le_measure h
    obtain ⟨V, hVm, hV0, hVc⟩ := hs c hc
    exact (hle V hVm hV0).not_gt hVc

end MeasureTheory.Measure
