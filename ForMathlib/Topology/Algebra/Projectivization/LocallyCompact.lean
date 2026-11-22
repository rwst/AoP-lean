/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Topology.Algebra.Projectivization.SecondCountable

/-!
# Locally compact projective spaces

`ℙ K V` carries the quotient topology of the nonzero vectors. For a Hausdorff topological vector
space `V` with a separating dual over a complete, locally compact field, `ℙ K V` is locally compact
only if `V` is finite-dimensional. The affine chart `v ↦ ([v], φ v)` of a continuous linear
functional `φ` is an open embedding of `{v | φ v ≠ 0}` into `ℙ K V × K`, so a locally compact
`ℙ K V` makes a nonempty open subset of `V` locally compact, and Riesz's theorem applies.

## Main results

* `Projectivization.isOpenEmbedding_chart`: the chart `v ↦ ([v], φ v)` is an open embedding;
* `Projectivization.finiteDimensional_of_locallyCompactSpace`: if `ℙ K V` is locally compact,
  `V` is finite-dimensional.
-/

open Set Filter Topology
open scoped LinearAlgebra.Projectivization

public section

namespace Projectivization

variable {K V : Type*} [NontriviallyNormedField K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V] [ContinuousSMul K V]

omit [ContinuousSMul K V] in
/-- The chart `v ↦ ([v], φ v)` is injective: `[v] = [w]` gives `v = a • w`, and `φ v = φ w ≠ 0`
forces `a = 1`. -/
theorem chart_injective (φ : V →L[K] K) : Function.Injective (chart φ) := by
  rintro ⟨v, hv⟩ ⟨w, hw⟩ h
  simp only [chart, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨a, rfl⟩ := (mk_eq_mk_iff' K v w _ _).1 h₁
  rw [map_smul, smul_eq_mul] at h₂
  have ha : a = 1 := mul_right_cancel₀ hw (h₂.trans (one_mul _).symm)
  simp [ha]

omit [ContinuousSMul K V] in
/-- The range of the chart `v ↦ ([v], φ v)` is the product of the open set of lines on which `φ`
does not vanish and the nonzero scalars. -/
theorem range_chart (φ : V →L[K] K) :
    range (chart φ) = (mk' K '' {v | φ v.1 ≠ 0}) ×ˢ {c | c ≠ 0} := by
  ext ⟨p, c⟩
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    simp only [chart, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨⟨v, fun h0 => hv (by rw [h0, map_zero])⟩, hv, rfl⟩, hv⟩
  · rintro ⟨⟨w, hw, rfl⟩, hc⟩
    have hw' : φ w.1 ≠ 0 := hw
    have hc' : c ≠ 0 := hc
    refine ⟨⟨(c / φ w.1) • w.1, by simp [map_smul, hw', hc']⟩, ?_⟩
    simp only [chart, Prod.mk.injEq, mk'_eq_mk]
    refine ⟨(mk_eq_mk_iff' K _ _ _ _).2 ⟨c / φ w.1, rfl⟩, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hw']

omit [ContinuousSMul K V] in
theorem isOpen_range_chart [ContinuousConstSMul Kˣ V] (φ : V →L[K] K) :
    IsOpen (range (chart φ)) := by
  rw [range_chart]
  exact (isOpenMap_mk' _ (isOpen_ne_fun (φ.continuous.comp continuous_subtypeVal)
    continuous_const)).prod isOpen_ne

/-- The chart `v ↦ ([v], φ v)` is an open embedding of `{v | φ v ≠ 0}` into `ℙ K V × K`. -/
theorem isOpenEmbedding_chart (φ : V →L[K] K) : IsOpenEmbedding (chart φ) :=
  ⟨⟨isInducing_chart φ, chart_injective φ⟩, isOpen_range_chart φ⟩

/-- **A locally compact projective space has finite dimension.** If `ℙ K V` is locally compact,
then so is the open set `{v | φ v ≠ 0}` of a nonzero continuous linear functional `φ`, through
the open embedding `v ↦ ([v], φ v)`; a compact neighbourhood of one point there makes `V` locally
compact, hence finite-dimensional by Riesz's theorem. -/
theorem finiteDimensional_of_locallyCompactSpace [CompleteSpace K] [LocallyCompactSpace K]
    [IsTopologicalAddGroup V] [T2Space V] [SeparatingDual K V] [LocallyCompactSpace (ℙ K V)] :
    FiniteDimensional K V := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · infer_instance
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := K) hv₀
  have : LocallyCompactSpace {v : V // φ v ≠ 0} := (isOpenEmbedding_chart φ).locallyCompactSpace
  obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds (⟨v₀, hφ⟩ : {v : V // φ v ≠ 0})
  have hU : IsOpen {v : V | φ v ≠ 0} := isOpen_ne_fun φ.continuous continuous_const
  have : LocallyCompactSpace V :=
    (hC.image continuous_subtypeVal).locallyCompactSpace_of_mem_nhds_of_addGroup
      (hU.isOpenEmbedding_subtypeVal.image_mem_nhds.2 hCn)
  exact FiniteDimensional.of_locallyCompactSpace K

end Projectivization
