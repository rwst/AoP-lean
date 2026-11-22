/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure

/-!
# Change of variables for the measure of a top form between model spaces

TauCeti's measure `|φ|` of a top form (`TauCeti.RoughForm.measure`) is carried along a
differentiable measurable embedding `f : M → N` by `MeasurableEmbedding.map_measure_mpullback`
when `M` and `N` are modelled on the same space. This file allows different model spaces `E` and
`E'` of the same dimension `k`, such as a projective line modelled on `Fin 1 → ℂ` and the
two-sphere modelled on `EuclideanSpace ℝ (Fin 2)`.

The chartwise change of variables (`TauCeti.RoughForm.setLIntegral_ofReal_abs_inChartAt_mpullback`)
already compares the two model spaces through a continuous linear equivalence `C : E ≃ E'`. Taking
for `C` the equivalence that sends the preferred basis of `E` to that of `E'`, it carries the
preferred basis and Haar measure of `E` to those of `E'`, which are the ones the measure on `N` is
computed with. Countably many chart pieces then cover `M`, as in the case of one model space.

## Main results

* `MeasurableEmbedding.map_measure_mpullback_of_finrank_eq`: the measure of `f^* ψ` is carried to
  the restriction of the measure of `ψ` to the range of `f`.
* `Homeomorph.measurePreserving_measure_mpullback_of_finrank_eq`: a differentiable homeomorphism
  carries the measure of `Φ^* ψ` to the measure of `ψ`.
* `Homeomorph.measurePreserving_liouvilleMeasure_of_finrank_eq`: a differentiable homeomorphism
  pulling one two-form back to another carries Liouville measure to Liouville measure.
-/

public section

noncomputable section

open Module MeasureTheory Set
open scoped Manifold ContDiff

variable {E E' H H' M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [MeasurableSpace N] [BorelSpace N] [LindelofSpace M] [LindelofSpace N]

attribute [local instance] TauCeti.extChartAtMeasurableSpaceE TauCeti.extChartAtBorelSpaceE

namespace MeasurableEmbedding

open TauCeti

variable [IsManifold I 1 M] [IsManifold J 1 N] {k : ℕ} [hk : Fact (finrank ℝ E = k)]
  [hk' : Fact (finrank ℝ E' = k)] {f : M → N}

/-- The chart-local case of `MeasurableEmbedding.map_measure_mpullback_of_finrank_eq`: on a
measurable set `A` inside a chart source at `x` and mapped by `f` into a chart source at `f x`,
the measure of `f^* ψ` is the measure of `ψ` on `f '' A`. -/
theorem measure_mpullback_apply_of_subset_of_finrank_eq (hf : MeasurableEmbedding f)
    (hfd : MDifferentiable I J f) (ψ : RoughForm J N ℝ k) {x : M} {A : Set M}
    (hA : MeasurableSet A)
    (hAsub : A ⊆ (extChartAt I x).source ∩ f ⁻¹' (extChartAt J (f x)).source) :
    (mpullback I J f ψ).measure A = ψ.measure (f '' A) := by
  set b := finBasisOfFinrankEq ℝ E hk.out
  set b' := finBasisOfFinrankEq ℝ E' hk'.out
  -- The equivalence sending the preferred basis of `E` to that of `E'`.
  let C : E ≃L[ℝ] E' := (b.equiv b' (Equiv.refl _)).toContinuousLinearEquiv
  have hC : b.map C.toLinearEquiv = b' := by
    refine Basis.eq_of_apply_eq fun i ↦ ?_
    simp [C]
  rw [RoughForm.measure_apply_of_subset _ hA (hAsub.trans inter_subset_left),
    ψ.measure_apply_of_subset (hf.measurableSet_image.2 hA)
      (image_subset_iff.2 (hAsub.trans inter_subset_right)),
    ψ.setLIntegral_ofReal_abs_inChartAt_mpullback b C hf.injective.injOn (fun x _ ↦ hfd x)
      hA.isChartMeasurable hAsub b.addHaar, b.map_addHaar C, hC]

/-- **Change of variables for the measure of a top form between model spaces.** A
differentiable measurable embedding `f : M → N` between manifolds modelled on spaces of the same
dimension carries the measure of the pulled-back form `f^* ψ` to the restriction of the measure
of `ψ` to the range of `f`. No orientation is involved. -/
theorem map_measure_mpullback_of_finrank_eq (hf : MeasurableEmbedding f)
    (hfd : MDifferentiable I J f) (ψ : RoughForm J N ℝ k) :
    (mpullback I J f ψ).measure.map f = ψ.measure.restrict (range f) := by
  -- Countably many open sets `V x`, each mapped by `f` into a chart source at `f x`, cover `M`.
  -- Their images, together with the complement of the range of `f`, cover `N`.
  set V : M → Set M := fun x ↦ (extChartAt I x).source ∩ f ⁻¹' (extChartAt J (f x)).source
  have hV (x : M) : IsOpen (V x) :=
    (isOpen_extChartAt_source x).inter ((isOpen_extChartAt_source _).preimage hfd.continuous)
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover V fun x ↦
    (hV x).mem_nhds ⟨mem_extChartAt_source x, mem_extChartAt_source (f x)⟩
  set U : Option M → Set N := fun o ↦ o.elim (range f)ᶜ fun x ↦ f '' V x
  refine Measure.ext_of_biUnion_eq_univ (S := insert none (some '' t)) (s := U)
    ((ht.image _).insert _) (eq_univ_of_forall fun y ↦ ?_) ?_
  · by_cases hy : y ∈ range f
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcover.symm ▸ mem_univ x : x ∈ ⋃ z ∈ t, V z)
      exact mem_iUnion₂.2 ⟨some z, mem_insert_of_mem _ (mem_image_of_mem _ hz),
        mem_image_of_mem f hxz⟩
    · exact mem_iUnion₂.2 ⟨none, mem_insert _ _, hy⟩
  rintro (_ | z) -
  · -- Off the range of `f`, both measures vanish.
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs, hf.map_apply,
      Measure.restrict_apply' hf.measurableSet_range]
    simp [U, inter_assoc]
  simp only [U, Option.elim_some]
  ext s hs
  -- Both sides are the measure of the chart piece `f ⁻¹' s ∩ V z` and of its image.
  have hrange : s ∩ f '' V z ⊆ range f := inter_subset_right.trans (image_subset_range f _)
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, hf.map_apply,
    Measure.restrict_apply' hf.measurableSet_range, inter_eq_left.2 hrange, preimage_inter,
    preimage_image_eq _ hf.injective, ← image_preimage_inter]
  exact measure_mpullback_apply_of_subset_of_finrank_eq hf hfd ψ
    ((hf.measurable hs).inter (hV z).measurableSet) inter_subset_right

end MeasurableEmbedding

namespace Homeomorph

open TauCeti

/-- **Change of variables for the measure of a top form between model spaces.** A
differentiable homeomorphism `Φ : M → N` between manifolds modelled on spaces of the same
dimension carries the measure of the pulled-back form `Φ^* ψ` to the measure of `ψ`. -/
theorem measurePreserving_measure_mpullback_of_finrank_eq [IsManifold I 1 M] [IsManifold J 1 N]
    {k : ℕ} [Fact (finrank ℝ E = k)] [Fact (finrank ℝ E' = k)] (Φ : M ≃ₜ N)
    (hΦ : MDifferentiable I J Φ) (ψ : RoughForm J N ℝ k) :
    MeasurePreserving Φ (mpullback I J Φ ψ).measure ψ.measure :=
  ⟨Φ.measurable, by
    rw [Φ.measurableEmbedding.map_measure_mpullback_of_finrank_eq hΦ, Φ.range_coe,
      Measure.restrict_univ]⟩

/-- **Maps pulling back the two-form preserve the Liouville measure, between model spaces.** A
differentiable homeomorphism `Φ : M → N` between manifolds modelled on spaces of the same
dimension `2 n`, with `Φ^* τ = σ`, carries the Liouville measure of `σ` to that of `τ`. -/
theorem measurePreserving_liouvilleMeasure_of_finrank_eq [IsManifold I ∞ M] [IsManifold J ∞ N]
    {n : ℕ} [Fact (finrank ℝ E = 2 * n)] [Fact (finrank ℝ E' = 2 * n)]
    {σ : SmoothTwoForm I M} {τ : SmoothTwoForm J N} (Φ : M ≃ₜ N) (hΦ : MDifferentiable I J Φ)
    (h : mpullback I J Φ τ.val = σ.val) :
    MeasurePreserving Φ (σ.liouvilleMeasure n) (τ.liouvilleMeasure n) := by
  rw [SmoothTwoForm.liouvilleMeasure_def, SmoothTwoForm.liouvilleMeasure_def,
    ← SmoothTwoForm.mpullback_volumeForm h]
  exact Φ.measurePreserving_measure_mpullback_of_finrank_eq hΦ _

end Homeomorph
