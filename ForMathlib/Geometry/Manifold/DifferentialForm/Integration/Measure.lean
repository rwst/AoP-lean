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

Conversely, the measure of a continuous top form determines the form up to a sign at each point:
in a chart both measures are Haar measure with continuous densities `|φ(∂₁, …, ∂ₖ)|`, which agree
almost everywhere and hence everywhere, and a top form is determined by its value on a basis.

* `TauCeti.RoughForm.eq_or_eq_neg_of_measure_eq`: continuous top forms with the same measure agree
  up to a sign at each point.
* `Homeomorph.measure_mpullback_eq_of_measurePreserving`: a differentiable homeomorphism that
  preserves the measure of `ψ` leaves it unchanged under pullback, `|Φ^* ψ| = |ψ|`.
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

/-! ### The measure determines the form up to sign -/

namespace TauCeti.RoughForm

variable [IsManifold I 1 M] {k : ℕ} [hk : Fact (finrank ℝ E = k)]

/-- **A top form is determined up to sign at each point by its measure.** On a manifold without
boundary, two continuous top forms `φ` and `ψ` with `|φ| = |ψ|` satisfy `ψ x = ± φ x` at every
point. In the chart at `x` both measures are Haar measure with the continuous densities
`|φ(∂₁, …, ∂ₖ)|` and `|ψ(∂₁, …, ∂ₖ)|` on the open chart target; these agree almost everywhere,
hence everywhere, and a top form is the multiple of the determinant given by its value on the
basis. The sign may change from point to point. -/
theorem eq_or_eq_neg_of_measure_eq [I.Boundaryless] {φ ψ : RoughForm I M ℝ k}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) (h : φ.measure = ψ.measure) (x : M) :
    ψ x = φ x ∨ ψ x = -φ x := by
  set b := finBasisOfFinrankEq ℝ E hk.out
  set e := extChartAt I x
  have hT : IsOpen e.target := isOpen_extChartAt_target x
  have hsrc : MeasurableSet e.source := (isOpen_extChartAt_source x).measurableSet
  have himg : e '' e.source = e.target := e.image_source_eq_target
  have hf := aemeasurable_ofReal_abs_inChartAt hφ b hsrc subset_rfl (μ := b.addHaar)
  have hg := aemeasurable_ofReal_abs_inChartAt hψ b hsrc subset_rfl (μ := b.addHaar)
  rw [himg] at hf hg
  -- The two coordinate densities define the same measure on the chart target.
  have hwd : (b.addHaar.restrict e.target).withDensity
        (fun y ↦ ENNReal.ofReal |φ.inChartAt x y b|) =
      (b.addHaar.restrict e.target).withDensity (fun y ↦ ENNReal.ofReal |ψ.inChartAt x y b|) := by
    ext A hA
    rw [withDensity_apply _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA]
    have hs : MeasurableSet (e.source ∩ e ⁻¹' A) := by
      have hm : Measurable (e.source.domRestrict e) :=
        (continuousOn_extChartAt x).domRestrict.measurable
      have h' := hsrc.subtype_image (hm hA)
      rwa [Set.domRestrict_eq, Set.preimage_comp, Subtype.image_preimage_coe] at h'
    have hes : e '' (e.source ∩ e ⁻¹' A) = A ∩ e.target := by
      ext y
      refine ⟨?_, fun hy ↦ ⟨e.symm y, ⟨e.map_target hy.2, ?_⟩, e.right_inv hy.2⟩⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hz.2, e.map_source hz.1⟩
      · simpa [Set.mem_preimage, e.right_inv hy.2] using hy.1
    rw [← hes, ← measure_apply_of_subset φ hs inter_subset_left, h,
      measure_apply_of_subset ψ hs inter_subset_left]
  -- Continuous densities that agree almost everywhere on an open set agree there.
  have hcont (χ : RoughForm I M ℝ k) (hχ : IsSmoothForm I 0 χ) :
      ContinuousOn (fun y ↦ ENNReal.ofReal |χ.inChartAt x y b|) e.target :=
    ENNReal.continuous_ofReal.comp_continuousOn (continuous_abs.comp_continuousOn
      ((continuous_eval_const (⇑b)).comp_continuousOn (hχ.continuousOn_inChartAt x)))
  have hx := Measure.eqOn_open_of_ae_eq ((withDensity_eq_iff_of_sigmaFinite hf hg).1 hwd) hT
    (hcont φ hφ) (hcont ψ hψ) (mem_extChartAt_target x)
  simp only at hx
  rw [ENNReal.ofReal_eq_ofReal_iff (abs_nonneg _) (abs_nonneg _)] at hx
  have hneg : (-φ).inChartAt x (e x) = -φ.inChartAt x (e x) := by
    ext v
    simp [inChartAt_apply]
  rcases abs_eq_abs.1 hx with h1 | h1
  · left
    rw [← inChartAt_chart_eq_iff (mem_extChartAt_source x)]
    ext v
    rw [ContinuousAlternatingMap.apply_eq_det_mul _ b,
      ContinuousAlternatingMap.apply_eq_det_mul _ b v, h1]
  · right
    change ψ x = (-φ) x
    rw [← inChartAt_chart_eq_iff (mem_extChartAt_source x), hneg]
    ext v
    rw [ContinuousAlternatingMap.apply_eq_det_mul _ b, ContinuousAlternatingMap.neg_apply,
      ContinuousAlternatingMap.apply_eq_det_mul _ b v, h1]
    ring

end TauCeti.RoughForm

namespace Homeomorph

open TauCeti

/-- A differentiable homeomorphism `Φ` of `M` that preserves the measure of a top form `ψ` leaves
the measure unchanged under pullback: `|Φ^* ψ| = |ψ|`. Both measures are carried to `|ψ|` by `Φ`
(`Homeomorph.measurePreserving_measure_mpullback`). -/
theorem measure_mpullback_eq_of_measurePreserving [IsManifold I 1 M] {k : ℕ}
    [Fact (finrank ℝ E = k)] (Φ : M ≃ₜ M) (hΦ : MDifferentiable I I Φ) (ψ : RoughForm I M ℝ k)
    (h : MeasurePreserving Φ ψ.measure ψ.measure) :
    (mpullback I I Φ ψ).measure = ψ.measure := by
  have h1 := (Φ.measurePreserving_measure_mpullback hΦ ψ).map_eq
  rw [← h.map_eq] at h1
  rw [← Φ.toMeasurableEquiv.map_symm_map (μ := (mpullback I I Φ ψ).measure),
    Φ.toMeasurableEquiv_coe, h1, ← Φ.toMeasurableEquiv_coe, MeasurableEquiv.map_symm_map]

end Homeomorph
