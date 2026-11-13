/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.PurePointSpectrum
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.BoundedSelfAdjointData

/-!
# Eigenprojections are the spectral projections of points

## i. Overview

Let `μ_S` be the spectral measure of a bounded self-adjoint operator `X`
(PhyslibAlpha's `boundedSelfAdjointSpectralMeasure`), and `spectralMeasureProj hX S` the projection
`μ_S(S)` as a bounded operator. Then `μ_S({a})` is the orthogonal projection onto the eigenspace
`ker(X - a)` (`spectralMeasureProj_singleton`).

The spectral measure is supported in some `[-C, C]`, so `X - a` is the bounded spectral integral
of `f(r) = 1_{[-C, C]}(r) r - a`, and `‖(X - a) v‖² = ∫ |f|² dν_v` with `ν_v(S) = ‖μ_S(S) v‖²`.
* If `v = μ_S({a}) u`, then `ν_v` lives on `{a}`, where `f = 0`; so `X v = a v`.
* If `X v = a v`, then `f = 0` `ν_v`-almost everywhere, so `ν_v` lives on `{a}` and
  `μ_S({a}ᶜ) v = 0`, that is, `μ_S({a}) v = v`.

Hence pure point spectrum (`HasPurePointSpectrum`) means `∑ₐ μ_S({a}) = 1` strongly, and then
`X = ∑ₐ a μ_S({a})` is an eigendecomposition (`isEigenDecomposition_spectralMeasureProj`).

## ii. Key results

- `QuantumMechanics.spectralMeasureProj`: the spectral projection `μ_S(S)` as a bounded operator.
- `QuantumMechanics.spectralMeasureProj_singleton`: `μ_S({a}) = eigenproj X a`.
- `QuantumMechanics.hasPurePointSpectrum_iff_hasSum_spectralMeasureProj`: pure point spectrum iff
  the spectral measure is atomic, `∑ₐ μ_S({a}) = 1` strongly.
- `QuantumMechanics.isEigenDecomposition_spectralMeasureProj`: `X = ∑ₐ a μ_S({a})`.
- `QuantumMechanics.IsEigenDecomposition.spectralMeasureProj_singleton_eq`: in every
  eigendecomposition `X = ∑ᵢ xᵢ Pᵢ`, `Pᵢ = μ_S({xᵢ})`.

## iii. Table of contents

- A. The spectral projections
- B. `X - a` as a spectral integral
- C. Points of the spectral measure
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open MeasureTheory Set Filter
open ProbabilisticTheory.QuantumMechanics (boundedSelfAdjointSpectralMeasure
  exists_boundedSelfAdjointSpectralSupport boundedSelfAdjointSpectralMeasure_reconstruction
  WOTSpectralMeasure)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {X : E →L[ℂ] E}

/-! ## A. The spectral projections -/

/-- The spectral projection `μ_S(S)` of a bounded self-adjoint `X`, as a bounded operator. -/
def spectralMeasureProj (hX : IsSelfAdjoint X) (S : Set ℝ) : E →L[ℂ] E :=
  ContinuousLinearMapWOT.toCLM (boundedSelfAdjointSpectralMeasure X hX S)

lemma spectralMeasureProj_apply (hX : IsSelfAdjoint X) (S : Set ℝ) (v : E) :
    spectralMeasureProj hX S v = boundedSelfAdjointSpectralMeasure X hX S v :=
  rfl

lemma isStarProjection_spectralMeasureProj (hX : IsSelfAdjoint X) (S : Set ℝ) :
    IsStarProjection (spectralMeasureProj hX S) where
  isIdempotentElem := by
    ext v
    have h := congrArg (fun A : E →WOT[ℂ] E => A v)
      ((boundedSelfAdjointSpectralMeasure X hX).comp_self S)
    exact h
  isSelfAdjoint :=
    congrArg ContinuousLinearMapWOT.toCLM
      ((boundedSelfAdjointSpectralMeasure X hX).isStarProjection S).isSelfAdjoint

/-! ## B. `X - a` as a spectral integral -/

section Integral

variable (hX : IsSelfAdjoint X) {C : ℝ}
  (hC : ProbabilisticTheory.QuantumMechanics.HasBoundedSpectralSupport
    (boundedSelfAdjointSpectralMeasure X hX) C)
include hC

/-- The spectral measure vanishes off `[-C, C]`. -/
lemma spectralMeasure_inter_compl_Icc {S : Set ℝ} (hS : MeasurableSet S) :
    boundedSelfAdjointSpectralMeasure X hX (S ∩ (Icc (-C) C)ᶜ) = 0 :=
  hC.2 _ (hS.inter measurableSet_Icc.compl) (disjoint_compl_left.mono_left inter_subset_right)

lemma spectralMeasure_inter_Icc {S : Set ℝ} (hS : MeasurableSet S) :
    boundedSelfAdjointSpectralMeasure X hX (S ∩ Icc (-C) C) =
      boundedSelfAdjointSpectralMeasure X hX S := by
  set I := Icc (-C) C
  have hd : Disjoint (S ∩ I) (S ∩ Iᶜ) :=
    (disjoint_compl_right (a := I)).mono inter_subset_right inter_subset_right
  have h := (boundedSelfAdjointSpectralMeasure X hX).toVectorMeasure.of_union hd
    (hS.inter measurableSet_Icc) (hS.inter measurableSet_Icc.compl)
  rw [inter_union_compl] at h
  change boundedSelfAdjointSpectralMeasure X hX S = boundedSelfAdjointSpectralMeasure X hX (S ∩ I) +
    boundedSelfAdjointSpectralMeasure X hX (S ∩ Iᶜ) at h
  rw [h, spectralMeasure_inter_compl_Icc hX hC hS, add_zero]

lemma diagonalMeasure_compl_Icc (v : E) :
    (boundedSelfAdjointSpectralMeasure X hX).diagonalMeasure v (Icc (-C) C)ᶜ = 0 := by
  rw [WOTSpectralMeasure.diagonalMeasure_apply_eq_norm_sq _ _ _ measurableSet_Icc.compl]
  have h := spectralMeasure_inter_compl_Icc hX hC MeasurableSet.univ
  rw [univ_inter] at h
  simp [h]

/-- The truncated identity `1_{[-C, C]}(r) r`. -/
def truncId (C : ℝ) : ℝ → ℂ := (Icc (-C) C).indicator fun r => (r : ℂ)

omit hC in
lemma measurable_truncId (C : ℝ) : Measurable (truncId C) :=
  Complex.measurable_ofReal.indicator measurableSet_Icc

omit hC in
lemma norm_truncId_le {C : ℝ} (hC : 0 ≤ C) (r : ℝ) : ‖truncId C r‖ ≤ C := by
  by_cases hr : r ∈ Icc (-C) C
  · rw [truncId, indicator_of_mem hr, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr hr
  · rw [truncId, indicator_of_notMem hr, norm_zero]
    exact hC

/-- `X` is the bounded spectral integral of the truncated identity. -/
lemma toCLM_boundedIntegral_truncId :
    ContinuousLinearMapWOT.toCLM ((boundedSelfAdjointSpectralMeasure X hX).boundedIntegral
      (truncId C) (measurable_truncId C) ⟨C, norm_truncId_le hC.1⟩) = X := by
  set μ := boundedSelfAdjointSpectralMeasure X hX
  ext x
  refine ext_inner_left ℂ fun y => ?_
  change ⟪y, μ.boundedIntegral (truncId C) _ _ x⟫_ℂ = _
  rw [μ.boundedIntegral_inner _ _ x y (μ.scalarMeasure_isFiniteVariation x y), truncId,
    VectorMeasure.integral_indicator measurableSet_Icc,
    ← boundedSelfAdjointSpectralMeasure_reconstruction X hX x y]
  have hres : (μ.scalarMeasure x y).restrict (Icc (-C) C) = μ.scalarMeasure x y := by
    refine VectorMeasure.ext fun j hj => ?_
    rw [VectorMeasure.restrict_apply _ measurableSet_Icc hj,
      WOTSpectralMeasure.scalarMeasure_apply, WOTSpectralMeasure.scalarMeasure_apply,
      spectralMeasure_inter_Icc hX hC hj]
  unfold WOTSpectralMeasure.complexWeakIntegral
  exact congrArg (fun m : ComplexMeasure ℝ => ∫ᵛ z : ℝ, (z : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ
    (E := ℂ); m]) hres

/-- `‖(X - a) v‖² = ∫ |1_{[-C, C]}(r) r - a|² dν_v`. -/
lemma ofReal_norm_sub_smul_sq (a : ℝ) (v : E) :
    ENNReal.ofReal (‖X v - (a : ℂ) • v‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal (‖truncId C r - a‖ ^ 2)
        ∂(boundedSelfAdjointSpectralMeasure X hX).diagonalMeasure v := by
  set μ := boundedSelfAdjointSpectralMeasure X hX
  have hb : ∃ D, ∀ r, ‖(fun _ : ℝ => (a : ℂ)) r‖ ≤ D := ⟨‖(a : ℂ)‖, fun _ => le_rfl⟩
  have h := μ.boundedIntegral_norm_sq ((measurable_truncId C).sub measurable_const)
    (by
      refine ⟨C + ‖(a : ℂ)‖, fun r => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add (norm_truncId_le hC.1 r) le_rfl)) v
  have hsub := μ.boundedIntegral_sub (measurable_truncId C) measurable_const
    ⟨C, norm_truncId_le hC.1⟩ hb
  have hconst := μ.boundedIntegral_const (a : ℂ)
  have hv : μ.boundedIntegral (truncId C - fun _ => (a : ℂ))
      ((measurable_truncId C).sub measurable_const) (by
        refine ⟨C + ‖(a : ℂ)‖, fun r => ?_⟩
        exact (norm_sub_le _ _).trans (add_le_add (norm_truncId_le hC.1 r) le_rfl)) v =
      X v - (a : ℂ) • v := by
    rw [hsub, hconst]
    have h1 := congrArg (fun T : E →L[ℂ] E => T v) (toCLM_boundedIntegral_truncId hX hC)
    change μ.boundedIntegral (truncId C) (measurable_truncId C) ⟨C, norm_truncId_le hC.1⟩ v -
      ((a : ℂ) • (1 : E →WOT[ℂ] E)) v = _
    rw [show μ.boundedIntegral (truncId C) (measurable_truncId C) ⟨C, norm_truncId_le hC.1⟩ v =
      X v from h1]
    rfl
  rw [hv] at h
  simpa using h

end Integral

/-! ## C. Points of the spectral measure -/

section Points

variable (hX : IsSelfAdjoint X)

/-- On the range of `μ_S({a})`, `X` acts as `a`. -/
lemma apply_spectralMeasureProj_singleton (a : ℝ) (u : E) :
    X (spectralMeasureProj hX {a} u) = (a : ℂ) • spectralMeasureProj hX {a} u := by
  obtain ⟨C, hC⟩ := exists_boundedSelfAdjointSpectralSupport X hX
  set μ := boundedSelfAdjointSpectralMeasure X hX
  set w := spectralMeasureProj hX {a} u
  -- `ν_w` lives on `{a}`
  have hνa : μ.diagonalMeasure w {a}ᶜ = 0 := by
    rw [WOTSpectralMeasure.diagonalMeasure_apply_eq_norm_sq _ _ _
      (measurableSet_singleton a).compl]
    have h := congrArg (fun A : E →WOT[ℂ] E => A u)
      (μ.comp_eq_of_inter (measurableSet_singleton a).compl (measurableSet_singleton a))
    simp only [compl_inter_self] at h
    change μ {a}ᶜ (μ {a} u) = μ ∅ u at h
    have h0 : μ {a}ᶜ w = 0 := by
      change μ {a}ᶜ (μ {a} u) = 0
      rw [h, μ.toVectorMeasure.empty]
      rfl
    simp [h0]
  have hae : ∀ᵐ r ∂μ.diagonalMeasure w, r = a ∧ r ∈ Icc (-C) C := by
    have h1 : ∀ᵐ r ∂μ.diagonalMeasure w, r ∈ ({a} : Set ℝ) := measure_eq_zero_iff_ae_notMem.mp
      (by simpa using hνa) |>.mono fun r hr => by simpa using hr
    have h2 : ∀ᵐ r ∂μ.diagonalMeasure w, r ∈ Icc (-C) C := measure_eq_zero_iff_ae_notMem.mp
      (diagonalMeasure_compl_Icc hX hC w) |>.mono fun r hr => by simpa using hr
    filter_upwards [h1, h2] with r hr1 hr2
    exact ⟨hr1, hr2⟩
  have h0 : ∫⁻ r, ENNReal.ofReal (‖truncId C r - a‖ ^ 2) ∂μ.diagonalMeasure w = 0 := by
    rw [lintegral_congr_ae (g := 0)]
    · simp
    filter_upwards [hae] with r ⟨hra, hrC⟩
    rw [hra] at hrC ⊢
    simp [truncId, indicator_of_mem hrC]
  have h := ofReal_norm_sub_smul_sq hX hC a w
  rw [h0, ENNReal.ofReal_eq_zero] at h
  have h' : ‖X w - (a : ℂ) • w‖ = 0 := by nlinarith [norm_nonneg (X w - (a : ℂ) • w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp h')

/-- An eigenvector for `a` is fixed by `μ_S({a})`. -/
lemma spectralMeasureProj_singleton_apply_of_apply_eq {a : ℝ} {v : E} (hv : X v = (a : ℂ) • v) :
    spectralMeasureProj hX {a} v = v := by
  obtain ⟨C, hC⟩ := exists_boundedSelfAdjointSpectralSupport X hX
  set μ := boundedSelfAdjointSpectralMeasure X hX
  have h := ofReal_norm_sub_smul_sq hX hC a v
  rw [hv, sub_self, norm_zero] at h
  have hae : ∀ᵐ r ∂μ.diagonalMeasure v, r = a := by
    have h0 : ∀ᵐ r ∂μ.diagonalMeasure v, ENNReal.ofReal (‖truncId C r - a‖ ^ 2) = 0 :=
      (lintegral_eq_zero_iff
        (((measurable_truncId C).sub measurable_const).norm.pow_const 2).ennreal_ofReal).mp
        (by simpa using h.symm)
    have h2 : ∀ᵐ r ∂μ.diagonalMeasure v, r ∈ Icc (-C) C := measure_eq_zero_iff_ae_notMem.mp
      (diagonalMeasure_compl_Icc hX hC v) |>.mono fun r hr => by simpa using hr
    filter_upwards [h0, h2] with r hr0 hrC
    rw [ENNReal.ofReal_eq_zero, truncId, indicator_of_mem hrC] at hr0
    have : ‖(r : ℂ) - a‖ = 0 := by nlinarith [norm_nonneg ((r : ℂ) - a)]
    exact_mod_cast sub_eq_zero.mp (norm_eq_zero.mp this)
  have hνa : μ.diagonalMeasure v {a}ᶜ = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr (hae.mono fun r hr => by simpa using hr)
  rw [WOTSpectralMeasure.diagonalMeasure_apply_eq_norm_sq _ _ _
    (measurableSet_singleton a).compl, ENNReal.ofReal_eq_zero] at hνa
  have h0 : μ {a}ᶜ v = 0 := by
    have : ‖μ {a}ᶜ v‖ = 0 := by nlinarith [norm_nonneg (μ {a}ᶜ v)]
    exact norm_eq_zero.mp this
  have hc := congrArg (fun A : E →WOT[ℂ] E => A v)
    (μ.toVectorMeasure.of_compl (measurableSet_singleton a))
  change μ {a}ᶜ v = (μ univ - μ {a}) v at hc
  rw [μ.univ, h0] at hc
  change 0 = v - μ {a} v at hc
  exact (sub_eq_zero.mp hc.symm).symm

/-- **The eigenprojections are the spectral projections of points**: `μ_S({a}) = eigenproj X a`. -/
theorem spectralMeasureProj_singleton (a : ℝ) : spectralMeasureProj hX {a} = eigenproj X a := by
  have hP := isStarProjection_spectralMeasureProj hX {a}
  ext v
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (mem_ker_sub_smul_one.mpr (apply_spectralMeasureProj_singleton hX a v)) fun u hu => ?_).symm
  set P := spectralMeasureProj hX {a}
  have hPP : P (P v) = P v := congrArg (fun T : E →L[ℂ] E => T v) hP.isIdempotentElem.eq
  rw [← spectralMeasureProj_singleton_apply_of_apply_eq hX (mem_ker_sub_smul_one.mp hu)]
  calc ⟪v - P v, P u⟫_ℂ = ⟪P (v - P v), u⟫_ℂ := by
        simpa using (hP.isSelfAdjoint.isSymmetric (v - P v) u).symm
    _ = 0 := by rw [map_sub, hPP, sub_self, inner_zero_left]

/-- Pure point spectrum means that the spectral measure is atomic: `∑ₐ μ_S({a}) = 1` strongly. -/
theorem hasPurePointSpectrum_iff_hasSum_spectralMeasureProj :
    HasPurePointSpectrum X ↔ ∀ v, HasSum (fun a : ℝ => spectralMeasureProj hX {a} v) v := by
  simp_rw [spectralMeasureProj_singleton hX]
  exact hasPurePointSpectrum_iff_hasSum_eigenproj hX

/-- **The bridge from the spectral theorem**: with pure point spectrum,
`X = ∑ₐ a μ_S({a})` is an eigendecomposition. -/
theorem isEigenDecomposition_spectralMeasureProj (hpp : HasPurePointSpectrum X) :
    IsEigenDecomposition X (fun a => spectralMeasureProj hX {a}) id := by
  simp_rw [spectralMeasureProj_singleton hX]
  exact hX.isEigenDecomposition_eigenproj hpp

end Points

/-- **Every eigendecomposition is spectral**: in `X = ∑ᵢ xᵢ Pᵢ`, `Pᵢ = μ_S({xᵢ})`. -/
theorem IsEigenDecomposition.spectralMeasureProj_singleton_eq {ι : Type*} {P : ι → E →L[ℂ] E}
    {x : ι → ℝ} (hX : IsEigenDecomposition X P x) (i : ι) :
    spectralMeasureProj hX.isSelfAdjoint {x i} = P i := by
  rw [spectralMeasureProj_singleton, hX.eigenproj_eq]

end QuantumMechanics
