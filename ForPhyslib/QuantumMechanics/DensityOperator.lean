/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.PositiveTrace
public import ForPhyslib.QuantumMechanics.Wigner.Density
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Basic

/-!
# Density operators on a Hilbert space

## i. Overview

A density operator on a complex Hilbert space `E` of any dimension is a positive trace-class
operator of trace one. `QuantumMechanics.Wigner.IsDensity` uses `LinearMap.trace`, which is zero
in infinite dimension; `IsDensityOperator` uses the trace-class trace instead and agrees with
`IsDensity` in finite dimension.

For a positive operator, being trace class and the value of the trace are both read off the trace
`posTrace` in `[0, ∞]`, which can be computed in any Hilbert basis and needs no summability
bookkeeping. This gives the closure properties: pure states, convex combinations, conjugation by
an isometry. A density operator that is a projection is a pure state.

## ii. Key results

- `QuantumMechanics.isTraceClass_iff_posTrace_ne_top`, `QuantumMechanics.trace_eq_posTrace`: for
  positive operators, the trace-class trace is the trace in `[0, ∞]`.
- `QuantumMechanics.IsDensityOperator`: positive, trace class, trace one.
- `QuantumMechanics.isDensityOperator_iff`: `0 ≤ ρ` and `posTrace ρ = 1`.
- `QuantumMechanics.IsDensityOperator.norm_le_one`, `IsDensityOperator.spectrum_subset_Icc`.
- `QuantumMechanics.isDensityOperator_proj`: a pure state is a density operator.
- `QuantumMechanics.IsDensityOperator.smul_add_smul`, `IsDensityOperator.mix`: convex combinations.
- `QuantumMechanics.IsDensityOperator.conj`: conjugation `ρ ↦ U ρ U†` by an isometry.
- `QuantumMechanics.IsDensityOperator.eq_proj_of_isIdempotentElem`: an idempotent density
  operator is `|ψ⟩⟨ψ|` for a unit `ψ`.
- `QuantumMechanics.isDensityOperator_iff_isDensity`: in finite dimension this is `IsDensity`.

## iii. Table of contents

- A. Positive trace-class operators
- B. Density operators
- C. Pure states and mixtures
- D. Conjugation by an isometry
- E. Idempotent density operators
- F. Finite dimension

## iv. References

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press (1980), §VI.6.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open InnerProductSpace ProbabilisticTheory QuantumMechanics.Wigner
open ContinuousLinearMap (posTrace posTraceBasis re_inner_apply_nonneg posTrace_add posTrace_smul
  posTrace_conj_of_star_mul_self posTrace_eq_zero_iff posTrace_rankOne_self norm_le_toReal_posTrace
  posTrace_eq_ofReal_re_trace nonneg_iff_isPositive isPositive_toLinearMap_iff)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. Positive trace-class operators -/

lemma summable_iff_tsum_ofReal_ne_top {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    Summable f ↔ ∑' i, ENNReal.ofReal (f i) ≠ ⊤ := by
  simp only [ENNReal.ofReal, ENNReal.tsum_coe_ne_top_iff_summable]
  refine ⟨Summable.toNNReal, fun h => ?_⟩
  simpa [Real.coe_toNNReal _ (hf _)] using NNReal.summable_coe.mpr h

/-- A positive operator is trace class iff its trace in `[0, ∞]` is finite. -/
theorem isTraceClass_iff_posTrace_ne_top {T : E →L[ℂ] E} (hT : 0 ≤ T) :
    IsTraceClass T ↔ posTrace T ≠ ⊤ := by
  rw [posTrace, ← summable_iff_tsum_ofReal_ne_top fun _ => re_inner_apply_nonneg hT _]
  refine ⟨fun h => ?_, fun h => ⟨_, posTraceBasis E, ?_⟩⟩
  · simpa [CFC.abs_of_nonneg T hT] using isTraceClass_iff.mp h _ (posTraceBasis E)
  · simpa [CFC.abs_of_nonneg T hT] using h

omit [CompleteSpace E] in
lemma ofReal_re_inner_apply {T : E →L[ℂ] E} (hT : 0 ≤ T) (x : E) :
    ((⟪x, T x⟫_ℂ).re : ℂ) = ⟪x, T x⟫_ℂ := by
  have hsym := (nonneg_iff_isPositive.mp hT).isSymmetric
  have h := hsym.coe_re_inner_apply_self x
  rw [hsym x x] at h
  simpa using h

/-- For a positive trace-class operator, the trace is the trace in `[0, ∞]`. -/
theorem trace_eq_posTrace {T : E →L[ℂ] E} (hT : 0 ≤ T) (h : IsTraceClass T) :
    trace T h = ((posTrace T).toReal : ℂ) := by
  have hs : Summable fun i => (⟪posTraceBasis E i, T (posTraceBasis E i)⟫_ℂ).re :=
    (summable_iff_tsum_ofReal_ne_top fun _ => re_inner_apply_nonneg hT _).mpr
      ((isTraceClass_iff_posTrace_ne_top hT).mp h)
  rw [trace_eq_of_hilbertBasis_of_nonneg hT h (posTraceBasis E), posTrace,
    ← ENNReal.ofReal_tsum_of_nonneg (fun _ => re_inner_apply_nonneg hT _) hs,
    ENNReal.toReal_ofReal (tsum_nonneg fun _ => re_inner_apply_nonneg hT _), Complex.ofReal_tsum]
  congr! 2 with i
  exact (ofReal_re_inner_apply hT _).symm

/-! ## B. Density operators -/

/-- A density operator: a positive trace-class operator of trace one. -/
structure IsDensityOperator (ρ : E →L[ℂ] E) : Prop where
  nonneg : 0 ≤ ρ
  isTraceClass : IsTraceClass ρ
  trace_eq_one : trace ρ isTraceClass = 1

variable {ρ σ : E →L[ℂ] E}

/-- A density operator is a positive operator whose trace in `[0, ∞]` is one. -/
theorem isDensityOperator_iff : IsDensityOperator ρ ↔ 0 ≤ ρ ∧ posTrace ρ = 1 := by
  refine ⟨fun h => ⟨h.nonneg, ?_⟩, fun ⟨h0, h1⟩ => ?_⟩
  · have h' := h.trace_eq_one
    rw [trace_eq_posTrace h.nonneg] at h'
    have hne := (isTraceClass_iff_posTrace_ne_top h.nonneg).mp h.isTraceClass
    rw [← ENNReal.ofReal_toReal hne, show (posTrace ρ).toReal = 1 by exact_mod_cast h']
    simp
  · have hc := (isTraceClass_iff_posTrace_ne_top h0).mpr (by simp [h1])
    exact ⟨h0, hc, by rw [trace_eq_posTrace h0, h1]; simp⟩

lemma IsDensityOperator.posTrace_eq_one (hρ : IsDensityOperator ρ) : posTrace ρ = 1 :=
  (isDensityOperator_iff.mp hρ).2

lemma IsDensityOperator.isSelfAdjoint (hρ : IsDensityOperator ρ) : IsSelfAdjoint ρ :=
  hρ.nonneg.isSelfAdjoint

lemma IsDensityOperator.ne_zero (hρ : IsDensityOperator ρ) : ρ ≠ 0 := by
  rintro rfl
  simpa using hρ.posTrace_eq_one

lemma IsDensityOperator.nontrivial (hρ : IsDensityOperator ρ) : Nontrivial E := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hρ.ne_zero (Subsingleton.elim _ _)

lemma IsDensityOperator.norm_le_one (hρ : IsDensityOperator ρ) : ‖ρ‖ ≤ 1 := by
  simpa [hρ.posTrace_eq_one] using norm_le_toReal_posTrace hρ.nonneg (by simp [hρ.posTrace_eq_one])

/-- The spectrum of a density operator lies in `[0, 1]`. -/
lemma IsDensityOperator.spectrum_subset_Icc (hρ : IsDensityOperator ρ) :
    spectrum ℝ ρ ⊆ Set.Icc 0 1 := fun x hx =>
  have := hρ.nontrivial
  ⟨spectrum_nonneg_of_nonneg hρ.nonneg hx,
    (le_abs_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hρ.norm_le_one)⟩

/-! ## C. Pure states and mixtures -/

omit [CompleteSpace E] in
lemma proj_nonneg (ψ : E) : 0 ≤ proj ψ :=
  nonneg_iff_isPositive.mpr (isPositive_rankOne_self ψ)

/-- A pure state is a density operator. -/
theorem isDensityOperator_proj {ψ : E} (hψ : ‖ψ‖ = 1) : IsDensityOperator (proj ψ) :=
  isDensityOperator_iff.mpr ⟨proj_nonneg ψ, by simp [proj, posTrace_rankOne_self, hψ]⟩

/-- Density operators are closed under convex combinations. -/
theorem IsDensityOperator.smul_add_smul (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    IsDensityOperator ((t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ) := by
  have h1 : 0 ≤ 1 - t := by linarith
  have hs : ∀ {r : ℝ}, 0 ≤ r → ∀ {τ : E →L[ℂ] E}, 0 ≤ τ → 0 ≤ (r : ℂ) • τ := fun hr _ hτ =>
    smul_nonneg (by exact_mod_cast hr) hτ
  refine isDensityOperator_iff.mpr ⟨add_nonneg (hs ht₀ hρ.nonneg) (hs h1 hσ.nonneg), ?_⟩
  rw [posTrace_add (hs ht₀ hρ.nonneg) (hs h1 hσ.nonneg), posTrace_smul ht₀, posTrace_smul h1,
    hρ.posTrace_eq_one, hσ.posTrace_eq_one, mul_one, mul_one, ← ENNReal.ofReal_add ht₀ h1]
  simp

/-- Density operators are closed under equal mixtures. -/
theorem IsDensityOperator.mix (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    IsDensityOperator (mix ρ σ) := by
  have h := hρ.smul_add_smul hσ (t := 2⁻¹) (by norm_num) (by norm_num)
  convert h using 3 <;> norm_num

/-! ## D. Conjugation by an isometry -/

/-- Conjugation `ρ ↦ U ρ U†` by an isometry `U` preserves density operators. -/
theorem IsDensityOperator.conj (hρ : IsDensityOperator ρ) {U : E →L[ℂ] E}
    (hU : star U * U = 1) : IsDensityOperator (U * ρ * star U) :=
  isDensityOperator_iff.mpr ⟨star_right_conjugate_nonneg hρ.nonneg U, by
    rw [posTrace_conj_of_star_mul_self hρ.nonneg hU, hρ.posTrace_eq_one]⟩

/-! ## E. Idempotent density operators -/

/-- A density operator that is idempotent is a pure state. -/
theorem IsDensityOperator.eq_proj_of_isIdempotentElem (hρ : IsDensityOperator ρ)
    (h : IsIdempotentElem ρ) : ∃ ψ : E, ‖ψ‖ = 1 ∧ ρ = proj ψ := by
  have hsym := hρ.isSelfAdjoint.isSymmetric
  obtain ⟨x, hx⟩ : ∃ x, ρ x ≠ 0 := by
    by_contra! h0
    exact hρ.ne_zero (ContinuousLinearMap.ext h0)
  set ψ := (‖ρ x‖⁻¹ : ℂ) • ρ x
  have hψ : ‖ψ‖ = 1 := by simp [ψ, norm_smul, hx]
  have hρψ : ρ ψ = ψ := by
    simp only [ψ, map_smul]
    rw [show ρ (ρ x) = (ρ * ρ) x from rfl, h.eq]
  have h1 : ρ * proj ψ = proj ψ := by
    ext y
    simp [hρψ]
  have h2 : proj ψ * ρ = proj ψ := by
    ext y
    change proj ψ (ρ y) = proj ψ y
    have hs := hsym ψ y
    simp only [ContinuousLinearMap.coe_coe] at hs
    simp only [proj_apply]
    rw [← hs, hρψ]
  have hp : IsIdempotentElem (proj ψ) := isIdempotentElem_rankOne_self hψ
  set P := ρ - proj ψ
  have hPP : star P * P = P := by
    rw [IsSelfAdjoint.star_eq (hρ.isSelfAdjoint.sub (proj_nonneg ψ).isSelfAdjoint)]
    simp only [P, sub_mul, mul_sub, h.eq, h1, h2, hp.eq]
    abel
  have hP0 : 0 ≤ P := hPP ▸ star_mul_self_nonneg P
  have htr := posTrace_add (proj_nonneg ψ) hP0
  rw [show proj ψ + P = ρ by simp [P], hρ.posTrace_eq_one,
    (isDensityOperator_proj hψ).posTrace_eq_one] at htr
  have hz : posTrace P = 0 :=
    ((ENNReal.add_right_inj ENNReal.one_ne_top).mp (by rw [add_zero]; exact htr)).symm
  refine ⟨ψ, hψ, ?_⟩
  have := (posTrace_eq_zero_iff hP0).mp hz
  exact sub_eq_zero.mp this

/-! ## F. Finite dimension -/

/-- In finite dimension, density operators are the positive operators of trace one. -/
theorem isDensityOperator_iff_isDensity [FiniteDimensional ℂ E] :
    IsDensityOperator ρ ↔ IsDensity ρ := by
  rw [isDensityOperator_iff]
  constructor
  · rintro ⟨h0, h1⟩
    have hpos := (isPositive_toLinearMap_iff ρ).mpr (nonneg_iff_isPositive.mp h0)
    refine ⟨hpos, ?_⟩
    rw [posTrace_eq_ofReal_re_trace h0] at h1
    have hre : (LinearMap.trace ℂ E ρ).re = 1 := by
      have := congrArg ENNReal.toReal h1
      rwa [ENNReal.toReal_ofReal (by
        rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E), Complex.re_sum]
        exact Finset.sum_nonneg fun i _ => re_inner_apply_nonneg h0 _)] at this
    have him : (LinearMap.trace ℂ E ρ).im = 0 := by
      rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ E), Complex.im_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ContinuousLinearMap.coe_coe, ← ofReal_re_inner_apply h0, Complex.ofReal_im]
    exact Complex.ext hre him
  · intro h
    have h0 : 0 ≤ ρ := nonneg_iff_isPositive.mpr ((isPositive_toLinearMap_iff ρ).mp h.isPositive)
    exact ⟨h0, by rw [posTrace_eq_ofReal_re_trace h0, h.trace_eq_one]; simp⟩

end QuantumMechanics
