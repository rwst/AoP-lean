/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import ForMathlib.MeasureTheory.Function.L2Multiplication

/-!
# The Fourier transform on `L²` of integrable functions

Mathlib's Fourier transform on `L²` is the continuous extension of the Fourier transform of
Schwartz functions. This file shows that on an `L²` function that is also integrable, the inverse
transform is given by the Fourier integral, and so is bounded by the `L¹` norm. On `ℝ`, an `L²`
function `f` with `ξ² f ∈ L²` is integrable, with `∫ ‖f‖ ≤ ε ‖ξ² f‖₂ + C_ε ‖f‖₂` for every `ε > 0`:
the Sobolev bound behind the Kato–Rellich theorem for `L² + L^∞` potentials in one dimension.

## Main results

* `MeasureTheory.Lp.fourierInv_coeFn_eq_of_integrable`: on `L²(ℝ)`, `𝓕⁻ f` is a.e. the Fourier
  integral;
* `MeasureTheory.Lp.ae_norm_fourierInv_le_of_integrable`: `‖(𝓕⁻ f)(x)‖ ≤ ∫ ‖f‖` for a.e. `x`;
* `MeasureTheory.Lp.integral_norm_le_of_ae_eq_sq_mul`: on `ℝ`, the bound
  `∫ ‖f‖ ≤ √(π/λ) (λ ‖f‖₂ + ‖ξ² f‖₂)` for `λ ≥ 1`, by Cauchy–Schwarz;
* `MeasureTheory.Lp.exists_integral_norm_le_of_ae_eq_sq_mul`: its form with `ε`.
-/

open FourierTransform SchwartzMap Real
open scoped ENNReal ContDiff

@[expose] public noncomputable section

namespace MeasureTheory.Lp

section Integrable

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma continuous_neg_innerₗ : Continuous fun p : ℝ × ℝ => (-innerₗ ℝ) p.1 p.2 := by
  simpa using (continuous_inner.neg : Continuous fun p : ℝ × ℝ => -inner ℝ p.1 p.2)

lemma flip_neg_innerₗ : (-innerₗ ℝ).flip = -innerₗ ℝ :=
  LinearMap.ext₂ fun x y => by simp [mul_comm]

/-- On an integrable `L²` function, the inverse Fourier transform on `L²` is a.e. the Fourier
integral. -/
theorem fourierInv_coeFn_eq_of_integrable (f : Lp F 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → F)) :
    (𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) =ᵐ[volume] 𝓕⁻ (f : ℝ → F) := by
  set g : ℝ → F := 𝓕⁻ (f : ℝ → F)
  have hgc : Continuous g :=
    VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_neg_innerₗ hf
  have hloc : LocallyIntegrable (fun x => (𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) x - g x) volume :=
    ((Lp.memLp _).locallyIntegrable (by norm_num)).sub hgc.locallyIntegrable
  have hw := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun φ hφ hφc => by
    have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
    have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
    set ψ : 𝓢(ℝ, ℂ) := h₁.toSchwartzMap h₂
    have hψ (x : ℝ) (v : F) : φ x • v = ψ x • v := (Complex.coe_smul (φ x) v).symm
    have e1 : ∫ x, ψ x • (𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) x = ∫ ξ, (𝓕⁻ ψ) ξ • f ξ := by
      rw [← Lp.toTemperedDistribution_apply, ← fourierInv_toTemperedDistribution_eq,
        TemperedDistribution.fourierInv_apply, Lp.toTemperedDistribution_apply]
    have e2 : ∫ x, ψ x • g x = ∫ ξ, (𝓕⁻ ψ) ξ • f ξ := by
      rw [SchwartzMap.fourierInv_coe]
      have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
        continuous_fourierChar continuous_neg_innerₗ ψ.integrable hf
      rw [flip_neg_innerₗ] at h
      exact h.symm
    have hi1 := ((Lp.memLp (𝓕⁻ f : Lp F 2 (volume : Measure ℝ))).locallyIntegrable
      (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
    have hi2 := hgc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport (μ := volume)
      hφ.continuous hφc
    have key : ∫ x, φ x • (𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) x = ∫ x, φ x • g x := by
      have h1 : ∫ x, φ x • (𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) x =
          ∫ x, ψ x • (𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hψ x _)
      have h2 : ∫ x, φ x • g x = ∫ x, ψ x • g x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => hψ x _)
      exact h1.trans (e1.trans (e2.symm.trans h2.symm))
    exact ((integral_congr_ae (Filter.Eventually.of_forall fun x =>
      smul_sub (φ x) ((𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) x) (g x))).trans
        (integral_sub hi1 hi2)).trans (sub_eq_zero.2 key)
  filter_upwards [hw] with x hx
  exact sub_eq_zero.1 hx

/-- On an integrable `L²` function, the inverse Fourier transform on `L²` is a.e. bounded by the
`L¹` norm. -/
theorem ae_norm_fourierInv_le_of_integrable (f : Lp F 2 (volume : Measure ℝ))
    (hf : Integrable (f : ℝ → F)) :
    ∀ᵐ x ∂volume, ‖(𝓕⁻ f : Lp F 2 (volume : Measure ℝ)) x‖ ≤ ∫ ξ, ‖f ξ‖ := by
  filter_upwards [fourierInv_coeFn_eq_of_integrable f hf] with x hx
  rw [hx]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

end Integrable

/-! ### The `L¹` bound on `ℝ` -/

variable {f g : Lp ℂ 2 (volume : Measure ℝ)}

/-- If `f` and `g = ξ² f` are in `L²(ℝ)`, then `f` is integrable and, for `λ ≥ 1`,
`∫ ‖f‖ ≤ √(π/λ) (λ ‖f‖₂ + ‖g‖₂)`. By Cauchy–Schwarz with `(λ + ξ²)⁻¹ ∈ L²`. -/
theorem integral_norm_le_of_ae_eq_sq_mul (hg : (g : ℝ → ℂ) =ᵐ[volume] fun ξ => (ξ : ℂ) ^ 2 * f ξ)
    {l : ℝ} (hl : 1 ≤ l) :
    Integrable (f : ℝ → ℂ) ∧ ∫ ξ, ‖f ξ‖ ≤ √(π / l) * (l * ‖f‖ + ‖g‖) := by
  have hl0 : 0 < l := by linarith
  set a : ℝ → ℝ := fun ξ => (l + ξ ^ 2)⁻¹
  set B : Lp ℂ 2 (volume : Measure ℝ) := (l : ℂ) • f + g
  have hpos (ξ : ℝ) : 0 < l + ξ ^ 2 := by positivity
  have hB : ∀ᵐ ξ ∂volume, ‖B ξ‖ = (l + ξ ^ 2) * ‖f ξ‖ := by
    filter_upwards [Lp.coeFn_add ((l : ℂ) • f) g, Lp.coeFn_smul (l : ℂ) f, hg] with ξ h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul, ← add_mul, norm_mul]
    congr 1
    rw [show (l : ℂ) + (ξ : ℂ) ^ 2 = ((l + ξ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (hpos ξ).le]
  -- `a² ≤ λ⁻¹ (1 + ξ²)⁻¹`, since `(λ + ξ²)² ≥ λ (1 + ξ²)` for `λ ≥ 1`.
  have ha2 (ξ : ℝ) : a ξ ^ 2 ≤ l⁻¹ * (1 + ξ ^ 2)⁻¹ := by
    simp only [a, inv_pow, ← mul_inv]
    refine inv_anti₀ (by positivity) ?_
    nlinarith [sq_nonneg ξ, sq_nonneg (ξ ^ 2)]
  have hac : Continuous a := by
    refine Continuous.inv₀ (by fun_prop) fun ξ => (hpos ξ).ne'
  have ha2i : Integrable fun ξ => a ξ ^ 2 :=
    (integrable_inv_one_add_sq.const_mul l⁻¹).mono' (by fun_prop)
      (Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact ha2 ξ)
  have haL : MemLp a 2 volume := (memLp_two_iff_integrable_sq hac.aestronglyMeasurable).2 ha2i
  have hbL : MemLp (fun ξ => ‖B ξ‖) 2 volume := (Lp.memLp B).norm
  have hab : ∀ᵐ ξ ∂volume, ‖f ξ‖ = a ξ * ‖B ξ‖ := by
    filter_upwards [hB] with ξ h
    rw [h, ← mul_assoc, inv_mul_cancel₀ (hpos ξ).ne', one_mul]
  have hfi : Integrable (f : ℝ → ℂ) := by
    refine (integrable_norm_iff (Lp.aestronglyMeasurable f)).1 ?_
    have hb2 : Integrable fun ξ => ‖B ξ‖ ^ 2 :=
      (memLp_two_iff_integrable_sq (Lp.aestronglyMeasurable B).norm).1 hbL
    refine ((ha2i.add hb2).div_const 2).mono' (Lp.aestronglyMeasurable f).norm ?_
    filter_upwards [hab] with ξ h
    rw [norm_norm, h, Pi.add_apply]
    nlinarith [sq_nonneg (a ξ - ‖B ξ‖)]
  refine ⟨hfi, ?_⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun ξ => (inv_pos.2 (hpos ξ)).le)
    (Filter.Eventually.of_forall fun ξ => norm_nonneg (B ξ)) (by simpa using haL)
    (by simpa using hbL)
  have h1 : ∫ ξ, ‖f ξ‖ = ∫ ξ, a ξ * ‖B ξ‖ := integral_congr_ae hab
  have h2 : (∫ ξ, a ξ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ √(π / l) := by
    rw [Real.sqrt_eq_rpow]
    refine Real.rpow_le_rpow (integral_nonneg fun ξ => by positivity) ?_ (by norm_num)
    simp_rw [Real.rpow_two]
    calc ∫ ξ, a ξ ^ 2 ≤ ∫ ξ, l⁻¹ * (1 + ξ ^ 2)⁻¹ :=
          integral_mono ha2i (integrable_inv_one_add_sq.const_mul l⁻¹) ha2
      _ = π / l := by rw [integral_const_mul, integral_univ_inv_one_add_sq, inv_mul_eq_div]
  have h3 : (∫ ξ, ‖B ξ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) = ‖B‖ := by
    simp_rw [Real.rpow_two]
    rw [← L2.norm_sq_eq_integral, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  have h4 : ‖B‖ ≤ l * ‖f‖ + ‖g‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hl0.le]
  rw [h1]
  refine hH.trans ?_
  rw [h3]
  exact mul_le_mul h2 h4 (norm_nonneg _) (Real.sqrt_nonneg _)

/-- The `ε`-form of `integral_norm_le_of_ae_eq_sq_mul`: for every `ε > 0` there is `C` with
`∫ ‖f‖ ≤ ε ‖ξ² f‖₂ + C ‖f‖₂` for all `f`. -/
theorem exists_integral_norm_le_of_ae_eq_sq_mul {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ f g : Lp ℂ 2 (volume : Measure ℝ),
      (g : ℝ → ℂ) =ᵐ[volume] (fun ξ => (ξ : ℂ) ^ 2 * f ξ) →
        Integrable (f : ℝ → ℂ) ∧ ∫ ξ, ‖f ξ‖ ≤ ε * ‖g‖ + C * ‖f‖ := by
  set l := max 1 (π / ε ^ 2)
  have hl : 1 ≤ l := le_max_left _ _
  have hl0 : 0 < l := by linarith
  have hs : √(π / l) ≤ ε := by
    rw [Real.sqrt_le_left hε.le, div_le_iff₀ hl0]
    have : π / ε ^ 2 ≤ l := le_max_right _ _
    rwa [div_le_iff₀ (by positivity), mul_comm] at this
  refine ⟨√(π / l) * l, fun f g hg => ?_⟩
  obtain ⟨hfi, hb⟩ := integral_norm_le_of_ae_eq_sq_mul hg hl
  refine ⟨hfi, hb.trans ?_⟩
  nlinarith [norm_nonneg g, Real.sqrt_nonneg (π / l)]

end MeasureTheory.Lp
