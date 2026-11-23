/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.FurtherResults.AnalyticVectors
public import ForMathlib.Analysis.Distribution.SchwartzSpace.Dilation
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Fourier.HilbertBasis

/-!
# Further results: Fourier invariance and coherent states in `S^{1/2}_{1/2}(ℝ)`

Not part of the brief. Two facts about the space `gelfandShilov` of `GelfandShilov.lean`
(Sec. 5 of `further-results.tex` in the brief's directory, R. Stephan, *Further results on the
brief "Physical vector spaces for quantum mechanics"*), the Schwartz functions with exponentially
decreasing Hermite coefficients.

**Fourier invariance.** The unitary Fourier transform `(F f)(ξ) = (2π)^{-1/2} ∫ e^{-ixξ} f(x) dx`
has the Hermite functions as eigenvectors, `F ψₙ = (-i)ⁿ ψₙ`, so it multiplies the `n`-th
Hermite coefficient by `(-i)ⁿ` and maps `S^{1/2}_{1/2}(ℝ)` onto itself. Here `F` is Mathlib's
Fourier transform, whose character is `e^{-2πixξ}`, conjugated by the dilation by `√(2π)`; the
eigenrelation is Tau Ceti's `TauCeti.fourier_twoPiHermiteSchwartzMap` for the dilated Hermite
functions.

**Coherent states.** A Schwartz eigenvector `a₋ g = z g` of the lowering operator has Hermite
coefficients with `|cₙ|² = (|z|²/2)ⁿ/n! |c₀|²`, so it lies in `S^{1/2}_{1/2}(ℝ)`. The translated
Gaussians `π^{-1/4} e^{-(x-x₀)²/2}` are such eigenvectors, with `z = x₀`, and their coefficients
are Poisson: `|cₙ|² = e^{-λ} λⁿ/n!` with `λ = x₀²/2`.

## Main definitions

* `fourierOp`: the unitary Fourier transform with kernel `(2π)^{-1/2} e^{-ixξ}`.
* `gaussianAt x₀`: the translated Gaussian `ψ₀(x - x₀)`.

## Main results

* `fourierOp_apply`: the integral formula for `fourierOp`;
* `fourierOp_hermite`, `coef_fourierOp`: `F ψₙ = (-i)ⁿ ψₙ` and `cₙ(F f) = (-i)ⁿ cₙ(f)`;
* `fourierOp_mem_gelfandShilov_iff`: `F f ∈ S^{1/2}_{1/2}(ℝ) ↔ f ∈ S^{1/2}_{1/2}(ℝ)`;
* `norm_coef_sq_of_lowerOp_eq_smul`, `mem_gelfandShilov_of_lowerOp_eq_smul`: eigenvectors of
  `a₋` are in `S^{1/2}_{1/2}(ℝ)`;
* `lowerOp_gaussianAt`, `norm_coef_gaussianAt_sq`, `gaussianAt_mem_gelfandShilov`: the
  translated Gaussians, with Poisson coefficients.
-/

open SchwartzMap MeasureTheory Complex FourierTransform Nat
open scoped InnerProductSpace ComplexConjugate

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

/-! ### The Fourier transform -/

/-- `√(2π)`, as a unit. -/
def twoPiScale : ℝˣ := Units.mk0 (√(2 * Real.pi)) (by positivity)

lemma coe_twoPiScale : (twoPiScale : ℝ) = √(2 * Real.pi) := rfl

/-- **The unitary Fourier transform** `(F f)(ξ) = (2π)^{-1/2} ∫ e^{-ixξ} f(x) dx`
(`fourierOp_apply`): Mathlib's `𝓕`, with character `e^{-2πixξ}`, conjugated by the dilation by
`√(2π)`. -/
def fourierOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  dilation twoPiScale⁻¹ ∘L fourierCLM ℂ 𝓢(ℝ, ℂ) ∘L dilation twoPiScale

lemma fourierOp_eq (f : 𝓢(ℝ, ℂ)) :
    fourierOp f = dilation twoPiScale⁻¹ (𝓕 (dilation twoPiScale f)) := rfl

lemma dilation_hermite (n : ℕ) :
    dilation twoPiScale (hermite n) = TauCeti.twoPiHermiteSchwartzMap n := by
  ext x
  rw [dilation_apply, TauCeti.twoPiHermiteSchwartzMap_apply, TauCeti.twoPiHermiteFunction_def,
    hermite_apply, coe_twoPiScale, abs_of_nonneg (Real.sqrt_nonneg _)]
  simp

/-- **`F ψₙ = (-i)ⁿ ψₙ`.** -/
theorem fourierOp_hermite (n : ℕ) : fourierOp (hermite n) = (-I) ^ n • hermite n := by
  rw [fourierOp_eq, dilation_hermite, TauCeti.fourier_twoPiHermiteSchwartzMap, map_smul,
    ← dilation_hermite, dilation_inv_dilation]

lemma integral_conj_mul (u v : 𝓢(ℝ, ℂ)) : ∫ x, conj (u x) * v x = ∫ x, ⟪u x, v x⟫_ℂ := by
  congr 1
  funext x
  rw [RCLike.inner_apply, mul_comm]

/-- `F` preserves the `L²` inner product (Plancherel). -/
theorem l2Core_inner_fourierOp (f g : 𝓢(ℝ, ℂ)) :
    l2Core.inner (fourierOp f) (fourierOp g) = l2Core.inner f g := by
  rw [l2Core_inner, l2Core_inner, integral_conj_mul, integral_conj_mul, fourierOp_eq,
    fourierOp_eq, integral_inner_dilation, integral_inner_fourier_fourier,
    integral_inner_dilation]

/-- **`cₙ(F f) = (-i)ⁿ cₙ(f)`.** -/
theorem coef_fourierOp (n : ℕ) (f : 𝓢(ℝ, ℂ)) : coef n (fourierOp f) = (-I) ^ n * coef n f := by
  have hψ : hermite n = I ^ n • fourierOp (hermite n) := by
    rw [fourierOp_hermite, smul_smul, ← mul_pow, mul_neg, I_mul_I, neg_neg, one_pow, one_smul]
  rw [coef_eq, coef_eq]
  conv_lhs => rw [hψ]
  rw [l2Core_inner_eq, map_smul, inner_smul_left, ← l2Core_inner_eq, l2Core_inner_fourierOp,
    map_pow, conj_I]

lemma coef_injective {f g : 𝓢(ℝ, ℂ)} (h : ∀ n, coef n f = coef n g) : f = g := by
  refine injective_toLp (μ := volume) 2 ?_
  show f.toLp 2 = g.toLp 2
  refine (TauCeti.hermiteHilbertBasis ℂ).repr.injective (lp.ext (funext fun n => ?_))
  rw [← coef_eq_repr, ← coef_eq_repr, h n]

/-- `F⁴ = 1`. -/
theorem fourierOp_four (f : 𝓢(ℝ, ℂ)) : fourierOp (fourierOp (fourierOp (fourierOp f))) = f :=
  coef_injective fun n => by
    simp only [coef_fourierOp, ← mul_assoc, ← mul_pow]
    norm_num [show (-I) * -I * -I * -I = (I * I) * (I * I) by ring]

lemma fourierOp_apply_mem {f : 𝓢(ℝ, ℂ)} (hf : f ∈ gelfandShilov) :
    fourierOp f ∈ gelfandShilov := by
  obtain ⟨C, ε, hε, hC⟩ := hf
  refine ⟨C, ε, hε, fun n => ?_⟩
  simpa only [coef_fourierOp, norm_mul, norm_pow, norm_neg, norm_I, one_pow, one_mul] using hC n

/-- **`S^{1/2}_{1/2}(ℝ)` is invariant under the Fourier transform**, and `F` maps it onto
itself. -/
theorem fourierOp_mem_gelfandShilov_iff {f : 𝓢(ℝ, ℂ)} :
    fourierOp f ∈ gelfandShilov ↔ f ∈ gelfandShilov :=
  ⟨fun h => fourierOp_four f ▸ fourierOp_apply_mem (fourierOp_apply_mem (fourierOp_apply_mem h)),
    fourierOp_apply_mem⟩

/-- The integral formula `(F f)(ξ) = (2π)^{-1/2} ∫ e^{-ixξ} f(x) dx`. -/
theorem fourierOp_apply (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    fourierOp f ξ = ((√(2 * Real.pi))⁻¹ : ℝ) * ∫ x : ℝ, cexp (-(x * ξ * I)) * f x := by
  set s := √(2 * Real.pi) with hs_def
  have hs : 0 < s := by positivity
  have hss : s * s = 2 * Real.pi := Real.mul_self_sqrt (by positivity)
  rw [fourierOp_eq, dilation_apply, fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp only [dilation_apply, smul_eq_mul, Units.val_inv_eq_inv_val, coe_twoPiScale, ← hs_def,
    abs_inv, abs_of_pos hs]
  have key : (fun v : ℝ => cexp (↑(-2 * Real.pi * v * (s⁻¹ * ξ)) * I) * ((√s : ℝ) * f (s * v))) =
      fun v => (fun y : ℝ => ((√s : ℝ) : ℂ) * (cexp (-(y * ξ * I)) * f y)) (s * v) := by
    funext v
    have hexp : ((-2 * Real.pi * v * (s⁻¹ * ξ) : ℝ) : ℂ) * I = -(((s * v : ℝ) : ℂ) * ξ * I) := by
      have hpi : Real.pi = s * s / 2 := by linarith
      rw [hpi]
      push_cast
      field_simp
    simp only [hexp]
    ring
  rw [key, Measure.integral_comp_mul_left
    (fun y : ℝ => ((√s : ℝ) : ℂ) * (cexp (-(y * ξ * I)) * f y)) s, integral_const_mul,
    abs_inv, abs_of_pos hs, Complex.real_smul]
  have h1 : √s⁻¹ * s⁻¹ * √s = s⁻¹ := by
    rw [Real.sqrt_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 hs).ne', one_mul]
  have h1' : ((√s⁻¹ : ℝ) : ℂ) * ((s⁻¹ : ℝ) : ℂ) * ((√s : ℝ) : ℂ) = ((s⁻¹ : ℝ) : ℂ) := by
    exact_mod_cast h1
  linear_combination (∫ y : ℝ, cexp (-(y * ξ * I)) * f y) * h1'

/-! ### Coherent states -/

section Coherent

variable {g : 𝓢(ℝ, ℂ)} {z : ℂ}

lemma norm_coef_succ_sq (hg : lowerOp g = z • g) (n : ℕ) :
    2 * ((n : ℝ) + 1) * ‖coef (n + 1) g‖ ^ 2 = ‖z‖ ^ 2 * ‖coef n g‖ ^ 2 := by
  have h := coef_lowerOp n g
  rw [hg, coef_smul] at h
  have h2 := congrArg (fun w => ‖w‖ ^ 2) h
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1))] at h2
  linarith

/-- **Coefficients of an eigenvector of `a₋`**: `|cₙ|² = (|z|²/2)ⁿ/n! |c₀|²`. -/
theorem norm_coef_sq_of_lowerOp_eq_smul (hg : lowerOp g = z • g) (n : ℕ) :
    ‖coef n g‖ ^ 2 = (‖z‖ ^ 2 / 2) ^ n / n ! * ‖coef 0 g‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := norm_coef_succ_sq hg n
    rw [ih] at h
    have hn : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
    have h' : ‖coef (n + 1) g‖ ^ 2 =
        ‖z‖ ^ 2 * ((‖z‖ ^ 2 / 2) ^ n / n ! * ‖coef 0 g‖ ^ 2) / (2 * ((n : ℝ) + 1)) := by
      rw [← h]
      field_simp
    rw [h', factorial_succ, cast_mul, pow_succ]
    push_cast
    field_simp
    ring

/-- **Eigenvectors of `a₋` lie in `S^{1/2}_{1/2}(ℝ)`.** -/
theorem mem_gelfandShilov_of_lowerOp_eq_smul (hg : lowerOp g = z • g) : g ∈ gelfandShilov := by
  set l := ‖z‖ ^ 2 / 2
  refine ⟨‖coef 0 g‖ * Real.exp (l * Real.exp 2 / 2), 1, one_pos, fun n => ?_⟩
  have hl : 0 ≤ l := by positivity
  have hb := Real.pow_div_factorial_le_exp _ (by positivity : 0 ≤ l * Real.exp 2) n
  have he : Real.exp 2 ^ n * Real.exp (-(2 * n)) = 1 := by
    rw [← Real.exp_natCast_mul, ← Real.exp_add, mul_comm, add_neg_cancel, Real.exp_zero]
  have h1 : l ^ n / n ! = (l * Real.exp 2) ^ n / n ! * Real.exp (-(2 * n)) := by
    rw [mul_pow, mul_div_right_comm, mul_assoc, he, mul_one]
  have h2 : (‖coef 0 g‖ * Real.exp (l * Real.exp 2 / 2) * Real.exp (-(1 * n))) ^ 2 =
      ‖coef 0 g‖ ^ 2 * Real.exp (l * Real.exp 2) * Real.exp (-(2 * n)) := by
    rw [mul_pow, mul_pow, sq (Real.exp _), sq (Real.exp (-(1 * n))), ← Real.exp_add,
      ← Real.exp_add]
    ring_nf
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [norm_coef_sq_of_lowerOp_eq_smul hg, h1, h2]
  calc (l * Real.exp 2) ^ n / n ! * Real.exp (-(2 * n)) * ‖coef 0 g‖ ^ 2
      = (l * Real.exp 2) ^ n / n ! * (‖coef 0 g‖ ^ 2 * Real.exp (-(2 * n))) := by ring
    _ ≤ Real.exp (l * Real.exp 2) * (‖coef 0 g‖ ^ 2 * Real.exp (-(2 * n))) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by ring

end Coherent

/-- The translated Gaussian `ψ₀(x - x₀) = π^{-1/4} e^{-(x-x₀)²/2}`. -/
def gaussianAt (x₀ : ℝ) : 𝓢(ℝ, ℂ) := compSubConstCLM ℂ x₀ (hermite 0)

lemma gaussianAt_apply (x₀ x : ℝ) :
    gaussianAt x₀ x = (Real.exp (-((x - x₀) ^ 2 / 2)) / √(√Real.pi) : ℝ) := by
  rw [gaussianAt, compSubConstCLM_apply, hermite_apply, TauCeti.hermiteFunction_zero]

/-- `a₋ ψ₀(· - x₀) = x₀ ψ₀(· - x₀)`. -/
theorem lowerOp_gaussianAt (x₀ : ℝ) : lowerOp (gaussianAt x₀) = (x₀ : ℂ) • gaussianAt x₀ := by
  have hg : ⇑(gaussianAt x₀) = fun y => hermite 0 (y - x₀) := by
    funext y
    rw [gaussianAt, compSubConstCLM_apply]
  ext x
  simp only [lowerOp, LinearMap.add_apply, add_apply, posOp_apply, derivOp_apply, smul_apply,
    smul_eq_mul, hg]
  rw [deriv_comp_sub_const, deriv_hermite, hermite_apply]
  have h := TauCeti.mul_add_deriv_hermiteFunction 0 (x - x₀)
  simp only [CharP.cast_eq_zero, mul_zero, Real.sqrt_zero, zero_mul] at h
  have hd : deriv (TauCeti.hermiteFunction 0) (x - x₀) =
      -((x - x₀) * TauCeti.hermiteFunction 0 (x - x₀)) := by linarith
  rw [hd]
  push_cast
  ring

theorem gaussianAt_mem_gelfandShilov (x₀ : ℝ) : gaussianAt x₀ ∈ gelfandShilov :=
  mem_gelfandShilov_of_lowerOp_eq_smul (lowerOp_gaussianAt x₀)

lemma l2Core_inner_gaussianAt (x₀ : ℝ) : l2Core.inner (gaussianAt x₀) (gaussianAt x₀) = 1 := by
  have h0 : l2Core.inner (hermite 0) (hermite 0) = 1 := by
    rw [← coef_eq, coef_hermite]
    simp
  rw [← h0, l2Core_inner, l2Core_inner]
  simp only [gaussianAt, compSubConstCLM_apply]
  exact integral_sub_right_eq_self (fun y => conj (hermite 0 y) * hermite 0 y) x₀

/-- **The translated Gaussians have Poisson coefficients**:
`|cₙ(ψ₀(· - x₀))|² = e^{-λ} λⁿ/n!` with `λ = x₀²/2`. -/
theorem norm_coef_gaussianAt_sq (x₀ : ℝ) (n : ℕ) :
    ‖coef n (gaussianAt x₀)‖ ^ 2 = Real.exp (-(x₀ ^ 2 / 2)) * ((x₀ ^ 2 / 2) ^ n / n !) := by
  set l := x₀ ^ 2 / 2
  have hz : ‖(x₀ : ℂ)‖ ^ 2 / 2 = l := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hc := norm_coef_sq_of_lowerOp_eq_smul (lowerOp_gaussianAt x₀)
  simp only [hz] at hc
  -- Parseval: `∑ₙ |cₙ|² = ‖ψ₀(· - x₀)‖² = 1`
  have hP := hasSum_norm_coef_sq (gaussianAt x₀)
  have hn : ‖(gaussianAt x₀).toLp 2‖ ^ 2 = 1 := by
    have h := l2Core_inner_gaussianAt x₀
    rw [l2Core_inner_eq, toLpCLM_apply, inner_self_eq_norm_sq_to_K] at h
    have h' : ((‖(gaussianAt x₀).toLp 2‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [ofReal_pow]
      exact h
    exact_mod_cast h'
  rw [hn, show (fun n => ‖coef n (gaussianAt x₀)‖ ^ 2) =
    fun n => l ^ n / n ! * ‖coef 0 (gaussianAt x₀)‖ ^ 2 from funext hc] at hP
  have hE := (NormedSpace.expSeries_div_hasSum_exp l).mul_right (‖coef 0 (gaussianAt x₀)‖ ^ 2)
  rw [← Real.exp_eq_exp_ℝ] at hE
  have h0 : ‖coef 0 (gaussianAt x₀)‖ ^ 2 = Real.exp (-l) := by
    rw [Real.exp_neg]
    exact eq_inv_of_mul_eq_one_right (hE.unique hP)
  rw [hc, h0]
  ring

end QuantumVectorSpaces.FurtherResults
