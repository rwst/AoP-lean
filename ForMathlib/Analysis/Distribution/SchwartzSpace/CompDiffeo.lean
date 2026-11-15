/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Unitary changes of variable on Schwartz space

Let `E` be a finite-dimensional real normed space and `e` a bijection of `E` such that `e` and
`e⁻¹` have temperate growth. Then `e` is a diffeomorphism, its Jacobian determinant never
vanishes, and `1 / |det De|` is polynomially bounded. The change of variable
`U_e f = |det De|^{1/2} • (f ∘ e)` is an automorphism of `𝓢(E, F)` with inverse `U_{e⁻¹}`, and it
preserves the `L²` inner product for every Haar measure. Mathlib's `SchwartzMap.compCLM` gives
`f ↦ f ∘ e` alone.

## Main definitions

* `SchwartzMap.jacobianDet e x`: the Jacobian determinant `det De(x)`;
* `SchwartzMap.jacobianWeight e x`: the factor `|det De(x)|^{1/2}`;
* `SchwartzMap.compDiffeoCLE`: the change of variable `U_e` as a continuous linear equivalence.

## Main results

* `SchwartzMap.hasTemperateGrowth_jacobianWeight`: the factor has temperate growth;
* `SchwartzMap.integral_abs_jacobianDet_smul_comp`: `∫ |det De| • g ∘ e ∂μ = ∫ g ∂μ`;
* `SchwartzMap.integral_inner_compDiffeoCLE`: `U_e` preserves the `L²` inner product.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped InnerProductSpace ContDiff

namespace SchwartzMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]

/-- The Jacobian determinant `det De(x)` of a map `e : E → E`. -/
def jacobianDet (e : E → E) (x : E) : ℝ := LinearMap.det (fderiv ℝ e x : E →ₗ[ℝ] E)

/-- The factor `|det De(x)|^{1/2}`, written as `((det De(x))²)^{1/4}`. -/
def jacobianWeight (e : E → E) (x : E) : ℝ := (jacobianDet e x ^ 2) ^ (1 / 4 : ℝ)

lemma jacobianWeight_sq (e : E → E) (x : E) : jacobianWeight e x ^ 2 = |jacobianDet e x| := by
  rw [jacobianWeight, ← Real.rpow_natCast, ← Real.rpow_mul (sq_nonneg _),
    ← Real.sqrt_sq_eq_abs, Real.sqrt_eq_rpow]
  norm_num

lemma jacobianWeight_nonneg (e : E → E) (x : E) : 0 ≤ jacobianWeight e x :=
  Real.rpow_nonneg (sq_nonneg _) _

variable {e : E ≃ E}

lemma jacobianDet_symm_mul (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (y : E) :
    jacobianDet e (e.symm y) * jacobianDet e.symm y = 1 := by
  have hd : Differentiable ℝ e := he.1.differentiable (by simp)
  have hd' : Differentiable ℝ e.symm := he'.1.differentiable (by simp)
  have h := fderiv_comp y (hd (e.symm y)) (hd' y)
  rw [show (e ∘ e.symm : E → E) = id from funext e.apply_symm_apply, fderiv_id] at h
  calc jacobianDet e (e.symm y) * jacobianDet e.symm y
      = LinearMap.det ((fderiv ℝ e (e.symm y) : E →ₗ[ℝ] E) ∘ₗ (fderiv ℝ e.symm y : E →ₗ[ℝ] E)) :=
        (LinearMap.det_comp _ _).symm
    _ = LinearMap.det ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) : E →ₗ[ℝ] E) := rfl
    _ = 1 := by rw [← h]; exact LinearMap.det_id

lemma jacobianDet_mul_symm (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (x : E) :
    jacobianDet e.symm (e x) * jacobianDet e x = 1 :=
  jacobianDet_symm_mul (e := e.symm) he' he x

lemma jacobianDet_ne_zero (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (x : E) : jacobianDet e x ≠ 0 :=
  right_ne_zero_of_mul_eq_one (jacobianDet_mul_symm he he' x)

lemma jacobianWeight_symm_mul (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (y : E) :
    jacobianWeight e.symm y * jacobianWeight e (e.symm y) = 1 := by
  rw [jacobianWeight, jacobianWeight, ← Real.mul_rpow (sq_nonneg _) (sq_nonneg _), ← mul_pow,
    mul_comm, jacobianDet_symm_mul he he', one_pow, Real.one_rpow]

lemma exists_norm_le_of_symm (he' : (e.symm : E → E).HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), ∀ x, ‖x‖ ≤ C * (1 + ‖e x‖) ^ k := by
  obtain ⟨k, C, hC⟩ := he'.2 0
  refine ⟨k, C, fun x => ?_⟩
  have := hC (e x)
  rwa [norm_iteratedFDeriv_zero, e.symm_apply_apply] at this

/-- The factor `|det De|^{1/2}` has temperate growth. -/
theorem hasTemperateGrowth_jacobianWeight [FiniteDimensional ℝ E] (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) : (jacobianWeight e).HasTemperateGrowth := by
  have hJ : (fun x => jacobianDet e.symm (e x) ^ 2).HasTemperateGrowth :=
    (he'.det_fderiv.comp he).pow 2
  obtain ⟨k, C, hC⟩ := hJ.2 0
  refine he.det_fderiv.pow 2 |>.rpow (fun x => ?_) ⟨k, C, fun x => ?_⟩ (1 / 4)
  · exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 (jacobianDet_ne_zero he he' x)).symm
  · have h1 : (jacobianDet e x)⁻¹ = jacobianDet e.symm (e x) :=
      (eq_inv_of_mul_eq_one_left (jacobianDet_mul_symm he he' x)).symm
    have h2 := hC x
    rw [norm_iteratedFDeriv_zero] at h2
    change (jacobianDet e x ^ 2)⁻¹ ≤ _
    rw [← inv_pow, h1]
    exact (le_abs_self _).trans h2

variable [FiniteDimensional ℝ E]

variable (𝕜 F) in
/-- The change of variable `f ↦ |det De|^{1/2} • (f ∘ e)` on `𝓢(E, F)`. -/
def compDiffeoCLM (e : E ≃ E) (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  (smulLeftCLM F fun x => (jacobianWeight e x : 𝕜)).comp
    (compCLM 𝕜 (F := F) he (exists_norm_le_of_symm he'))

lemma compDiffeoCLM_apply (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) :
    compDiffeoCLM 𝕜 F e he he' f x = (jacobianWeight e x : 𝕜) • f (e x) := by
  have hw : (fun x => (jacobianWeight e x : 𝕜)).HasTemperateGrowth :=
    (RCLike.hasTemperateGrowth_ofReal 𝕜).comp (hasTemperateGrowth_jacobianWeight he he')
  rw [compDiffeoCLM, ContinuousLinearMap.comp_apply, smulLeftCLM_apply_apply hw]
  rfl

lemma compDiffeoCLM_symm_comp (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, F)) :
    compDiffeoCLM 𝕜 F e.symm he' he (compDiffeoCLM 𝕜 F e he he' f) = f := by
  ext y
  rw [compDiffeoCLM_apply, compDiffeoCLM_apply, smul_smul, ← RCLike.ofReal_mul,
    jacobianWeight_symm_mul he he', RCLike.ofReal_one, one_smul, e.apply_symm_apply]

variable (𝕜 F) in
/-- **Unitary changes of variable.** For a bijection `e` of `E` such that `e` and `e⁻¹` have
temperate growth, `f ↦ |det De|^{1/2} • (f ∘ e)` is an automorphism of `𝓢(E, F)`. -/
def compDiffeoCLE (e : E ≃ E) (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) : 𝓢(E, F) ≃L[𝕜] 𝓢(E, F) :=
  .equivOfInverse (compDiffeoCLM 𝕜 F e he he') (compDiffeoCLM 𝕜 F e.symm he' he)
    (compDiffeoCLM_symm_comp he he') (compDiffeoCLM_symm_comp (e := e.symm) he' he)

lemma compDiffeoCLE_apply (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (f : 𝓢(E, F)) (x : E) :
    compDiffeoCLE 𝕜 F e he he' f x = (jacobianWeight e x : 𝕜) • f (e x) :=
  compDiffeoCLM_apply he he' f x

lemma compDiffeoCLE_symm (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) :
    (compDiffeoCLE 𝕜 F e he he').symm = compDiffeoCLE 𝕜 F e.symm he' he :=
  rfl

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Change of variables along `e`.** `∫ |det De| • g ∘ e ∂μ = ∫ g ∂μ`. -/
theorem integral_abs_jacobianDet_smul_comp {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (he : (e : E → E).HasTemperateGrowth) (g : E → G) :
    ∫ x, |jacobianDet e x| • g (e x) ∂μ = ∫ y, g y ∂μ := by
  have hd : Differentiable ℝ e := he.1.differentiable (by simp)
  have := integral_image_eq_integral_abs_det_fderiv_smul μ MeasurableSet.univ
    (fun x _ => (hd x).hasFDerivAt.hasFDerivWithinAt) e.injective.injOn g
  rw [Set.image_univ, e.range_eq_univ, Measure.restrict_univ] at this
  exact this.symm

/-- **`U_e` is unitary.** The change of variable `f ↦ |det De|^{1/2} • (f ∘ e)` preserves the `L²`
inner product. -/
theorem integral_inner_compDiffeoCLE {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedSpace ℝ H] (he : (e : E → E).HasTemperateGrowth)
    (he' : (e.symm : E → E).HasTemperateGrowth) (f g : 𝓢(E, H)) :
    ∫ x, ⟪compDiffeoCLE 𝕜 H e he he' f x, compDiffeoCLE 𝕜 H e he he' g x⟫_𝕜 ∂μ =
      ∫ x, ⟪f x, g x⟫_𝕜 ∂μ := by
  rw [← integral_abs_jacobianDet_smul_comp μ he (fun y => ⟪f y, g y⟫_𝕜)]
  congr 1
  ext x
  rw [compDiffeoCLE_apply, compDiffeoCLE_apply, inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal, ← mul_assoc, ← RCLike.ofReal_mul, ← sq, jacobianWeight_sq,
    RCLike.real_smul_eq_coe_mul]

end SchwartzMap

