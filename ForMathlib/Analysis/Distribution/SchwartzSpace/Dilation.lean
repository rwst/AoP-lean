/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilations of Schwartz functions on `ℝ`

For a unit `a : ℝˣ`, the dilation `f ↦ √|a| f(a ·)` is a continuous linear map on `𝓢(ℝ, F)`. The
factor `√|a|` makes it preserve the `L²` inner product. Dilations compose multiplicatively, so
the dilation by `a⁻¹` inverts the dilation by `a`.

## Main definitions

* `SchwartzMap.dilation a`: `f ↦ √|a| f(a ·)`.

## Main statements

* `SchwartzMap.dilation_dilation`, `SchwartzMap.dilation_inv_dilation`: composition and inverse;
* `SchwartzMap.integral_inner_dilation`: `∫ ⟪D f, D g⟫ = ∫ ⟪f, g⟫`.
-/

@[expose] public section

noncomputable section

namespace SchwartzMap

open MeasureTheory
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The dilation `f ↦ √|a| f(a ·)` of Schwartz functions on `ℝ`. -/
def dilation (a : ℝˣ) : 𝓢(ℝ, F) →L[ℂ] 𝓢(ℝ, F) :=
  ((√|(a : ℝ)| : ℝ) : ℂ) •
    compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.unitsEquivAut ℝ a)

theorem dilation_apply (a : ℝˣ) (f : 𝓢(ℝ, F)) (x : ℝ) :
    dilation a f x = ((√|(a : ℝ)| : ℝ) : ℂ) • f (a * x) := by
  simp [dilation, mul_comm (x : ℝ)]

theorem dilation_dilation (a b : ℝˣ) (f : 𝓢(ℝ, F)) :
    dilation a (dilation b f) = dilation (a * b) f := by
  ext x
  simp only [dilation_apply, smul_smul, Units.val_mul, abs_mul,
    Real.sqrt_mul (abs_nonneg _), Complex.ofReal_mul]
  congr 2
  ring

theorem dilation_one (f : 𝓢(ℝ, F)) : dilation 1 f = f := by
  ext x
  simp [dilation_apply]

theorem dilation_inv_dilation (a : ℝˣ) (f : 𝓢(ℝ, F)) : dilation a⁻¹ (dilation a f) = f := by
  rw [dilation_dilation, inv_mul_cancel, dilation_one]

theorem dilation_dilation_inv (a : ℝˣ) (f : 𝓢(ℝ, F)) : dilation a (dilation a⁻¹ f) = f := by
  rw [dilation_dilation, mul_inv_cancel, dilation_one]

/-- Dilations preserve the `L²` inner product. -/
theorem integral_inner_dilation {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (a : ℝˣ) (f g : 𝓢(ℝ, F)) :
    ∫ x, ⟪dilation a f x, dilation a g x⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ := by
  have ha : (a : ℝ) ≠ 0 := a.ne_zero
  simp only [dilation_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
  rw [integral_const_mul (μ := volume),
    Measure.integral_comp_mul_left (fun x => ⟪f x, g x⟫_ℂ), Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, ← abs_mul, mul_inv_cancel₀ ha, abs_one, Complex.ofReal_one, one_mul]

end SchwartzMap
