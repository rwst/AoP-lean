/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The integral of `(1 + x²)⁻²`

Mathlib has `∫ (1 + x²)⁻¹ = π` (`integral_univ_inv_one_add_sq`). This file adds

  `∫ (1 + x²)⁻² = π / 2`,

from the antiderivative `x / (2(1 + x²)) + arctan x / 2`, and `∫_{|x| > 1} x⁻² = 2`.

## Main results

* `integrable_inv_one_add_sq_sq`, `integral_univ_inv_one_add_sq_sq`;
* `integral_Ioi_one_inv_sq`, `integral_Iio_neg_one_inv_sq`.
-/

open Real Filter Topology Set MeasureTheory

@[expose] public section

theorem integrable_inv_one_add_sq_sq : Integrable fun x : ℝ => ((1 + x ^ 2) ^ 2)⁻¹ := by
  refine integrable_inv_one_add_sq.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  have h1 : 1 ≤ 1 + x ^ 2 := by nlinarith
  rw [Real.norm_of_nonneg (by positivity)]
  exact inv_anti₀ (by positivity) (by nlinarith)

lemma hasDerivAt_antideriv_inv_one_add_sq_sq (x : ℝ) :
    HasDerivAt (fun x => x / (2 * (1 + x ^ 2)) + arctan x / 2) ((1 + x ^ 2) ^ 2)⁻¹ x := by
  have h1 : (1 + x ^ 2) ≠ 0 := by positivity
  have := ((hasDerivAt_id x).div (((hasDerivAt_pow 2 x).const_add 1).const_mul 2)
    (by positivity)).add ((hasDerivAt_arctan x).div_const 2)
  refine this.congr_deriv ?_
  simp only [id, Nat.cast_ofNat]
  field_simp
  ring

lemma tendsto_div_two_mul_one_add_sq (l : Filter ℝ) (hl : Tendsto (fun x : ℝ => |x|) l atTop) :
    Tendsto (fun x : ℝ => x / (2 * (1 + x ^ 2))) l (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => (2 * |x|)⁻¹) l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (hl.const_mul_atTop two_pos)
  refine squeeze_zero_norm (fun x => ?_) h
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : 0 < |x| := abs_pos.mpr hx
  rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity),
    div_le_iff₀ (by positivity)]
  have : |x| ^ 2 = x ^ 2 := sq_abs x
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  nlinarith

theorem integral_univ_inv_one_add_sq_sq : ∫ x : ℝ, ((1 + x ^ 2) ^ 2)⁻¹ = π / 2 := by
  have hbot : Tendsto (fun x => x / (2 * (1 + x ^ 2)) + arctan x / 2) atBot
      (𝓝 (0 + -(π / 2) / 2)) :=
    (tendsto_div_two_mul_one_add_sq _ tendsto_abs_atBot_atTop).add
      ((tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).div_const 2)
  have htop : Tendsto (fun x => x / (2 * (1 + x ^ 2)) + arctan x / 2) atTop
      (𝓝 (0 + π / 2 / 2)) :=
    (tendsto_div_two_mul_one_add_sq _ tendsto_abs_atTop_atTop).add
      ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).div_const 2)
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_antideriv_inv_one_add_sq_sq
    integrable_inv_one_add_sq_sq hbot htop]
  ring

lemma inv_sq_eq_rpow {x : ℝ} (hx : 0 < x) : (x ^ 2)⁻¹ = x ^ (-2 : ℝ) := by
  rw [rpow_neg hx.le, show (2 : ℝ) = (2 : ℕ) by norm_num, rpow_natCast]

theorem integrableOn_Ioi_one_inv_sq : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).congr_fun
    (fun x hx => (inv_sq_eq_rpow (one_pos.trans hx)).symm) measurableSet_Ioi

theorem integral_Ioi_one_inv_sq : ∫ x in Ioi (1 : ℝ), (x ^ 2)⁻¹ = 1 := by
  rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => inv_sq_eq_rpow (one_pos.trans hx),
    integral_Ioi_rpow_of_lt (by norm_num) one_pos]
  norm_num

theorem integrableOn_Iio_neg_one_inv_sq : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Iio (-1)) := by
  have := integrableOn_Ioi_one_inv_sq.comp_neg
  simpa using this

theorem integral_Iio_neg_one_inv_sq : ∫ x in Iio (-1 : ℝ), (x ^ 2)⁻¹ = 1 := by
  have := integral_comp_neg_Ioi (1 : ℝ) fun x : ℝ => (x ^ 2)⁻¹
  simp only [neg_sq] at this
  rw [← integral_Iic_eq_integral_Iio, ← this, integral_Ioi_one_inv_sq]
