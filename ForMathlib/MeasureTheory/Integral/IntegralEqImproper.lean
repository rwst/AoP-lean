/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A sup bound from an integrable derivative

If `f : ℝ → E` and its derivative are integrable, then `f` tends to `0` at `-∞`, so
`f x = ∫_{-∞}^x f'` and `‖f x‖ ≤ ∫ ‖f'‖` for every `x`.

## Main results

* `MeasureTheory.enorm_le_lintegral_enorm_deriv`;
* `MeasureTheory.norm_le_integral_norm_deriv`.
-/

open Set Filter Topology

@[expose] public section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem enorm_le_lintegral_enorm_deriv {f f' : ℝ → E} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Integrable f') (hf : Integrable f) (x : ℝ) : ‖f x‖ₑ ≤ ∫⁻ y, ‖f' y‖ₑ := by
  have h0 := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := x) (fun y _ => hderiv y)
    hf'.integrableOn hf.integrableOn
  have hx := integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (fun y _ => hderiv y)
    hf'.integrableOn h0
  rw [sub_zero] at hx
  rw [← hx]
  exact (enorm_integral_le_lintegral_enorm _).trans (setLIntegral_le_lintegral _ _)

theorem norm_le_integral_norm_deriv {f f' : ℝ → E} (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Integrable f') (hf : Integrable f) (x : ℝ) : ‖f x‖ ≤ ∫ y, ‖f' y‖ := by
  have := enorm_le_lintegral_enorm_deriv hderiv hf' hf x
  rw [← ofReal_integral_norm_eq_lintegral_enorm hf', ← ofReal_norm] at this
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => norm_nonneg _)).mp this

end MeasureTheory
