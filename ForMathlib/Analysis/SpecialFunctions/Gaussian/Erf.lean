/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The error function

Mathlib has the Gaussian integral but no error function. This file defines

  `erf x = (2 / √π) ∫₀ˣ e^{-t²} dt`

and proves the basic facts needed to use it as a change of variables.

## Main results

* `Real.hasDerivAt_erf`: `erf' x = (2/√π) e^{-x²}`;
* `Real.strictMono_erf`: `erf` is strictly increasing;
* `Real.erf_neg`: `erf` is odd;
* `Real.tendsto_erf_atTop`: `erf x → 1` as `x → ∞`;
* `Real.abs_erf_lt_one`: `|erf x| < 1`.
-/

open Filter Topology Set MeasureTheory

@[expose] public noncomputable section

namespace Real

/-- The error function `erf x = (2/√π) ∫₀ˣ e^{-t²} dt`. -/
def erf (x : ℝ) : ℝ := 2 / √π * ∫ t in (0 : ℝ)..x, exp (-t ^ 2)

lemma continuous_exp_neg_sq : Continuous fun t : ℝ => exp (-t ^ 2) := by fun_prop

lemma hasDerivAt_integral_exp_neg_sq (x : ℝ) :
    HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, exp (-t ^ 2)) (exp (-x ^ 2)) x :=
  (continuous_exp_neg_sq.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem hasDerivAt_erf (x : ℝ) : HasDerivAt erf (2 / √π * exp (-x ^ 2)) x :=
  (hasDerivAt_integral_exp_neg_sq x).const_mul _

theorem continuous_erf : Continuous erf :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_erf x).continuousAt

lemma strictMono_integral_exp_neg_sq :
    StrictMono fun u => ∫ t in (0 : ℝ)..u, exp (-t ^ 2) :=
  strictMono_of_hasDerivAt_pos hasDerivAt_integral_exp_neg_sq fun _ => exp_pos _

theorem strictMono_erf : StrictMono erf :=
  strictMono_integral_exp_neg_sq.const_mul (by positivity)

lemma tendsto_integral_exp_neg_sq :
    Tendsto (fun u => ∫ t in (0 : ℝ)..u, exp (-t ^ 2)) atTop (𝓝 (√π / 2)) := by
  have hi : IntegrableOn (fun t : ℝ => exp (-t ^ 2)) (Ioi 0) := by
    simpa using (integrable_exp_neg_mul_sq (b := 1) one_pos).integrableOn
  have := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
  have hv : ∫ t in Ioi (0 : ℝ), exp (-t ^ 2) = √π / 2 := by
    simpa using integral_gaussian_Ioi 1
  rwa [hv] at this

lemma integral_exp_neg_sq_neg (x : ℝ) :
    ∫ t in (0 : ℝ)..(-x), exp (-t ^ 2) = -∫ t in (0 : ℝ)..x, exp (-t ^ 2) := by
  have := intervalIntegral.integral_comp_neg (a := 0) (b := -x) (fun t : ℝ => exp (-t ^ 2))
  simp only [neg_sq, neg_neg, neg_zero] at this
  rw [this, intervalIntegral.integral_symm]

theorem erf_neg (x : ℝ) : erf (-x) = -erf x := by
  rw [erf, erf, integral_exp_neg_sq_neg, mul_neg]

theorem tendsto_erf_atTop : Tendsto erf atTop (𝓝 1) := by
  have h := tendsto_integral_exp_neg_sq.const_mul (2 / √π)
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  rwa [show 2 / √π * (√π / 2) = 1 by field_simp] at h

lemma integral_exp_neg_sq_lt (x : ℝ) : ∫ t in (0 : ℝ)..x, exp (-t ^ 2) < √π / 2 :=
  (strictMono_integral_exp_neg_sq (lt_add_one x)).trans_le
    (strictMono_integral_exp_neg_sq.monotone.ge_of_tendsto tendsto_integral_exp_neg_sq _)

theorem erf_lt_one (x : ℝ) : erf x < 1 := by
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  rw [erf, ← lt_div_iff₀' (by positivity)]
  calc ∫ t in (0 : ℝ)..x, exp (-t ^ 2) < √π / 2 := integral_exp_neg_sq_lt x
    _ = 1 / (2 / √π) := by field_simp

theorem abs_erf_lt_one (x : ℝ) : |erf x| < 1 := by
  refine abs_lt.mpr ⟨?_, erf_lt_one x⟩
  have := erf_lt_one (-x)
  rw [erf_neg] at this
  linarith

end Real
