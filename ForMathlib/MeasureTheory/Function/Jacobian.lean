/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Maps with unit Jacobian preserve Haar measure

A differentiable bijection of a finite-dimensional real space whose Jacobian determinant has
absolute value `1` everywhere preserves every additive Haar measure. This is the measure-theoretic
half of Liouville's theorem: canonical transformations preserve phase-space volume.

## Main results

* `MeasureTheory.measurePreserving_of_abs_det_fderiv_eq_one`
-/

@[expose] public section

open Set Function

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A differentiable bijection with `|det f'| = 1` everywhere preserves an additive Haar
measure. -/
theorem measurePreserving_of_abs_det_fderiv_eq_one {f : E → E} {f' : E → E →L[ℝ] E}
    (hf' : ∀ x, HasFDerivAt f (f' x) x) (hbij : Bijective f) (hdet : ∀ x, |(f' x).det| = 1) :
    MeasurePreserving f μ μ := by
  have hm : Measurable f :=
    (continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt).measurable
  refine ⟨hm, Measure.ext fun A hA => ?_⟩
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ MeasurableSet.univ
    (fun x _ => (hf' x).hasFDerivWithinAt) hbij.1.injOn (A.indicator 1)
  rw [image_univ, hbij.2.range_eq, Measure.restrict_univ,
    lintegral_indicator_one hA] at h
  simp only [hdet, ENNReal.ofReal_one, one_mul] at h
  rw [Measure.map_apply hm hA, h, ← lintegral_indicator_one (hm hA)]
  rfl

end MeasureTheory
