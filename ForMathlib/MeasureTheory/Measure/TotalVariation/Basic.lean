/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic

import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Total variation distance between measures with densities

For integrable densities `f` and `g` with respect to the same measure `μ`, the total variation
distance between `μ.withDensity f` and `μ.withDensity g` is the `L¹(μ)` distance of `f` and `g`.
This generalizes `MeasureTheory.tvDist_withDensity_self_eq_integral`, the case `g = 1`.

## Main statements

* `MeasureTheory.isHahnDecomposition_withDensity_of_ae_le`: a set on which `f ≤ g`, with
  `g ≤ f` on its complement, is a Hahn decomposition;
* `MeasureTheory.tvDist_withDensity_eq_integral`,
  `MeasureTheory.etvDist_withDensity_eq_lintegral`: the total variation distance is the `L¹`
  distance of the densities.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ : Measure 𝓧} {f g : 𝓧 → ℝ≥0∞}

lemma isHahnDecomposition_withDensity_of_ae_le {s : Set 𝓧} (hs : MeasurableSet s)
    (h_le : ∀ᵐ x ∂μ.restrict s, f x ≤ g x) (h_ge : ∀ᵐ x ∂μ.restrict sᶜ, g x ≤ f x) :
    IsHahnDecomposition (μ.withDensity f) (μ.withDensity g) s where
  measurableSet := hs
  le_on := by
    rw [restrict_withDensity hs, restrict_withDensity hs]
    exact withDensity_mono h_le
  ge_on_compl := by
    rw [restrict_withDensity hs.compl, restrict_withDensity hs.compl]
    exact withDensity_mono h_ge

lemma tvDist_withDensity_eq_integral (hf : Integrable f μ) (hg : Integrable g μ) :
    tvDist (μ.withDensity f) (μ.withDensity g) = ∫ x, |(f x).toReal - (g x).toReal| ∂μ := by
  have hf_meas : AEMeasurable f μ := hf.aemeasurable
  have hg_meas : AEMeasurable g μ := hg.aemeasurable
  have : IsFiniteMeasure (μ.withDensity f) := isFiniteMeasure_withDensity hf.hasFiniteIntegral.ne
  have : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.hasFiniteIntegral.ne
  have hf_top : ∀ᵐ x ∂μ, f x ≠ ∞ := by
    filter_upwards [ae_lt_top' hf_meas hf.hasFiniteIntegral.ne] with x hx using hx.ne
  have hg_top : ∀ᵐ x ∂μ, g x ≠ ∞ := by
    filter_upwards [ae_lt_top' hg_meas hg.hasFiniteIntegral.ne] with x hx using hx.ne
  have hF : Integrable (fun x ↦ (f x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hf_meas hf.hasFiniteIntegral.ne
  have hG : Integrable (fun x ↦ (g x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hg_meas hg.hasFiniteIntegral.ne
  set s := {x | hf_meas.mk f x ≤ hg_meas.mk g x}
  have hs : MeasurableSet s := measurableSet_le hf_meas.measurable_mk hg_meas.measurable_mk
  have hs_le : ∀ᵐ x ∂μ.restrict s, f x ≤ g x := by
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hf_meas.ae_eq_mk,
      ae_restrict_of_ae hg_meas.ae_eq_mk] with x hxs hfx hgx
    rw [hfx, hgx]
    exact hxs
  have hs_ge : ∀ᵐ x ∂μ.restrict sᶜ, g x ≤ f x := by
    filter_upwards [ae_restrict_mem hs.compl, ae_restrict_of_ae hf_meas.ae_eq_mk,
      ae_restrict_of_ae hg_meas.ae_eq_mk] with x hxs hfx hgx
    rw [hfx, hgx]
    exact (not_le.mp hxs).le
  have hreal {h : 𝓧 → ℝ≥0∞} (hm : AEMeasurable h μ) (htop : ∀ᵐ x ∂μ, h x ≠ ∞) {t : Set 𝓧}
      (ht : MeasurableSet t) : (μ.withDensity h).real t = ∫ x in t, (h x).toReal ∂μ :=
    withDensity_real_apply_eq_integral hm.restrict
      (by filter_upwards [htop] with x hx _ using hx.lt_top) ht.nullMeasurableSet
  rw [(isHahnDecomposition_withDensity_of_ae_le hs hs_le hs_ge).tvDist_eq,
    hreal hg_meas hg_top hs, hreal hf_meas hf_top hs, hreal hf_meas hf_top hs.compl,
    hreal hg_meas hg_top hs.compl, ← integral_sub hG.integrableOn hF.integrableOn,
    ← integral_sub hF.integrableOn hG.integrableOn,
    ← integral_add_compl hs (f := fun x ↦ |(f x).toReal - (g x).toReal|) (hF.sub hG).abs]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [hs_le, ae_restrict_of_ae hf_top, ae_restrict_of_ae hg_top] with x hx hfx hgx
    rw [abs_of_nonpos (sub_nonpos.mpr ((ENNReal.toReal_le_toReal hfx hgx).mpr hx)), neg_sub]
  · refine integral_congr_ae ?_
    filter_upwards [hs_ge, ae_restrict_of_ae hf_top, ae_restrict_of_ae hg_top] with x hx hfx hgx
    rw [abs_of_nonneg (sub_nonneg.mpr ((ENNReal.toReal_le_toReal hgx hfx).mpr hx))]

lemma etvDist_withDensity_eq_lintegral (hf : Integrable f μ) (hg : Integrable g μ) :
    etvDist (μ.withDensity f) (μ.withDensity g) = ∫⁻ x, ‖(f x).toReal - (g x).toReal‖ₑ ∂μ := by
  have : IsFiniteMeasure (μ.withDensity f) := isFiniteMeasure_withDensity hf.hasFiniteIntegral.ne
  have : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.hasFiniteIntegral.ne
  rw [← ofReal_tvDist, tvDist_withDensity_eq_integral hf hg,
    ofReal_integral_eq_lintegral_ofReal]
  · congr with x
    rw [← Real.norm_eq_abs, ofReal_norm]
  · exact ((integrable_toReal_of_lintegral_ne_top hf.aemeasurable hf.hasFiniteIntegral.ne).sub
      (integrable_toReal_of_lintegral_ne_top hg.aemeasurable hg.hasFiniteIntegral.ne)).abs
  · filter_upwards with x
    positivity

end MeasureTheory
