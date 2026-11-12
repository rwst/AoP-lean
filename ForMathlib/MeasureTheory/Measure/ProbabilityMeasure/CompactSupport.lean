/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Measures concentrated on a compact set

For finite measures that give no mass to the complement of a compact set `K`, every continuous
function is integrable, and on the probability measures concentrated on `K` the integral of a
continuous real function is continuous for the topology of weak convergence, although the
function need not be bounded. Continuous images keep measures concentrated on compact sets.

## Main results

* `MeasureTheory.integrable_of_isCompact`: a continuous function is integrable for a finite
  measure concentrated on a compact set;
* `MeasureTheory.ProbabilityMeasure.continuousOn_integral_of_isCompact`: `μ ↦ ∫ g dμ` is
  continuous on the probability measures concentrated on a compact set;
* `MeasureTheory.Measure.map_compl_image_eq_zero`: the image of a measure concentrated on `K`
  under a continuous map is concentrated on the compact set `φ '' K`.
-/

open Set
open scoped BoundedContinuousFunction

public section

namespace MeasureTheory

variable {X Y E : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  {K : Set X}

/-- A continuous function is integrable for a finite measure concentrated on a compact set. -/
theorem integrable_of_isCompact [T2Space X] [NormedAddCommGroup E] {μ : Measure X}
    [IsFiniteMeasure μ] (hK : IsCompact K) (hμ : μ Kᶜ = 0) {g : X → E} (hg : Continuous g) :
    Integrable g μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμ)]
  exact hg.continuousOn.integrableOn_compact hK

/-- On the probability measures concentrated on a compact set `K`, the integral of a continuous
real function is continuous for the topology of weak convergence. -/
theorem ProbabilityMeasure.continuousOn_integral_of_isCompact (hK : IsCompact K) {g : X → ℝ}
    (hg : Continuous g) :
    ContinuousOn (fun μ : ProbabilityMeasure X => ∫ x, g x ∂μ)
      {μ | (μ : Measure X) Kᶜ = 0} := by
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  set C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  set h : X →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun x => max (-C) (min (g x) C), by fun_prop⟩ (2 * C) fun x y => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq, abs_le]
      constructor <;>
      linarith [le_max_left (-C) (min (g x) C), le_max_left (-C) (min (g y) C),
        max_le (by linarith : -C ≤ C) (min_le_right (g x) C),
        max_le (by linarith : -C ≤ C) (min_le_right (g y) C)]
  refine (ProbabilityMeasure.continuous_integral_boundedContinuousFunction h).continuousOn.congr
    fun μ hμ => integral_congr_ae ?_
  filter_upwards [ae_iff.2 hμ] with x hx
  have hgx : |g x| ≤ C := (Real.norm_eq_abs _ ▸ hC₀ x hx).trans (le_max_left _ _)
  rw [abs_le] at hgx
  simp [h, min_eq_left hgx.2, max_eq_right hgx.1]

/-- The image of a measure concentrated on a compact set `K` under a continuous map `φ` is
concentrated on the compact set `φ '' K`. -/
theorem Measure.map_compl_image_eq_zero [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y]
    [BorelSpace Y] {μ : Measure X} {φ : X → Y} (hφ : Continuous φ) (hK : IsCompact K)
    (hμ : μ Kᶜ = 0) : μ.map φ (φ '' K)ᶜ = 0 := by
  rw [Measure.map_apply hφ.measurable (hK.image hφ).isClosed.measurableSet.compl]
  exact measure_mono_null (show φ ⁻¹' (φ '' K)ᶜ ⊆ Kᶜ from fun x hx hxK => hx ⟨x, hxK, rfl⟩) hμ

end MeasureTheory
