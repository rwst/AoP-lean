/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Densities moved by measure-preserving equivalences

A measurable equivalence `e` carrying `μ` to `ν` carries the distribution with density `ρ` with
respect to `μ` to the distribution with density `ρ ∘ e⁻¹` with respect to `ν`. The Gibbs entropy
`∫ -ρ log ρ` is unchanged: it is the same integral after the change of variables `y = e x`.

## Main results

* `MeasureTheory.MeasurePreserving.map_withDensity`: `e_* (ρ μ) = (ρ ∘ e⁻¹) ν`.
* `MeasureTheory.MeasurePreserving.integral_negMulLog_comp_symm`: the moved density has the same
  Gibbs entropy.
-/

public section

open Real

namespace MeasureTheory.MeasurePreserving

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {e : α ≃ᵐ β}

/-- **A measure-preserving equivalence moves densities by composition with its inverse.** The
image under `e` of the distribution with density `ρ` with respect to `μ` has density `ρ ∘ e⁻¹`
with respect to `ν`. -/
theorem map_withDensity (h : MeasurePreserving e μ ν) (ρ : α → ENNReal) :
    (μ.withDensity ρ).map e = ν.withDensity (ρ ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, ← h.setLIntegral_comp_preimage_emb e.measurableEmbedding]
  simp

/-- **Measure-preserving equivalences preserve the Gibbs entropy.** The density `ρ ∘ e⁻¹` moved
by `e` has the same Gibbs entropy `∫ -ρ log ρ` as `ρ`. -/
theorem integral_negMulLog_comp_symm (h : MeasurePreserving e μ ν) (ρ : α → ℝ) :
    ∫ y, negMulLog (ρ (e.symm y)) ∂ν = ∫ x, negMulLog (ρ x) ∂μ := by
  simpa using (h.integral_comp' (fun y ↦ negMulLog (ρ (e.symm y)))).symm

end MeasureTheory.MeasurePreserving
