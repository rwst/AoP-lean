/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Geometry.Symplectic.Manifold.FubiniStudy
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Measure.OpenPos
import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure

/-!
# The Liouville measure of the Fubini–Study form

`ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`, a real manifold of dimension `2 n` with the Borel σ-algebra, carries
the Liouville measure `|ωⁿ / n!|` of its Fubini–Study form `ω`
(`Projectivization.fubiniStudyMeasure`). Since `ℂPⁿ` is compact and `ω` is nondegenerate, it is a
finite measure that is positive on nonempty open sets, so it is not zero; for `n ≥ 1` points are
null. The maps of `ℂPⁿ` induced by unitary maps of `ℂⁿ⁺¹` preserve it.

## Main definitions

* `Projectivization.fubiniStudyMeasure n`: the Liouville measure of the Fubini–Study form.

## Main results

* `Projectivization.isFiniteMeasure_fubiniStudyMeasure`: it is finite;
* `Projectivization.isOpenPosMeasure_fubiniStudyMeasure`: it is positive on nonempty open sets;
* `Projectivization.fubiniStudyMeasure_ne_zero`: it is not zero;
* `Projectivization.nullSingletonClass_fubiniStudyMeasure`: for `n ≥ 1` points are null;
* `Projectivization.measurePreserving_unitaryMap`: unitary maps preserve it.
-/

open MeasureTheory
open scoped LinearAlgebra.Projectivization Manifold ContDiff

public section

noncomputable section

namespace Projectivization

variable {𝕜 V : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [TopologicalSpace V]

/-- Projective space carries the Borel σ-algebra of its quotient topology. -/
instance instMeasurableSpace : MeasurableSpace (ℙ 𝕜 V) := borel _

instance instBorelSpace : BorelSpace (ℙ 𝕜 V) := ⟨rfl⟩

variable {n : ℕ}

/-- `ℂPⁿ` is modelled on `Fin n → ℂ`, of real dimension `2 n`. -/
instance fact_finrank_fin_complex : Fact (Module.finrank ℝ (Fin n → ℂ) = 2 * n) :=
  ⟨by simp [Module.finrank_pi_fintype, mul_comm]⟩

variable (n) in
/-- **The Liouville measure of `ℂPⁿ`**: the measure `|ωⁿ / n!|` of the Fubini–Study form `ω`. -/
def fubiniStudyMeasure : Measure (ℙ ℂ (Fin (n + 1) → ℂ)) :=
  (fubiniStudyForm n).liouvilleMeasure n

/-- The Liouville measure of `ℂPⁿ` is finite, since `ℂPⁿ` is compact. -/
instance isFiniteMeasure_fubiniStudyMeasure : IsFiniteMeasure (fubiniStudyMeasure n) := by
  unfold fubiniStudyMeasure
  infer_instance

/-- The Liouville measure of `ℂPⁿ` is positive on nonempty open sets, since the Fubini–Study form
is nondegenerate. -/
instance isOpenPosMeasure_fubiniStudyMeasure : (fubiniStudyMeasure n).IsOpenPosMeasure :=
  isSymplectic_fubiniStudyForm.isNondegenerate.isOpenPosMeasure_liouvilleMeasure

/-- The Liouville measure of `ℂPⁿ` is not zero. -/
theorem fubiniStudyMeasure_ne_zero : fubiniStudyMeasure n ≠ 0 := fun h ↦ by
  have : Nonempty (ℙ ℂ (Fin (n + 1) → ℂ)) := ⟨mk ℂ (Pi.single 0 1) (by simp)⟩
  exact (isOpen_univ.measure_pos (fubiniStudyMeasure n) Set.univ_nonempty).ne' (by simp [h])

/-- For `n ≥ 1` points of `ℂPⁿ` have Liouville measure zero. -/
instance nullSingletonClass_fubiniStudyMeasure [NeZero n] :
    NullSingletonClass (fubiniStudyMeasure n) := by
  unfold fubiniStudyMeasure
  infer_instance

/-- **Unitary maps preserve the Liouville measure of `ℂPⁿ`**, since they preserve the Fubini–Study
form. -/
theorem measurePreserving_unitaryMap
    (U : EuclideanSpace ℂ (Fin (n + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (n + 1))) :
    MeasurePreserving (unitaryMap U) (fubiniStudyMeasure n) (fubiniStudyMeasure n) := by
  refine (unitaryMap U).measurePreserving_liouvilleMeasure
    ((contMDiff_unitaryMap U ∞).mdifferentiable (by simp)) ?_
  rw [← TauCeti.SmoothForm.coe_mpullback _ (contMDiff_unitaryMap U ∞),
    mpullback_unitaryMap_fubiniStudyForm]

end Projectivization
