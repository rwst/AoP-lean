/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Geometry.Symplectic.Manifold.FubiniStudy.ProjectiveLine
public import ForPhyslib.QuantumMechanics.Qubit.BlochSphere

/-!
# The Bloch sphere as a symplectic sphere

The Bloch map `blochSphere` sends a ray `[z₀ : z₁]` of `ℂ²` to its Bloch vector
`(2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁), |z₀|² - |z₁|²) / (|z₀|² + |z₁|²)` on the unit sphere of
`ℝ³`. It is the diffeomorphism `Projectivization.sphereDiffeomorph` of the projective line onto the
round sphere (`QuantumMechanics.Qubit.coe_blochSphere_eq_sphereDiffeomorph`). So it is smooth, it
pulls the area form `x ⬝ (v × w)` of the sphere back to `4` times the Fubini–Study form of
`P(ℂ²)`, and it carries the Liouville measure of `P(ℂ²)` to a quarter of the area of the sphere.

## Main results

- `QuantumMechanics.Qubit.coe_blochSphere_eq_sphereDiffeomorph`: the Bloch map is the
  diffeomorphism of the projective line onto the sphere.
- `QuantumMechanics.Qubit.contMDiff_blochSphere`: the Bloch map is smooth.
- `QuantumMechanics.Qubit.mpullback_blochSphere_sphereAreaForm`: it pulls the area form back to `4`
  times the Fubini–Study form.
- `QuantumMechanics.Qubit.map_fubiniStudyMeasure_blochSphere`: it carries the Liouville measure to
  a quarter of the area measure.
-/

@[expose] public noncomputable section

open Complex Projectivization TauCeti MeasureTheory
open scoped LinearAlgebra.Projectivization Manifold ContDiff EuclideanSpace

namespace QuantumMechanics.Qubit

/-- **The Bloch map is the diffeomorphism of the projective line onto the round sphere** through
the Riemann sphere. -/
theorem coe_blochSphere_eq_sphereDiffeomorph : ⇑blochSphere = ⇑sphereDiffeomorph := by
  funext p
  obtain ⟨z, rfl⟩ := (OnePoint.equivProjectivization ℂ).surjective p
  refine Subtype.ext ?_
  induction z using OnePoint.rec with
  | infty =>
    rw [sphereDiffeomorph_equivProjectivization_infty, coe_blochSphere,
      OnePoint.equivProjectivization_apply_infinity, blochPoint_mk]
    ext i
    fin_cases i <;> simp [unitBlochVector, blochVector, EuclideanSpace.norm_sq_eq]
  | coe t =>
    rw [sphereDiffeomorph_equivProjectivization_coe, coe_blochSphere,
      OnePoint.equivProjectivization_apply_coe, blochPoint_mk]
    have hn : ‖WithLp.toLp 2 (![t, 1] : Fin 2 → ℂ)‖ ^ 2 = 1 + ‖t‖ ^ 2 := by
      simp [EuclideanSpace.norm_sq_eq, add_comm]
    ext i
    fin_cases i <;> simp [unitBlochVector, blochVector, hn]

/-- The Bloch map is smooth. -/
theorem contMDiff_blochSphere : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞ blochSphere := by
  rw [coe_blochSphere_eq_sphereDiffeomorph]
  exact sphereDiffeomorph.contMDiff

/-- **The Bloch map pulls the area form of the sphere back to `4` times the Fubini–Study form.** -/
theorem mpullback_blochSphere_sphereAreaForm :
    SmoothForm.mpullback blochSphere contMDiff_blochSphere sphereAreaForm =
      (4 : ℝ) • fubiniStudyForm 1 := by
  have hcongr (f g : ℙ ℂ (Fin 2 → ℂ) → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (hf : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞ f) (hg : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞ g)
      (hfg : f = g) :
      SmoothForm.mpullback f hf sphereAreaForm = SmoothForm.mpullback g hg sphereAreaForm := by
    subst hfg
    rfl
  rw [hcongr _ _ _ sphereDiffeomorph.contMDiff coe_blochSphere_eq_sphereDiffeomorph,
    mpullback_sphereDiffeomorph_sphereAreaForm]

/-- **The Bloch map carries the Liouville measure of `P(ℂ²)` to a quarter of the area of the
sphere.** -/
theorem map_fubiniStudyMeasure_blochSphere :
    (fubiniStudyMeasure 1).map blochSphere =
      (ENNReal.ofReal 4)⁻¹ • sphereAreaForm.liouvilleMeasure 1 := by
  rw [coe_blochSphere_eq_sphereDiffeomorph, map_fubiniStudyMeasure_sphereDiffeomorph]

end QuantumMechanics.Qubit
