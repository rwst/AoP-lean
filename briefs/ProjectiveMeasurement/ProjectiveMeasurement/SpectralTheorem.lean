/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ProjectiveMeasurement.InfiniteDimensional
public import ForPhyslib.QuantumMechanics.PurePointSpectralMeasure

/-!
# Projective measurements: the bridge from the spectral theorem

The part of the formalization in any dimension gives an observable by an eigendecomposition
`X = ∑ₓ x Pₓ` (`IsEigenDecomposition`). This module connects it with the spectral theorem.
A bounded self-adjoint `X` has pure point spectrum (`HasPurePointSpectrum`: its eigenvectors span
a dense subspace) exactly when its spectral measure `μ_S` is atomic, and then
`X = ∑ₓ x μ_S({x})` is an eigendecomposition (`isEigenDecomposition_spectral`). Conversely, every
eigendecomposition has `Pₓ = μ_S({x})` (`IsEigenDecomposition.spectralMeasureProj_singleton_eq`),
so the pinching `∑ₓ Pₓ ρ Pₓ` depends on `X` only. Hence EQ-MEAS can be stated with the spectral
projections of `X` (`eqMeas_iff_spectral`).

This module is separate from the main files of the brief, so that the comparator lane is
unchanged. No certified statement depends on it.
-/

@[expose] public noncomputable section

namespace ProjectiveMeasurement.InfiniteDimensional

open QuantumMechanics

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A self-adjoint `X` with pure point spectrum is `∑ₓ x μ_S({x})`, indexed in the universe of
`E`. -/
theorem isEigenDecomposition_spectral {X : E →L[ℂ] E} (hX : IsSelfAdjoint X)
    (hpp : HasPurePointSpectrum X) :
    IsEigenDecomposition X (fun a : ULift.{u} ℝ => spectralMeasureProj hX {a.down})
      fun a => a.down :=
  (isEigenDecomposition_spectralMeasureProj hX hpp).comp_equiv Equiv.ulift

variable {Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E}

/-- **EQ-MEAS with the spectral theorem**: the process returns `∑ₓ μ_S({x}) ρ μ_S({x})` for every
self-adjoint `X` with pure point spectrum. -/
theorem eqMeas_iff_spectral :
    EqMeas Φ ↔ ∀ (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (hpp : HasPurePointSpectrum X) ρ,
      IsDensityOperator ρ →
        Φ X ρ = (isEigenDecomposition_spectral hX hpp).isResolutionOfIdentity.pinching ρ := by
  refine ⟨fun h X hX hpp ρ hρ => h X _ _ (isEigenDecomposition_spectral hX hpp) ρ hρ,
    fun h X ι P x hX ρ hρ => ?_⟩
  rw [h X hX.isSelfAdjoint hX.hasPurePointSpectrum ρ hρ]
  exact IsEigenDecomposition.pinching_eq_pinching
    (isEigenDecomposition_spectral hX.isSelfAdjoint hX.hasPurePointSpectrum) hX ρ

end ProjectiveMeasurement.InfiniteDimensional
