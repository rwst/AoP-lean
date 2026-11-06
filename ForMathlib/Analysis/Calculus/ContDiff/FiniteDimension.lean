/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smoothness of the determinant

On a finite-dimensional space the determinant of an endomorphism is a polynomial in its matrix
entries, each of which is a continuous linear function of the endomorphism. So it is smooth.

## Main results

* `ContinuousLinearMap.contDiff_det`: `f ↦ det f` is `C^n` for every `n`.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {n : WithTop ℕ∞}

theorem ContinuousLinearMap.contDiff_det : ContDiff 𝕜 n fun f : E →L[𝕜] E => f.det := by
  classical
  let b := Module.finBasis 𝕜 E
  have hentry : ∀ i j, ContDiff 𝕜 n fun f : E →L[𝕜] E =>
      LinearMap.toMatrix b b (f : E →ₗ[𝕜] E) i j := fun i j => by
    simp only [LinearMap.toMatrix_apply]
    exact ((LinearMap.toContinuousLinearMap (b.coord i)).comp
      (ContinuousLinearMap.apply 𝕜 E (b j))).contDiff
  change ContDiff 𝕜 n fun f : E →L[𝕜] E => LinearMap.det (f : E →ₗ[𝕜] E)
  simp_rw [← LinearMap.det_toMatrix b, Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hentry _ _)

end
