/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# A Hilbert basis of eigenvectors of a compact self-adjoint operator

Mathlib's spectral theorem for compact self-adjoint operators,
`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`, says that the eigenspaces span
a dense subspace. Choosing a Hilbert basis of each (closed) eigenspace and collecting them gives a
Hilbert basis of the whole space that consists of eigenvectors.

## Main results

* `ContinuousLinearMap.exists_hilbertBasis_eigenvectors`
-/

@[expose] public section

open scoped InnerProductSpace
open Module End

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {T : E →L[𝕜] E}

/-- **A compact self-adjoint operator has a Hilbert basis of eigenvectors.** -/
theorem exists_hilbertBasis_eigenvectors (hT : IsCompactOperator T)
    (hT' : (T : E →ₗ[𝕜] E).IsSymmetric) :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) ∧ ∀ x ∈ w, ∃ μ : 𝕜, T x = μ • x := by
  let K : 𝕜 → Submodule 𝕜 E := fun μ => eigenspace (T : E →ₗ[𝕜] E) μ
  have : ∀ μ, CompleteSpace (K μ) := fun μ => (isClosed_eigenspace T μ).completeSpace_coe
  choose w b _ using fun μ => exists_hilbertBasis 𝕜 (K μ)
  let v : (Σ μ, w μ) → E := fun a => (b a.1 a.2 : E)
  have hv : Orthonormal 𝕜 v :=
    hT'.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal fun μ => (b μ).orthonormal
  -- Every eigenspace lies in the closure of the span of `v`.
  have hK : ∀ μ, K μ ≤ (Submodule.span 𝕜 (Set.range v))ᗮᗮ := by
    intro μ u hu y hy
    let L : K μ →L[𝕜] 𝕜 := (innerSL 𝕜 y).comp (K μ).subtypeL
    have h := ((b μ).hasSum_repr ⟨u, hu⟩).mapL L
    have h0 : ∀ i, L ((b μ).repr ⟨u, hu⟩ i • b μ i) = 0 := fun i => by
      have : ⟪y, v ⟨μ, i⟩⟫_𝕜 = 0 :=
        Submodule.inner_left_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self _)) hy
      simp [L, v] at this ⊢
      exact Or.inr this
    simp only [h0] at h
    simpa [L] using h.unique hasSum_zero
  have hspan : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ := by
    refine eq_bot_iff.2 ((Submodule.le_orthogonal_orthogonal _).trans ?_)
    rw [← orthogonalComplement_iSup_eigenspaces_eq_bot hT hT']
    exact Submodule.orthogonal_le (iSup_le hK)
  have hs : Orthonormal 𝕜 ((↑) : Set.range v → E) :=
    (orthonormal_subtype_range hv.linearIndependent.injective).2 hv
  refine ⟨Set.range v, HilbertBasis.mkOfOrthogonalEqBot hs (by rwa [Subtype.range_coe]),
    HilbertBasis.coe_mkOfOrthogonalEqBot _ _, ?_⟩
  rintro _ ⟨⟨μ, i⟩, rfl⟩
  exact ⟨μ, mem_eigenspace_iff.1 (b μ i).2⟩

end ContinuousLinearMap
