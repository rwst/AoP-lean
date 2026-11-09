/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Stinespring.Kernel
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Positive matrices of operators

A `k × k` matrix `M` of bounded operators on a Hilbert space `H` acts block by block on `Hᵏ`,
and this block operator `blockMatrixMap M` is an injective ⋆-homomorphism of C⋆-algebras: the
entry `M i j` is the block operator applied to a vector supported in the `j`-th slot, read off
in the `i`-th slot. An injective ⋆-homomorphism of C⋆-algebras is an order embedding, so `M` is
positive in the C⋆-algebra of matrices exactly when its block operator is positive, that is,
when `∑ᵢⱼ ⟪xᵢ, Mᵢⱼ xⱼ⟫ ≥ 0` for every `x ∈ Hᵏ`. This turns complete positivity of a map into
pointwise inequalities, which survive limits and integrals in any operator topology.

## Main results

* `ProbabilisticTheory.blockMatrixMap_injective`
* `ProbabilisticTheory.blockMatrixMap_nonneg_iff`: `0 ≤ blockMatrixMap M ↔ 0 ≤ M`.
* `ProbabilisticTheory.cstarMatrix_nonneg_iff`: `0 ≤ M ↔ ∀ x, 0 ≤ ∑ᵢⱼ ⟪xᵢ, Mᵢⱼ xⱼ⟫`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder

namespace ProbabilisticTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {k : ℕ}

omit [CompleteSpace H] in
lemma blockMatrixMap_injective :
    Function.Injective (blockMatrixMap : CStarMatrix (Fin k) (Fin k) (H →L[ℂ] H) → _) := by
  intro M N h
  refine CStarMatrix.ext fun i j => ContinuousLinearMap.ext fun v => ?_
  have hv := congrArg (fun T => (T (WithLp.toLp 2 (Pi.single j v))).ofLp i) h
  simpa [blockMatrixMap_apply, Pi.single_apply, apply_ite, Finset.sum_ite_eq'] using hv

/-- A matrix of operators is positive exactly when its block operator is. -/
lemma blockMatrixMap_nonneg_iff {M : CStarMatrix (Fin k) (Fin k) (H →L[ℂ] H)} :
    0 ≤ blockMatrixMap M ↔ 0 ≤ M := by
  have h := NonUnitalStarAlgHom.map_le_map_iff (blockMatrixRepresentation (H := H) (n := k))
    blockMatrixMap_injective (x := 0) (y := M)
  rwa [map_zero] at h

/-- **Positive matrices of operators.** A matrix `M` of operators on `H` is positive exactly when
`∑ᵢⱼ ⟪xᵢ, Mᵢⱼ xⱼ⟫ ≥ 0` for every `x ∈ Hᵏ`. -/
theorem cstarMatrix_nonneg_iff {M : CStarMatrix (Fin k) (Fin k) (H →L[ℂ] H)} :
    0 ≤ M ↔ ∀ x : PiLp 2 (fun _ : Fin k => H), 0 ≤ ∑ i, ∑ j, ⟪x i, M i j (x j)⟫_ℂ := by
  have hsum : ∀ x : PiLp 2 (fun _ : Fin k => H),
      ⟪x, blockMatrixMap M x⟫_ℂ = ∑ i, ∑ j, ⟪x i, M i j (x j)⟫_ℂ := fun x => by
    simp [PiLp.inner_apply, blockMatrixMap_apply, inner_sum]
  rw [← blockMatrixMap_nonneg_iff, ContinuousLinearMap.nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  refine ⟨fun h x => ?_, fun h x => ?_⟩
  · rw [← hsum, ← inner_conj_symm, ← (h x).1]
    simpa using (h x).2
  · have hx := h x
    rw [← hsum, Complex.nonneg_iff] at hx
    have hre : ⟪blockMatrixMap M x, x⟫_ℂ = ((⟪x, blockMatrixMap M x⟫_ℂ).re : ℂ) := by
      rw [← inner_conj_symm]
      apply Complex.ext
      · rw [Complex.conj_re, Complex.ofReal_re]
      · rw [Complex.conj_im, Complex.ofReal_im, ← hx.2, neg_zero]
    rw [hre, RCLike.re_to_complex, Complex.ofReal_re]
    exact ⟨rfl, hx.1⟩

end ProbabilisticTheory
