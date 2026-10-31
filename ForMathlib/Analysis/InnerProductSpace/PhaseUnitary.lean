/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Diagonal phase unitaries and the phase form of Cauchy–Schwarz equality

Given an orthonormal basis `b` and scalars `δ i` of norm one, multiplying each `b i` by `δ i` gives
another orthonormal basis, and the unitary sending one basis to the other is the diagonal unitary
with entries `δ i` in the basis `b`.

The equality case of Cauchy–Schwarz is also stated in the form used for rays: two unit vectors
whose inner product has norm one differ by a scalar of norm one.

## Main definitions

* `OrthonormalBasis.phaseSMul`: the basis `i ↦ δ i • b i`.
* `OrthonormalBasis.phaseUnitary`: the unitary `b i ↦ δ i • b i`.

## Main results

* `OrthonormalBasis.phaseUnitary_symm_apply_basis`: its inverse, `b i ↦ (δ i)⁻¹ • b i`.
* `OrthonormalBasis.inner_basis_phaseUnitary`: its coordinates, `⟪b i, U x⟫ = δ i * ⟪b i, x⟫`.
* `exists_norm_eq_one_smul_of_norm_inner_eq_one`: unit vectors `x`, `y` with `‖⟪x, y⟫‖ = 1`
  satisfy `x = c • y` for some `c` of norm one.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι]

namespace OrthonormalBasis

variable (b : OrthonormalBasis ι 𝕜 E) (δ : ι → 𝕜) (hδ : ∀ i, ‖δ i‖ = 1)

include hδ in
theorem orthonormal_phase_smul : Orthonormal 𝕜 fun i => δ i • b i :=
  ⟨fun i => by rw [norm_smul, hδ, b.orthonormal.1 i, one_mul], fun i j hij => by
    dsimp only
    rw [inner_smul_left, inner_smul_right, b.orthonormal.2 hij, mul_zero, mul_zero]⟩

/-- Multiplying every vector of an orthonormal basis by a scalar of norm one gives an orthonormal
basis. -/
protected def phaseSMul : OrthonormalBasis ι 𝕜 E :=
  .mk (orthonormal_phase_smul b δ hδ) (by
    rw [← b.toBasis.span_eq, OrthonormalBasis.coe_toBasis]
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ?_)
    have hδ₀ : δ i ≠ 0 := by rw [← norm_ne_zero_iff, hδ]; exact one_ne_zero
    have : b i = (δ i)⁻¹ • δ i • b i := by rw [smul_smul, inv_mul_cancel₀ hδ₀, one_smul]
    exact this ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

@[simp]
theorem phaseSMul_apply (i : ι) : b.phaseSMul δ hδ i = δ i • b i :=
  congrFun (OrthonormalBasis.coe_mk _ _) i

/-- The diagonal unitary with entries `δ i` in the orthonormal basis `b`. -/
def phaseUnitary : E ≃ₗᵢ[𝕜] E :=
  b.equiv (b.phaseSMul δ hδ) (Equiv.refl ι)

@[simp]
theorem phaseUnitary_apply_basis (i : ι) : b.phaseUnitary δ hδ (b i) = δ i • b i := by
  simp [phaseUnitary]

theorem phaseUnitary_symm_apply_basis (i : ι) :
    (b.phaseUnitary δ hδ).symm (b i) = (δ i)⁻¹ • b i := by
  have hδ₀ : δ i ≠ 0 := by rw [← norm_ne_zero_iff, hδ]; exact one_ne_zero
  rw [LinearIsometryEquiv.symm_apply_eq, map_smul, phaseUnitary_apply_basis, smul_smul,
    inv_mul_cancel₀ hδ₀, one_smul]

theorem inner_basis_phaseUnitary (i : ι) (x : E) :
    ⟪b i, b.phaseUnitary δ hδ x⟫_𝕜 = δ i * ⟪b i, x⟫_𝕜 := by
  classical
  simp [phaseUnitary, equiv_apply, inner_sum, inner_smul_right,
    orthonormal_iff_ite.1 b.orthonormal, b.repr_apply_apply, mul_comm]

theorem inner_basis_phaseUnitary_symm (i : ι) (x : E) :
    ⟪b i, (b.phaseUnitary δ hδ).symm x⟫_𝕜 = (δ i)⁻¹ * ⟪b i, x⟫_𝕜 := by
  have hδ₀ : δ i ≠ 0 := by rw [← norm_ne_zero_iff, hδ]; exact one_ne_zero
  conv_rhs => rw [← (b.phaseUnitary δ hδ).apply_symm_apply x, inner_basis_phaseUnitary]
  rw [inv_mul_cancel_left₀ hδ₀]

end OrthonormalBasis

/-- Equality in Cauchy–Schwarz for unit vectors, in phase form: if `‖⟪x, y⟫‖ = 1`, then `x` is
`y` times a scalar of norm one. -/
theorem exists_norm_eq_one_smul_of_norm_inner_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : ‖⟪x, y⟫_𝕜‖ = 1) : ∃ c : 𝕜, ‖c‖ = 1 ∧ x = c • y := by
  have hx₀ : x ≠ 0 := by rintro rfl; simp at hx
  have hy₀ : y ≠ 0 := by rintro rfl; simp at hy
  obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := 𝕜) hy₀ hx₀).1
    (by rw [norm_inner_symm, h, hx, hy, one_mul])
  refine ⟨r, ?_, hr⟩
  have := congrArg norm hr
  rwa [norm_smul, hx, hy, mul_one, eq_comm] at this
