/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Operators defined by a Hilbert basis

Let `b` be a Hilbert basis of a Hilbert space `E`. This file builds three operators from `b`,
in any dimension:

* the diagonal unitary `b i ↦ δ i • b i` for scalars `δ i` of norm one;
* coordinatewise conjugation, the anti-unitary with `⟪b i, J x⟫ = conj ⟪b i, x⟫`;
* the isometry `b i ↦ v i` onto the closed span of an orthonormal family `v`.

It also records Parseval's identity for the moduli of the coordinates, and that an isometry `V`
fixes `x` after its adjoint as soon as `‖V† x‖ = ‖x‖`.

## Main definitions

* `HilbertBasis.phaseSMul`: the Hilbert basis `i ↦ δ i • b i`.
* `HilbertBasis.phaseUnitary`: the unitary `b i ↦ δ i • b i`.
* `HilbertBasis.conjugation`: coordinatewise conjugation as `E ≃ₗᵢ⋆[𝕜] E`.
* `HilbertBasis.isometryOfOrthonormal`: the isometry `b i ↦ v i`.

## Main results

* `HilbertBasis.ext_inner`: a vector is determined by its coordinates.
* `HilbertBasis.hasSum_norm_inner_sq`: Parseval, `∑ᵢ ‖⟪b i, x⟫‖² = ‖x‖²`.
* `HilbertBasis.inner_basis_phaseUnitary_symm`: `⟪b i, U⁻¹ x⟫ = (δ i)⁻¹ * ⟪b i, x⟫`.
* `HilbertBasis.inner_basis_conjugation`: `⟪b i, J x⟫ = conj ⟪b i, x⟫`.
* `LinearIsometry.apply_adjoint_apply_of_norm_eq`: `‖V† x‖ = ‖x‖` implies `V (V† x) = x`.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace HilbertBasis

variable (b : HilbertBasis ι 𝕜 E)

/-- A vector is determined by its coordinates in a Hilbert basis. -/
theorem ext_inner {x y : E} (h : ∀ i, ⟪b i, x⟫_𝕜 = ⟪b i, y⟫_𝕜) : x = y :=
  b.repr.injective <| lp.ext <| funext fun i => by
    rw [b.repr_apply_apply, b.repr_apply_apply, h]

/-- Parseval's identity: the squared moduli of the coordinates sum to the squared norm. -/
theorem hasSum_norm_inner_sq (x : E) : HasSum (fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2) (‖x‖ ^ 2) := by
  rw [← RCLike.hasSum_ofReal (𝕜 := 𝕜)]
  convert b.hasSum_inner_mul_inner x x using 1
  · ext i
    rw [← inner_conj_symm x (b i), RCLike.conj_mul]
    push_cast
    rfl
  · rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl

/-! ### Coordinatewise conjugation -/

/-- Coordinatewise conjugation in the Hilbert basis `b`. It is its own inverse. -/
def conjugation : E ≃ₗᵢ⋆[𝕜] E where
  toFun x := b.repr.symm (star (b.repr x))
  invFun x := b.repr.symm (star (b.repr x))
  map_add' x y := by simp [star_add]
  map_smul' c x := by simp [star_smul]
  left_inv x := by simp
  right_inv x := by simp
  norm_map' x := by simp [norm_star]

theorem inner_basis_conjugation (i : ι) (x : E) :
    ⟪b i, b.conjugation x⟫_𝕜 = conj ⟪b i, x⟫_𝕜 := by
  rw [← b.repr_apply_apply, ← b.repr_apply_apply]
  change b.repr (b.repr.symm (star (b.repr x))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply, lp.star_apply, RCLike.star_def]

@[simp]
theorem conjugation_conjugation (x : E) : b.conjugation (b.conjugation x) = x :=
  b.conjugation.left_inv x

@[simp]
theorem conjugation_symm : b.conjugation.symm = b.conjugation :=
  LinearIsometryEquiv.ext fun _ => Eq.refl _

@[simp]
theorem conjugation_basis (i : ι) : b.conjugation (b i) = b i := by
  classical
  refine b.ext_inner fun j => ?_
  rw [inner_basis_conjugation, orthonormal_iff_ite.1 b.orthonormal]
  split_ifs <;> simp

/-! ### Isometries onto orthonormal families -/

section Isometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  {v : ι → F} (hv : Orthonormal 𝕜 v)

/-- The isometry sending the Hilbert basis `b` to the orthonormal family `v`. -/
def isometryOfOrthonormal : E →ₗᵢ[𝕜] F :=
  hv.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry

@[simp]
theorem isometryOfOrthonormal_apply_basis (i : ι) : b.isometryOfOrthonormal hv (b i) = v i := by
  classical
  simp [isometryOfOrthonormal, b.repr_self]

end Isometry

/-! ### Diagonal phase unitaries -/

section Phase

variable (δ : ι → 𝕜) (hδ : ∀ i, ‖δ i‖ = 1)

include hδ in
theorem orthonormal_phase_smul : Orthonormal 𝕜 fun i => δ i • b i :=
  ⟨fun i => by rw [norm_smul, hδ, b.orthonormal.1 i, one_mul], fun i j hij => by
    dsimp only
    rw [inner_smul_left, inner_smul_right, b.orthonormal.2 hij, mul_zero, mul_zero]⟩

include hδ in
theorem span_phase_smul :
    Submodule.span 𝕜 (Set.range fun i => δ i • b i) = Submodule.span 𝕜 (Set.range b) := by
  refine le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 fun i =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))) ?_
  refine Submodule.span_le.2 (Set.range_subset_iff.2 fun i => ?_)
  have hδ₀ : δ i ≠ 0 := by rw [← norm_ne_zero_iff, hδ]; exact one_ne_zero
  have : b i = (δ i)⁻¹ • δ i • b i := by rw [smul_smul, inv_mul_cancel₀ hδ₀, one_smul]
  exact this ▸ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable [CompleteSpace E]

/-- Multiplying every vector of a Hilbert basis by a scalar of norm one gives a Hilbert basis. -/
protected def phaseSMul : HilbertBasis ι 𝕜 E :=
  .mk (b.orthonormal_phase_smul δ hδ) (by rw [b.span_phase_smul δ hδ, b.dense_span])

@[simp]
theorem phaseSMul_apply (i : ι) : b.phaseSMul δ hδ i = δ i • b i :=
  congrFun (HilbertBasis.coe_mk _ _) i

/-- The diagonal unitary with entries `δ i` in the Hilbert basis `b`. -/
def phaseUnitary : E ≃ₗᵢ[𝕜] E :=
  b.repr.trans (b.phaseSMul δ hδ).repr.symm

@[simp]
theorem phaseUnitary_apply_basis (i : ι) : b.phaseUnitary δ hδ (b i) = δ i • b i := by
  classical
  rw [phaseUnitary, LinearIsometryEquiv.trans_apply, b.repr_self, HilbertBasis.repr_symm_single,
    phaseSMul_apply]

theorem phaseUnitary_symm_apply_basis (i : ι) :
    (b.phaseUnitary δ hδ).symm (b i) = (δ i)⁻¹ • b i := by
  have hδ₀ : δ i ≠ 0 := by rw [← norm_ne_zero_iff, hδ]; exact one_ne_zero
  rw [LinearIsometryEquiv.symm_apply_eq, map_smul, phaseUnitary_apply_basis, smul_smul,
    inv_mul_cancel₀ hδ₀, one_smul]

theorem inner_basis_phaseUnitary_symm (i : ι) (x : E) :
    ⟪b i, (b.phaseUnitary δ hδ).symm x⟫_𝕜 = (δ i)⁻¹ * ⟪b i, x⟫_𝕜 := by
  rw [← LinearIsometryEquiv.inner_map_map (b.phaseUnitary δ hδ),
    LinearIsometryEquiv.apply_symm_apply, phaseUnitary_apply_basis, inner_smul_left,
    RCLike.inv_def, hδ]
  simp

end Phase

end HilbertBasis

/-- An isometry `V` fixes `x` after its adjoint as soon as `V†` does not shrink `x`, that is,
`x` lies in the range of `V`. -/
theorem LinearIsometry.apply_adjoint_apply_of_norm_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F] (V : E →ₗᵢ[𝕜] F) {x : F}
    (h : ‖V.toContinuousLinearMap.adjoint x‖ = ‖x‖) :
    V (V.toContinuousLinearMap.adjoint x) = x := by
  set y := V.toContinuousLinearMap.adjoint x
  have hxy : ⟪x, V y⟫_𝕜 = ⟪y, y⟫_𝕜 :=
    (ContinuousLinearMap.adjoint_inner_left V.toContinuousLinearMap y x).symm
  have h0 : ‖x - V y‖ ^ 2 = 0 := by
    rw [@norm_sub_sq 𝕜, hxy, inner_self_eq_norm_sq_to_K, V.norm_map, h, ← RCLike.ofReal_pow,
      RCLike.ofReal_re]
    ring
  exact (sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h0))).symm
