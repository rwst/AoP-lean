/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Qubit.BlochSphere
public import TauCeti.RepresentationTheory.SU2.Adjoint

/-!
# Unitaries rotate the Bloch sphere

A unitary `2 × 2` matrix `U` acts on the rays of `ℂ²`. Through the Bloch map this action is the
rotation `pauliRotation U ∈ SO(3)` of TauCeti, the matrix with `pauli (R x) = U (pauli x) U*`.
Every rotation arises in this way, already from `SU(2)` (TauCeti's double cover `SU(2) → SO(3)`),
and two unitaries act in the same way on rays exactly when they differ by a phase.

Complex conjugation of the components is an antiunitary map of rays. It acts on the Bloch sphere by
the reflection `(a₀, a₁, a₂) ↦ (a₀, -a₁, a₂)`, which has determinant `-1`, so no unitary acts in the
same way.

## Key results

- `QuantumMechanics.Qubit.unitaryAction`: the action of `U(2)` on the rays of `ℂ²`.
- `QuantumMechanics.Qubit.blochPoint_unitaryAction`: it is `pauliRotation U` on Bloch vectors.
- `QuantumMechanics.Qubit.exists_unitaryAction_eq`: every rotation is the action of an element of
  `SU(2)`.
- `QuantumMechanics.Qubit.unitaryAction_eq_iff`: two unitaries act in the same way on rays if and
  only if they differ by a phase.
- `QuantumMechanics.Qubit.blochPoint_conjAction`: complex conjugation is a reflection of the Bloch
  sphere.
- `QuantumMechanics.Qubit.conjAction_ne_unitaryAction`: it is not the action of a unitary.
-/

@[expose] public noncomputable section

open Complex Matrix Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

namespace QuantumMechanics.Qubit

lemma injective_toLin' (U : unitaryGroup (Fin 2) ℂ) :
    Function.Injective (toLin' (U : Matrix (Fin 2) (Fin 2) ℂ)) := fun x y h ↦ by
  have h' := congrArg (mulVec (star (U : Matrix (Fin 2) (Fin 2) ℂ))) h
  simpa only [toLin'_apply, mulVec_mulVec, Unitary.star_mul_self_of_mem U.2, one_mulVec] using h'

/-- The action of a unitary matrix on the rays of `ℂ²`. -/
def unitaryAction (U : unitaryGroup (Fin 2) ℂ) : ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (Fin 2 → ℂ) :=
  map (toLin' (U : Matrix (Fin 2) (Fin 2) ℂ)) (injective_toLin' U)

/-- The Hermitian projector of `U` applied to a ray is `U P U*`. -/
theorem hermitianProjector_unitaryAction (U : unitaryGroup (Fin 2) ℂ) (p : ℙ ℂ (Fin 2 → ℂ)) :
    hermitianProjector (unitaryAction U p) =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * hermitianProjector p *
        star (U : Matrix (Fin 2) (Fin 2) ℂ) := by
  induction p using ind with | h x hx =>
  have hd : star ((U : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) ⬝ᵥ ((U : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) =
      star x ⬝ᵥ x := by
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, ← star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem U.2, one_mulVec]
  rw [unitaryAction, Projectivization.map_mk, hermitianProjector_mk, hermitianProjector_mk,
    toLin'_apply, rankOneHermitianProjector_def, rankOneHermitianProjector_def, hd]
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, star_mulVec,
    star_eq_conjTranspose]

/-- **Unitaries rotate the Bloch sphere**: the Bloch vector of `U` applied to a ray is
`pauliRotation U` applied to its Bloch vector. -/
theorem blochPoint_unitaryAction (U : unitaryGroup (Fin 2) ℂ) (p : ℙ ℂ (Fin 2 → ℂ)) :
    blochPoint (unitaryAction U p) = pauliRotation U *ᵥ blochPoint p := by
  apply pauli_injective
  have h := hermitianProjector_unitaryAction U p
  rw [hermitianProjector_eq, hermitianProjector_eq, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Unitary.mul_star_self_of_mem U.2] at h
  rw [pauli_pauliRotation_mulVec]
  exact add_left_cancel (smul_right_injective _ (by norm_num : (1 / 2 : ℂ) ≠ 0) h)

/-- A matrix is determined by its values on the Bloch vectors of rays. -/
theorem eq_of_mulVec_blochPoint {R S : Matrix (Fin 3) (Fin 3) ℝ}
    (h : ∀ p, R *ᵥ blochPoint p = S *ᵥ blochPoint p) : R = S := by
  refine ext_of_mulVec_single fun j ↦ ?_
  obtain ⟨p, hp⟩ := blochPoint_surjective (Pi.single j 1) (by simp)
  rw [← hp, h]

/-- **Every rotation of the Bloch sphere is the action of a unitary**, already of an element of
`SU(2)`. -/
theorem exists_unitaryAction_eq (R : specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ g : SU2, ∀ p, blochPoint (unitaryAction
      (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup g) p) =
        (R : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ blochPoint p := by
  obtain ⟨g, hg⟩ := SU2.toSO3_surjective R
  exact ⟨g, fun p ↦ by rw [blochPoint_unitaryAction, ← SU2.coe_toSO3, hg]⟩

/-- Two unitaries act in the same way on rays if and only if they give the same rotation. -/
theorem unitaryAction_eq_iff_pauliRotation_eq (U V : unitaryGroup (Fin 2) ℂ) :
    unitaryAction U = unitaryAction V ↔ pauliRotation U = pauliRotation V := by
  constructor
  · intro h
    exact eq_of_mulVec_blochPoint fun p ↦ by
      rw [← blochPoint_unitaryAction, h, blochPoint_unitaryAction]
  · intro h
    funext p
    apply blochPoint_injective
    rw [blochPoint_unitaryAction, blochPoint_unitaryAction, h]

/-- Two unitaries give the same rotation if and only if they differ by a phase. -/
theorem pauliRotation_eq_iff_exists_smul (U V : unitaryGroup (Fin 2) ℂ) :
    pauliRotation U = pauliRotation V ↔
      ∃ c : ℂ, (U : Matrix (Fin 2) (Fin 2) ℂ) = c • (V : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hV := Unitary.mul_star_self_of_mem V.2
  have hV' := Unitary.star_mul_self_of_mem V.2
  have hk : pauliRotation U = pauliRotation V ↔ pauliRotation (V⁻¹ * U) = 1 := by
    have h1 : pauliRotation (V⁻¹ * U) = 1 ↔ pauliRotationHom (V⁻¹ * U) = 1 := by
      rw [Subtype.ext_iff, coe_pauliRotationHom, OneMemClass.coe_one]
    rw [h1, map_mul, map_inv, inv_mul_eq_one, Subtype.ext_iff, coe_pauliRotationHom,
      coe_pauliRotationHom]
    exact eq_comm
  rw [hk, pauliRotation_eq_one_iff, Submonoid.coe_mul, ← Unitary.star_eq_inv, Unitary.coe_star]
  refine exists_congr fun c ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← Matrix.one_mul (U : Matrix (Fin 2) (Fin 2) ℂ), ← hV, Matrix.mul_assoc, h,
      Matrix.mul_smul, Matrix.mul_one]
  · rw [h, Matrix.mul_smul, hV']

/-- **Two unitaries act in the same way on rays if and only if they differ by a phase.** -/
theorem unitaryAction_eq_iff (U V : unitaryGroup (Fin 2) ℂ) :
    unitaryAction U = unitaryAction V ↔
      ∃ c : ℂ, (U : Matrix (Fin 2) (Fin 2) ℂ) = c • (V : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [unitaryAction_eq_iff_pauliRotation_eq, pauliRotation_eq_iff_exists_smul]

/-- Complex conjugation of the components, an antiunitary map of the rays of `ℂ²`. -/
def conjAction : ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (Fin 2 → ℂ) :=
  map (starLinearEquiv ℂ (A := Fin 2 → ℂ)).toLinearMap (starLinearEquiv ℂ).injective

/-- Complex conjugation reflects the Bloch sphere in the plane `a₁ = 0`. -/
theorem blochPoint_conjAction (p : ℙ ℂ (Fin 2 → ℂ)) :
    blochPoint (conjAction p) = ![blochPoint p 0, -blochPoint p 1, blochPoint p 2] := by
  induction p using ind with | h x hx =>
  simp only [conjAction, map_mk, blochPoint_mk]
  ext i
  fin_cases i
  · simp [unitBlochVector, blochVector, EuclideanSpace.norm_sq_eq]
  · simp [unitBlochVector, blochVector, EuclideanSpace.norm_sq_eq]
    ring
  · simp [unitBlochVector, blochVector, EuclideanSpace.norm_sq_eq]

/-- Complex conjugation is not the action of any unitary: it reverses the orientation of the Bloch
sphere. -/
theorem conjAction_ne_unitaryAction (U : unitaryGroup (Fin 2) ℂ) :
    conjAction ≠ unitaryAction U := by
  intro h
  have hR : pauliRotation U = diagonal ![1, -1, 1] := eq_of_mulVec_blochPoint fun p ↦ by
    rw [← blochPoint_unitaryAction, ← h, blochPoint_conjAction]
    ext i
    fin_cases i <;> simp [mulVec_diagonal]
  have hd := det_pauliRotation U
  rw [hR, det_diagonal] at hd
  norm_num [Fin.prod_univ_three] at hd

end QuantumMechanics.Qubit
