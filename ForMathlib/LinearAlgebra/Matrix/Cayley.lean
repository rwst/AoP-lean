/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The Cayley transform of a skew-symmetric matrix

Over a linearly ordered field, `1 - A` is invertible for a skew-symmetric matrix `A`: if
`A x = x`, then `x ⬝ᵥ x = x ⬝ᵥ A x = 0`. The Cayley transform `(1 + A) (1 - A)⁻¹` is then a
special orthogonal matrix, since `1 + A` and `1 - A` commute, `(1 ± A)ᵀ = 1 ∓ A`, and so
`det (1 + A) = det (1 - A)`.

## Main definitions

* `Matrix.cayley`: the Cayley transform `(1 + A) (1 - A)⁻¹`.

## Main results

* `Matrix.isUnit_one_sub_of_transpose_eq_neg`: `1 - A` is invertible for skew-symmetric `A`.
* `Matrix.cayley_mem_specialOrthogonalGroup`: the Cayley transform of a skew-symmetric matrix is
  special orthogonal.
-/

@[expose] public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [Field R]

/-- The **Cayley transform** `(1 + A) (1 - A)⁻¹` of a square matrix. -/
noncomputable def cayley (A : Matrix n n R) : Matrix n n R := (1 + A) * (1 - A)⁻¹

variable [LinearOrder R] [IsStrictOrderedRing R] {A : Matrix n n R}

/-- `1 - A` is invertible for a skew-symmetric matrix `A` over a linearly ordered field. -/
theorem isUnit_one_sub_of_transpose_eq_neg (hA : Aᵀ = -A) : IsUnit (1 - A) := by
  refine mulVec_injective_iff_isUnit.mp fun y z hyz => sub_eq_zero.mp ?_
  set x := y - z
  have hx : (1 - A) *ᵥ x = 0 := by rw [mulVec_sub, hyz, sub_self]
  have hAx : A *ᵥ x = x := by rw [sub_mulVec, one_mulVec, sub_eq_zero] at hx; exact hx.symm
  have h : x ⬝ᵥ A *ᵥ x = -(x ⬝ᵥ A *ᵥ x) := by
    conv_lhs => rw [dotProduct_mulVec, ← mulVec_transpose, hA, neg_mulVec, neg_dotProduct,
      dotProduct_comm]
  have h0 : x ⬝ᵥ A *ᵥ x = 0 := by linarith
  rwa [hAx, dotProduct_self_eq_zero] at h0

/-- The Cayley transform of a skew-symmetric matrix over a linearly ordered field is special
orthogonal. -/
theorem cayley_mem_specialOrthogonalGroup (hA : Aᵀ = -A) :
    A.cayley ∈ specialOrthogonalGroup n R := by
  have hneg : (-A)ᵀ = -(-A) := by rw [transpose_neg, hA]
  have hm : IsUnit (1 - A) := isUnit_one_sub_of_transpose_eq_neg hA
  have hp : IsUnit (1 + A) := by
    simpa [sub_eq_add_neg] using isUnit_one_sub_of_transpose_eq_neg hneg
  have hmd : IsUnit (1 - A).det := (isUnit_iff_isUnit_det _).mp hm
  have hpd : IsUnit (1 + A).det := (isUnit_iff_isUnit_det _).mp hp
  have hcomm : (1 - A) * (1 + A) = (1 + A) * (1 - A) := by noncomm_ring
  have htp : (1 + A)ᵀ = 1 - A := by rw [transpose_add, transpose_one, hA, sub_eq_add_neg]
  have htm : (1 - A)ᵀ = 1 + A := by rw [transpose_sub, transpose_one, hA, sub_neg_eq_add]
  refine mem_specialOrthogonalGroup_iff.mpr ⟨(mem_orthogonalGroup_iff' n R).mpr ?_, ?_⟩
  · rw [cayley, transpose_mul, transpose_nonsing_inv, htm, htp]
    calc (1 + A)⁻¹ * (1 - A) * ((1 + A) * (1 - A)⁻¹)
        = (1 + A)⁻¹ * ((1 - A) * (1 + A)) * (1 - A)⁻¹ := by simp only [mul_assoc]
      _ = (1 + A)⁻¹ * (1 + A) * ((1 - A) * (1 - A)⁻¹) := by rw [hcomm]; simp only [mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hpd, mul_nonsing_inv _ hmd, one_mul]
  · have hdet : (1 + A).det = (1 - A).det := by rw [← det_transpose, htp]
    rw [cayley, det_mul, det_nonsing_inv, hdet, Ring.mul_inverse_cancel _ hmd]

end Matrix
