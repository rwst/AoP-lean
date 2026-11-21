/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

import Mathlib.Tactic.LinearCombination

/-!
# Linear maps preserving a nondegenerate bilinear form

A linear self-map `f` of a finite-dimensional vector space that preserves a nondegenerate
bilinear form `B`, `B (f x) (f y) = B x y`, has `det f ^ 2 = 1`: in a basis, `Aᵀ M A = M` with
`det M ≠ 0`. For the symplectic form this is the linear algebra behind Liouville's theorem.

## Main results

* `LinearMap.BilinForm.det_sq_eq_one_of_comp_eq`
-/

@[expose] public section

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- A linear map preserving a nondegenerate bilinear form has determinant `±1`. -/
theorem det_sq_eq_one_of_comp_eq {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)
    {f : V →ₗ[K] V} (hf : B.comp f f = B) : LinearMap.det f ^ 2 = 1 := by
  classical
  let b := Module.finBasis K V
  have h := congrArg (fun B => (LinearMap.BilinForm.toMatrix b B).det) hf
  simp only [toMatrix_comp b b, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix]
    at h
  have h0 := (nondegenerate_iff_det_ne_zero b).1 hB
  have h' : (LinearMap.det f ^ 2 - 1) * (LinearMap.BilinForm.toMatrix b B).det = 0 := by
    linear_combination h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h').resolve_right h0)

end LinearMap.BilinForm
