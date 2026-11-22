/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Qubit.Bloch
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.LinearAlgebra.Matrix.CrossProduct
public import TauCeti.LinearAlgebra.Matrix.Pauli
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
import TauCeti.Geometry.Lie.Exponential.Matrix.SpecialOrthogonal

/-!
# Larmor precession of the Bloch vector

Every Hermitian `2 × 2` matrix is `H = c + ½ n · σ` with `c ∈ ℝ` and `n ∈ ℝ³`. If a state `ψ(t)`
solves the Schrödinger equation `i ψ' = H ψ`, its Bloch vector `a(t)` precesses about `n`:

`a' = n × a`.

So every quantum evolution of a qubit rotates the Bloch sphere, with angular velocity `n`; the
Hamiltonian `½ n · σ` is the quantum counterpart of the linear classical Hamiltonian `n · x`.
The constant `c` only changes the global phase.

Integrated, `a(t) = exp (t n̂) a(0)`, where `n̂` is the cross-product matrix of `n`: both sides
solve the linear equation `a' = n × a` with the same initial value, and such solutions are unique.
Since `n̂` is skew-symmetric, `exp (t n̂)` is a rotation, about `n` by the angle `|n| t`.

## Main results

- `QuantumMechanics.Qubit.exists_eq_smul_one_add_pauli`: every Hermitian `2 × 2` matrix is
  `c + ½ n · σ`.
- `QuantumMechanics.Qubit.hasDerivAt_blochVector`: under the Schrödinger equation for
  `c + ½ n · σ`, the Bloch vector satisfies `a' = n × a`.
- `QuantumMechanics.Qubit.exists_hasDerivAt_blochVector`: the same for any Hermitian Hamiltonian.
- `QuantumMechanics.Qubit.exp_smul_crossProductMatrix_mem_specialOrthogonalGroup`: `exp (t n̂)`
  is a rotation.
- `QuantumMechanics.Qubit.blochVector_eq_exp_mulVec`: the Bloch vector of every solution is
  `a(t) = exp (t n̂) a(0)`.
- `QuantumMechanics.Qubit.exists_blochVector_eq_exp_mulVec`: the same for any Hermitian
  Hamiltonian, with the same `n` as `a' = n × a`.
-/

@[expose] public noncomputable section

open Complex ComplexConjugate Matrix TauCeti

namespace QuantumMechanics.Qubit

/-- Every Hermitian `2 × 2` matrix is `c + ½ n · σ` for a real `c` and a vector `n ∈ ℝ³`. -/
theorem exists_eq_smul_one_add_pauli {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    ∃ (c : ℝ) (n : Fin 3 → ℝ), H = (c : ℂ) • 1 + (1 / 2 : ℂ) • pauli n := by
  have him (i : Fin 2) : (H i i).im = 0 := by
    have h := congrArg Complex.im (congrFun₂ hH i i)
    simp only [conjTranspose_apply, star_def, conj_im] at h
    linarith
  have h01 : H 0 1 = conj (H 1 0) := by simpa using (congrFun₂ hH 0 1).symm
  refine ⟨((H 0 0).re + (H 1 1).re) / 2,
    ![2 * (H 1 0).re, 2 * (H 1 0).im, (H 0 0).re - (H 1 1).re], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli_apply, Complex.ext_iff, h01, him] <;> ring

/-- **Larmor precession.** If `ψ` solves the Schrödinger equation `i ψ' = H ψ` at `t` for the
Hamiltonian `H = c + ½ n · σ`, the Bloch vector of `ψ` satisfies `a' = n × a` at `t`. -/
theorem hasDerivAt_blochVector {ψ : ℝ → EuclideanSpace ℂ (Fin 2)} {H : Matrix (Fin 2) (Fin 2) ℂ}
    {c : ℝ} {n : Fin 3 → ℝ} (hH : H = (c : ℂ) • 1 + (1 / 2 : ℂ) • pauli n) {t : ℝ}
    (hψ : HasDerivAt ψ (-I • WithLp.toLp 2 (H *ᵥ (ψ t).ofLp)) t) :
    HasDerivAt (fun s ↦ blochVector (ψ s)) (n ⨯₃ blochVector (ψ t)) t := by
  have hc (i : Fin 2) : HasDerivAt (fun s ↦ ψ s i)
      ((-I • WithLp.toLp 2 (H *ᵥ (ψ t).ofLp)) i) t :=
    ((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 2) →L[ℂ] ℂ).restrictScalars ℝ).hasFDerivAt
      |>.comp_hasDerivAt t hψ
  have hp := HasDerivAt.mul (HasDerivAt.star (hc 0)) (hc 1)
  have h0 := ((Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hp).const_mul 2)
  have h1 := ((Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hp).const_mul 2)
  have h2 := HasDerivAt.sub (hc 0).norm_sq (hc 1).norm_sq
  refine hasDerivAt_pi.2 fun i ↦ ?_
  subst hH
  fin_cases i
  · refine h0.congr_deriv ?_
    simp [blochVector, cross_apply, pauli_apply, mulVec, dotProduct, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  · refine h1.congr_deriv ?_
    simp [blochVector, cross_apply, pauli_apply, mulVec, dotProduct, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  · refine h2.congr_deriv ?_
    simp [blochVector, cross_apply, pauli_apply, mulVec, dotProduct, Fin.sum_univ_two,
      Complex.sq_norm, Complex.normSq_apply, Complex.inner]
    ring

/-- **Every Hamiltonian rotates the Bloch sphere.** For a Hermitian `H` there is a vector `n` such
that the Bloch vector of every solution of `i ψ' = H ψ` satisfies `a' = n × a`. -/
theorem exists_hasDerivAt_blochVector {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    ∃ n : Fin 3 → ℝ, ∀ (ψ : ℝ → EuclideanSpace ℂ (Fin 2)) (t : ℝ),
      HasDerivAt ψ (-I • WithLp.toLp 2 (H *ᵥ (ψ t).ofLp)) t →
        HasDerivAt (fun s ↦ blochVector (ψ s)) (n ⨯₃ blochVector (ψ t)) t := by
  obtain ⟨c, n, hcn⟩ := exists_eq_smul_one_add_pauli hH
  exact ⟨n, fun ψ t hψ ↦ hasDerivAt_blochVector hcn hψ⟩

section Integrated

open scoped Matrix.Norms.Operator

/-- The curve `t ↦ exp (t A) c` solves `y' = A y`. -/
theorem hasDerivAt_exp_smul_mulVec (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • A) *ᵥ c)
      (A *ᵥ (NormedSpace.exp (t • A) *ᵥ c)) t := by
  let L : Matrix (Fin 3) (Fin 3) ℝ →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun M ↦ M *ᵥ c
      map_add' := fun M N ↦ add_mulVec M N c
      map_smul' := fun r M ↦ smul_mulVec r M c }
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const' A t)
  convert h using 1
  · rfl
  · exact mulVec_mulVec _ _ _

attribute [local instance] LieRing.ofAssociativeRing in
/-- The exponential `exp (t n̂)` of the cross-product matrix of `n` is a rotation. -/
theorem exp_smul_crossProductMatrix_mem_specialOrthogonalGroup (n : Fin 3 → ℝ) (t : ℝ) :
    NormedSpace.exp (t • crossProductMatrix ℝ n) ∈ specialOrthogonalGroup (Fin 3) ℝ :=
  Matrix.exp_mem_specialOrthogonalGroup_of_mem_so _
    ((LieAlgebra.Orthogonal.so (Fin 3) ℝ).smul_mem t (crossProductMatrix_mem_so n))

/-- **Integrated Larmor precession.** If `ψ` solves the Schrödinger equation `i ψ' = H ψ` for the
Hamiltonian `H = c + ½ n · σ` at all times, its Bloch vector is `a(t) = exp (t n̂) a(0)`, a rotation
about `n` (`QuantumMechanics.Qubit.exp_smul_crossProductMatrix_mem_specialOrthogonalGroup`). -/
theorem blochVector_eq_exp_mulVec {ψ : ℝ → EuclideanSpace ℂ (Fin 2)}
    {H : Matrix (Fin 2) (Fin 2) ℂ} {c : ℝ} {n : Fin 3 → ℝ}
    (hH : H = (c : ℂ) • 1 + (1 / 2 : ℂ) • pauli n)
    (hψ : ∀ t, HasDerivAt ψ (-I • WithLp.toLp 2 (H *ᵥ (ψ t).ofLp)) t) (t : ℝ) :
    blochVector (ψ t) = NormedSpace.exp (t • crossProductMatrix ℝ n) *ᵥ blochVector (ψ 0) := by
  set A := crossProductMatrix ℝ n
  have hL : LipschitzWith ‖(Matrix.mulVecLin A).toContinuousLinearMap‖₊ (Matrix.mulVecLin A) :=
    (Matrix.mulVecLin A).toContinuousLinearMap.lipschitzWith
  have h := ODE_solution_unique_univ (v := fun _ x ↦ A *ᵥ x) (s := fun _ ↦ Set.univ)
    (f := fun s ↦ blochVector (ψ s))
    (g := fun s ↦ NormedSpace.exp (s • A) *ᵥ blochVector (ψ 0)) (t₀ := 0)
    (fun _ ↦ hL.lipschitzOnWith)
    (fun s ↦ ⟨by simpa [A, crossProductMatrix_mulVec] using hasDerivAt_blochVector hH (hψ s),
      Set.mem_univ _⟩)
    (fun s ↦ ⟨hasDerivAt_exp_smul_mulVec A _ s, Set.mem_univ _⟩) (by simp)
  exact congrFun h t

/-- **Every Hamiltonian rotates the Bloch sphere, integrated.** For a Hermitian `H` there is a
vector `n` such that the Bloch vector of every solution of `i ψ' = H ψ` satisfies `a' = n × a`, and
of every global solution `a(t) = exp (t n̂) a(0)`. -/
theorem exists_blochVector_eq_exp_mulVec {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    ∃ n : Fin 3 → ℝ,
      (∀ (ψ : ℝ → EuclideanSpace ℂ (Fin 2)) (t : ℝ),
        HasDerivAt ψ (-I • WithLp.toLp 2 (H *ᵥ (ψ t).ofLp)) t →
          HasDerivAt (fun s ↦ blochVector (ψ s)) (n ⨯₃ blochVector (ψ t)) t) ∧
      ∀ ψ : ℝ → EuclideanSpace ℂ (Fin 2),
        (∀ t, HasDerivAt ψ (-I • WithLp.toLp 2 (H *ᵥ (ψ t).ofLp)) t) →
          ∀ t, blochVector (ψ t) =
            NormedSpace.exp (t • crossProductMatrix ℝ n) *ᵥ blochVector (ψ 0) := by
  obtain ⟨c, n, hcn⟩ := exists_eq_smul_one_add_pauli hH
  exact ⟨n, fun ψ t hψ ↦ hasDerivAt_blochVector hcn hψ,
    fun ψ hψ t ↦ blochVector_eq_exp_mulVec hcn hψ t⟩

end Integrated

end QuantumMechanics.Qubit
