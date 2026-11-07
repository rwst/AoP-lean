/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Qubit.Bloch
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.LinearAlgebra.Matrix.Pauli
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Larmor precession of the Bloch vector

Every Hermitian `2 × 2` matrix is `H = c + ½ n · σ` with `c ∈ ℝ` and `n ∈ ℝ³`. If a state `ψ(t)`
solves the Schrödinger equation `i ψ' = H ψ`, its Bloch vector `a(t)` precesses about `n`:

`a' = n × a`.

So every quantum evolution of a qubit rotates the Bloch sphere, with angular velocity `n`; the
Hamiltonian `½ n · σ` is the quantum counterpart of the linear classical Hamiltonian `n · x`.
The constant `c` only changes the global phase.

## Main results

- `QuantumMechanics.Qubit.exists_eq_smul_one_add_pauli`: every Hermitian `2 × 2` matrix is
  `c + ½ n · σ`.
- `QuantumMechanics.Qubit.hasDerivAt_blochVector`: under the Schrödinger equation for
  `c + ½ n · σ`, the Bloch vector satisfies `a' = n × a`.
- `QuantumMechanics.Qubit.exists_hasDerivAt_blochVector`: the same for any Hermitian Hamiltonian.
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

end QuantumMechanics.Qubit
