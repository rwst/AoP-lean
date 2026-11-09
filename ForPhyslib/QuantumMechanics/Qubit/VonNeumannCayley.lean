/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.LinearAlgebra.Matrix.Cayley
public import ForPhyslib.QuantumMechanics.Qubit.Precession
public import ForPhyslib.QuantumMechanics.VonNeumannResolvent.Cayley
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The resolvent of a qubit on the Bloch ball

A self-adjoint qubit operator of trace one is `ρ_a = (1 + a · σ) / 2` for a unique `a ∈ ℝ³`, its
Bloch vector. For the Hamiltonian `K = c + ½ n · σ` the von Neumann generator
`L ρ = -i (K ρ - ρ K)` acts on Bloch vectors as the cross product `a ↦ n × a`, the skew-symmetric
matrix `[n]×`: `L ρ_a = ½ (n × a) · σ`. So the resolvent `Ψ τ = (1 - τ L)⁻¹` acts as
`(1 - τ [n]×)⁻¹`, and the Cayley transform `C τ = (1 + τ L) (1 - τ L)⁻¹` as the rotation
`R = (1 + τ [n]×) (1 - τ [n]×)⁻¹ ∈ SO(3)` about `n`. Since
`(1 - A)⁻¹ = (1 + (1 + A) (1 - A)⁻¹) / 2`, `Ψ τ` sends a Bloch vector to the midpoint between it
and its rotated image.

## Main definitions

* `QuantumMechanics.Qubit.blochOperator`: the operator `(1 + a · σ) / 2` on `ℂ²`.
* `QuantumMechanics.Qubit.crossMatrix`: the matrix `[n]×` of `a ↦ n × a`.

## Main results

* `QuantumMechanics.Qubit.exists_blochOperator_eq`: every self-adjoint operator of trace one is a
  `blochOperator`.
* `QuantumMechanics.Qubit.vonNeumannGenerator_blochOperator`: `L ρ_a = ½ (n × a) · σ`.
* `QuantumMechanics.Qubit.exists_vonNeumannCayley_blochOperator`: `C τ` rotates Bloch vectors by a
  rotation `R ∈ SO(3)` fixing `n`, and `Ψ τ` sends `a` to the midpoint of `a` and `R a`.
-/

@[expose] public noncomputable section

open Complex Matrix TauCeti

namespace QuantumMechanics.Qubit

/-- Matrices as operators on `ℂ²`. -/
local notation "toE" => toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)

/-- The qubit operator `(1 + a · σ) / 2` with Bloch vector `a`. -/
def blochOperator (a : Fin 3 → ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  toE ((2⁻¹ : ℂ) • (1 + pauli a))

/-- The skew-symmetric matrix `[n]×` of the cross product `a ↦ n × a`. -/
def crossMatrix (n : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -n 2, n 1; n 2, 0, -n 0; -n 1, n 0, 0]

lemma crossMatrix_mulVec (n a : Fin 3 → ℝ) : crossMatrix n *ᵥ a = n ⨯₃ a := by
  ext i
  fin_cases i <;> simp [crossMatrix, cross_apply, mulVec, dotProduct, Fin.sum_univ_three] <;> ring

lemma transpose_crossMatrix (n : Fin 3 → ℝ) : (crossMatrix n)ᵀ = -crossMatrix n := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMatrix]

/-- Every self-adjoint qubit operator of trace one is `(1 + a · σ) / 2` for some `a`. -/
theorem exists_blochOperator_eq {ρ : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)}
    (hρ : IsSelfAdjoint ρ) (htr : LinearMap.trace ℂ (EuclideanSpace ℂ (Fin 2)) ρ = 1) :
    ∃ a, ρ = blochOperator a := by
  set M := (toE).symm ρ
  have hM : M.IsHermitian := by
    rw [isHermitian_iff_isSelfAdjoint, IsSelfAdjoint,
      show star M = (toE).symm (star ρ) from ((toE).symm.map_star' ρ).symm, hρ.star_eq]
  have hMtr : M.trace = 1 := by
    rw [← htr, ← (toE).apply_symm_apply ρ, coe_toEuclideanCLM_eq_toEuclideanLin,
      LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis,
      toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin]
  have hN : (M + M - 1).IsHermitian := (hM.add hM).sub isHermitian_one
  have hNtr : (M + M - 1).trace = 0 := by
    rw [trace_sub, trace_add, hMtr, trace_one]
    norm_num
  refine ⟨pauliCoord (M + M - 1), ?_⟩
  rw [blochOperator, pauli_pauliCoord hN hNtr, ← (toE).apply_symm_apply ρ]
  congr 1
  module

/-- **The generator on Bloch vectors**: for `K = c + ½ n · σ`, `L ρ_a = ½ (n × a) · σ`. -/
theorem vonNeumannGenerator_blochOperator {c : ℝ} {n : Fin 3 → ℝ} (a : Fin 3 → ℝ) :
    vonNeumannGenerator (toE ((c : ℂ) • 1 + (2⁻¹ : ℂ) • pauli n)) (blochOperator a) =
      toE ((2⁻¹ : ℂ) • pauli (n ⨯₃ a)) := by
  rw [vonNeumannGenerator_apply, blochOperator, ← map_mul, ← map_mul, ← map_sub, ← map_smul]
  congr 1
  have h := pauli_mul_sub_mul_pauli n a
  calc (-I) • (((c : ℂ) • 1 + (2⁻¹ : ℂ) • pauli n) * ((2⁻¹ : ℂ) • (1 + pauli a)) -
        (2⁻¹ : ℂ) • (1 + pauli a) * ((c : ℂ) • 1 + (2⁻¹ : ℂ) • pauli n))
      = (-I / 4) • (pauli n * pauli a - pauli a * pauli n) := by
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add,
          smul_sub, smul_smul]
        module
    _ = (2⁻¹ : ℂ) • pauli (n ⨯₃ a) := by
        rw [h, smul_smul]
        congr 1
        linear_combination (-2⁻¹ : ℂ) * I_sq

/-- `(1 - τ L) ρ_b = ρ_{(1 - τ [n]×) b}` for `K = c + ½ n · σ`. -/
lemma vonNeumannStep_blochOperator {c : ℝ} {n : Fin 3 → ℝ} (τ : ℝ) (b : Fin 3 → ℝ) :
    vonNeumannStep (toE ((c : ℂ) • 1 + (2⁻¹ : ℂ) • pauli n)) τ (blochOperator b) =
      blochOperator ((1 - τ • crossMatrix n) *ᵥ b) := by
  rw [vonNeumannStep_apply, vonNeumannGenerator_blochOperator, sub_mulVec, one_mulVec,
    smul_mulVec, crossMatrix_mulVec, blochOperator, blochOperator, ← Complex.coe_smul,
    ← map_smul (toE), ← map_sub (toE)]
  congr 1
  rw [map_sub, map_smul, ← Complex.coe_smul]
  module

/-- `2 ρ_b - ρ_a = ρ_{2 b - a}`. -/
lemma two_smul_blochOperator_sub (a b : Fin 3 → ℝ) :
    (2 : ℂ) • blochOperator b - blochOperator a = blochOperator ((2 : ℝ) • b - a) := by
  rw [blochOperator, blochOperator, blochOperator, ← map_smul (toE), ← map_sub (toE)]
  congr 1
  rw [map_sub, map_smul, ← Complex.coe_smul]
  push_cast
  module

/-- **The qubit picture of the resolvent.** For a qubit Hamiltonian, the Cayley transform
`C τ = (1 + τ L) (1 - τ L)⁻¹` acts on Bloch vectors by a rotation `R ∈ SO(3)` about the field `n`,
and the resolvent `Ψ τ = (1 + C τ) / 2` sends a Bloch vector `a` to the midpoint of `a` and
`R a`. -/
theorem exists_vonNeumannCayley_blochOperator
    (V : UnitaryOneParameterGroup (EuclideanSpace ℂ (Fin 2))) (τ : ℝ) :
    ∃ n : Fin 3 → ℝ, ∃ R ∈ specialOrthogonalGroup (Fin 3) ℝ, R *ᵥ n = n ∧
      ∀ a, vonNeumannCayley V τ (blochOperator a) = blochOperator (R *ᵥ a) ∧
        vonNeumannResolvent V τ (blochOperator a) = blochOperator (midpoint ℝ a (R *ᵥ a)) := by
  obtain ⟨c, n, hcn⟩ := exists_eq_smul_one_add_pauli
    (H := (toE).symm V.generator) (by
      rw [isHermitian_iff_isSelfAdjoint, IsSelfAdjoint,
        show star ((toE).symm V.generator) = (toE).symm (star V.generator) from
          ((toE).symm.map_star' V.generator).symm, V.generator_isSelfAdjoint.star_eq])
  have hK : V.generator = toE ((c : ℂ) • 1 + (2⁻¹ : ℂ) • pauli n) := by
    rw [← one_div, ← hcn, StarAlgEquiv.apply_symm_apply]
  set A := τ • crossMatrix n
  have hA : Aᵀ = -A := by rw [transpose_smul, transpose_crossMatrix, smul_neg]
  have hdet : IsUnit (1 - A).det :=
    (isUnit_iff_isUnit_det _).mp (isUnit_one_sub_of_transpose_eq_neg hA)
  have hAn : A *ᵥ n = 0 := by rw [smul_mulVec, crossMatrix_mulVec, cross_self, smul_zero]
  -- the resolvent acts as `(1 - A)⁻¹`
  have hΨ : ∀ a, vonNeumannResolvent V τ (blochOperator a) = blochOperator ((1 - A)⁻¹ *ᵥ a) := by
    intro a
    have h := vonNeumannStep_blochOperator (c := c) (n := n) τ ((1 - A)⁻¹ *ᵥ a)
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, ← hK] at h
    rw [← h, vonNeumannResolvent_vonNeumannStep]
  have hmid : ∀ a, (1 - A)⁻¹ *ᵥ a = midpoint ℝ a (A.cayley *ᵥ a) := by
    intro a
    rw [midpoint_eq_smul_add, cayley, ← mulVec_mulVec]
    set b := (1 - A)⁻¹ *ᵥ a
    have ha : a = (1 - A) *ᵥ b := by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
    rw [ha, ← add_mulVec, sub_add_add_cancel, ← two_smul ℝ (1 : Matrix (Fin 3) (Fin 3) ℝ),
      smul_mulVec, one_mulVec, smul_smul]
    norm_num
  refine ⟨n, A.cayley, cayley_mem_specialOrthogonalGroup hA, ?_, fun a => ⟨?_, ?_⟩⟩
  · have h1 : (1 - A) *ᵥ n = n := by rw [sub_mulVec, one_mulVec, hAn, sub_zero]
    have h2 : (1 - A)⁻¹ *ᵥ n = n := by
      conv_lhs => rw [← h1]
      rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
    rw [cayley, ← mulVec_mulVec, h2, add_mulVec, one_mulVec, hAn, add_zero]
  · rw [vonNeumannCayley_apply, hΨ, two_smul_blochOperator_sub, hmid, midpoint_eq_smul_add,
      smul_smul]
    norm_num
  · rw [hΨ, hmid]

end QuantumMechanics.Qubit
