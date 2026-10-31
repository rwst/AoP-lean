/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Physlib.Relativity.PauliMatrices.Basic

/-!
# The Bloch vector of a qubit

## i. Overview

A vector `ψ = ψ₀ e₀ + ψ₁ e₁` of `ℂ²` has the Bloch vector `(⟨σ₁⟩, ⟨σ₂⟩, ⟨σ₃⟩)`, the expectations
of the three Pauli matrices. It is not normalized: its length is `‖ψ‖²`. The Born probability is
affine in it, `|⟨χ|ψ⟩|² = (‖χ‖² ‖ψ‖² + a · b) / 2`, and for unit vectors this shows that the Bloch
vector determines the ray of `ψ` and nothing more, and that orthogonal unit vectors have opposite
Bloch vectors.

## ii. Key results

- `QuantumMechanics.Qubit.blochVector`: the Bloch vector.
- `QuantumMechanics.Qubit.blochVector_apply`: it is the vector of Pauli expectations.
- `QuantumMechanics.Qubit.vecMulVec_eq`: `|ψ⟩⟨ψ| = (‖ψ‖² + a · σ) / 2`.
- `QuantumMechanics.Qubit.norm_inner_sq`: the Born probability is affine in the Bloch vectors.
- `QuantumMechanics.Qubit.exists_eq_smul_iff`: two unit vectors span the same ray if and only if
  they have the same Bloch vector.
- `QuantumMechanics.Qubit.inner_eq_zero_iff`: two unit vectors are orthogonal if and only if
  their Bloch vectors are opposite.
-/

@[expose] public noncomputable section

open Complex ComplexConjugate Matrix PauliMatrix

namespace QuantumMechanics.Qubit

/-- The Bloch vector `(⟨σ₁⟩, ⟨σ₂⟩, ⟨σ₃⟩)` of `ψ`, not normalized. -/
def blochVector (ψ : EuclideanSpace ℂ (Fin 2)) : Fin 3 → ℝ :=
  ![2 * (conj (ψ 0) * ψ 1).re, 2 * (conj (ψ 0) * ψ 1).im, ‖ψ 0‖ ^ 2 - ‖ψ 1‖ ^ 2]

lemma norm_sq (ψ : EuclideanSpace ℂ (Fin 2)) : ‖ψ‖ ^ 2 = ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

/-- The Bloch vector is the vector of Pauli expectations `⟨ψ|σᵢ|ψ⟩`. -/
theorem blochVector_apply (ψ : EuclideanSpace ℂ (Fin 2)) (i : Fin 3) :
    (blochVector ψ i : ℂ) = star ψ.ofLp ⬝ᵥ (σ (Sum.inr i) *ᵥ ψ.ofLp) := by
  fin_cases i <;>
  · apply Complex.ext <;>
    simp [blochVector, pauliMatrix, dotProduct, mulVec, Fin.sum_univ_two, Complex.sq_norm,
      Complex.normSq_apply] <;> ring

/-- `|ψ⟩⟨ψ| = (‖ψ‖² + a · σ) / 2`, with `a` the Bloch vector of `ψ`. -/
theorem vecMulVec_eq (ψ : EuclideanSpace ℂ (Fin 2)) :
    vecMulVec ψ.ofLp (star ψ.ofLp) =
      (1 / 2 : ℂ) • ((‖ψ‖ ^ 2 : ℝ) • 1 + vectorMatrix (blochVector ψ)) := by
  rw [norm_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · apply Complex.ext <;>
    simp [blochVector, vectorMatrix, pauliMatrix, vecMulVec, Fin.sum_univ_three,
      Complex.sq_norm, Complex.normSq_apply] <;> ring

lemma blochVector_smul (c : ℂ) (ψ : EuclideanSpace ℂ (Fin 2)) :
    blochVector (c • ψ) = ‖c‖ ^ 2 • blochVector ψ := by
  ext i
  fin_cases i
  · simp [blochVector, Complex.sq_norm, Complex.normSq_apply]; ring
  · simp [blochVector, Complex.sq_norm, Complex.normSq_apply]; ring
  · simp [blochVector]; ring

/-- The Born probability is affine in the Bloch vectors:
`|⟨χ|ψ⟩|² = (‖χ‖² ‖ψ‖² + a · b) / 2`. -/
theorem norm_inner_sq (χ ψ : EuclideanSpace ℂ (Fin 2)) :
    ‖inner ℂ χ ψ‖ ^ 2 = (‖χ‖ ^ 2 * ‖ψ‖ ^ 2 + blochVector χ ⬝ᵥ blochVector ψ) / 2 := by
  rw [norm_sq, norm_sq]
  simp [PiLp.inner_apply, Fin.sum_univ_two, blochVector, dotProduct, Fin.sum_univ_three,
    Complex.sq_norm, Complex.normSq_apply]
  ring

lemma blochVector_dotProduct_self (ψ : EuclideanSpace ℂ (Fin 2)) :
    blochVector ψ ⬝ᵥ blochVector ψ = ‖ψ‖ ^ 4 := by
  rw [show ‖ψ‖ ^ 4 = (‖ψ‖ ^ 2) ^ 2 by ring, norm_sq]
  simp [blochVector, dotProduct, Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- Two unit vectors span the same ray if and only if they have the same Bloch vector. -/
theorem exists_eq_smul_iff {χ ψ : EuclideanSpace ℂ (Fin 2)} (hχ : ‖χ‖ = 1) (hψ : ‖ψ‖ = 1) :
    (∃ c : ℂ, χ = c • ψ) ↔ blochVector χ = blochVector ψ := by
  constructor
  · rintro ⟨c, rfl⟩
    have hc : ‖c‖ = 1 := by simpa [norm_smul, hψ] using hχ
    rw [blochVector_smul, hc, one_pow, one_smul]
  · intro h
    have hχ0 : χ ≠ 0 := by rintro rfl; simp at hχ
    have hψ0 : ψ ≠ 0 := by rintro rfl; simp at hψ
    have hi := norm_inner_sq ψ χ
    rw [h, blochVector_dotProduct_self, hχ, hψ] at hi
    have h1 : ‖inner ℂ ψ χ‖ = ‖ψ‖ * ‖χ‖ := by
      rw [hχ, hψ, mul_one]
      nlinarith [norm_nonneg (inner ℂ ψ χ)]
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hψ0 hχ0).mp h1
    exact ⟨r, hr⟩

/-- Two unit vectors are orthogonal if and only if their Bloch vectors are opposite. -/
theorem inner_eq_zero_iff {χ ψ : EuclideanSpace ℂ (Fin 2)} (hχ : ‖χ‖ = 1) (hψ : ‖ψ‖ = 1) :
    inner ℂ χ ψ = 0 ↔ blochVector χ = -blochVector ψ := by
  have hi := norm_inner_sq χ ψ
  have ha := blochVector_dotProduct_self χ
  have hb := blochVector_dotProduct_self ψ
  simp only [hχ, hψ, one_pow, one_mul] at hi ha hb
  have hsum : (blochVector χ + blochVector ψ) ⬝ᵥ (blochVector χ + blochVector ψ) =
      4 * ‖inner ℂ χ ψ‖ ^ 2 := by
    simp only [add_dotProduct, dotProduct_add, dotProduct_comm (blochVector ψ)]
    linarith
  constructor
  · intro h0
    have h : blochVector χ + blochVector ψ = 0 := by
      rw [← dotProduct_self_eq_zero, hsum, h0]
      simp
    exact eq_neg_of_add_eq_zero_left h
  · intro h
    have h0 : ‖inner ℂ χ ψ‖ ^ 2 = 0 := by
      rw [hi, h, neg_dotProduct, hb]
      norm_num
    simpa using h0
