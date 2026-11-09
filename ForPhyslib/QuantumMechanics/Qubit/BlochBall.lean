/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Qubit.Bloch
public import ForPhyslib.QuantumMechanics.Wigner.Density

/-!
# The Bloch ball of a plane

## i. Overview

Two orthonormal vectors `ψ`, `χ` of a complex inner product space `E` of any dimension span a
qubit inside `E`. The isometry `u ↦ u₀ ψ + u₁ χ` from `ℂ²` carries the Bloch picture of `ℂ²` into
`E`. A `2 × 2` matrix `M` becomes the operator `∑ᵢⱼ Mᵢⱼ |eᵢ⟩⟨eⱼ|` with `e₀ = ψ`, `e₁ = χ`, and
the point `r` of `ℝ³` becomes the operator `½ (|ψ⟩⟨ψ| + |χ⟩⟨χ| + r · σ)`, which is affine in `r`.
A unit Bloch vector gives a pure state of the plane, and every unit vector of the plane arises.
The Born probability of two unit vectors of the plane is `(1 + a · b) / 2`, affine in their Bloch
vectors, and they are orthogonal if and only if their Bloch vectors are opposite. So `|⟨u|v⟩|` is
the cosine of half the angle between the Bloch vectors.

This gives the geometric diagonalization of a qubit state. A point `r` of the ball lies on the
diameter through `±r / |r|`, whose ends are orthogonal pure states, and `r` is their mixture with
weights `(1 ± |r|) / 2`. The equal mixture of two pure states is the midpoint of their Bloch
vectors, of length `|⟨u|v⟩|`, so its eigenvalues are `(1 ± |⟨u|v⟩|) / 2`.

## ii. Key results

- `QuantumMechanics.Qubit.planeVector`: the vector `u₀ ψ + u₁ χ`.
- `QuantumMechanics.Qubit.blochOperator`: the operator `½ (|ψ⟩⟨ψ| + |χ⟩⟨χ| + r · σ)`.
- `QuantumMechanics.Qubit.blochOperator_convex`: it is affine in `r`.
- `QuantumMechanics.Qubit.proj_planeVector`: `|u⟩⟨u|` has the Bloch vector of `u`.
- `QuantumMechanics.Qubit.exists_proj_planeVector_eq`: every unit Bloch vector is a pure state.
- `QuantumMechanics.Qubit.exists_planeVector_eq`: every vector of the plane is a `planeVector`.
- `QuantumMechanics.Qubit.norm_inner_planeVector_sq`: the Born probability is `(1 + a · b) / 2`.
- `QuantumMechanics.Qubit.inner_planeVector_eq_zero_iff`: orthogonal means antipodal.
- `QuantumMechanics.Qubit.norm_inner_planeVector_eq_cos`: `|⟨u|v⟩| = cos (θ / 2)`.
- `QuantumMechanics.Qubit.eq_smul_or_exists_planeVector_eq`: a unit vector and any vector lie in a
  plane.
- `QuantumMechanics.Qubit.exists_blochOperator_eq`: diagonalization along a diameter.
- `QuantumMechanics.Qubit.exists_mix_proj_planeVector_eq`: the equal mixture of two pure states
  is `((1 + |⟨u|v⟩|) / 2) |u₁⟩⟨u₁| + ((1 - |⟨u|v⟩|) / 2) |u₂⟩⟨u₂|`, with `u₁ ⊥ u₂`.

## iii. Table of contents

- A. Vectors and operators of the plane
- B. Pure states and Bloch vectors
- C. The Born rule on the Bloch sphere
- D. Diagonalization along a diameter

## iv. References

- M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), §2.2.3 and §4.2.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open InnerProductSpace Matrix PauliMatrix QuantumMechanics.Wigner

namespace QuantumMechanics.Qubit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ψ χ : E}

/-! ## A. Vectors and operators of the plane -/

/-- The vector `u₀ ψ + u₁ χ` of the plane spanned by `ψ` and `χ`. -/
def planeVector (ψ χ : E) (u : EuclideanSpace ℂ (Fin 2)) : E := u 0 • ψ + u 1 • χ

/-- The operator `∑ᵢⱼ Mᵢⱼ |eᵢ⟩⟨eⱼ|` of a `2 × 2` matrix `M`, with `e₀ = ψ` and `e₁ = χ`. -/
def planeOperator (ψ χ : E) : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] E →L[ℂ] E where
  toFun M := ∑ i, ∑ j, M i j • rankOne ℂ (![ψ, χ] i) (![ψ, χ] j)
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by simp [smul_smul]

/-- The operator `½ (|ψ⟩⟨ψ| + |χ⟩⟨χ| + r · σ)` of the point `r` of `ℝ³`. -/
def blochOperator (ψ χ : E) (r : Fin 3 → ℝ) : E →L[ℂ] E :=
  planeOperator ψ χ ((1 / 2 : ℂ) • (1 + vectorMatrix r))

lemma planeOperator_vecMulVec (u : EuclideanSpace ℂ (Fin 2)) :
    planeOperator ψ χ (vecMulVec u.ofLp (star u.ofLp)) = proj (planeVector ψ χ u) := by
  ext v
  simp only [planeOperator, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_two, vecMulVec_apply,
    Pi.star_apply, add_apply, smul_apply, rankOne_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    planeVector, inner_add_left, inner_smul_left, RCLike.star_def]
  module

lemma vectorMatrix_convex (a b : Fin 3 → ℝ) (t : ℝ) :
    vectorMatrix (t • a + (1 - t) • b) =
      (t : ℂ) • vectorMatrix a + ((1 - t : ℝ) : ℂ) • vectorMatrix b := by
  simp only [vectorMatrix, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  module

/-- The operator of a point of `ℝ³` is affine in the point. -/
theorem blochOperator_convex (a b : Fin 3 → ℝ) (t : ℝ) :
    blochOperator ψ χ (t • a + (1 - t) • b) =
      (t : ℂ) • blochOperator ψ χ a + ((1 - t : ℝ) : ℂ) • blochOperator ψ χ b := by
  rw [blochOperator, blochOperator, blochOperator, ← map_smul, ← map_smul, ← map_add,
    vectorMatrix_convex]
  congr 1
  push_cast
  module

/-- A unit vector `ψ` and any vector `ϕ` lie in a plane: either `ϕ` is a multiple of `ψ`, or
`ϕ = u₀ ψ + u₁ χ` for a unit vector `χ ⊥ ψ`, the normalized part of `ϕ` orthogonal to `ψ`. -/
lemma eq_smul_or_exists_planeVector_eq (hψ : ‖ψ‖ = 1) (ϕ : E) :
    (∃ c : ℂ, ϕ = c • ψ) ∨
      ∃ χ : E, ‖χ‖ = 1 ∧ ⟪ψ, χ⟫_ℂ = 0 ∧ ∃ u : EuclideanSpace ℂ (Fin 2), planeVector ψ χ u = ϕ := by
  set r := ϕ - ⟪ψ, ϕ⟫_ℂ • ψ with hr_def
  by_cases hr : r = 0
  · exact Or.inl ⟨⟪ψ, ϕ⟫_ℂ, sub_eq_zero.mp hr⟩
  have hr0 : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hψr : ⟪ψ, r⟫_ℂ = 0 := by
    simp [r, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
  refine Or.inr ⟨(‖r‖ : ℂ)⁻¹ • r, ?_, ?_, WithLp.toLp 2 ![⟪ψ, ϕ⟫_ℂ, ‖r‖], ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hr0]
  · rw [inner_smul_right, hψr, mul_zero]
  · simp only [planeVector, Matrix.cons_val_zero, Matrix.cons_val_one, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr0), one_smul, r]
    abel

/-! ## B. Pure states and Bloch vectors -/

/-- The pure state of a unit vector `u₀ ψ + u₁ χ` is the operator of the Bloch vector of `u`. -/
theorem proj_planeVector {u : EuclideanSpace ℂ (Fin 2)} (hu : ‖u‖ = 1) :
    proj (planeVector ψ χ u) = blochOperator ψ χ (blochVector u) := by
  rw [← planeOperator_vecMulVec, vecMulVec_eq, hu, blochOperator]
  simp

/-- Every unit Bloch vector is the pure state of a unit vector `u₀ ψ + u₁ χ`. -/
theorem exists_proj_planeVector_eq {a : Fin 3 → ℝ} (ha : a ⬝ᵥ a = 1) :
    ∃ u : EuclideanSpace ℂ (Fin 2), ‖u‖ = 1 ∧ blochVector u = a ∧
      proj (planeVector ψ χ u) = blochOperator ψ χ a := by
  obtain ⟨u, hu, rfl⟩ := exists_blochVector_eq ha
  exact ⟨u, hu, rfl, proj_planeVector hu⟩

/-- Every vector of the plane spanned by `ψ` and `χ` is a `planeVector`. -/
lemma exists_planeVector_eq {v : E} (hv : v ∈ Submodule.span ℂ {ψ, χ}) :
    ∃ u : EuclideanSpace ℂ (Fin 2), planeVector ψ χ u = v := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hv
  exact ⟨WithLp.toLp 2 ![α, β], by simp [planeVector]⟩

/-- The point `s n` of the diameter through `±n` is the mixture of its ends with weights
`(1 ± s) / 2`. -/
lemma blochOperator_smul (n : Fin 3 → ℝ) (s : ℝ) :
    blochOperator ψ χ (s • n) = (((1 + s) / 2 : ℝ) : ℂ) • blochOperator ψ χ n +
      (((1 - s) / 2 : ℝ) : ℂ) • blochOperator ψ χ (-n) := by
  have h := blochOperator_convex (ψ := ψ) (χ := χ) n (-n) ((1 + s) / 2)
  rwa [show ((1 + s) / 2) • n + (1 - (1 + s) / 2) • -n = s • n by module,
    show 1 - (1 + s) / 2 = (1 - s) / 2 by ring] at h

/-- The equal mixture of two pure states of the plane is the operator of the midpoint of their
Bloch vectors. -/
lemma mix_proj_planeVector {u v : EuclideanSpace ℂ (Fin 2)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    mix (proj (planeVector ψ χ u)) (proj (planeVector ψ χ v)) =
      blochOperator ψ χ ((2⁻¹ : ℝ) • (blochVector u + blochVector v)) := by
  have h := blochOperator_convex (ψ := ψ) (χ := χ) (blochVector u) (blochVector v) 2⁻¹
  rw [show (2⁻¹ : ℝ) • blochVector u + (1 - 2⁻¹ : ℝ) • blochVector v =
    (2⁻¹ : ℝ) • (blochVector u + blochVector v) by module] at h
  rw [h, proj_planeVector hu, proj_planeVector hv, mix]
  norm_num

/-! ## C. The Born rule on the Bloch sphere -/

variable (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) (hψχ : ⟪ψ, χ⟫_ℂ = 0)
include hψ hχ hψχ

/-- `u ↦ u₀ ψ + u₁ χ` preserves the inner product. -/
lemma inner_planeVector (u v : EuclideanSpace ℂ (Fin 2)) :
    ⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ = ⟪u, v⟫_ℂ := by
  have hχψ : ⟪χ, ψ⟫_ℂ = 0 := inner_eq_zero_symm.mp hψχ
  simp only [planeVector, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    hψχ, hχψ, inner_self_eq_norm_sq_to_K, hψ, hχ, PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply]
  simp only [map_one, one_pow, mul_one, mul_zero, add_zero, zero_add]

lemma norm_planeVector (u : EuclideanSpace ℂ (Fin 2)) : ‖planeVector ψ χ u‖ = ‖u‖ := by
  have h := inner_planeVector hψ hχ hψχ u u
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast h)

/-- The Born probability of two unit vectors of the plane is `(1 + a · b) / 2`, with `a`, `b` their
Bloch vectors. -/
theorem norm_inner_planeVector_sq {u v : EuclideanSpace ℂ (Fin 2)} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    ‖⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ‖ ^ 2 =
      (1 + blochVector u ⬝ᵥ blochVector v) / 2 := by
  rw [inner_planeVector hψ hχ hψχ, norm_inner_sq, hu, hv]
  norm_num

/-- Two unit vectors of the plane are orthogonal if and only if their Bloch vectors are
opposite. -/
theorem inner_planeVector_eq_zero_iff {u v : EuclideanSpace ℂ (Fin 2)} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    ⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ = 0 ↔ blochVector u = -blochVector v := by
  rw [inner_planeVector hψ hχ hψχ]
  exact inner_eq_zero_iff hu hv

/-- **The Born rule is the squared cosine of the half-angle.** `|⟨u|v⟩| = cos (θ / 2)` with `θ` the
angle between the Bloch vectors of two unit vectors of the plane. -/
theorem norm_inner_planeVector_eq_cos {u v : EuclideanSpace ℂ (Fin 2)} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    ‖⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ‖ =
      Real.cos (Real.arccos (blochVector u ⬝ᵥ blochVector v) / 2) := by
  have hB := norm_inner_planeVector_sq hψ hχ hψχ hu hv
  have h1 : ‖⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ‖ ≤ 1 := by
    simpa [norm_planeVector hψ hχ hψχ, hu, hv] using
      norm_inner_le_norm (𝕜 := ℂ) (planeVector ψ χ u) (planeVector ψ χ v)
  have h0 := norm_nonneg ⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ
  rw [Real.cos_half (by linarith [Real.arccos_nonneg (blochVector u ⬝ᵥ blochVector v),
    Real.pi_pos]) (Real.arccos_le_pi _), Real.cos_arccos (by nlinarith) (by nlinarith), ← hB,
    Real.sqrt_sq h0]

/-! ## D. Diagonalization along a diameter -/

/-- **Diagonalization along a diameter** (Fig. 1). Every point `r` of `ℝ³` is the mixture
`((1 + |r|) / 2) |u₁⟩⟨u₁| + ((1 - |r|) / 2) |u₂⟩⟨u₂|` of two orthogonal pure states of the plane,
the ends of a diameter through `r`; for `|r| ≤ 1` the weights lie in `[0, 1]`. -/
theorem exists_blochOperator_eq (r : Fin 3 → ℝ) :
    ∃ u₁ u₂ : EuclideanSpace ℂ (Fin 2), ‖u₁‖ = 1 ∧ ‖u₂‖ = 1 ∧
      ⟪planeVector ψ χ u₁, planeVector ψ χ u₂⟫_ℂ = 0 ∧
      blochOperator ψ χ r =
        (((1 + √(r ⬝ᵥ r)) / 2 : ℝ) : ℂ) • proj (planeVector ψ χ u₁) +
          (((1 - √(r ⬝ᵥ r)) / 2 : ℝ) : ℂ) • proj (planeVector ψ χ u₂) := by
  obtain ⟨n, hn, hr⟩ : ∃ n : Fin 3 → ℝ, n ⬝ᵥ n = 1 ∧ r = √(r ⬝ᵥ r) • n := by
    by_cases h0 : r = 0
    · exact ⟨![0, 0, 1], by simp [dotProduct, Fin.sum_univ_three], by simp [h0]⟩
    have hnn : 0 ≤ r ⬝ᵥ r := by
      simp only [dotProduct, Fin.sum_univ_three]
      nlinarith [mul_self_nonneg (r 0), mul_self_nonneg (r 1), mul_self_nonneg (r 2)]
    have hne : r ⬝ᵥ r ≠ 0 := fun h => h0 (dotProduct_self_eq_zero.mp h)
    have hpos : 0 < √(r ⬝ᵥ r) := Real.sqrt_pos.mpr (hnn.lt_of_ne' hne)
    refine ⟨(√(r ⬝ᵥ r))⁻¹ • r, ?_, by rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]⟩
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← sq, inv_pow,
      Real.sq_sqrt hnn, inv_mul_cancel₀ hne]
  obtain ⟨u₁, h₁, hb₁, hp₁⟩ := exists_proj_planeVector_eq (ψ := ψ) (χ := χ) hn
  obtain ⟨u₂, h₂, hb₂, hp₂⟩ := exists_proj_planeVector_eq (ψ := ψ) (χ := χ) (a := -n)
    (by rw [neg_dotProduct, dotProduct_neg, neg_neg, hn])
  refine ⟨u₁, u₂, h₁, h₂, (inner_planeVector_eq_zero_iff hψ hχ hψχ h₁ h₂).mpr
    (by rw [hb₁, hb₂, neg_neg]), ?_⟩
  rw [hp₁, hp₂]
  calc blochOperator ψ χ r = blochOperator ψ χ (√(r ⬝ᵥ r) • n) := congrArg _ hr
    _ = _ := blochOperator_smul n _

/-- The midpoint of the Bloch vectors of two unit vectors of the plane has squared length their
Born probability. -/
lemma midpoint_dotProduct_self {u v : EuclideanSpace ℂ (Fin 2)} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ((2⁻¹ : ℝ) • (blochVector u + blochVector v)) ⬝ᵥ ((2⁻¹ : ℝ) • (blochVector u + blochVector v)) =
      ‖⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ‖ ^ 2 := by
  have ha := blochVector_dotProduct_self u
  have hb := blochVector_dotProduct_self v
  rw [hu, one_pow] at ha
  rw [hv, one_pow] at hb
  rw [norm_inner_planeVector_sq hψ hχ hψχ hu hv]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul, ha, hb,
    dotProduct_comm (blochVector v)]
  ring

/-- **The geometric diagonalization of an equal mixture** (Fig. 1, eqs. (4)–(5)). The equal
mixture of two pure states `u`, `v` of the plane is
`((1 + |⟨u|v⟩|) / 2) |u₁⟩⟨u₁| + ((1 - |⟨u|v⟩|) / 2) |u₂⟩⟨u₂|` for orthogonal pure states `u₁`, `u₂`
of the plane: its Bloch vector is the midpoint of theirs, of length `|⟨u|v⟩|`, and lies on the
diameter through `u₁` and `u₂`. -/
theorem exists_mix_proj_planeVector_eq {u v : EuclideanSpace ℂ (Fin 2)} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    ∃ u₁ u₂ : EuclideanSpace ℂ (Fin 2), ‖u₁‖ = 1 ∧ ‖u₂‖ = 1 ∧
      ⟪planeVector ψ χ u₁, planeVector ψ χ u₂⟫_ℂ = 0 ∧
      mix (proj (planeVector ψ χ u)) (proj (planeVector ψ χ v)) =
        (((1 + ‖⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ‖) / 2 : ℝ) : ℂ) •
            proj (planeVector ψ χ u₁) +
          (((1 - ‖⟪planeVector ψ χ u, planeVector ψ χ v⟫_ℂ‖) / 2 : ℝ) : ℂ) •
            proj (planeVector ψ χ u₂) := by
  rw [mix_proj_planeVector hu hv]
  have h := exists_blochOperator_eq hψ hχ hψχ ((2⁻¹ : ℝ) • (blochVector u + blochVector v))
  rwa [midpoint_dotProduct_self hψ hχ hψχ hu hv, Real.sqrt_sq (norm_nonneg _)] at h

end QuantumMechanics.Qubit
