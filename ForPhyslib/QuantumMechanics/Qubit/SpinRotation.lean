/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import TauCeti.RepresentationTheory.SU2.Adjoint

/-!
# Spin rotations: the unitary of half the angle

The rotation of `ℝ³` about a unit vector `n` by the angle `α` is the image, under TauCeti's double
cover `SU(2) → SO(3)`, of the spin rotation `cos (α / 2) - i sin (α / 2) (n · σ)`: the rotation by
`α` acts on spinors through half the angle. A full turn, `α = 2π`, is the identity on `ℝ³` and `-1`
on spinors, and the two elements of `SU(2)` above the rotation by `α` are the spin rotations by `α`
and by `α + 2π`.

## Key results

- `QuantumMechanics.Qubit.axisRotation`: the rotation about `n` by `α` (Rodrigues' formula).
- `QuantumMechanics.Qubit.spinRotation`: the spin rotation `cos (α / 2) - i sin (α / 2) (n · σ)`.
- `QuantumMechanics.Qubit.coe_toSO3_spinRotationSU2`: the double cover takes the spin rotation by
  `α` to the rotation by `α`.
- `QuantumMechanics.Qubit.spinRotation_two_pi`, `QuantumMechanics.Qubit.axisRotation_two_pi`: a
  full turn is `-1` on spinors and `1` on `ℝ³`.
- `QuantumMechanics.Qubit.toSO3_eq_toSO3_iff`: the double cover is two-to-one.
- `QuantumMechanics.Qubit.coe_toSO3_eq_axisRotation_iff`: the elements of `SU(2)` above the rotation
  by `α` are the spin rotations by `α` and `α + 2π`.
-/

@[expose] public noncomputable section

open Complex Matrix TauCeti

namespace QuantumMechanics.Qubit

/-- The rotation of `ℝ³` about the axis `n` by the angle `α`, by Rodrigues' formula
`x ↦ cos α x + sin α (n ⨯₃ x) + (1 - cos α) (n ⬝ᵥ x) n` (`axisRotation_mulVec`); for a unit vector
`n` it turns the plane orthogonal to `n` by `α` in the positive sense about `n`. -/
def axisRotation (n : Fin 3 → ℝ) (α : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  of fun i j ↦ Real.cos α * (1 : Matrix (Fin 3) (Fin 3) ℝ) i j +
    Real.sin α * (n ⨯₃ Pi.single j 1) i + (1 - Real.cos α) * n i * n j

/-- Rodrigues' formula. -/
theorem axisRotation_mulVec (n : Fin 3 → ℝ) (α : ℝ) (x : Fin 3 → ℝ) :
    axisRotation n α *ᵥ x =
      Real.cos α • x + Real.sin α • n ⨯₃ x + ((1 - Real.cos α) * (n ⬝ᵥ x)) • n := by
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases i <;>
  · simp [axisRotation, mulVec, dotProduct, Fin.sum_univ_three, cross_apply, Matrix.one_apply]
    ring

/-- The spin-`1/2` rotation `cos (α / 2) - i sin (α / 2) (n · σ)`, which is `exp (-i α (n · σ) / 2)`
for a unit vector `n`: the unitary of half the angle. -/
def spinRotation (n : Fin 3 → ℝ) (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos (α / 2) : ℂ) • 1 - (I * Real.sin (α / 2)) • pauli n

/-- The adjoint of the spin rotation. -/
theorem star_spinRotation (n : Fin 3 → ℝ) (α : ℝ) :
    star (spinRotation n α) = (Real.cos (α / 2) : ℂ) • 1 + (I * Real.sin (α / 2)) • pauli n := by
  rw [spinRotation, star_sub, star_smul, star_smul, star_one, star_eq_conjTranspose (pauli n),
    (isHermitian_pauli n).eq]
  simp only [Complex.star_def, star_mul', conj_I, conj_ofReal]
  rw [sub_eq_add_neg, ← neg_smul]
  simp only [neg_mul, neg_neg]

/-- Conjugation by the spin rotation of angle `α` about a unit vector `n` is the rotation by `α`
about `n`, read through the Pauli map. -/
theorem pauli_axisRotation_mulVec {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (α : ℝ) (x : Fin 3 → ℝ) :
    pauli (axisRotation n α *ᵥ x) = spinRotation n α * pauli x * star (spinRotation n α) := by
  obtain ⟨β, rfl⟩ : ∃ β, α = 2 * β := ⟨α / 2, by ring⟩
  have hβ : 2 * β / 2 = β := by ring
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hn
  have hsc := Real.sin_sq_add_cos_sq β
  rw [star_spinRotation, axisRotation_mulVec, Real.cos_two_mul, Real.sin_two_mul]
  simp only [spinRotation, hβ]
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [pauli_apply, Matrix.mul_apply, Fin.sum_univ_two, cross_apply, dotProduct, Pi.smul_apply,
      smul_eq_mul, vecHead, vecTail, sq,
      Fin.sum_univ_three, -ofReal_cos, -ofReal_sin] <;>
  first
  | linear_combination (x 2 - 2 * (n 0 * x 0 + n 1 * x 1 + n 2 * x 2) * n 2) * hsc +
      Real.sin β ^ 2 * x 2 * hn'
  | linear_combination (-x 2 + 2 * (n 0 * x 0 + n 1 * x 1 + n 2 * x 2) * n 2) * hsc -
      Real.sin β ^ 2 * x 2 * hn'
  | linear_combination (x 0 - 2 * (n 0 * x 0 + n 1 * x 1 + n 2 * x 2) * n 0) * hsc +
      Real.sin β ^ 2 * x 0 * hn'
  | linear_combination (x 1 - 2 * (n 0 * x 0 + n 1 * x 1 + n 2 * x 2) * n 1) * hsc +
      Real.sin β ^ 2 * x 1 * hn'
  | linear_combination (-x 1 + 2 * (n 0 * x 0 + n 1 * x 1 + n 2 * x 2) * n 1) * hsc -
      Real.sin β ^ 2 * x 1 * hn'
  | ring_nf

/-- For a unit vector `n` the spin rotation lies in `SU(2)`. -/
theorem spinRotation_mem_specialUnitaryGroup {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (α : ℝ) :
    spinRotation n α ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hn
  have hsc := Real.sin_sq_add_cos_sq (α / 2)
  refine mem_specialUnitaryGroup_iff.mpr ⟨mem_unitaryGroup_iff.mpr ?_, ?_⟩
  · rw [star_spinRotation]
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [spinRotation, pauli_apply, Matrix.mul_apply, Fin.sum_univ_two, -ofReal_cos,
        -ofReal_sin] <;>
      first
      | linear_combination hsc + Real.sin (α / 2) ^ 2 * hn'
      | ring_nf
  · simp only [spinRotation, pauli_apply, det_fin_two]
    apply Complex.ext <;> simp [-ofReal_cos, -ofReal_sin] <;>
      first
      | linear_combination hsc + Real.sin (α / 2) ^ 2 * hn'
      | ring_nf

/-- The spin rotation as an element of `SU(2)`. -/
def spinRotationSU2 {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (α : ℝ) : SU2 :=
  ⟨spinRotation n α, spinRotation_mem_specialUnitaryGroup hn α⟩

@[simp]
theorem coe_spinRotationSU2 {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (α : ℝ) :
    (spinRotationSU2 hn α : Matrix (Fin 2) (Fin 2) ℂ) = spinRotation n α :=
  rfl

/-- **The rotation by `α` is the image of the unitary of half the angle** under the double cover
`SU(2) → SO(3)`. -/
theorem coe_toSO3_spinRotationSU2 {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (α : ℝ) :
    (SU2.toSO3 (spinRotationSU2 hn α) : Matrix (Fin 3) (Fin 3) ℝ) = axisRotation n α := by
  rw [SU2.coe_toSO3, pauliRotation_eq_iff]
  exact fun x ↦ pauli_axisRotation_mulVec hn α x

/-- Turning the angle by `2π` changes the sign of the spin rotation. -/
theorem spinRotation_add_two_pi (n : Fin 3 → ℝ) (α : ℝ) :
    spinRotation n (α + 2 * Real.pi) = -spinRotation n α := by
  have h : (α + 2 * Real.pi) / 2 = α / 2 + Real.pi := by ring
  rw [spinRotation, spinRotation, h, Real.cos_add_pi, Real.sin_add_pi, ofReal_neg, ofReal_neg,
    neg_smul, mul_neg, neg_smul, neg_sub, sub_neg_eq_add, neg_add_eq_sub]

/-- A full turn is `-1` on spinors. -/
theorem spinRotation_two_pi (n : Fin 3 → ℝ) : spinRotation n (2 * Real.pi) = -1 := by
  simp [spinRotation]

/-- Turning the angle by `2π` does not change the rotation. -/
theorem axisRotation_add_two_pi (n : Fin 3 → ℝ) (α : ℝ) :
    axisRotation n (α + 2 * Real.pi) = axisRotation n α := by
  simp only [axisRotation, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- A full turn is the identity on `ℝ³`. -/
theorem axisRotation_two_pi (n : Fin 3 → ℝ) : axisRotation n (2 * Real.pi) = 1 := by
  have h := axisRotation_add_two_pi n 0
  rw [zero_add] at h
  rw [h]
  ext i j
  simp [axisRotation]

/-- The double cover `SU(2) → SO(3)` is two-to-one: two elements have the same image exactly when
they agree up to sign. -/
theorem toSO3_eq_toSO3_iff (g h : SU2) :
    SU2.toSO3 g = SU2.toSO3 h ↔
      (g : Matrix (Fin 2) (Fin 2) ℂ) = h ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) = -h := by
  have hu := (mem_specialUnitaryGroup_iff.mp h.2).1
  have h1 : (h : Matrix (Fin 2) (Fin 2) ℂ) * star (h : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Unitary.mul_star_self_of_mem hu
  have h2 : star (h : Matrix (Fin 2) (Fin 2) ℂ) * h = 1 := Unitary.star_mul_self_of_mem hu
  have key : ∀ c : Matrix (Fin 2) (Fin 2) ℂ,
      ((h⁻¹ * g : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = c ↔
        (g : Matrix (Fin 2) (Fin 2) ℂ) = h * c := fun c ↦ by
    change star (h : Matrix (Fin 2) (Fin 2) ℂ) * g = c ↔ _
    constructor
    · rintro rfl
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    · intro e
      rw [e, ← Matrix.mul_assoc, h2, Matrix.one_mul]
  rw [eq_comm, ← inv_mul_eq_one, ← map_inv, ← map_mul, SU2.toSO3_eq_one_iff, key, key,
    Matrix.mul_one, Matrix.mul_neg, Matrix.mul_one]

/-- The two elements of `SU(2)` above the rotation by `α` about `n` are the spin rotations by `α`
and by `α + 2π`. -/
theorem coe_toSO3_eq_axisRotation_iff {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (α : ℝ) (g : SU2) :
    (SU2.toSO3 g : Matrix (Fin 3) (Fin 3) ℝ) = axisRotation n α ↔
      (g : Matrix (Fin 2) (Fin 2) ℂ) = spinRotation n α ∨
        (g : Matrix (Fin 2) (Fin 2) ℂ) = spinRotation n (α + 2 * Real.pi) := by
  rw [← coe_toSO3_spinRotationSU2 hn, Subtype.coe_inj, toSO3_eq_toSO3_iff, coe_spinRotationSU2,
    spinRotation_add_two_pi]

/-- The rotation fixes its axis. -/
theorem axisRotation_mulVec_self {n : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (α : ℝ) :
    axisRotation n α *ᵥ n = n := by
  rw [axisRotation_mulVec, cross_self, smul_zero, add_zero, hn, mul_one, ← add_smul]
  simp

end QuantumMechanics.Qubit
