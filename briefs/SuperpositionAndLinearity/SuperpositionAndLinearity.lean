/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Directional vectors vs quantum state vectors.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

A direction in space is a unit vector `cos φ sin θ eₓ + sin φ sin θ e_y + cos θ e_z`, linear in
its components along orthogonal directions. The qubit state for the same direction is the vector
`cos (θ/2) e^{-iφ/2} |z⁺⟩ + sin (θ/2) e^{iφ/2} |z⁻⟩`, linear in the square roots of the
probabilities, and only its ray is physical.

Formalized here (`H = EuclideanSpace ℂ (Fin 2)`, `|z⁺⟩ = e₀`, `|z⁻⟩ = e₁`):
* `direction_dotProduct_self`  eq. (1): the direction is a unit vector;
* `prob_zp`, `prob_zm`        eqs. (2), (3): `p(z±) = (1 ± cos θ) / 2 = cos² (θ/2), sin² (θ/2)`;
* `norm_stateVector`          eq. (3): `⟨ψ|ψ⟩ = 1`;
* `blochVector_stateVector`   the state vector has the direction as its Bloch vector;
* `born_stateVector`          the probability is affine in the components of the directions,
                              `p = (1 + v · w) / 2`; eq. (2) is the case `w = e_z`;
* `stateVector_add_two_pi`    `θ + 2π` gives the vector `-ψ`, with the same direction
                              (`direction_add_two_pi`) and the same probabilities;
* `exists_eq_smul_stateVector_iff`  two state vectors give the same state (ray) if and only if
                              they give the same direction;
* `inner_stateVector_eq_zero_iff`   they are orthogonal if and only if the directions are
                              opposite (the outcomes `z⁺`, `z⁻` are opposite directions);
* `exists_eq_smul_stateVector` every unit vector of `H` is a phase times a state vector of the
                              brief's form, with `0 ≤ θ ≤ π`;
* `exists_direction_eq`       every unit vector of `ℝ³` is a direction of the brief's form;
* `blochSphere_mk_stateVector` the homeomorphism `blochSphere` of the projective line
                              `ℙ ℂ ℂ²` onto the unit sphere of `ℝ³` takes the ray of the state
                              vector to its direction;
* `exists_homeomorph_sphere`  so the rays of `ℂ²` form the unit sphere of `ℝ³`, the ray of
                              `ψ(θ, φ)` going to `v(θ, φ)`;
* `axisRotation_y_mulVec_direction`, `spinRotation_y_mulVec_stateVector`  half a turn: in the
                              `(x, z)` plane, turning the direction by `α` is turning the state
                              vector by `α / 2`, by the spin rotation that the double cover
                              `SU(2) → SO(3)` takes to the rotation by `α`
                              (`coe_toSO3_spinRotationSU2`); a full turn of the direction is `-1`
                              on state vectors (`spinRotation_two_pi`);
* `axisRotation_z_mulVec_direction`, `spinRotation_z_mulVec_stateVector`  the same about `e_z`,
                              where the rotation shifts `φ`.

The brief writes `|z⁺⟩` for both kets in the abstract and in eq. (3); the second is `|z⁻⟩`, as
the computation of `p(z⁻)` in eq. (3) shows.
-/
public import ForPhyslib.QuantumMechanics.Qubit.BlochSphere
public import ForPhyslib.QuantumMechanics.Qubit.SpinRotation

open Complex ComplexConjugate Matrix QuantumMechanics.Qubit TauCeti
open scoped LinearAlgebra.Projectivization

@[expose] public noncomputable section

namespace SuperpositionAndLinearity

/-- The two-state Hilbert space `ℂ²`. -/
abbrev H := EuclideanSpace ℂ (Fin 2)

/-- `|z⁺⟩`. -/
abbrev zp : H := EuclideanSpace.single 0 1

/-- `|z⁻⟩`. -/
abbrev zm : H := EuclideanSpace.single 1 1

/-- Eq. (1): the direction with polar angle `θ` and azimuth `φ`. -/
def direction (θ φ : ℝ) : Fin 3 → ℝ :=
  ![Real.cos φ * Real.sin θ, Real.sin φ * Real.sin θ, Real.cos θ]

/-- Eq. (3): the state vector `cos (θ/2) e^{-iφ/2} |z⁺⟩ + sin (θ/2) e^{iφ/2} |z⁻⟩`. -/
def stateVector (θ φ : ℝ) : H :=
  !₂[Real.cos (θ / 2) * exp (-(φ / 2 : ℝ) * I), Real.sin (θ / 2) * exp ((φ / 2 : ℝ) * I)]

/-- Eq. (1): `(vˣ)² + (vʸ)² + (vᶻ)² = 1`. -/
theorem direction_dotProduct_self (θ φ : ℝ) : direction θ φ ⬝ᵥ direction θ φ = 1 := by
  simp only [direction, dotProduct, Fin.sum_univ_three]
  simp
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

lemma stateVector_zero (θ φ : ℝ) :
    stateVector θ φ 0 = Real.cos (θ / 2) * exp (-(φ / 2 : ℝ) * I) := rfl

lemma stateVector_one (θ φ : ℝ) :
    stateVector θ φ 1 = Real.sin (θ / 2) * exp ((φ / 2 : ℝ) * I) := rfl

lemma norm_stateVector_zero (θ φ : ℝ) : ‖stateVector θ φ 0‖ = |Real.cos (θ / 2)| := by
  rw [stateVector_zero, norm_mul, ← ofReal_neg, norm_exp_ofReal_mul_I, mul_one, norm_real,
    Real.norm_eq_abs]

lemma norm_stateVector_one (θ φ : ℝ) : ‖stateVector θ φ 1‖ = |Real.sin (θ / 2)| := by
  rw [stateVector_one, norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs]

lemma cos_sq_half (θ : ℝ) : Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
  rw [Real.cos_sq, show 2 * (θ / 2) = θ by ring]
  ring

lemma sin_sq_half (θ : ℝ) : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
  rw [Real.sin_sq, cos_sq_half]
  ring

/-- Eqs. (2), (3): `p(z⁺) = ⟨ψ|z⁺⟩⟨z⁺|ψ⟩ = cos² (θ/2) = (1 + cos θ) / 2`. -/
theorem prob_zp (θ φ : ℝ) :
    ‖inner ℂ zp (stateVector θ φ)‖ ^ 2 = Real.cos (θ / 2) ^ 2 ∧
      Real.cos (θ / 2) ^ 2 = (1 + Real.cos θ) / 2 := by
  refine ⟨?_, cos_sq_half θ⟩
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, norm_stateVector_zero, sq_abs]

/-- Eqs. (2), (3): `p(z⁻) = ⟨ψ|z⁻⟩⟨z⁻|ψ⟩ = sin² (θ/2) = (1 - cos θ) / 2`. -/
theorem prob_zm (θ φ : ℝ) :
    ‖inner ℂ zm (stateVector θ φ)‖ ^ 2 = Real.sin (θ / 2) ^ 2 ∧
      Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
  refine ⟨?_, sin_sq_half θ⟩
  rw [EuclideanSpace.inner_single_left, map_one, one_mul, norm_stateVector_one, sq_abs]

/-- Eq. (3): `⟨ψ|ψ⟩ = cos² (θ/2) + sin² (θ/2) = 1`. -/
theorem norm_stateVector (θ φ : ℝ) : ‖stateVector θ φ‖ = 1 := by
  have h : ‖stateVector θ φ‖ ^ 2 = 1 := by
    rw [norm_sq, norm_stateVector_zero, norm_stateVector_one, sq_abs, sq_abs,
      Real.cos_sq_add_sin_sq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

lemma stateVector_zero_re (θ φ : ℝ) :
    (stateVector θ φ 0).re = Real.cos (θ / 2) * Real.cos (φ / 2) := by
  rw [stateVector_zero, ← ofReal_neg, re_ofReal_mul, exp_ofReal_mul_I_re, Real.cos_neg]

lemma stateVector_zero_im (θ φ : ℝ) :
    (stateVector θ φ 0).im = -(Real.cos (θ / 2) * Real.sin (φ / 2)) := by
  rw [stateVector_zero, ← ofReal_neg, im_ofReal_mul, exp_ofReal_mul_I_im, Real.sin_neg, mul_neg]

lemma stateVector_one_re (θ φ : ℝ) :
    (stateVector θ φ 1).re = Real.sin (θ / 2) * Real.cos (φ / 2) := by
  rw [stateVector_one, re_ofReal_mul, exp_ofReal_mul_I_re]

lemma stateVector_one_im (θ φ : ℝ) :
    (stateVector θ φ 1).im = Real.sin (θ / 2) * Real.sin (φ / 2) := by
  rw [stateVector_one, im_ofReal_mul, exp_ofReal_mul_I_im]

/-- The state vector has the direction as its Bloch vector. -/
theorem blochVector_stateVector (θ φ : ℝ) : blochVector (stateVector θ φ) = direction θ φ := by
  ext i
  fin_cases i
  · simp only [blochVector, direction, Fin.zero_eta, Matrix.cons_val_zero, mul_re, conj_re,
      conj_im, stateVector_zero_re, stateVector_zero_im, stateVector_one_re, stateVector_one_im]
    conv_rhs => rw [show θ = 2 * (θ / 2) by ring, show φ = 2 * (φ / 2) by ring]
    rw [Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (-2 * Real.cos (θ / 2) * Real.sin (θ / 2)) * Real.sin_sq_add_cos_sq (φ / 2)
  · simp only [blochVector, direction, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      mul_im, conj_re, conj_im, stateVector_zero_re, stateVector_zero_im, stateVector_one_re,
      stateVector_one_im]
    conv_rhs => rw [show θ = 2 * (θ / 2) by ring, show φ = 2 * (φ / 2) by ring]
    rw [Real.sin_two_mul, Real.sin_two_mul]
    ring
  · simp only [blochVector, direction, Fin.reduceFinMk, Matrix.cons_val, norm_stateVector_zero,
      norm_stateVector_one, sq_abs]
    conv_rhs => rw [show θ = 2 * (θ / 2) by ring]
    rw [Real.cos_two_mul]
    linear_combination (-1 : ℝ) * Real.sin_sq_add_cos_sq (θ / 2)

/-- The probability is affine in the components of the directions: `p = (1 + v · w) / 2`. -/
theorem born_stateVector (θ φ θ' φ' : ℝ) :
    ‖inner ℂ (stateVector θ' φ') (stateVector θ φ)‖ ^ 2 =
      (1 + direction θ' φ' ⬝ᵥ direction θ φ) / 2 := by
  rw [norm_inner_sq, norm_stateVector, norm_stateVector, blochVector_stateVector,
    blochVector_stateVector]
  ring

/-- `|z⁺⟩` is the state vector of `e_z`, so eq. (2) is the case `w = e_z` of
`born_stateVector`. -/
theorem stateVector_zero_zero : stateVector 0 0 = zp := by
  ext i
  fin_cases i <;> simp [stateVector]

lemma direction_zero_zero : direction 0 0 = ![0, 0, 1] := by
  simp [direction]

/-- `θ + 2π` gives the vector `-ψ`. -/
theorem stateVector_add_two_pi (θ φ : ℝ) :
    stateVector (θ + 2 * Real.pi) φ = -stateVector θ φ := by
  have h : (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi := by ring
  ext i
  fin_cases i <;> simp [stateVector, h, Real.cos_add_pi, Real.sin_add_pi]

/-- `θ + 2π` gives the same direction. -/
theorem direction_add_two_pi (θ φ : ℝ) : direction (θ + 2 * Real.pi) φ = direction θ φ := by
  simp [direction, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Two state vectors give the same state (span the same ray) if and only if they give the same
direction. -/
theorem exists_eq_smul_stateVector_iff (θ φ θ' φ' : ℝ) :
    (∃ c : ℂ, stateVector θ' φ' = c • stateVector θ φ) ↔ direction θ' φ' = direction θ φ := by
  rw [exists_eq_smul_iff (norm_stateVector θ' φ') (norm_stateVector θ φ),
    blochVector_stateVector, blochVector_stateVector]

/-- Two state vectors are orthogonal if and only if their directions are opposite. -/
theorem inner_stateVector_eq_zero_iff (θ φ θ' φ' : ℝ) :
    inner ℂ (stateVector θ' φ') (stateVector θ φ) = 0 ↔ direction θ' φ' = -direction θ φ := by
  rw [inner_eq_zero_iff (norm_stateVector θ' φ') (norm_stateVector θ φ),
    blochVector_stateVector, blochVector_stateVector]

/-- Every unit vector of `H` is a phase times a state vector of the form (3), with
`0 ≤ θ ≤ π`. -/
theorem exists_eq_smul_stateVector {ψ : H} (hψ : ‖ψ‖ = 1) :
    ∃ θ ∈ Set.Icc 0 Real.pi, ∃ φ : ℝ, ∃ c : ℂ, ‖c‖ = 1 ∧ ψ = c • stateVector θ φ := by
  have h1 : ‖ψ 0‖ ^ 2 + ‖ψ 1‖ ^ 2 = 1 := by rw [← norm_sq, hψ, one_pow]
  have hx1 : ‖ψ 0‖ ≤ 1 := by nlinarith [norm_nonneg (ψ 0), norm_nonneg (ψ 1)]
  have hx0 := norm_nonneg (ψ 0)
  set α := arg (ψ 0)
  set β := arg (ψ 1)
  set θ := 2 * Real.arccos ‖ψ 0‖
  have hθ : θ / 2 = Real.arccos ‖ψ 0‖ := by simp only [θ]; ring
  have hcos : Real.cos (θ / 2) = ‖ψ 0‖ := by
    rw [hθ, Real.cos_arccos (by linarith) hx1]
  have hsin : Real.sin (θ / 2) = ‖ψ 1‖ := by
    rw [hθ, Real.sin_arccos, show 1 - ‖ψ 0‖ ^ 2 = ‖ψ 1‖ ^ 2 by linarith,
      Real.sqrt_sq (norm_nonneg _)]
  refine ⟨θ, ⟨mul_nonneg zero_le_two (Real.arccos_nonneg _), ?_⟩, β - α,
    exp (((α + β) / 2 : ℝ) * I), norm_exp_ofReal_mul_I _, ?_⟩
  · have := Real.arccos_le_pi_div_two.mpr hx0
    simp only [θ]
    linarith
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, PiLp.smul_apply, smul_eq_mul, stateVector_zero, hcos]
    calc ψ 0 = ‖ψ 0‖ * exp (α * I) := (norm_mul_exp_arg_mul_I _).symm
      _ = _ := by
        rw [mul_left_comm, ← exp_add]
        congr 2
        push_cast
        ring
  · simp only [Fin.mk_one, PiLp.smul_apply, smul_eq_mul, stateVector_one, hsin]
    calc ψ 1 = ‖ψ 1‖ * exp (β * I) := (norm_mul_exp_arg_mul_I _).symm
      _ = _ := by
        rw [mul_left_comm, ← exp_add]
        congr 2
        push_cast
        ring

/-- Every unit vector of `ℝ³` is a direction of the form (1). -/
theorem exists_direction_eq {v : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) :
    ∃ θ φ : ℝ, direction θ φ = v := by
  have hv' : v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 = 1 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hv
  set w : ℂ := v 0 + v 1 * I
  have hsin : Real.sin (Real.arccos (v 2)) = ‖w‖ := by
    rw [Real.sin_arccos, norm_add_mul_I, show 1 - v 2 ^ 2 = v 0 ^ 2 + v 1 ^ 2 by linarith]
  refine ⟨Real.arccos (v 2), arg w, ?_⟩
  ext i
  fin_cases i
  · simp only [direction, Fin.zero_eta, Matrix.cons_val_zero, hsin, mul_comm, norm_mul_cos_arg]
    simp [w]
  · simp only [direction, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hsin, mul_comm,
      norm_mul_sin_arg]
    simp [w]
  · simp only [direction, Fin.reduceFinMk, Matrix.cons_val]
    exact Real.cos_arccos (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)])
      (by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)])

/-- The homeomorphism `blochSphere` of the projective line onto the unit sphere takes the ray of
`ψ(θ, φ)` to `v(θ, φ)`. -/
theorem blochSphere_mk_stateVector (θ φ : ℝ) (h : (stateVector θ φ).ofLp ≠ 0) :
    (blochSphere (Projectivization.mk ℂ (stateVector θ φ).ofLp h) : EuclideanSpace ℝ (Fin 3)) =
      WithLp.toLp 2 (direction θ φ) := by
  rw [coe_blochSphere, blochPoint_mk, unitBlochVector, WithLp.toLp_ofLp, norm_stateVector,
    one_pow, inv_one, one_smul, blochVector_stateVector]

/-- The rays of `ℂ²` form the unit sphere of `ℝ³`: Mathlib's projective line `ℙ ℂ ℂ²` is
homeomorphic to the sphere, by a homeomorphism that takes the ray of `ψ(θ, φ)` to `v(θ, φ)`. -/
theorem exists_homeomorph_sphere :
    ∃ e : ℙ ℂ (Fin 2 → ℂ) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ (θ φ : ℝ) (h : (stateVector θ φ).ofLp ≠ 0),
        (e (Projectivization.mk ℂ (stateVector θ φ).ofLp h) : EuclideanSpace ℝ (Fin 3)) =
          WithLp.toLp 2 (direction θ φ) :=
  ⟨blochSphere, blochSphere_mk_stateVector⟩

/-- The rotation by `α` about `e_z` takes the direction `v(θ, φ)` to `v(θ, φ + α)`. -/
theorem axisRotation_z_mulVec_direction (α θ φ : ℝ) :
    axisRotation ![0, 0, 1] α *ᵥ direction θ φ = direction θ (φ + α) := by
  rw [axisRotation_mulVec]
  ext i
  fin_cases i <;>
    simp [direction, cross_apply, dotProduct, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;>
    ring

/-- In the `(x, z)` plane, the rotation by `α` about `e_y` takes the direction `v(θ, 0)` to
`v(θ + α, 0)`. -/
theorem axisRotation_y_mulVec_direction (α θ : ℝ) :
    axisRotation ![0, 1, 0] α *ᵥ direction θ 0 = direction (θ + α) 0 := by
  rw [axisRotation_mulVec]
  ext i
  fin_cases i <;>
    simp [direction, cross_apply, dotProduct, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;>
    ring

/-- The spin rotation of half the angle about `e_z`, `diag (e^{-iα/2}, e^{iα/2})`, takes the state
vector `ψ(θ, φ)` to `ψ(θ, φ + α)`. -/
theorem spinRotation_z_mulVec_stateVector (α θ φ : ℝ) :
    spinRotation ![0, 0, 1] α *ᵥ (stateVector θ φ).ofLp = (stateVector θ (φ + α)).ofLp := by
  have hU : spinRotation ![0, 0, 1] α =
      !![exp (-(α / 2 : ℝ) * I), 0; 0, exp ((α / 2 : ℝ) * I)] := by
    rw [← ofReal_neg, exp_mul_I, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ← ofReal_cos,
      ← ofReal_sin, Real.cos_neg, Real.sin_neg]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [spinRotation, pauli_apply, -ofReal_cos, -ofReal_sin] <;>
      ring
  rw [hU]
  ext i
  fin_cases i <;>
  · simp [stateVector, mulVec, dotProduct, Fin.sum_univ_two]
    rw [mul_left_comm, ← exp_add]
    congr 2
    ring

/-- In the `(x, z)` plane, the spin rotation about `e_y` turns the state vector by half the angle:
it takes `ψ(θ, 0)` to `ψ(θ + α, 0)`, the vector at angle `(θ + α) / 2` from `|z⁺⟩`. -/
theorem spinRotation_y_mulVec_stateVector (α θ : ℝ) :
    spinRotation ![0, 1, 0] α *ᵥ (stateVector θ 0).ofLp = (stateVector (θ + α) 0).ofLp := by
  have h : (θ + α) / 2 = θ / 2 + α / 2 := by ring
  ext i
  fin_cases i <;>
    simp [stateVector, spinRotation, pauli_apply, mulVec, dotProduct, Fin.sum_univ_two, h,
      Real.cos_add, Real.sin_add, -ofReal_cos, -ofReal_sin]
  · linear_combination ((Real.sin (α / 2) : ℂ) * Real.sin (θ / 2)) * I_sq
  · linear_combination (-(Real.sin (α / 2) : ℂ) * Real.cos (θ / 2)) * I_sq

end SuperpositionAndLinearity
