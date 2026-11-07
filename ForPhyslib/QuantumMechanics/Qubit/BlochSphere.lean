/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Qubit.Bloch
public import TauCeti.LinearAlgebra.Matrix.Pauli
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
public import TauCeti.Topology.Algebra.Projectivization

/-!
# The Bloch sphere

The pure states of a qubit, the rays of `ℂ²`, form a two-sphere: the Bloch vector of a unit
vector depends only on its ray and lies on the unit sphere of `ℝ³`, and every point of the sphere
is the Bloch vector of exactly one ray. Since `ℙ ℂ (Fin 2 → ℂ)` is compact and the sphere is
Hausdorff, the continuous bijection is a homeomorphism.

The Hermitian projector of a ray, `|ψ⟩⟨ψ|` for a unit vector `ψ`, is `(1 + a · σ) / 2` with `a` the
Bloch vector of the ray; `a · σ` is TauCeti's Pauli map, which agrees with physlib's
`vectorMatrix`.

## Key results

- `QuantumMechanics.Qubit.unitBlochVector`: the Bloch vector of the unit vector along `x ≠ 0`.
- `QuantumMechanics.Qubit.blochPoint`: the Bloch vector of a ray.
- `QuantumMechanics.Qubit.blochPoint_injective`, `QuantumMechanics.Qubit.blochPoint_surjective`.
- `QuantumMechanics.Qubit.blochSphere`: the homeomorphism from `ℙ ℂ (Fin 2 → ℂ)` onto the unit
  sphere of `ℝ³`.
- `QuantumMechanics.Qubit.vectorMatrix_eq_pauli`: physlib's `vectorMatrix` is TauCeti's `pauli`.
- `QuantumMechanics.Qubit.hermitianProjector_eq`: `|ψ⟩⟨ψ| = (1 + a · σ) / 2`.
-/

@[expose] public noncomputable section

open Complex ComplexConjugate Matrix PauliMatrix Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

namespace QuantumMechanics.Qubit

/-- Physlib's `vectorMatrix a = a · σ` is TauCeti's Pauli map. -/
theorem vectorMatrix_eq_pauli (a : Fin 3 → ℝ) : vectorMatrix a = pauli a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  · apply Complex.ext <;> simp [vectorMatrix, pauliMatrix, pauli_apply, Fin.sum_univ_three]

lemma norm_toLp_sq (a : Fin 3 → ℝ) : ‖WithLp.toLp 2 a‖ ^ 2 = a ⬝ᵥ a := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, sq]

theorem continuous_blochVector : Continuous blochVector := by
  have h0 : Continuous fun ψ : EuclideanSpace ℂ (Fin 2) ↦ ψ 0 :=
    (continuous_apply 0).comp (PiLp.continuous_ofLp 2 _)
  have h1 : Continuous fun ψ : EuclideanSpace ℂ (Fin 2) ↦ ψ 1 :=
    (continuous_apply 1).comp (PiLp.continuous_ofLp 2 _)
  have hp : Continuous fun ψ : EuclideanSpace ℂ (Fin 2) ↦ conj (ψ 0) * ψ 1 :=
    (continuous_conj.comp h0).mul h1
  refine continuous_pi fun i ↦ ?_
  fin_cases i
  · exact continuous_const.mul (continuous_re.comp hp)
  · exact continuous_const.mul (continuous_im.comp hp)
  · exact (h0.norm.pow 2).sub (h1.norm.pow 2)

/-- The Bloch vector of the unit vector along `x`, for `x ≠ 0`; it is `0` for `x = 0`. -/
def unitBlochVector (x : Fin 2 → ℂ) : Fin 3 → ℝ :=
  (‖WithLp.toLp 2 x‖ ^ 2)⁻¹ • blochVector (WithLp.toLp 2 x)

lemma unitBlochVector_smul {c : ℂ} (hc : c ≠ 0) (x : Fin 2 → ℂ) :
    unitBlochVector (c • x) = unitBlochVector x := by
  have hc' : ‖c‖ ^ 2 ≠ 0 := by positivity
  simp only [unitBlochVector, WithLp.toLp_smul, blochVector_smul, norm_smul, mul_pow, smul_smul]
  congr 1
  field_simp

lemma unitBlochVector_dotProduct_self {x : Fin 2 → ℂ} (hx : x ≠ 0) :
    unitBlochVector x ⬝ᵥ unitBlochVector x = 1 := by
  have h : ‖WithLp.toLp 2 x‖ ≠ 0 := by simpa using hx
  simp only [unitBlochVector, smul_dotProduct, dotProduct_smul, blochVector_dotProduct_self,
    smul_eq_mul]
  field_simp

/-- The Bloch vector of a ray of `ℂ²`. -/
def blochPoint (p : ℙ ℂ (Fin 2 → ℂ)) : Fin 3 → ℝ :=
  p.lift (fun x ↦ unitBlochVector x.1) fun x y c h ↦ by
    rw [h, unitBlochVector_smul]
    rintro rfl
    exact x.2 (by simp [h])

@[simp]
theorem blochPoint_mk (x : Fin 2 → ℂ) (hx : x ≠ 0) :
    blochPoint (mk ℂ x hx) = unitBlochVector x :=
  Projectivization.lift_mk _ _ x hx

theorem blochPoint_dotProduct_self (p : ℙ ℂ (Fin 2 → ℂ)) : blochPoint p ⬝ᵥ blochPoint p = 1 := by
  induction p using ind with
  | h x hx => simpa using unitBlochVector_dotProduct_self hx

theorem continuous_blochPoint : Continuous blochPoint := by
  rw [continuous_iff]
  have h : blochPoint ∘ mk' ℂ = fun x : {x : Fin 2 → ℂ // x ≠ 0} ↦ unitBlochVector x.1 :=
    funext fun x ↦ blochPoint_mk x.1 x.2
  rw [h]
  have hn : ∀ x : {x : Fin 2 → ℂ // x ≠ 0}, ‖WithLp.toLp 2 x.1‖ ^ 2 ≠ 0 := fun x ↦ by
    simpa using x.2
  have hψ : Continuous fun x : {x : Fin 2 → ℂ // x ≠ 0} ↦ WithLp.toLp 2 x.1 :=
    (PiLp.continuous_toLp 2 _).comp continuous_subtype_val
  exact ((hψ.norm.pow 2).inv₀ hn).smul (continuous_blochVector.comp hψ)

theorem blochPoint_injective : Function.Injective blochPoint := by
  intro p q h
  induction p using ind with | h x hx =>
  induction q using ind with | h y hy =>
  simp only [blochPoint_mk] at h
  set ψ := WithLp.toLp 2 x
  set χ := WithLp.toLp 2 y
  have hψ : ‖ψ‖ ≠ 0 := by simpa [ψ] using hx
  have hχ : ‖χ‖ ≠ 0 := by simpa [χ] using hy
  have hu : ∀ (φ : EuclideanSpace ℂ (Fin 2)), ‖φ‖ ≠ 0 →
      ‖((‖φ‖ : ℂ)⁻¹ • φ)‖ = 1 ∧
        blochVector ((‖φ‖ : ℂ)⁻¹ • φ) = (‖φ‖ ^ 2)⁻¹ • blochVector φ := fun φ hφ ↦ by
    refine ⟨?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ hφ]
    · rw [blochVector_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        inv_pow]
  obtain ⟨hψ1, hψb⟩ := hu ψ hψ
  obtain ⟨hχ1, hχb⟩ := hu χ hχ
  obtain ⟨c, hc⟩ := (exists_eq_smul_iff hψ1 hχ1).mpr (by
    rw [hψb, hχb]
    exact h)
  rw [mk_eq_mk_iff']
  refine ⟨(‖ψ‖ : ℂ) * c * (‖χ‖ : ℂ)⁻¹, ?_⟩
  have hψ' : (‖ψ‖ : ℂ) ≠ 0 := by exact_mod_cast hψ
  have hx' : ψ = ((‖ψ‖ : ℂ) * c * (‖χ‖ : ℂ)⁻¹) • χ := by
    rw [mul_assoc, mul_smul, ← smul_smul, ← hc, smul_smul, mul_inv_cancel₀ hψ', one_smul]
  have := congrArg WithLp.ofLp hx'
  simpa [ψ, χ] using this.symm

theorem blochPoint_surjective (a : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1) :
    ∃ p : ℙ ℂ (Fin 2 → ℂ), blochPoint p = a := by
  simp only [dotProduct, Fin.sum_univ_three] at ha
  by_cases h2 : a 2 = -1
  · have h0 : a 0 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    have h1 : a 1 = 0 := by nlinarith [sq_nonneg (a 0), sq_nonneg (a 1)]
    refine ⟨mk ℂ ![0, 1] (by simp), ?_⟩
    ext i
    fin_cases i <;> simp [unitBlochVector, blochVector, EuclideanSpace.norm_sq_eq, h0, h1, h2]
  · have h2' : (1 + a 2 : ℝ) ≠ 0 := fun h ↦ h2 (by linarith)
    have hx : (![1 + (a 2 : ℂ), a 0 + a 1 * I] : Fin 2 → ℂ) ≠ 0 := fun h ↦
      h2' (by have := congrFun h 0; simp at this; exact_mod_cast this)
    refine ⟨mk ℂ _ hx, ?_⟩
    have hn : ‖WithLp.toLp 2 (![1 + (a 2 : ℂ), a 0 + a 1 * I] : Fin 2 → ℂ)‖ ^ 2 =
        2 * (1 + a 2) := by
      simp [EuclideanSpace.norm_sq_eq, Complex.sq_norm, Complex.normSq_apply]
      nlinarith
    ext i
    fin_cases i
    · simp [unitBlochVector, hn, blochVector]
      field_simp
    · simp [unitBlochVector, hn, blochVector]
      field_simp
    · simp [unitBlochVector, hn, blochVector, Complex.sq_norm, Complex.normSq_apply]
      field_simp
      nlinarith

theorem blochPoint_mem_sphere (p : ℙ ℂ (Fin 2 → ℂ)) :
    WithLp.toLp 2 (blochPoint p) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    norm_toLp_sq, blochPoint_dotProduct_self]

/-- The Bloch map as a bijection onto the unit sphere. -/
def blochEquiv : ℙ ℂ (Fin 2 → ℂ) ≃ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Equiv.ofBijective (fun p ↦ ⟨WithLp.toLp 2 (blochPoint p), blochPoint_mem_sphere p⟩)
    ⟨fun p q h ↦ blochPoint_injective (by simpa using congrArg Subtype.val h), fun a ↦ by
      obtain ⟨p, hp⟩ := blochPoint_surjective a.1.ofLp (by
        rw [← norm_toLp_sq, WithLp.toLp_ofLp, mem_sphere_zero_iff_norm.mp a.2, one_pow])
      exact ⟨p, Subtype.ext (by simp [hp])⟩⟩

/-- **The Bloch sphere**: the rays of `ℂ²` form the unit sphere of `ℝ³`. -/
def blochSphere : ℙ ℂ (Fin 2 → ℂ) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Continuous.homeoOfEquivCompactToT2 (f := blochEquiv)
    (((PiLp.continuous_toLp 2 _).comp continuous_blochPoint).subtype_mk _)

@[simp]
theorem coe_blochSphere (p : ℙ ℂ (Fin 2 → ℂ)) :
    (blochSphere p : EuclideanSpace ℝ (Fin 3)) = WithLp.toLp 2 (blochPoint p) :=
  rfl

/-- The Hermitian projector of a ray with Bloch vector `a` is `(1 + a · σ) / 2`. -/
theorem hermitianProjector_eq (p : ℙ ℂ (Fin 2 → ℂ)) :
    hermitianProjector p = (1 / 2 : ℂ) • (1 + pauli (blochPoint p)) := by
  induction p using ind with | h x hx =>
  have hn : ‖WithLp.toLp 2 x‖ ^ 2 ≠ 0 := by simpa using hx
  have hd : star x ⬝ᵥ x = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : ℂ) := by
    simp [EuclideanSpace.norm_sq_eq, dotProduct, Fin.sum_univ_two, Complex.conj_mul']
  have hv := vecMulVec_eq (WithLp.toLp 2 x)
  rw [vectorMatrix_eq_pauli] at hv
  rw [hermitianProjector_mk, blochPoint_mk, rankOneHermitianProjector_def, hd]
  change _ • vecMulVec (WithLp.toLp 2 x).ofLp (star (WithLp.toLp 2 x).ofLp) = _
  have hn' : (‖WithLp.toLp 2 x‖ : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hn
  rw [hv, unitBlochVector, map_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli_apply] <;> field_simp <;>
    simp only [add_div, div_self hn', neg_div]

end QuantumMechanics.Qubit
