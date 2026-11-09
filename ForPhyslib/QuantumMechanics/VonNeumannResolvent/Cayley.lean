/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.VonNeumannResolvent

/-!
# The Cayley transform of the von Neumann generator

Let `L ρ = -i (K ρ - ρ K)` be the von Neumann generator of a self-adjoint `K` on a
finite-dimensional complex Hilbert space, and `Ψ τ = (1 - τ L)⁻¹` its resolvent. The Cayley
transform

  `C τ = (1 + τ L) (1 - τ L)⁻¹`

is `2 Ψ τ - 1`, so that `Ψ τ = (1 + C τ) / 2`: the resolvent is the midpoint between the identity
and the Cayley transform.

`L` is skew for the Hilbert–Schmidt inner product `⟨A, B⟩ = tr (A† B)`: `L A† = (L A)†` and the
trace is cyclic. So `(1 ± τ L) x` both have Hilbert–Schmidt products
`⟨x, y⟩ + τ² ⟨L x, L y⟩`, and `C τ` preserves the Hilbert–Schmidt inner product: it is unitary on
all operators, and orthogonal on the real space of self-adjoint ones.

## Main definitions

* `QuantumMechanics.vonNeumannCayley`: the Cayley transform `(1 + τ L) (1 - τ L)⁻¹`.

## Main results

* `QuantumMechanics.vonNeumannResolvent_eq_midpoint`: `Ψ τ = (1 + C τ) / 2`.
* `QuantumMechanics.trace_star_vonNeumannGenerator_mul`: `L` is skew for `tr (A† B)`.
* `QuantumMechanics.trace_star_vonNeumannCayley_mul`: `C τ` preserves `tr (A† B)`.
-/

@[expose] public noncomputable section

open Complex

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {K : E →L[ℂ] E}

/-- The trace of operators, as a linear map. -/
private abbrev tr : (E →L[ℂ] E) →ₗ[ℂ] ℂ :=
  (LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ)

omit [CompleteSpace E] in
private lemma trace_eq_tr (X : E →L[ℂ] E) : LinearMap.trace ℂ E ↑X = tr X := by
  simp only [tr, LinearMap.comp_apply, ContinuousLinearMap.coeLM_apply]

omit [CompleteSpace E] in
private lemma tr_mul_comm (X Y : E →L[ℂ] E) : tr (X * Y) = tr (Y * X) := by
  simp only [tr, LinearMap.comp_apply, ContinuousLinearMap.coeLM_apply,
    ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm]

/-- **Skewness of `L`** for the Hilbert–Schmidt inner product: `tr ((L A)† B) = -tr (A† (L B))`. -/
theorem trace_star_vonNeumannGenerator_mul (hK : IsSelfAdjoint K) (A B : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(star (vonNeumannGenerator K A) * B) =
      -LinearMap.trace ℂ E ↑(star A * vonNeumannGenerator K B) := by
  rw [trace_eq_tr, trace_eq_tr]
  rw [← vonNeumannGenerator_star hK]
  simp only [vonNeumannGenerator_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, map_smul,
    map_sub, mul_assoc]
  rw [tr_mul_comm K (star A * B), mul_assoc]
  ring

/-- `(1 - s L) x` and `(1 - s L) y` have the Hilbert–Schmidt product
`tr (x† y) + s² tr ((L x)† (L y))`. -/
lemma trace_star_vonNeumannStep_mul (hK : IsSelfAdjoint K) (s : ℝ) (x y : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(star (vonNeumannStep K s x) * vonNeumannStep K s y) =
      LinearMap.trace ℂ E ↑(star x * y) +
        (s : ℂ) ^ 2 * LinearMap.trace ℂ E
          ↑(star (vonNeumannGenerator K x) * vonNeumannGenerator K y) := by
  have hskew := trace_star_vonNeumannGenerator_mul hK x y
  rw [trace_eq_tr, trace_eq_tr] at hskew
  rw [trace_eq_tr, trace_eq_tr, trace_eq_tr]
  simp only [vonNeumannStep_apply, ← Complex.coe_smul, star_sub, star_smul, Complex.star_def,
    conj_ofReal, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, map_sub, map_smul,
    smul_eq_mul] at *
  linear_combination (-(s : ℂ)) * hskew

variable [FiniteDimensional ℂ E] (V : UnitaryOneParameterGroup E)

/-- The **Cayley transform** `C τ = (1 + τ L) (1 - τ L)⁻¹` of the von Neumann generator. -/
def vonNeumannCayley (τ : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E :=
  vonNeumannStep V.generator (-τ) ∘ₗ (vonNeumannResolvent V τ).toLinearMap

/-- `C τ ((1 - τ L) σ) = (1 + τ L) σ`. -/
lemma vonNeumannCayley_vonNeumannStep (τ : ℝ) (σ : E →L[ℂ] E) :
    vonNeumannCayley V τ (vonNeumannStep V.generator τ σ) = vonNeumannStep V.generator (-τ) σ := by
  rw [vonNeumannCayley, LinearMap.comp_apply, LinearEquiv.coe_coe,
    vonNeumannResolvent_vonNeumannStep]

/-- `C τ = 2 Ψ τ - 1`. -/
lemma vonNeumannCayley_apply (τ : ℝ) (ρ : E →L[ℂ] E) :
    vonNeumannCayley V τ ρ = (2 : ℂ) • vonNeumannResolvent V τ ρ - ρ := by
  have h := vonNeumannResolvent_sub_self V τ ρ
  rw [vonNeumannCayley, LinearMap.comp_apply, LinearEquiv.coe_coe, vonNeumannStep_apply, neg_smul,
    sub_neg_eq_add, ← h, two_smul]
  abel

/-- **The resolvent is the midpoint** of the identity and the Cayley transform:
`Ψ τ = (1 + C τ) / 2`. -/
theorem vonNeumannResolvent_eq_midpoint (τ : ℝ) :
    (vonNeumannResolvent V τ : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E) =
      (2⁻¹ : ℂ) • (LinearMap.id + vonNeumannCayley V τ) := by
  ext1 ρ
  rw [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, vonNeumannCayley_apply,
    LinearEquiv.coe_coe, add_sub_cancel, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

/-- **The Cayley transform is unitary** for the Hilbert–Schmidt inner product:
`tr ((C τ A)† (C τ B)) = tr (A† B)`. On self-adjoint operators it is orthogonal. -/
theorem trace_star_vonNeumannCayley_mul (τ : ℝ) (A B : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(star (vonNeumannCayley V τ A) * vonNeumannCayley V τ B) =
      LinearMap.trace ℂ E ↑(star A * B) := by
  have hK := V.generator_isSelfAdjoint
  have hA : vonNeumannStep V.generator τ (vonNeumannResolvent V τ A) = A :=
    vonNeumannResolvent_sub V τ A
  have hB : vonNeumannStep V.generator τ (vonNeumannResolvent V τ B) = B :=
    vonNeumannResolvent_sub V τ B
  conv_rhs => rw [← hA, ← hB]
  rw [vonNeumannCayley, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    trace_star_vonNeumannStep_mul hK, trace_star_vonNeumannStep_mul hK]
  push_cast
  ring

end QuantumMechanics
