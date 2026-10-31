/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DensityOperator
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The von Neumann entropy in `[0, ∞]`

## i. Overview

The von Neumann entropy of a density operator `ρ` on a Hilbert space of any dimension is
`S(ρ) = -tr (ρ log ρ) = tr η(ρ)` with `η(x) = -x log x`. The spectrum of `ρ` lies in `[0, 1]`,
where `η ≥ 0`, so `η(ρ)` (continuous functional calculus) is a positive operator and its trace
`posTrace` exists in `[0, ∞]`. It is infinite for some density operators in infinite dimension.

Conjugation `X ↦ U X U†` by an isometry is a non-unital star algebra homomorphism, so it commutes
with the functional calculus of functions vanishing at `0`. Since it also preserves the trace,
the entropy is invariant. A density operator has zero entropy iff `η` vanishes on its spectrum,
i.e. the spectrum lies in `{0, 1}`, i.e. it is a projection, i.e. it is a pure state.

## ii. Key results

- `QuantumMechanics.vonNeumannEntropy`: `tr η(ρ)` in `[0, ∞]`.
- `QuantumMechanics.IsDensityOperator.cfc_negMulLog_nonneg`: `η(ρ)` is positive.
- `QuantumMechanics.conjHom`: `X ↦ U X U†` as a non-unital star algebra homomorphism.
- `QuantumMechanics.IsDensityOperator.vonNeumannEntropy_conj`: invariance under conjugation by an
  isometry.
- `QuantumMechanics.vonNeumannEntropy_proj`: a pure state has entropy zero.
- `QuantumMechanics.IsDensityOperator.vonNeumannEntropy_eq_zero_iff`: and only pure states.

## iii. Table of contents

- A. Definition
- B. Conjugation by an isometry
- C. Pure states

## iv. References

- J. von Neumann, *Mathematical Foundations of Quantum Mechanics*, Princeton University Press
  (1955), §V.3.
- A. Wehrl, *General properties of entropy*, Rev. Mod. Phys. **50** (1978), 221–260.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open InnerProductSpace Real QuantumMechanics.Wigner
open ContinuousLinearMap (posTrace posTrace_conj_of_star_mul_self posTrace_eq_zero_iff)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ρ : E →L[ℂ] E}

/-! ## A. Definition -/

/-- The von Neumann entropy `S(ρ) = -tr (ρ log ρ) = tr η(ρ)`, `η(x) = -x log x`, in `[0, ∞]`. -/
def vonNeumannEntropy (ρ : E →L[ℂ] E) : ℝ≥0∞ := posTrace (cfc negMulLog ρ)

/-- `η(ρ) ≥ 0`, since `η ≥ 0` on the spectrum `⊆ [0, 1]`. -/
lemma IsDensityOperator.cfc_negMulLog_nonneg (hρ : IsDensityOperator ρ) :
    0 ≤ cfc negMulLog ρ :=
  cfc_nonneg fun _ hx => negMulLog_nonneg (hρ.spectrum_subset_Icc hx).1
    (hρ.spectrum_subset_Icc hx).2

/-! ## B. Conjugation by an isometry -/

/-- Conjugation `X ↦ U X U†` by an isometry, as a non-unital star algebra homomorphism. -/
def conjHom {U : E →L[ℂ] E} (hU : star U * U = 1) : (E →L[ℂ] E) →⋆ₙₐ[ℂ] (E →L[ℂ] E) where
  toFun X := U * X * star U
  map_smul' c X := by simp
  map_zero' := by simp
  map_add' X Y := by noncomm_ring
  map_mul' X Y := by
    calc U * (X * Y) * star U = U * X * (star U * U) * Y * star U := by rw [hU]; noncomm_ring
      _ = _ := by noncomm_ring
  map_star' X := by simp [mul_assoc]

lemma conjHom_apply {U : E →L[ℂ] E} (hU : star U * U = 1) (X : E →L[ℂ] E) :
    conjHom hU X = U * X * star U := rfl

lemma continuous_conjHom {U : E →L[ℂ] E} (hU : star U * U = 1) : Continuous (conjHom hU) :=
  ((continuous_const_mul U).mul continuous_const : Continuous fun X => U * X * star U)

/-- Conjugation by an isometry commutes with `η`. -/
lemma cfc_negMulLog_conj (hρ : IsSelfAdjoint ρ) {U : E →L[ℂ] E} (hU : star U * U = 1) :
    cfc negMulLog (U * ρ * star U) = U * cfc negMulLog ρ * star U := by
  have hρ' : IsSelfAdjoint (U * ρ * star U) := hρ.conjugate U
  rw [← cfcₙ_eq_cfc (hf0 := negMulLog_zero), ← cfcₙ_eq_cfc (hf0 := negMulLog_zero),
    ← conjHom_apply hU, ← conjHom_apply hU]
  exact ((conjHom hU).map_cfcₙ negMulLog ρ (hφ := continuous_conjHom hU)).symm

/-- The entropy is invariant under conjugation by an isometry. -/
theorem IsDensityOperator.vonNeumannEntropy_conj (hρ : IsDensityOperator ρ) {U : E →L[ℂ] E}
    (hU : star U * U = 1) : vonNeumannEntropy (U * ρ * star U) = vonNeumannEntropy ρ := by
  rw [vonNeumannEntropy, cfc_negMulLog_conj hρ.isSelfAdjoint hU,
    posTrace_conj_of_star_mul_self hρ.cfc_negMulLog_nonneg hU, vonNeumannEntropy]

/-! ## C. Pure states -/

/-- A pure state has entropy zero. -/
theorem vonNeumannEntropy_proj {ψ : E} (hψ : ‖ψ‖ = 1) : vonNeumannEntropy (proj ψ) = 0 := by
  have hsa : IsSelfAdjoint (proj ψ) := (proj_nonneg ψ).isSelfAdjoint
  have h : cfc negMulLog (proj ψ) = cfc (fun _ : ℝ => (0 : ℝ)) (proj ψ) := by
    refine cfc_congr fun x hx => ?_
    rcases (isIdempotentElem_rankOne_self hψ).spectrum_subset ℝ hx with rfl | rfl <;> simp
  rw [vonNeumannEntropy, h, cfc_const_zero, ContinuousLinearMap.posTrace_zero]

lemma negMulLog_eq_zero_iff_of_nonneg {x : ℝ} (hx : 0 ≤ x) : negMulLog x = 0 ↔ x = 0 ∨ x = 1 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> simp⟩
  simp only [negMulLog, neg_eq_zero, mul_eq_zero] at h
  rcases h with h | h
  · exact Or.inl h
  rcases Real.log_eq_zero.mp h with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · linarith

/-- A density operator has entropy zero iff it is a pure state. -/
theorem IsDensityOperator.vonNeumannEntropy_eq_zero_iff (hρ : IsDensityOperator ρ) :
    vonNeumannEntropy ρ = 0 ↔ ∃ ψ : E, ‖ψ‖ = 1 ∧ ρ = proj ψ := by
  refine ⟨fun h => ?_, fun ⟨ψ, hψ, h⟩ => h ▸ vonNeumannEntropy_proj hψ⟩
  have := hρ.nontrivial
  have hsa := hρ.isSelfAdjoint
  have h0 : cfc negMulLog ρ = 0 := (posTrace_eq_zero_iff hρ.cfc_negMulLog_nonneg).mp h
  have h01 : ∀ x ∈ spectrum ℝ ρ, x = 0 ∨ x = 1 := fun x hx => by
    have hmem : negMulLog x ∈ spectrum ℝ (cfc negMulLog ρ) := by
      rw [cfc_map_spectrum negMulLog ρ]
      exact ⟨x, hx, rfl⟩
    rw [h0, spectrum.zero_eq, Set.mem_singleton_iff] at hmem
    exact (negMulLog_eq_zero_iff_of_nonneg (hρ.spectrum_subset_Icc hx).1).mp hmem
  refine hρ.eq_proj_of_isIdempotentElem ?_
  have hc : cfc (fun x : ℝ => x * x) ρ = cfc (fun x : ℝ => x) ρ :=
    cfc_congr fun x hx => by rcases h01 x hx with rfl | rfl <;> simp
  rwa [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) ρ, cfc_id' ℝ ρ] at hc

end QuantumMechanics
