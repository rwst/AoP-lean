/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Wigner.Theorem
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Wigner's theorem for rank-one projections

## i. Overview

Pure states of a finite-dimensional quantum system are the rank-one projections `|ψ⟩⟨ψ|`, written
`rankOne ℂ ψ ψ` for a unit vector `ψ`, and the transition probability between two of them is
`tr (P Q) = |⟪ψ, ϕ⟫|²`. A map `Φ` on operators that sends pure states to pure states and preserves
transition probabilities is induced by a unitary or an anti-unitary `U`:
`Φ (|ψ⟩⟨ψ|) = |U ψ⟩⟨U ψ|`. This is Wigner's theorem stated on states instead of vectors; it
follows from the vector form by choosing one representative of each image ray.

## ii. Key results

- `QuantumMechanics.Wigner.phaseEq_of_rankOne_self_eq`: unit vectors with the same rank-one
  projection agree up to phase.
- `QuantumMechanics.Wigner.trace_rankOne_mul_rankOne`: `tr (|x⟩⟨x| |y⟩⟨y|) = |⟪x, y⟫|²`.
- `QuantumMechanics.Wigner.wigner_rankOne`: Wigner's theorem for rank-one projections.

## iii. Table of contents

- A. Rank-one projections
- B. Wigner's theorem for rank-one projections

## iv. References

- V. Bargmann, *Note on Wigner's theorem on symmetry operations*, J. Math. Phys. 5 (1964),
  862–868.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open InnerProductSpace

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. Rank-one projections
-/

/-- Vectors that agree up to phase have the same rank-one projection. -/
lemma PhaseEq.rankOne_self {x y : E} (h : PhaseEq x y) : rankOne ℂ x x = rankOne ℂ y y := by
  obtain ⟨c, hc, rfl⟩ := h
  ext z
  simp [smul_smul, Complex.mul_conj', hc]

/-- Unit vectors with the same rank-one projection agree up to phase. -/
lemma phaseEq_of_rankOne_self_eq {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : rankOne ℂ x x = rankOne ℂ y y) : PhaseEq x y := by
  have e : x = ⟪y, x⟫_ℂ • y := by
    have := congrArg (fun T => T x) h
    simpa [hx] using this
  refine ⟨⟪y, x⟫_ℂ, ?_, e⟩
  have := congrArg norm e
  rwa [norm_smul, hx, hy, mul_one, eq_comm] at this

/-- The transition probability between two rank-one projections:
`tr (|x⟩⟨x| |y⟩⟨y|) = |⟪x, y⟫|²`. -/
lemma trace_rankOne_mul_rankOne [FiniteDimensional ℂ E] (x y : E) :
    LinearMap.trace ℂ E ((rankOne ℂ x x * rankOne ℂ y y : E →L[ℂ] E) : E →ₗ[ℂ] E) =
      ((‖⟪x, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [ContinuousLinearMap.mul_def, rankOne_comp_rankOne, ContinuousLinearMap.toLinearMap_smul,
    map_smul, trace_rankOne, ← inner_conj_symm y x, smul_eq_mul, Complex.mul_conj']
  push_cast
  ring

/-!
## B. Wigner's theorem for rank-one projections
-/

/-- **Wigner's theorem** for rank-one projections: a map on operators that sends rank-one
projections to rank-one projections and preserves `tr (P Q)` between them is induced by a unitary
or an anti-unitary. -/
theorem wigner_rankOne [FiniteDimensional ℂ E] (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hP : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ Φ (rankOne ℂ ψ ψ) = rankOne ℂ ψ' ψ')
    (htr : ∀ ψ ϕ : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      LinearMap.trace ℂ E ((Φ (rankOne ℂ ψ ψ) * Φ (rankOne ℂ ϕ ϕ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((rankOne ℂ ψ ψ * rankOne ℂ ϕ ϕ : E →L[ℂ] E) : E →ₗ[ℂ] E)) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (U ψ) (U ψ)) ∨
      (∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (U ψ) (U ψ)) := by
  classical
  let f : E → E := fun ψ => if h : ‖ψ‖ = 1 then (hP ψ h).choose else ψ
  have hfΦ : ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (f ψ) (f ψ) := fun ψ hψ => by
    simp only [f, hψ, ↓reduceDIte]
    exact (hP ψ hψ).choose_spec.2
  have hf : IsWignerMap f := fun v w hv hw => by
    have h := htr v w hv hw
    rw [hfΦ v hv, hfΦ w hw, trace_rankOne_mul_rankOne, trace_rankOne_mul_rankOne,
      Complex.ofReal_inj] at h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h
  rcases hf.exists_unitary_or_antiunitary with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun ψ hψ => by rw [hfΦ ψ hψ, (hU ψ hψ).rankOne_self]⟩
  · exact Or.inr ⟨U, fun ψ hψ => by rw [hfΦ ψ hψ, (hU ψ hψ).rankOne_self]⟩

end QuantumMechanics.Wigner
