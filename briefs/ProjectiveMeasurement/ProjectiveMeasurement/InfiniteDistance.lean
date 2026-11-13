/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ProjectiveMeasurement.InfiniteDimensional
public import ForPhyslib.QuantumMechanics.VonNeumannEntropyMixture

/-!
# Projective measurements: infinite distance when `S(P_X(ρ)) = ∞`

The remark "Relative entropy in infinite dimensions" of the brief says that when
`S(P_X(ρ)) = +∞`, "every ensemble commuting with `X` is infinitely distant from `ρ`". This module
proves the claim when `S(ρ) < ∞`, and refutes it as stated:

* `vonNeumannEntropy_pinching_le`: `S(P_X(ρ)) ≤ D(ρ‖σ) + S(ρ)` for every density operator `σ`
  commuting with `X`, with no finiteness assumption. Both sides equal
  `-tr(P_X(ρ) log σ) = D(P_X(ρ)‖σ) + S(P_X(ρ))` resp. `-tr(ρ log σ)`.
* `relativeEntropy_eq_top_of_vonNeumannEntropy_pinching_eq_top`: if `S(ρ) < ∞` and
  `S(P_X(ρ)) = ∞`, then `D(ρ‖σ) = ∞` for every density operator `σ` commuting with `X`.
* `not_forall_relativeEntropy_eq_top`: without `S(ρ) < ∞` the claim fails in every
  infinite-dimensional space. For `X = 0`, with the single eigenprojection `1`, the pinching is
  the identity; a density operator `ρ` of infinite entropy commutes with `X` and has
  `D(ρ‖ρ) = 0`.

This module is separate from the main files of the brief, so that the comparator lane is
unchanged. No certified statement depends on it.
-/

@[expose] public noncomputable section

namespace ProjectiveMeasurement.InfiniteDimensional

open QuantumMechanics
open scoped ENNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `S(P(ρ)) ≤ D(ρ‖σ) + S(ρ)` for every density operator `σ` commuting with every `Pᵢ`. -/
theorem _root_.QuantumMechanics.IsResolutionOfIdentity.vonNeumannEntropy_pinching_le
    {ι : Type*} {P : ι → E →L[ℂ] E} (hP : IsResolutionOfIdentity P) {ρ σ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) (hc : ∀ i, Commute σ (P i)) :
    vonNeumannEntropy (hP.pinching ρ) ≤ relativeEntropy ρ σ + vonNeumannEntropy ρ := by
  rw [relativeEntropy_add_vonNeumannEntropy hρ hσ, ← hP.crossEntropy_pinching hρ hc,
    ← relativeEntropy_add_vonNeumannEntropy (hP.isDensityOperator_pinching hρ) hσ]
  exact le_add_self

/-- **Infinite distance**: if `S(ρ) < ∞` and `S(P_X(ρ)) = ∞`, every density operator commuting
with `X` is infinitely distant from `ρ` in relative entropy. -/
theorem relativeEntropy_eq_top_of_vonNeumannEntropy_pinching_eq_top {X : E →L[ℂ] E}
    {ι : Type u} {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x)
    {ρ σ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (hSρ : vonNeumannEntropy ρ ≠ ⊤)
    (hS : vonNeumannEntropy (hX.isResolutionOfIdentity.pinching ρ) = ⊤)
    (hσ : σ ∈ commutingDensityOperators X) : relativeEntropy ρ σ = ⊤ := by
  have h := hX.isResolutionOfIdentity.vonNeumannEntropy_pinching_le hρ hσ.1
    (hX.commute_iff.mp hσ.2)
  rw [hS, top_le_iff, ENNReal.add_eq_top] at h
  exact h.resolve_right hSρ

/-- `X = 0` has the eigendecomposition with the single eigenprojection `1`. -/
lemma isEigenDecomposition_zero :
    IsEigenDecomposition (0 : E →L[ℂ] E) (fun _ : PUnit.{u + 1} => 1) (fun _ => 0) where
  isResolutionOfIdentity :=
    { isStarProjection := fun _ => IsStarProjection.one _
      mul_eq_zero := fun i j h => absurd (Subsingleton.elim i j) h
      hasSum := fun v => by simp }
  injective := Function.injective_of_subsingleton _
  mul_eq := fun _ => by simp

/-- **The brief's claim fails as stated**: in infinite dimension, some density operator `ρ` with
`S(P_X(ρ)) = ∞` has a density operator commuting with `X` at relative entropy `0`, namely
`σ = ρ`, for `X = 0`. -/
theorem not_forall_relativeEntropy_eq_top (hE : ¬ FiniteDimensional ℂ E) :
    ¬ ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ)
      (hX : IsEigenDecomposition X P x), ∀ ρ, IsDensityOperator ρ →
        vonNeumannEntropy (hX.isResolutionOfIdentity.pinching ρ) = ⊤ →
        ∀ σ ∈ commutingDensityOperators X, relativeEntropy ρ σ = ⊤ := by
  intro h
  obtain ⟨ρ, hρ, hS⟩ := exists_isDensityOperator_vonNeumannEntropy_eq_top hE
  have hX := isEigenDecomposition_zero (E := E)
  have hP : hX.isResolutionOfIdentity.pinching ρ = ρ :=
    hX.isResolutionOfIdentity.pinching_eq_self_iff.mpr fun _ => Commute.one_right ρ
  have h' := h 0 _ _ hX ρ hρ (by rw [hP]; exact hS) ρ ⟨hρ, Commute.zero_right ρ⟩
  rw [relativeEntropy_self hρ] at h'
  exact ENNReal.zero_ne_top h'

end ProjectiveMeasurement.InfiniteDimensional
