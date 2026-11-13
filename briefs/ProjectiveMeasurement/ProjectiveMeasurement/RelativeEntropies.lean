/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ProjectiveMeasurement.InfiniteDimensional
public import ForPhyslib.QuantumMechanics.RelativeEntropyAgreement

/-!
# Projective measurements: the two relative entropies in finite dimension

The finite-dimensional part of the formalization states EQ-KL with `relEntropy`
(`tr(ρ (log ρ - log σ))` under a support condition), over the density operators commuting with
`X` (`commutingDensities`). The part in any dimension states it with `relativeEntropy`
(Lindblad's formula), over the density operators of finite entropy commuting with `X`. In finite
dimension the two relative entropies agree on density operators
(`QuantumMechanics.relativeEntropy_eq_relEntropy`), every entropy is finite, and the two sets of
candidates are the same (`commutingDensities_eq`). So the finite-dimensional EQ-KL asks for the
same minimizer as the minimization of the part in any dimension (`eqKL_iff_relativeEntropy`).

This module is separate from the main files of the brief, so that the comparator lane is
unchanged. No certified statement depends on it.
-/

@[expose] public noncomputable section

namespace ProjectiveMeasurement

open QuantumMechanics QuantumMechanics.Wigner

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-- In finite dimension, the candidates of EQ-KL are the same in both parts: the density operators
commuting with `X` are those of finite entropy commuting with `X`. -/
theorem commutingDensities_eq (X : E →L[ℂ] E) :
    commutingDensities X =
      {σ | σ ∈ InfiniteDimensional.commutingDensityOperators X ∧ vonNeumannEntropy σ ≠ ⊤} := by
  ext σ
  simp only [commutingDensities, InfiniteDimensional.commutingDensityOperators,
    Set.mem_ofPred_eq]
  refine ⟨fun h => ?_, fun h => ⟨isDensityOperator_iff_isDensity.mp h.1.1, h.1.2⟩⟩
  have hσ := isDensityOperator_iff_isDensity.mpr h.1
  exact ⟨⟨hσ, h.2⟩, hσ.vonNeumannEntropy_ne_top⟩

theorem IsUniqueMinOn.congr {α β : Type*} [Preorder β] {f g : α → β} {s : Set α} {a : α}
    (h : ∀ b ∈ s, f b = g b) : IsUniqueMinOn f s a ↔ IsUniqueMinOn g s a := by
  refine ⟨fun ⟨ha, hf⟩ => ⟨ha, fun b hb hne => ?_⟩, fun ⟨ha, hg⟩ => ⟨ha, fun b hb hne => ?_⟩⟩
  · rw [← h a ha, ← h b hb]
    exact hf b hb hne
  · rw [h a ha, h b hb]
    exact hg b hb hne

variable {Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E}

/-- **The finite-dimensional EQ-KL is the minimization of the part in any dimension**: the same
relative entropy, Lindblad's formula, over the same set, the density operators of finite entropy
commuting with `X`. -/
theorem eqKL_iff_relativeEntropy :
    EqKL Φ ↔ ∀ X : E →L[ℂ] E, IsSelfAdjoint X → ∀ ρ, IsDensity ρ →
      IsUniqueMinOn (fun σ => relativeEntropy ρ σ)
        {σ | σ ∈ InfiniteDimensional.commutingDensityOperators X ∧ vonNeumannEntropy σ ≠ ⊤}
        (Φ X ρ) := by
  refine forall_congr' fun X => forall_congr' fun _ => forall_congr' fun ρ =>
    forall_congr' fun hρ => ?_
  rw [← commutingDensities_eq]
  exact IsUniqueMinOn.congr fun σ hσ => (hρ.relativeEntropy_eq_relEntropy hσ.1).symm

end ProjectiveMeasurement
