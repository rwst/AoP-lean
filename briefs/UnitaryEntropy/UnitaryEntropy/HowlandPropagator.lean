/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Howland's quasi-energy operator for an evolution satisfying DR-INFO + EVDIFF.

Setting: a finite-dimensional complex Hilbert space `E` and a two-parameter evolution `Ψ` as in
`UnitaryEntropy.TwoParameter`. Under DR-INFO + EVDIFF, `exists_propagator` gives one
differentiable family of unitaries `U(t)` with `Ψ t₀ t₁` induced by `U(t₁) U(t₀)†`. Then
`U(t, s) = U(t) U(s)†` is a strongly continuous unitary propagator in the sense of
`QuantumMechanics.UnitaryPropagator` (`QuantumMechanics.UnitaryPropagator.ofContinuous`), and
Howland's construction applies to it:
* `exists_unitaryPropagator`  a unitary propagator `P` with `Ψ t₀ t₁` induced by `P t₁ t₀`;
* `exists_isSelfAdjoint_howlandGenerator`  its Howland generator `K` on `L²(ℝ; E)` is
  self-adjoint, with `W σ = e^{-iσK/ħ}` for Howland's group `W`.
-/

public import UnitaryEntropy.TwoParameter
public import ForPhyslib.QuantumMechanics.HowlandGenerator

@[expose] public noncomputable section

namespace UnitaryEntropy.TwoParameter

open QuantumMechanics QuantumMechanics.Wigner
open SchroedingerEvolution.TwoParameter (IsEvolution)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] {Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E}

/-- **The two-parameter propagator.** Under DR-INFO and EVDIFF there is a strongly continuous
unitary propagator `P` with `Ψ t₀ t₁` induced by `P t₁ t₀` on pure states. -/
theorem exists_unitaryPropagator [Nontrivial E] (hΨ : IsEvolution Ψ) (hI : DrInfo Ψ)
    (hd : EvDiff Ψ) :
    ∃ P : UnitaryPropagator E, ∀ t₀ t₁, t₀ ≤ t₁ → ∀ χ : E, ‖χ‖ = 1 →
      Ψ t₀ t₁ (proj χ) = proj (P t₁ t₀ χ) := by
  obtain ⟨U, hu, -, hdiff, hΨU⟩ := exists_propagator hΨ hI hd
  exact ⟨UnitaryPropagator.ofContinuous hu
    (continuous_iff_continuousAt.mpr fun t => (hdiff t).continuousAt), hΨU⟩

/-- **Howland's quasi-energy operator.** Under DR-INFO and EVDIFF the propagator of
`exists_unitaryPropagator` has a self-adjoint Howland generator `K` on `L²(ℝ; E)`, with
`W σ = e^{-iσK/ħ}`. -/
theorem exists_isSelfAdjoint_howlandGenerator [Nontrivial E] (hΨ : IsEvolution Ψ)
    (hI : DrInfo Ψ) (hd : EvDiff Ψ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    ∃ P : UnitaryPropagator E, (∀ t₀ t₁, t₀ ≤ t₁ → ∀ χ : E, ‖χ‖ = 1 →
      Ψ t₀ t₁ (proj χ) = proj (P t₁ t₀ χ)) ∧
      ∃ hK : IsSelfAdjoint (P.howlandGenerator ħ),
        ∀ σ, P.howland σ = schrodingerPropagator hħ hK σ := by
  obtain ⟨P, hP⟩ := exists_unitaryPropagator hΨ hI hd
  exact ⟨P, hP, P.isSelfAdjoint_howlandGenerator hħ, P.howland_eq_schrodingerPropagator hħ⟩

end UnitaryEntropy.TwoParameter
