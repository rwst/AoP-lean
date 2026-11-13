/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ProjectiveMeasurement.InfiniteDimensional
public import ForPhyslib.QuantumMechanics.LuedersRule

/-!
# Projective measurements: repeatability and state update

The conclusion of the brief claims two things.

* "The repeatability of the measurement is intrinsic in requiring that all outputs are equilibria
  of the process." The equilibria of the dephasing equation, `L(σ) = 0`, are exactly the operators
  commuting with `X` (`dephasingGenerator_eq_zero_iff`). Under EQ-LIND a commuting density
  operator is its own output, since the constant solution stays at it (`EqLind.apply_eq_self`).
  The outputs commute with `X`, so the process applied to its own output returns it
  (`EqLind.apply_apply`). The outcome probabilities `pₓ = tr(Pₓ ρ Pₓ)` are unchanged by the
  process (`EqMeas.outcomeProb_apply`). The state `ρₓ = Pₓ ρ Pₓ / pₓ` after an outcome `x` is again
  an equilibrium (`commute_luders`), and a second measurement gives `x` with certainty
  (`IsResolutionOfIdentity.outcomeProb_luders`).
* "As the output of the process is a classical statistical mixture of possible measurement
  outcomes, the second part of the measurement (i.e. the update of the state based on the
  measurement outcome) is equivalent to what happens in the classical case." The output is the
  mixture `∑ₓ pₓ ρₓ` of states `ρₓ` that give the outcome `x` with certainty
  (`EqMeas.hasSum_apply_luders`). Updating such a mixture on the outcome `x` selects the
  component `ρₓ`, as classical conditioning does
  (`IsResolutionOfIdentity.luders_of_hasSum`), and this is the Lüders rule applied to the
  incoming `ρ` (`EqMeas.luders_apply`).

The general statements are in `ForPhyslib/QuantumMechanics/LuedersRule`. This module is separate
from the main files of the brief, so that the comparator lane is unchanged.
-/

@[expose] public noncomputable section

namespace ProjectiveMeasurement.InfiniteDimensional

open Filter Set QuantumMechanics
open scoped Topology ENNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Equilibria of the dephasing equation**: `L(σ) = 0` iff `σ` commutes with `X`. -/
theorem dephasingGenerator_eq_zero_iff {X : E →L[ℂ] E} {ι : Type*} {P : ι → E →L[ℂ] E}
    {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {σ : E →L[ℂ] E} :
    dephasingGenerator X σ = 0 ↔ Commute σ X := by
  have hP := hX.isResolutionOfIdentity
  rw [hX.commute_iff, ← hP.pinching_eq_self_iff]
  constructor
  · intro h
    refine hP.ext_block fun i j => ?_
    have h' := hX.mul_dephasingGenerator_mul i j σ
    rw [h, mul_zero, zero_mul] at h'
    rw [hP.mul_pinching_mul]
    split_ifs with hij
    · rw [hij]
    · have hc : -((x i - x j) ^ 2 / 2) ≠ 0 := by
        have : x i - x j ≠ 0 := sub_ne_zero.mpr (hX.injective.ne hij)
        exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 this) two_ne_zero)
      exact ((smul_eq_zero.mp h'.symm).resolve_left hc).symm
  · intro h
    refine hP.ext_block fun i j => ?_
    rw [hX.mul_dephasingGenerator_mul, mul_zero, zero_mul, ← h, hP.mul_pinching_mul]
    split_ifs with hij
    · subst hij
      simp
    · simp

variable {Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E}

/-- Under EQ-LIND, a density operator commuting with `X` is an equilibrium, hence its own
output. -/
theorem EqLind.apply_eq_self (hΦ : EqLind Φ) {X : E →L[ℂ] E} {ι : Type u}
    {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {σ : E →L[ℂ] E}
    (hσ : IsDensityOperator σ) (hc : Commute σ X) : Φ X σ = σ := by
  have h := hΦ X P x hX σ hσ (fun _ => σ) rfl
    (fun t _ => by
      rw [(dephasingGenerator_eq_zero_iff hX).mpr hc]
      exact hasDerivAt_const t σ)
    continuousWithinAt_const
  have h2 : Tendsto (fun _ : ℝ => traceENorm (σ - σ)) atTop (𝓝 0) := by simp
  exact eq_of_tendsto_traceENorm h h2

/-- **Repeatability**: under EQ-LIND the outputs are equilibria, so the process applied to its own
output returns it. -/
theorem EqLind.apply_apply (hΦ : EqLind Φ) {X : E →L[ℂ] E} {ι : Type u}
    {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) : Φ X (Φ X ρ) = Φ X ρ := by
  have hm := (eqMeas_iff_eqLind.mpr hΦ) X P x hX ρ hρ
  obtain ⟨hd, hc⟩ := hm ▸ pinching_mem_commutingDensityOperators hX hρ
  exact hΦ.apply_eq_self hX hd hc

/-- The process does not change the outcome probabilities. -/
theorem EqMeas.outcomeProb_apply (hΦ : EqMeas Φ) {X : E →L[ℂ] E} {ι : Type u}
    {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) (i : ι) : outcomeProb P (Φ X ρ) i = outcomeProb P ρ i := by
  rw [hΦ X P x hX ρ hρ, hX.isResolutionOfIdentity.outcomeProb_pinching]

/-- The state after an outcome commutes with `X`: it is an equilibrium. -/
theorem commute_luders {X : E →L[ℂ] E} {ι : Type*} {P : ι → E →L[ℂ] E} {x : ι → ℝ}
    (hX : IsEigenDecomposition X P x) (ρ : E →L[ℂ] E) (i : ι) : Commute (luders P ρ i) X :=
  hX.commute_iff.mpr (hX.isResolutionOfIdentity.commute_luders ρ i)

/-- **Classical mixture**: the output is `∑ₓ pₓ ρₓ`, with `ρₓ` the state after the outcome `x`. -/
theorem EqMeas.hasSum_apply_luders (hΦ : EqMeas Φ) {X : E →L[ℂ] E} {ι : Type u}
    {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) (v : E) :
    HasSum (fun i => (((outcomeProb P ρ i).toReal : ℝ) : ℂ) • luders P ρ i v) (Φ X ρ v) := by
  rw [hΦ X P x hX ρ hρ]
  exact hX.isResolutionOfIdentity.hasSum_pinching_apply_luders hρ v

/-- **State update**: updating the output on an outcome gives the Lüders state of the input. -/
theorem EqMeas.luders_apply (hΦ : EqMeas Φ) {X : E →L[ℂ] E} {ι : Type u}
    {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) (i : ι) : luders P (Φ X ρ) i = luders P ρ i := by
  rw [hΦ X P x hX ρ hρ, hX.isResolutionOfIdentity.luders_pinching]

/-- **State update is classical conditioning**: the output is the mixture `∑ₓ pₓ ρₓ` of
operators `ρₓ` in the block of `x`, and updating it on an outcome `x` with `pₓ ≠ 0` selects the
component `ρₓ`, a density operator. -/
theorem EqMeas.luders_apply_eq_component (hΦ : EqMeas Φ) {X : E →L[ℂ] E} {ι : Type u}
    {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) {i : ι} (hi : outcomeProb P ρ i ≠ 0) :
    IsDensityOperator (luders P ρ i) ∧ luders P (Φ X ρ) i = luders P ρ i := by
  have hP := hX.isResolutionOfIdentity
  have hd := hP.isDensityOperator_luders hρ hi
  refine ⟨hd, hP.luders_of_hasSum (hP.mul_luders_mul ρ) (hΦ.hasSum_apply_luders hX hρ)
    ENNReal.toReal_nonneg hd ?_⟩
  exact (ENNReal.toReal_pos hi (hP.outcomeProb_ne_top hρ i)).ne'

end ProjectiveMeasurement.InfiniteDimensional
