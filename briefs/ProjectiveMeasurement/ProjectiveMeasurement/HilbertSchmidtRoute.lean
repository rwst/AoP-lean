/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ProjectiveMeasurement.InfiniteDimensional
public import ForPhyslib.QuantumMechanics.DephasingHilbertSchmidt

/-!
# Projective measurements: EQ-LIND by the route of the brief

`eqMeas_iff_eqLind` proves the convergence in EQ-LIND through the Gaussian average of the initial
state and its trace-norm contraction. This module follows the brief instead, eqs. (6)–(10). The
Hilbert–Schmidt distance `‖ρ(t) - P_X(ρ)‖²_HS = ∑_{x ≠ y} e^{-t(x - y)²} ‖Pₓ ρ P_y‖²_HS` tends to
zero by dominated convergence over the blocks
(`IsEigenDecomposition.tendsto_hilbertSchmidtNorm_of_hasDerivAt`). Both `ρ(t)` and `P_X(ρ)` are
density operators (`IsEigenDecomposition.isDensityOperator_of_hasDerivAt`), so the
non-commutative Scheffé lemma (`tendsto_traceENorm_of_tendsto_hilbertSchmidtNorm`) turns this into
trace-norm convergence (`IsEigenDecomposition.tendsto_traceENorm_of_hasDerivAt'`).

The general statements are in `ForPhyslib/QuantumMechanics/NoncommutativeScheffe` and
`ForPhyslib/QuantumMechanics/DephasingHilbertSchmidt`. This module is separate from the main files
of the brief, so that the comparator lane is unchanged.
-/

@[expose] public noncomputable section

namespace ProjectiveMeasurement.InfiniteDimensional

open Filter Set QuantumMechanics
open scoped Topology ENNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E}

/-- **Theorem 1**, EQ-LIND ⇔ EQ-MEAS, with the convergence proved as in the brief: Hilbert–Schmidt
convergence and the non-commutative Scheffé lemma. -/
theorem eqMeas_iff_eqLind' : EqMeas Φ ↔ EqLind Φ := by
  refine ⟨fun h X ι P x hX ρ hρ r hr hd hc => ?_, fun h X ι P x hX ρ hρ => ?_⟩
  · subst hr
    rw [h X P x hX (r 0) hρ]
    exact hX.tendsto_traceENorm_of_hasDerivAt' hd hc hρ
  · have hd : ∀ t, 0 < t → HasDerivAt (fun s => dephasingFlow X s ρ)
        (dephasingGenerator X (dephasingFlow X t ρ)) t := fun t _ => hasDerivAt_dephasingFlow X ρ t
    have hc : ContinuousWithinAt (fun s => dephasingFlow X s ρ) (Ici 0) 0 :=
      (hasDerivAt_dephasingFlow X ρ 0).continuousAt.continuousWithinAt
    have h1 := h X P x hX ρ hρ _ (dephasingFlow_zero X ρ) hd hc
    have hρ0 : IsDensityOperator (dephasingFlow X 0 ρ) := by rw [dephasingFlow_zero]; exact hρ
    have h2 := hX.tendsto_traceENorm_of_hasDerivAt' hd hc hρ0
    rw [dephasingFlow_zero] at h2
    exact eq_of_tendsto_traceENorm h1 h2

end ProjectiveMeasurement.InfiniteDimensional
