/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ProjectiveMeasurement.InfiniteDimensional
public import ForPhyslib.QuantumMechanics.ContinuousSpectrum

/-!
# Projective measurements: observables with continuous spectra

The brief claims that "all four conditions fail when `X` has purely continuous spectrum, and they
fail on the continuous part when both discrete and continuous spectra are present": an operator
"supported on a non-atomic spectral sector and commuting with `X`" cannot be a nonzero trace-class
operator, and fixed points of the Lindblad equation "supported on that sector would not be density
operators".

Let `X` be bounded and self-adjoint, with spectral measure `μ_S`, and let `H_pp` be the closed span
of its eigenvectors (`pointSubspace X`).

*The continuous part, in general.*
* A density operator commuting with `X` lives on `H_pp`
  (`apply_mem_pointSubspace_of_mem_commutingDensityOperators`), and is not supported on a spectral
  sector `S` without atoms (`not_mem_commutingDensityOperators_of_spectralMeasureProj_mul_eq`).
* The equilibria of the Lindblad equation, `L(σ) = 0`, are the operators commuting with `X`
  (`dephasingGenerator_eq_zero_iff_commute`), so a density operator that is an equilibrium lives on
  `H_pp` (`apply_mem_pointSubspace_of_dephasingGenerator_eq_zero`).
* A density operator that is the trace-norm limit of a solution of the Lindblad equation is an
  equilibrium, hence lives on `H_pp` (`apply_mem_pointSubspace_of_tendsto_traceENorm`).

*Purely continuous spectrum*, `μ_S({a}) = 0` for every `a`:
* EQ-MEAS: `X` has no eigendecomposition `X = ∑ₓ x Pₓ` (`not_isEigenDecomposition`), so the
  pinching is not defined;
* EQ-HS and EQ-KL: there is no density operator commuting with `X`
  (`commutingDensityOperators_eq_empty`), so neither minimization has a solution
  (`not_isUniqueMinOn_commutingDensityOperators`);
* EQ-LIND: the Lindblad equation has no density-operator equilibrium
  (`not_exists_isDensityOperator_dephasingGenerator_eq_zero`), and no solution converges in trace
  norm to a density operator (`not_tendsto_traceENorm`).

The general statements are in `ForPhyslib/QuantumMechanics/ContinuousSpectrum`. This module is
separate from the main files of the brief, so that the comparator lane is unchanged.
-/

@[expose] public noncomputable section

namespace ProjectiveMeasurement.InfiniteDimensional

open Filter Set QuantumMechanics ProbabilisticTheory
open scoped Topology ENNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {X : E →L[ℂ] E}

/-! ## The continuous part of the spectrum -/

/-- A density operator commuting with `X` lives on the point-spectral subspace. -/
theorem apply_mem_pointSubspace_of_mem_commutingDensityOperators (hX : IsSelfAdjoint X)
    {σ : E →L[ℂ] E} (hσ : σ ∈ commutingDensityOperators X) (v : E) :
    σ v ∈ pointSubspace X :=
  apply_mem_pointSubspace_of_isTraceClass hX hσ.1.isTraceClass hσ.2 v

/-- **No ensemble on a non-atomic sector**: a density operator commuting with `X` is not supported
on a spectral sector `S` with `μ_S(S ∩ {a}) = 0` for every `a`. -/
theorem not_mem_commutingDensityOperators_of_spectralMeasureProj_mul_eq (hX : IsSelfAdjoint X)
    {S : Set ℝ} (hS : MeasurableSet S) (hatom : ∀ a, spectralMeasureProj hX (S ∩ {a}) = 0)
    {σ : E →L[ℂ] E} (hσS : spectralMeasureProj hX S * σ = σ) :
    σ ∉ commutingDensityOperators X := fun hσ =>
  hσ.1.ne_zero (eq_zero_of_spectralMeasureProj_mul_eq hX hS hatom
    hσ.1.isTraceClass.isCompactOperator hσ.2 hσS)

/-- A density operator that is an equilibrium of the Lindblad equation lives on the point-spectral
subspace. -/
theorem apply_mem_pointSubspace_of_dephasingGenerator_eq_zero (hX : IsSelfAdjoint X)
    {σ : E →L[ℂ] E} (hσ : IsDensityOperator σ) (h : dephasingGenerator X σ = 0) (v : E) :
    σ v ∈ pointSubspace X :=
  apply_mem_pointSubspace_of_mem_commutingDensityOperators hX
    ⟨hσ, (dephasingGenerator_eq_zero_iff_commute hX).mp h⟩ v

/-- A density operator that is the trace-norm limit of a solution of the Lindblad equation lives on
the point-spectral subspace. -/
theorem apply_mem_pointSubspace_of_tendsto_traceENorm (hX : IsSelfAdjoint X)
    {r : ℝ → E →L[ℂ] E} (hr : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    {σ : E →L[ℂ] E} (hσ : IsDensityOperator σ)
    (hlim : Tendsto (fun t => traceENorm (r t - σ)) atTop (𝓝 0)) (v : E) :
    σ v ∈ pointSubspace X :=
  apply_mem_pointSubspace_of_dephasingGenerator_eq_zero hX hσ
    (dephasingGenerator_eq_zero_of_tendsto_traceENorm hr hlim) v

/-! ## Purely continuous spectrum -/

section PurelyContinuous

variable (hX : IsSelfAdjoint X) (hatom : ∀ a, spectralMeasureProj hX {a} = 0)
include hatom

/-- With purely continuous spectrum, no density operator commutes with `X`. -/
theorem commutingDensityOperators_eq_empty : commutingDensityOperators X = ∅ :=
  eq_empty_of_forall_notMem fun _ hσ => hσ.1.ne_zero
    (eq_zero_of_commute_of_pointSubspace_eq_bot hX
      (pointSubspace_eq_bot_of_spectralMeasureProj_singleton hX hatom)
      hσ.1.isTraceClass.isCompactOperator hσ.2)

/-- **EQ-HS and EQ-KL fail**: with purely continuous spectrum, no operator minimizes anything over
the density operators commuting with `X`. -/
theorem not_isUniqueMinOn_commutingDensityOperators {β : Type*} [Preorder β]
    (f : (E →L[ℂ] E) → β) (σ : E →L[ℂ] E) :
    ¬ IsUniqueMinOn f (commutingDensityOperators X) σ := fun h => by
  simpa [commutingDensityOperators_eq_empty hX hatom] using h.1

/-- **EQ-LIND fails**: with purely continuous spectrum, the Lindblad equation has no
density-operator equilibrium. -/
theorem not_exists_isDensityOperator_dephasingGenerator_eq_zero :
    ¬ ∃ σ, IsDensityOperator σ ∧ dephasingGenerator X σ = 0 := fun ⟨σ, hσ, h⟩ => by
  have h' : σ ∈ commutingDensityOperators X :=
    ⟨hσ, (dephasingGenerator_eq_zero_iff_commute hX).mp h⟩
  simp [commutingDensityOperators_eq_empty hX hatom] at h'

/-- **EQ-LIND fails**: with purely continuous spectrum, no solution of the Lindblad equation
converges in trace norm to a density operator. -/
theorem not_tendsto_traceENorm {r : ℝ → E →L[ℂ] E}
    (hr : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t) {σ : E →L[ℂ] E}
    (hσ : IsDensityOperator σ) : ¬ Tendsto (fun t => traceENorm (r t - σ)) atTop (𝓝 0) :=
  fun hlim => not_exists_isDensityOperator_dephasingGenerator_eq_zero hX hatom
    ⟨σ, hσ, dephasingGenerator_eq_zero_of_tendsto_traceENorm hr hlim⟩

/-- **EQ-MEAS fails**: with purely continuous spectrum on a nonzero space, `X` has no
eigendecomposition `X = ∑ₓ x Pₓ`, so the pinching `∑ₓ Pₓ ρ Pₓ` is not defined. -/
theorem not_isEigenDecomposition [Nontrivial E] {ι : Type*} (P : ι → E →L[ℂ] E) (x : ι → ℝ) :
    ¬ IsEigenDecomposition X P x := fun hP => by
  have h := hasPurePointSpectrum_iff_pointSubspace_eq_top.mp hP.hasPurePointSpectrum
  rw [pointSubspace_eq_bot_of_spectralMeasureProj_singleton hX hatom] at h
  exact bot_ne_top h

end PurelyContinuous

end ProjectiveMeasurement.InfiniteDimensional
