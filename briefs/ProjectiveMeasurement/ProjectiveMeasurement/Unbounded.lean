/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ProjectiveMeasurement.InfiniteDimensional
public import ForPhyslib.QuantumMechanics.UnboundedDephasing
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.CayleySpectralData.SpecTheorem

/-!
# Projective measurements: unbounded observables

The brief notes that "if `X` is unbounded, the differential equation is initially valid only on
the domain of its generator. The blockwise solution extends the resulting semigroup to every
density operator", and that `ρ(t)` stays a density operator.

An observable is now a self-adjoint, in general unbounded, operator `T : E →ₗ.[ℂ] E` (Mathlib's
`LinearPMap`). PhyslibAlpha's spectral theorem gives its spectral measure `μ_S`
(`cayleyRealSpectralMeasure`), with domain the vectors of finite second moment. `T` has pure point
spectrum when `μ_S` is atomic, `∑ₐ μ_S({a}) = 1` strongly (`IsAtomic`). Then `μ_S({a})` projects
onto eigenvectors of eigenvalue `a` (`apply_pointProj_apply`), so `T = ∑ₐ a μ_S({a})`. A density
operator commutes with `T` when it commutes with every spectral projection `μ_S(S)`, equivalently
with every `μ_S({a})` (`IsAtomic.commute_iff`).

*The semigroup.* On the spectral window `[-m, m]`, `T` is the bounded operator `X_m`
(`apply_spectralCutoffProj_apply`), and the dephasing equation `ρ' = X_m ρ X_m - ½ {X_m², ρ}` holds
for the operators living there (`IsWindowed`). The Gaussian average
`e^{tL} ρ = ∫ e^{isT} ρ e^{-isT} dN(0, t)(s)`, with PhyslibAlpha's unitary group `e^{isT}`, has the
blocks of eq. (5) and:
* solves the dephasing equation on every window (`IsAtomic.hasDerivAt_dephasingSemigroup`);
* is the unique extension of these solutions that is continuous in trace norm
  (`exists_unique_extension`);
* maps density operators to density operators, `e^{tL} ρ` stays a density operator
  (`isDensityOperator_dephasingSemigroup`), and is a semigroup.

*Theorem 1 for unbounded observables.* The conditions quantify over self-adjoint `T` with pure
point spectrum. EQ-LIND asks every extension of the dephasing equation from the windows to tend to
`Φ T ρ` in trace norm.
* `eqMeas_iff_eqLind`  EQ-LIND ⇔ EQ-MEAS;
* `eqMeas_iff_eqHS`    EQ-HS ⇔ EQ-MEAS;
* `eqKL_iff_eqMeasFinEnt`  under [B]FINENT, EQ-KL ⇔ EQ-MEAS;
* `projective_measurement_tfae`  EQ-MEAS, EQ-LIND and EQ-HS are equivalent.

The general statements are in `ForPhyslib/QuantumMechanics/UnboundedDephasing`. This module is
separate from the main files of the brief, so that the comparator lane is unchanged.
-/

@[expose] public noncomputable section

namespace ProjectiveMeasurement.Unbounded

open Filter Set QuantumMechanics ProbabilisticTheory.QuantumMechanics
open scoped Topology ENNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The spectral measure of a self-adjoint, in general unbounded, operator (PhyslibAlpha). -/
abbrev spectralMeasure (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) : WOTSpectralMeasure ℝ E :=
  cayleyRealSpectralMeasure T hT

/-- The density operators commuting with `T`: with every spectral projection `μ_S(S)`. -/
def commutingDensityOperators (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) : Set (E →L[ℂ] E) :=
  {σ | IsDensityOperator σ ∧ ∀ S, Commute σ (spectralMeasure T hT S).toCLM}

/-! ## The observable and its semigroup -/

section Observable

variable {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T)

/-- The eigenprojections project onto eigenvectors: `T (μ_S({a}) v) = a μ_S({a}) v`. -/
theorem apply_pointProj_apply (a : ℝ) (v : E) :
    T ⟨pointProj (spectralMeasure T hT) a v,
      pointProj_apply_mem_domain (unboundedSpectralTheorem T hT) a v⟩ =
      (a : ℂ) • pointProj (spectralMeasure T hT) a v :=
  QuantumMechanics.apply_pointProj_apply (unboundedSpectralTheorem T hT) a v

/-- On the spectral window `[-m, m]`, `T` is the bounded operator `X_m`. -/
theorem apply_spectralCutoffProj_apply (m : ℝ) (v : E) :
    T ⟨spectralCutoffProj (spectralMeasure T hT) m v,
      spectralCutoffProj_apply_mem_domain (unboundedSpectralTheorem T hT) m v⟩ =
      windowObservable (spectralMeasure T hT) m v :=
  QuantumMechanics.apply_spectralCutoffProj_apply (unboundedSpectralTheorem T hT) m v

variable {hT} (hpp : IsAtomic (spectralMeasure T hT))
include hpp

/-- **The blockwise solution extends the semigroup to every density operator**: the Gaussian
average extends the solutions of the dephasing equation from the spectral windows, continuously in
trace norm, and every such extension agrees with it on density operators. -/
theorem exists_unique_extension :
    IsDephasingExtension (spectralMeasure T hT) (dephasingSemigroup (spectralMeasure T hT)) ∧
      ∀ S, IsDephasingExtension (spectralMeasure T hT) S → ∀ t, 0 ≤ t → ∀ ρ,
        IsDensityOperator ρ → S t ρ = dephasingSemigroup (spectralMeasure T hT) t ρ :=
  ⟨hpp.isDephasingExtension, fun _ hS _ ht _ hρ => hpp.eq_of_isDephasingExtension hS ht hρ⟩

/-- **`ρ(t)` stays a density operator.** -/
theorem isDensityOperator_dephasingSemigroup (t : ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (dephasingSemigroup (spectralMeasure T hT) t ρ) :=
  hpp.isDensityOperator_dephasingSemigroup t hρ

lemma pinching_mem_commutingDensityOperators {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    hpp.isResolutionOfIdentity.pinching ρ ∈ commutingDensityOperators T hT :=
  ⟨hpp.isResolutionOfIdentity.isDensityOperator_pinching hρ, hpp.commute_iff.mpr
    (hpp.isResolutionOfIdentity.pinching_eq_self_iff.mp
      (hpp.isResolutionOfIdentity.pinching_pinching ρ))⟩

end Observable

/-! ## The conditions -/

/-- EQ-MEAS: the process returns `∑ₐ μ_S({a}) ρ μ_S({a})`. -/
def EqMeas (Φ : (E →ₗ.[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) (hpp : IsAtomic (spectralMeasure T hT)), ∀ ρ,
    IsDensityOperator ρ → Φ T ρ = hpp.isResolutionOfIdentity.pinching ρ

/-- EQ-LIND: every extension of the dephasing equation from the spectral windows, continuous in
trace norm, tends to `Φ T ρ` in trace norm. -/
def EqLind (Φ : (E →ₗ.[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T), IsAtomic (spectralMeasure T hT) → ∀ ρ,
    IsDensityOperator ρ → ∀ S, IsDephasingExtension (spectralMeasure T hT) S →
      Tendsto (fun t => traceENorm (S t ρ - Φ T ρ)) atTop (𝓝 0)

/-- EQ-HS: the process returns the closest ensemble commuting with `T` in Hilbert–Schmidt
distance. -/
def EqHS (Φ : (E →ₗ.[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T), IsAtomic (spectralMeasure T hT) → ∀ ρ,
    IsDensityOperator ρ →
      IsUniqueMinOn (fun σ => (ρ - σ).hilbertSchmidtNorm) (commutingDensityOperators T hT) (Φ T ρ)

/-- EQ-KL under [B]FINENT: for `S(ρ)` and `S(P_T(ρ))` finite, the process returns the closest
ensemble of finite entropy commuting with `T` in relative entropy. -/
def EqKL (Φ : (E →ₗ.[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) (hpp : IsAtomic (spectralMeasure T hT)), ∀ ρ,
    IsDensityOperator ρ → vonNeumannEntropy ρ ≠ ⊤ →
      vonNeumannEntropy (hpp.isResolutionOfIdentity.pinching ρ) ≠ ⊤ →
      IsUniqueMinOn (fun σ => relativeEntropy ρ σ)
        {σ | σ ∈ commutingDensityOperators T hT ∧ vonNeumannEntropy σ ≠ ⊤} (Φ T ρ)

/-- EQ-MEAS on the domain of [B]FINENT. -/
def EqMeasFinEnt (Φ : (E →ₗ.[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) (hpp : IsAtomic (spectralMeasure T hT)), ∀ ρ,
    IsDensityOperator ρ → vonNeumannEntropy ρ ≠ ⊤ →
      vonNeumannEntropy (hpp.isResolutionOfIdentity.pinching ρ) ≠ ⊤ →
      Φ T ρ = hpp.isResolutionOfIdentity.pinching ρ

variable {Φ : (E →ₗ.[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E}

/-! ## Theorem 1 for unbounded observables -/

/-- **Theorem 1**, EQ-LIND ⇔ EQ-MEAS, for unbounded observables. -/
theorem eqMeas_iff_eqLind : EqMeas Φ ↔ EqLind Φ := by
  refine ⟨fun h T hT hpp ρ hρ S hS => ?_, fun h T hT hpp ρ hρ => ?_⟩
  · rw [h T hT hpp ρ hρ]
    refine (hpp.tendsto_traceENorm_dephasingSemigroup hρ).congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [hpp.eq_of_isDephasingExtension hS ht hρ]
  · exact InfiniteDimensional.eq_of_tendsto_traceENorm
      (h T hT hpp ρ hρ _ hpp.isDephasingExtension) (hpp.tendsto_traceENorm_dephasingSemigroup hρ)

/-- **Theorem 1**, EQ-HS ⇔ EQ-MEAS, for unbounded observables. -/
theorem eqMeas_iff_eqHS : EqMeas Φ ↔ EqHS Φ := by
  have hP : ∀ (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) (hpp : IsAtomic (spectralMeasure T hT)),
      ∀ ρ, IsDensityOperator ρ →
      IsUniqueMinOn (fun σ => (ρ - σ).hilbertSchmidtNorm) (commutingDensityOperators T hT)
        (hpp.isResolutionOfIdentity.pinching ρ) := fun T hT hpp ρ hρ =>
    ⟨pinching_mem_commutingDensityOperators hpp hρ, fun σ hσ hne =>
      hpp.isResolutionOfIdentity.hilbertSchmidtNorm_sub_pinching_lt hρ hσ.1
        (hpp.commute_iff.mp hσ.2) hne⟩
  refine ⟨fun h T hT hpp ρ hρ => h T hT hpp ρ hρ ▸ hP T hT hpp ρ hρ,
    fun h T hT hpp ρ hρ => ?_⟩
  exact (h T hT hpp ρ hρ).unique (hP T hT hpp ρ hρ)

/-- **Theorem 1**, under [B]FINENT: EQ-KL ⇔ EQ-MEAS on ensembles of finite entropy, for unbounded
observables. -/
theorem eqKL_iff_eqMeasFinEnt : EqMeasFinEnt Φ ↔ EqKL Φ := by
  have hP : ∀ (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) (hpp : IsAtomic (spectralMeasure T hT)),
      ∀ ρ, IsDensityOperator ρ →
      vonNeumannEntropy (hpp.isResolutionOfIdentity.pinching ρ) ≠ ⊤ →
      IsUniqueMinOn (fun σ => relativeEntropy ρ σ)
        {σ | σ ∈ commutingDensityOperators T hT ∧ vonNeumannEntropy σ ≠ ⊤}
        (hpp.isResolutionOfIdentity.pinching ρ) := fun T hT hpp ρ hρ hS =>
    ⟨⟨pinching_mem_commutingDensityOperators hpp hρ, hS⟩, fun σ hσ hne =>
      hpp.isResolutionOfIdentity.relativeEntropy_pinching_lt hρ hσ.1.1
        (hpp.commute_iff.mp hσ.1.2) hS hne⟩
  refine ⟨fun h T hT hpp ρ hρ hSρ hS => h T hT hpp ρ hρ hSρ hS ▸ hP T hT hpp ρ hρ hS,
    fun h T hT hpp ρ hρ hSρ hS => ?_⟩
  exact (h T hT hpp ρ hρ hSρ hS).unique (hP T hT hpp ρ hρ hS)

/-- **Theorem 1** for unbounded observables: EQ-MEAS, EQ-LIND and EQ-HS are equivalent (and
EQ-KL is equivalent to EQ-MEAS on ensembles of finite entropy, `eqKL_iff_eqMeasFinEnt`). -/
theorem projective_measurement_tfae : [EqMeas Φ, EqLind Φ, EqHS Φ].TFAE := by
  tfae_have 1 ↔ 2 := eqMeas_iff_eqLind
  tfae_have 1 ↔ 3 := eqMeas_iff_eqHS
  tfae_finish

end ProjectiveMeasurement.Unbounded
