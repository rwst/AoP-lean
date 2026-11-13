/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Projective measurements are equilibration processes: Hilbert spaces of any dimension.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a complex Hilbert space `E` of any dimension, as in QSTO:H; no separability is used.
Density operators are the positive trace-class operators of trace one (`IsDensityOperator`), and
the entropy is the von Neumann entropy `vonNeumannEntropy ∈ [0, ∞]`. An observable is a bounded
operator with pure point spectrum, `X = ∑ₓ x Pₓ` (`IsEigenDecomposition X P x`): the
eigenprojections `Pₓ` form a resolution of the identity, the sum converging strongly, and the
eigenvalues are distinct. The index set is arbitrary. The black-box process `Φ X ρ` sends an
observable and an incoming ensemble to the outgoing ensemble. The pinching
`P_X(ρ) = ∑ₓ Pₓ ρ Pₓ` (`IsResolutionOfIdentity.pinching`, a strong sum) is in
`ForPhyslib/QuantumMechanics/DiscreteObservable`, the dephasing flow in
`ForPhyslib/QuantumMechanics/DephasingFlow`, and the relative entropy in
`ForPhyslib/QuantumMechanics/VonNeumannRelativeEntropy`.

Conditions (for every observable `X = ∑ₓ x Pₓ` and density operator `ρ`):
* `EqMeas`  EQ-MEAS: `Φ X ρ = P_X(ρ)`;
* `EqLind`  EQ-LIND: every solution of `ρ' = X ρ X - ½ {X², ρ}` for `t > 0`, continuous from the
  right at `0` with `ρ(0) = ρ`, tends to `Φ X ρ` in trace norm;
* `EqHS`    EQ-HS: `Φ X ρ` is the unique minimizer of `‖ρ - σ‖_HS` over density operators `σ`
  commuting with `X`;
* `EqKL`    EQ-KL under [B]FINENT: for `S(ρ), S(P_X(ρ)) < ∞`, `Φ X ρ` is the unique minimizer of
  `D(ρ‖σ)` over density operators `σ` of finite entropy commuting with `X`;
* `EqMeasFinEnt`  EQ-MEAS on the same domain.

Theorem 1:
* `eqMeas_iff_eqLind`  EQ-LIND ⇔ EQ-MEAS: every solution is the Gaussian average
  `∫ e^{isX} ρ e^{-isX} dN(0, t)(s)` of its initial value, eqs. (2)–(5); it tends to `P_X(ρ)` in
  trace norm, eqs. (6)–(10);
* `eqMeas_iff_eqHS`    EQ-HS ⇔ EQ-MEAS, eq. (11): the Hilbert–Schmidt Pythagoras identity;
* `eqKL_iff_eqMeasFinEnt`  under [B]FINENT, EQ-KL ⇔ EQ-MEAS, eq. (12): the relative-entropy
  Pythagoras identity and Klein's inequality;
* `relativeEntropy_pinching_eq`  eq. (13): `D(ρ‖P_X(ρ)) = S(P_X(ρ)) - S(ρ)`;
* `projective_measurement_tfae`  EQ-MEAS, EQ-LIND and EQ-HS are equivalent.

The remark "every ensemble commuting with `X` is infinitely distant from `ρ`" when
`S(P_X(ρ)) = ∞` is proved for `S(ρ) < ∞`, and refuted otherwise, in
`ProjectiveMeasurement.InfiniteDistance`. In finite dimension `relativeEntropy` agrees with the
finite-dimensional `relEntropy`, and EQ-KL is the same minimization in both parts, in
`ProjectiveMeasurement.RelativeEntropies`. A self-adjoint `X` has an eigendecomposition exactly
when it has pure point spectrum, with `Pₓ = μ_S({x})` its spectral projections, so the conditions
depend on `X` only, in `ProjectiveMeasurement.SpectralTheorem`. The conclusion's claims on
repeatability and on state update as classical conditioning are in
`ProjectiveMeasurement.Repeatability`. A second proof of EQ-LIND ⇔ EQ-MEAS by the route of the
brief, Hilbert–Schmidt convergence and the non-commutative Scheffé lemma, is in
`ProjectiveMeasurement.HilbertSchmidtRoute`.
-/

public import ForPhyslib.QuantumMechanics.DephasingFlow
public import ForPhyslib.QuantumMechanics.VonNeumannRelativeEntropy
public import ProjectiveMeasurement

@[expose] public noncomputable section

namespace ProjectiveMeasurement.InfiniteDimensional

open Filter Set QuantumMechanics
open scoped Topology ENNReal

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The density operators commuting with `X`. -/
def commutingDensityOperators (X : E →L[ℂ] E) : Set (E →L[ℂ] E) :=
  {σ | IsDensityOperator σ ∧ Commute σ X}

/-! ## The conditions -/

/-- EQ-MEAS: the process returns the nonselective projective measurement `∑ₓ Pₓ ρ Pₓ`. -/
def EqMeas (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ)
    (hX : IsEigenDecomposition X P x), ∀ ρ, IsDensityOperator ρ →
      Φ X ρ = hX.isResolutionOfIdentity.pinching ρ

/-- EQ-LIND: the process returns the trace-norm limit of the dephasing Lindblad equation with
vanishing Hamiltonian and jump operator `X`. Solutions are differentiable in operator norm. -/
def EqLind (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ),
    IsEigenDecomposition X P x → ∀ ρ, IsDensityOperator ρ → ∀ r : ℝ → E →L[ℂ] E, r 0 = ρ →
      (∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t) →
      ContinuousWithinAt r (Ici 0) 0 →
      Tendsto (fun t => traceENorm (r t - Φ X ρ)) atTop (𝓝 0)

/-- EQ-HS: the process returns the closest ensemble commuting with `X` in Hilbert–Schmidt
distance. -/
def EqHS (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ),
    IsEigenDecomposition X P x → ∀ ρ, IsDensityOperator ρ →
      IsUniqueMinOn (fun σ => (ρ - σ).hilbertSchmidtNorm) (commutingDensityOperators X) (Φ X ρ)

/-- EQ-KL, over QSTO:H constrained by [B]FINENT: for `ρ` with `S(ρ)` and `S(P_X(ρ))` finite, the
process returns the closest ensemble of finite entropy commuting with `X` in relative entropy. -/
def EqKL (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ)
    (hX : IsEigenDecomposition X P x), ∀ ρ, IsDensityOperator ρ →
      vonNeumannEntropy ρ ≠ ⊤ → vonNeumannEntropy (hX.isResolutionOfIdentity.pinching ρ) ≠ ⊤ →
      IsUniqueMinOn (fun σ => relativeEntropy ρ σ)
        {σ | σ ∈ commutingDensityOperators X ∧ vonNeumannEntropy σ ≠ ⊤} (Φ X ρ)

/-- EQ-MEAS on the domain of [B]FINENT: `S(ρ)` and `S(P_X(ρ))` finite. -/
def EqMeasFinEnt (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ)
    (hX : IsEigenDecomposition X P x), ∀ ρ, IsDensityOperator ρ →
      vonNeumannEntropy ρ ≠ ⊤ → vonNeumannEntropy (hX.isResolutionOfIdentity.pinching ρ) ≠ ⊤ →
      Φ X ρ = hX.isResolutionOfIdentity.pinching ρ

variable {Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E}

/-! ## Theorem 1 -/

lemma pinching_mem_commutingDensityOperators {X : E →L[ℂ] E} {ι : Type u} {P : ι → E →L[ℂ] E}
    {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    hX.isResolutionOfIdentity.pinching ρ ∈ commutingDensityOperators X :=
  ⟨hX.isResolutionOfIdentity.isDensityOperator_pinching hρ, hX.commute_iff.mpr
    (hX.isResolutionOfIdentity.pinching_eq_self_iff.mp
      (hX.isResolutionOfIdentity.pinching_pinching ρ))⟩

/-- Trace-norm limits are unique. -/
lemma eq_of_tendsto_traceENorm {α : Type*} {l : Filter α} [l.NeBot] {r : α → E →L[ℂ] E}
    {A B : E →L[ℂ] E} (hA : Tendsto (fun a => traceENorm (r a - A)) l (𝓝 0))
    (hB : Tendsto (fun a => traceENorm (r a - B)) l (𝓝 0)) : A = B := by
  have hsum : Tendsto (fun a => traceENorm (r a - A) + traceENorm (r a - B)) l (𝓝 0) := by
    simpa using hA.add hB
  have h0 : traceENorm (A - B) = 0 := by
    refine le_antisymm (ge_of_tendsto hsum (Eventually.of_forall fun a => ?_)) zero_le
    rw [traceENorm_sub_comm (r a) A]
    exact traceENorm_sub_le A (r a) B
  have h1 : ‖A - B‖ₑ = 0 := le_antisymm (h0 ▸ enorm_le_traceENorm (A - B)) zero_le
  exact sub_eq_zero.mp (enorm_eq_zero.mp h1)

/-- **Theorem 1**, EQ-LIND ⇔ EQ-MEAS. -/
theorem eqMeas_iff_eqLind : EqMeas Φ ↔ EqLind Φ := by
  refine ⟨fun h X ι P x hX ρ hρ r hr hd hc => ?_, fun h X ι P x hX ρ hρ => ?_⟩
  · subst hr
    rw [h X P x hX (r 0) hρ]
    exact hX.tendsto_traceENorm_of_hasDerivAt hd hc hρ
  · have hd : ∀ t, 0 < t → HasDerivAt (fun s => dephasingFlow X s ρ)
        (dephasingGenerator X (dephasingFlow X t ρ)) t := fun t _ => hasDerivAt_dephasingFlow X ρ t
    have hc : ContinuousWithinAt (fun s => dephasingFlow X s ρ) (Ici 0) 0 :=
      (hasDerivAt_dephasingFlow X ρ 0).continuousAt.continuousWithinAt
    have h1 := h X P x hX ρ hρ _ (dephasingFlow_zero X ρ) hd hc
    have hρ0 : IsDensityOperator (dephasingFlow X 0 ρ) := by rw [dephasingFlow_zero]; exact hρ
    have h2 := hX.tendsto_traceENorm_of_hasDerivAt hd hc hρ0
    rw [dephasingFlow_zero] at h2
    exact eq_of_tendsto_traceENorm h1 h2

/-- **Theorem 1**, EQ-HS ⇔ EQ-MEAS. -/
theorem eqMeas_iff_eqHS : EqMeas Φ ↔ EqHS Φ := by
  have hP : ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ)
      (hX : IsEigenDecomposition X P x), ∀ ρ, IsDensityOperator ρ →
      IsUniqueMinOn (fun σ => (ρ - σ).hilbertSchmidtNorm) (commutingDensityOperators X)
        (hX.isResolutionOfIdentity.pinching ρ) := fun X ι P x hX ρ hρ =>
    ⟨pinching_mem_commutingDensityOperators hX hρ, fun σ hσ hne =>
      hX.isResolutionOfIdentity.hilbertSchmidtNorm_sub_pinching_lt hρ hσ.1
        (hX.commute_iff.mp hσ.2) hne⟩
  refine ⟨fun h X ι P x hX ρ hρ => h X P x hX ρ hρ ▸ hP X P x hX ρ hρ,
    fun h X ι P x hX ρ hρ => ?_⟩
  exact (h X P x hX ρ hρ).unique (hP X P x hX ρ hρ)

/-- **Theorem 1**, under [B]FINENT: EQ-KL ⇔ EQ-MEAS on ensembles of finite entropy. -/
theorem eqKL_iff_eqMeasFinEnt : EqMeasFinEnt Φ ↔ EqKL Φ := by
  have hP : ∀ (X : E →L[ℂ] E) {ι : Type u} (P : ι → E →L[ℂ] E) (x : ι → ℝ)
      (hX : IsEigenDecomposition X P x), ∀ ρ, IsDensityOperator ρ →
      vonNeumannEntropy (hX.isResolutionOfIdentity.pinching ρ) ≠ ⊤ →
      IsUniqueMinOn (fun σ => relativeEntropy ρ σ)
        {σ | σ ∈ commutingDensityOperators X ∧ vonNeumannEntropy σ ≠ ⊤}
        (hX.isResolutionOfIdentity.pinching ρ) := fun X ι P x hX ρ hρ hS =>
    ⟨⟨pinching_mem_commutingDensityOperators hX hρ, hS⟩, fun σ hσ hne =>
      hX.isResolutionOfIdentity.relativeEntropy_pinching_lt hρ hσ.1.1
        (hX.commute_iff.mp hσ.1.2) hS hne⟩
  refine ⟨fun h X ι P x hX ρ hρ hSρ hS => h X P x hX ρ hρ hSρ hS ▸ hP X P x hX ρ hρ hS,
    fun h X ι P x hX ρ hρ hSρ hS => ?_⟩
  exact (h X P x hX ρ hρ hSρ hS).unique (hP X P x hX ρ hρ hS)

/-- **Eq. (13)**: `D(ρ‖P_X(ρ)) = S(P_X(ρ)) - S(ρ)`, finite exactly when `S(P_X(ρ))` is. -/
theorem relativeEntropy_pinching_eq {X : E →L[ℂ] E} {ι : Type u} {P : ι → E →L[ℂ] E}
    {x : ι → ℝ} (hX : IsEigenDecomposition X P x) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (hS : vonNeumannEntropy (hX.isResolutionOfIdentity.pinching ρ) ≠ ⊤) :
    relativeEntropy ρ (hX.isResolutionOfIdentity.pinching ρ) =
      vonNeumannEntropy (hX.isResolutionOfIdentity.pinching ρ) - vonNeumannEntropy ρ :=
  hX.isResolutionOfIdentity.relativeEntropy_pinching hρ hS

/-- **Theorem 1**: EQ-MEAS, EQ-LIND and EQ-HS are equivalent (and EQ-KL is equivalent to EQ-MEAS
on ensembles of finite entropy, `eqKL_iff_eqMeasFinEnt`). -/
theorem projective_measurement_tfae : [EqMeas Φ, EqLind Φ, EqHS Φ].TFAE := by
  tfae_have 1 ↔ 2 := eqMeas_iff_eqLind
  tfae_have 1 ↔ 3 := eqMeas_iff_eqHS
  tfae_finish

end ProjectiveMeasurement.InfiniteDimensional
