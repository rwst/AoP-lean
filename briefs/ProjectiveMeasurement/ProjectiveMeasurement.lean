/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Projective measurements are equilibration processes.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a finite-dimensional complex Hilbert space `E`, density operators `IsDensity`
(`ForPhyslib/QuantumMechanics/Wigner/Density`), and a black-box process
`Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E` sending an observable `X` and an incoming ensemble `ρ`
to the outgoing ensemble `Φ X ρ`. The pinching `P_X(ρ) = ∑ₓ Pₓ ρ Pₓ` over the spectral projectors
of `X`, the dephasing Lindblad equation, and the relative entropy are in
`ForPhyslib/QuantumMechanics/{Pinching, Dephasing, RelativeEntropy}`. In finite dimension every
density operator has finite entropy, so condition [B]FINENT holds automatically.

Conditions (for every self-adjoint `X` and density operator `ρ`):
* `EqMeas`  EQ-MEAS: `Φ X ρ = P_X(ρ)`;
* `EqLind`  EQ-LIND: every solution of `ρ' = X ρ X - ½ {X², ρ}` for `t > 0`, continuous from the
  right at `0` with `ρ(0) = ρ`, tends to `Φ X ρ`;
* `EqHS`    EQ-HS: `Φ X ρ` is the unique minimizer of `‖ρ - σ‖_HS` over density operators `σ`
  commuting with `X`;
* `EqKL`    EQ-KL: `Φ X ρ` is the unique minimizer of `D(ρ‖σ)` over the same set.

Theorem 1:
* `eqMeas_iff_eqLind`  EQ-LIND ⇔ EQ-MEAS, eqs. (2)–(10): blockwise exponential decay; the
  solution exists (`hasDerivAt_dephasing`) and is unique (`eq_dephasing`);
* `eqMeas_iff_eqHS`    EQ-HS ⇔ EQ-MEAS, eq. (11): the Hilbert–Schmidt Pythagoras identity;
* `eqMeas_iff_eqKL`    EQ-KL ⇔ EQ-MEAS, eq. (12): the relative-entropy Pythagoras identity and
  Klein's inequality;
* `relEntropy_pinching_eq`  eq. (13): `D(ρ‖P_X(ρ)) = S(P_X(ρ)) - S(ρ)`;
* `projective_measurement_tfae`  all four conditions are equivalent.
-/

public import ForPhyslib.QuantumMechanics.Dephasing
public import ForPhyslib.QuantumMechanics.RelativeEntropy
public import UnitaryEntropy

@[expose] public noncomputable section

namespace ProjectiveMeasurement

open Filter Set QuantumMechanics QuantumMechanics.Wigner
open scoped Topology ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-! ## Unique minimizers -/

/-- `a` is the unique minimizer of `f` on `s`. -/
def IsUniqueMinOn {α β : Type*} [Preorder β] (f : α → β) (s : Set α) (a : α) : Prop :=
  a ∈ s ∧ ∀ b ∈ s, b ≠ a → f a < f b

theorem IsUniqueMinOn.unique {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {a b : α}
    (ha : IsUniqueMinOn f s a) (hb : IsUniqueMinOn f s b) : a = b := by
  by_contra h
  exact lt_asymm (ha.2 b hb.1 (Ne.symm h)) (hb.2 a ha.1 h)

/-- The density operators commuting with `X`. -/
def commutingDensities (X : E →L[ℂ] E) : Set (E →L[ℂ] E) := {σ | IsDensity σ ∧ Commute σ X}

/-! ## The four conditions -/

/-- EQ-MEAS: the process returns the nonselective projective measurement `∑ₓ Pₓ ρ Pₓ`. -/
def EqMeas (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ X : E →L[ℂ] E, IsSelfAdjoint X → ∀ ρ, IsDensity ρ → Φ X ρ = pinching X ρ

/-- EQ-LIND: the process returns the limit of the dephasing Lindblad equation with vanishing
Hamiltonian and jump operator `X`. -/
def EqLind (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ X : E →L[ℂ] E, IsSelfAdjoint X → ∀ ρ, IsDensity ρ → ∀ r : ℝ → E →L[ℂ] E, r 0 = ρ →
    (∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t) →
    ContinuousWithinAt r (Ici 0) 0 → Tendsto r atTop (𝓝 (Φ X ρ))

/-- EQ-HS: the process returns the closest ensemble commuting with `X` in Hilbert–Schmidt
distance. -/
def EqHS (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ X : E →L[ℂ] E, IsSelfAdjoint X → ∀ ρ, IsDensity ρ →
    IsUniqueMinOn (fun σ => (ρ - σ).hilbertSchmidtNorm) (commutingDensities X) (Φ X ρ)

/-- EQ-KL: the process returns the closest ensemble commuting with `X` in relative entropy. -/
def EqKL (Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ X : E →L[ℂ] E, IsSelfAdjoint X → ∀ ρ, IsDensity ρ →
    IsUniqueMinOn (fun σ => relEntropy ρ σ) (commutingDensities X) (Φ X ρ)

variable {Φ : (E →L[ℂ] E) → (E →L[ℂ] E) → E →L[ℂ] E}

/-! ## Theorem 1 -/

lemma pinching_mem_commutingDensities {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) {ρ : E →L[ℂ] E}
    (hρ : IsDensity ρ) : pinching X ρ ∈ commutingDensities X :=
  ⟨isDensity_pinching hX hρ, commute_pinching hX ρ⟩

/-- EQ-LIND ⇔ EQ-MEAS. -/
theorem eqMeas_iff_eqLind : EqMeas Φ ↔ EqLind Φ := by
  refine ⟨fun h X hX ρ hρ r hr hd hc => ?_, fun h X hX ρ hρ => ?_⟩
  · rw [h X hX ρ hρ, ← hr]
    exact tendsto_pinching_of_hasDerivAt hX hd hc
  · refine tendsto_nhds_unique (h X hX ρ hρ (fun t => dephasing X t ρ) (dephasing_zero hX ρ)
      (fun t _ => hasDerivAt_dephasing hX ρ t)
      (hasDerivAt_dephasing hX ρ 0).continuousAt.continuousWithinAt) (tendsto_dephasing ρ)

/-- EQ-HS ⇔ EQ-MEAS. -/
theorem eqMeas_iff_eqHS : EqMeas Φ ↔ EqHS Φ := by
  have hP : ∀ X : E →L[ℂ] E, IsSelfAdjoint X → ∀ ρ, IsDensity ρ →
      IsUniqueMinOn (fun σ => (ρ - σ).hilbertSchmidtNorm) (commutingDensities X)
        (pinching X ρ) := fun X hX ρ hρ =>
    ⟨pinching_mem_commutingDensities hX hρ, fun σ hσ hne =>
      hilbertSchmidtNorm_sub_pinching_lt hX ρ hσ.2 hne⟩
  refine ⟨fun h X hX ρ hρ => h X hX ρ hρ ▸ hP X hX ρ hρ, fun h X hX ρ hρ => ?_⟩
  exact (h X hX ρ hρ).unique (hP X hX ρ hρ)

/-- EQ-KL ⇔ EQ-MEAS. -/
theorem eqMeas_iff_eqKL : EqMeas Φ ↔ EqKL Φ := by
  have hP : ∀ X : E →L[ℂ] E, IsSelfAdjoint X → ∀ ρ, IsDensity ρ →
      IsUniqueMinOn (fun σ => relEntropy ρ σ) (commutingDensities X) (pinching X ρ) :=
    fun X hX ρ hρ => ⟨pinching_mem_commutingDensities hX hρ, fun σ hσ hne =>
      relEntropy_pinching_lt hX hρ hσ.1 hσ.2 hne⟩
  refine ⟨fun h X hX ρ hρ => h X hX ρ hρ ▸ hP X hX ρ hρ, fun h X hX ρ hρ => ?_⟩
  exact (h X hX ρ hρ).unique (hP X hX ρ hρ)

/-- The von Neumann entropy is `-tr(ρ log ρ)`. -/
lemma vonNeumann_eq_neg_re_trace {ρ : E →L[ℂ] E} (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) :
    UnitaryEntropy.vonNeumann ρ = -RCLike.re (LinearMap.trace ℂ E ↑(ρ * cfc Real.log ρ)) := by
  rw [UnitaryEntropy.vonNeumann_eq_sum hρ, re_trace_mul_log_self hρ, ← Finset.sum_neg_distrib]
  simp [Real.negMulLog]

/-- Eq. (13): `D(ρ‖P_X(ρ)) = S(P_X(ρ)) - S(ρ)`. -/
theorem relEntropy_pinching_eq {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) {ρ : E →L[ℂ] E}
    (hρ : IsDensity ρ) :
    relEntropy ρ (pinching X ρ) =
      ENNReal.ofReal (UnitaryEntropy.vonNeumann (pinching X ρ) - UnitaryEntropy.vonNeumann ρ) := by
  rw [relEntropy_pinching hX hρ, vonNeumann_eq_neg_re_trace hρ.isPositive.isSymmetric,
    vonNeumann_eq_neg_re_trace (isDensity_pinching hX hρ).isPositive.isSymmetric]
  ring_nf

/-- **Theorem 1.** EQ-MEAS, EQ-LIND, EQ-HS and EQ-KL are equivalent. -/
theorem projective_measurement_tfae : [EqMeas Φ, EqLind Φ, EqHS Φ, EqKL Φ].TFAE := by
  tfae_have 1 ↔ 2 := eqMeas_iff_eqLind
  tfae_have 1 ↔ 3 := eqMeas_iff_eqHS
  tfae_have 1 ↔ 4 := eqMeas_iff_eqKL
  tfae_finish

end ProjectiveMeasurement
