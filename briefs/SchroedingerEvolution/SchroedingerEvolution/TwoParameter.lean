/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Multiple equivalent characterizations of the Schrödinger equation: the conditions as the brief
writes them.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: as in `SchroedingerEvolution`, a finite-dimensional complex Hilbert space `E`. The brief
states [B]EVMIX for a two-parameter family `Ψ t₀ t₁ = Φ_{t₀→t₁}`, `t₀ ≤ t₁`, then restricts to the
time-independent case by EVTI, `Φ_{t₀→t₁} = Φ_{t₁-t₀}`, and writes DR-SCEQ with a time-dependent
Hamiltonian `H(t)`. Here these are stated as written, and Theorem 3 is derived from the
one-parameter version.

Conditions:
* `IsEvolution`  QST:H + [B]EVMIX: `Ψ t₀ t₁` maps density operators affinely to density
  operators, `Ψ t t = id`, `Ψ t₁ t₂ ∘ Ψ t₀ t₁ = Ψ t₀ t₂`, and `(ρ, t₀, t₁) ↦ Ψ t₀ t₁ ρ` is jointly
  continuous;
* `Evti`  EVTI: `Ψ t₀ t₁ = Φ (t₁ - t₀)` on density operators;
* `DrSceq`  DR-SCEQ with `H(t)`: `Ψ t₀ t₁` is conjugation by `U t₁ U t₀†`, where `U` solves
  `U' = (iħ)⁻¹ H(t) U` with self-adjoint `H(t)` and `U 0 = 1`.

Theorem 3:
* `IsEvolution.isEvolution`  [B]EVMIX + EVTI make `Φ` an evolution in the one-parameter sense
  of `SchroedingerEvolution.IsEvolution`;
* `drSceq_iff`  under EVTI, DR-SCEQ with `H(t)` ⇔ DR-SCEQ with a constant `H`; the solution is
  unitary for any self-adjoint `H(t)`, so DR-UNIT follows from Proposition 1;
* `schrodinger_tfae`  over QST:H + [B]EVMIX + EVTI, DR-SCEQ (with `H(t)`), DR-UNIT, DR-EV,
  DR-PROB and DR-INFO are equivalent.
-/

public import SchroedingerEvolution

@[expose] public noncomputable section

namespace SchroedingerEvolution.TwoParameter

open InnerProductSpace QuantumMechanics.Wigner Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Conditions -/

/-- **QST:H + [B]EVMIX**: an evolution `Ψ t₀ t₁` from each `t₀` to each `t₁ ≥ t₀` of the density
operators that preserves statistical mixtures, with `Ψ t t = id`, the composition law and joint
continuity in `(ρ, t₀, t₁)`. -/
structure IsEvolution (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  isDensity : ∀ t₀ t₁, t₀ ≤ t₁ → ∀ ρ, IsDensity ρ → IsDensity (Ψ t₀ t₁ ρ)
  affine : ∀ t₀ t₁, t₀ ≤ t₁ → AffineOnDensities (Ψ t₀ t₁)
  map_self : ∀ t ρ, IsDensity ρ → Ψ t t ρ = ρ
  map_comp : ∀ t₀ t₁ t₂, t₀ ≤ t₁ → t₁ ≤ t₂ → ∀ ρ, IsDensity ρ →
    Ψ t₁ t₂ (Ψ t₀ t₁ ρ) = Ψ t₀ t₂ ρ
  continuousOn : ContinuousOn (fun p : (E →L[ℂ] E) × ℝ × ℝ => Ψ p.2.1 p.2.2 p.1)
    {p | IsDensity p.1 ∧ p.2.1 ≤ p.2.2}

/-- **EVTI**: the evolution depends only on the elapsed time, `Ψ t₀ t₁ = Φ (t₁ - t₀)`. -/
def Evti (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t₀ t₁, t₀ ≤ t₁ → ∀ ρ, IsDensity ρ → Ψ t₀ t₁ ρ = Φ (t₁ - t₀) ρ

variable [CompleteSpace E] in
/-- **DR-SCEQ**, with a time-dependent Hamiltonian: `Ψ t₀ t₁` is conjugation by the propagator
`U t₁ U t₀†`, where `U` solves `d/dt U(t) = (iħ)⁻¹ H(t) U(t)` with self-adjoint `H(t)` and
`U(0) = 1`. -/
def DrSceq (ħ : ℝ) (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ (H : ℝ → E →L[ℂ] E) (U : ℝ → E →L[ℂ] E), (∀ t, IsSelfAdjoint (H t)) ∧ U 0 = 1 ∧
    (∀ t, HasDerivAt U ((I * ħ)⁻¹ • (H t * U t)) t) ∧
    ∀ t₀ t₁, t₀ ≤ t₁ → ∀ ρ, IsDensity ρ →
      Ψ t₀ t₁ ρ = U t₁ * star (U t₀) * ρ * star (U t₁ * star (U t₀))

variable {Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}

lemma Evti.apply (hΦ : Evti Ψ Φ) {t : ℝ} (ht : 0 ≤ t) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    Φ t ρ = Ψ 0 t ρ := by
  simpa using (hΦ 0 t ht ρ hρ).symm

/-! ## The one-parameter evolution -/

/-- [B]EVMIX and EVTI make `Φ` a one-parameter evolution (QST:H + [B]EVMIX + EVTI in the
one-parameter form of `SchroedingerEvolution`). -/
theorem IsEvolution.isEvolution (hΨ : IsEvolution Ψ) (hΦ : Evti Ψ Φ) :
    SchroedingerEvolution.IsEvolution Φ where
  isDensity t ht ρ hρ := hΦ.apply ht hρ ▸ hΨ.isDensity 0 t ht ρ hρ
  affine t ht ρ σ hρ hσ s hs0 hs1 := by
    rw [hΦ.apply ht (hρ.smul_add_smul hσ hs0 hs1), hΦ.apply ht hρ, hΦ.apply ht hσ]
    exact hΨ.affine 0 t ht ρ σ hρ hσ s hs0 hs1
  map_zero ρ hρ := by rw [hΦ.apply le_rfl hρ, hΨ.map_self 0 ρ hρ]
  map_add s hs t ht ρ hρ := by
    rw [hΦ.apply (add_nonneg hs ht) hρ, hΦ.apply ht hρ,
      ← hΨ.map_comp 0 t (s + t) ht (le_add_of_nonneg_left hs) ρ hρ,
      hΦ t (s + t) (le_add_of_nonneg_left hs) _ (hΨ.isDensity 0 t ht ρ hρ), add_sub_cancel_right]
  continuousWithinAt ρ hρ := by
    have hc : Continuous fun t : ℝ => (ρ, (0 : ℝ), t) := by fun_prop
    have hm : Set.MapsTo (fun t : ℝ => (ρ, (0 : ℝ), t)) (Set.Ici 0)
        {p : (E →L[ℂ] E) × ℝ × ℝ | IsDensity p.1 ∧ p.2.1 ≤ p.2.2} := fun t ht => ⟨hρ, ht⟩
    have h := (hΨ.continuousOn (ρ, 0, 0) ⟨hρ, le_rfl⟩).comp (x := (0 : ℝ))
      hc.continuousWithinAt hm
    exact h.congr (fun t ht => hΦ.apply ht hρ) (hΦ.apply le_rfl hρ)

/-! ## DR-SCEQ with a time-dependent Hamiltonian -/

variable [CompleteSpace E]

/-- A solution of the Schrödinger equation with self-adjoint `H(t)` and `U 0 = 1` is an isometry
at every time: `d/dt (U† U) = 0`. No continuity of `H` is needed. -/
lemma star_mul_self_of_hasDerivAt {ħ : ℝ} {H : ℝ → E →L[ℂ] E} {U : ℝ → E →L[ℂ] E}
    (hH : ∀ t, IsSelfAdjoint (H t)) (h₀ : U 0 = 1)
    (hU : ∀ t, HasDerivAt U ((I * ħ)⁻¹ • (H t * U t)) t) (t : ℝ) : star (U t) * U t = 1 := by
  have hc : star ((I * ħ)⁻¹ : ℂ) = -(I * ħ)⁻¹ := by
    simp
  have hW : ∀ s, HasDerivAt (fun s => star (U s) * U s) 0 s := fun s => by
    refine ((hU s).star.mul (hU s)).congr_deriv ?_
    rw [star_smul, star_mul, (hH s).star_eq, hc, neg_smul, neg_mul, smul_mul_assoc,
      mul_smul_comm, mul_assoc, neg_add_cancel]
  have h := is_const_of_deriv_eq_zero (fun s => (hW s).differentiableAt) (fun s => (hW s).deriv)
    t 0
  rwa [h₀, star_one, one_mul] at h

variable [FiniteDimensional ℂ E]

/-- **Theorem 3**, DR-SCEQ with `H(t)` ⇔ DR-SCEQ with a constant `H`, under [B]EVMIX and EVTI.
The solution `U` is unitary, so each `Φ t` is unitary conjugation, which gives DR-UNIT; a
unitary group conversely solves the equation with a constant `H`. -/
theorem drSceq_iff (hΨ : IsEvolution Ψ) (hΦ : Evti Ψ Φ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    DrSceq ħ Ψ ↔ SchroedingerEvolution.DrSceq ħ Φ := by
  rw [← drUnit_iff_drSceq hħ]
  constructor
  · rintro ⟨H, U, hH, hU₀, hU, hΨU⟩
    have : IsDedekindFiniteMonoid (E →L[ℂ] E) :=
      .of_injective ContinuousLinearMap.toLinearMapRingHom ContinuousLinearMap.coe_injective
    have hu : ∀ t, U t ∈ unitary (E →L[ℂ] E) := fun t =>
      have h := star_mul_self_of_hasDerivAt hH hU₀ hU t
      ⟨h, mul_eq_one_comm.mp h⟩
    refine drUnit_of_implemented (hΨ.isEvolution hΦ) fun t ht => Or.inl
      ⟨Unitary.linearIsometryEquiv ⟨U t, hu t⟩, fun ρ hρ => ?_⟩
    rw [hΦ.apply ht hρ, hΨU 0 t ht ρ hρ, hU₀, star_one, mul_one]
    exact mul_mul_star_eq_conjOp ⟨U t, hu t⟩ ρ
  · rintro ⟨V, hV⟩
    refine ⟨fun _ => (ħ : ℂ) • V.generator, V,
      fun _ => .smul (conj_ofReal ħ) V.generator_isSelfAdjoint, V.toAddChar.map_zero_eq_one,
      hasDerivAt_unitaryOneParameterGroup hħ V, fun t₀ t₁ h ρ hρ => ?_⟩
    have hV₁ : V t₁ * star (V t₀) = V (t₁ - t₀) := by
      conv_lhs => rw [← sub_add_cancel t₁ t₀]
      rw [V.toAddChar.map_add_eq_mul, mul_assoc, Unitary.mul_star_self_of_mem (V.mem_unitary t₀),
        mul_one]
    rw [hV₁, hΦ t₀ t₁ h ρ hρ, hV _ (sub_nonneg.mpr h) ρ hρ]

/-- **Theorem 3**, as the brief states it: over QST:H + [B]EVMIX + EVTI, DR-SCEQ (with a
time-dependent Hamiltonian), DR-UNIT, DR-EV, DR-PROB and DR-INFO are equivalent. -/
theorem schrodinger_tfae (hΨ : IsEvolution Ψ) (hΦ : Evti Ψ Φ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    [DrSceq ħ Ψ, DrUnit Φ, DrEv Φ, DrProb Φ, DrInfo Φ].TFAE := by
  rw [drSceq_iff hΨ hΦ hħ]
  exact SchroedingerEvolution.schrodinger_tfae (hΨ.isEvolution hΦ) hħ

end SchroedingerEvolution.TwoParameter
