/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Multiple equivalent characterizations of the Schrödinger equation.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a finite-dimensional complex Hilbert space `E`. Density operators are positive operators
of trace one (`IsDensity`), pure states are the projectors `proj ψ = |ψ⟩⟨ψ|` for unit `ψ`, the
conditional probability is the Born rule `born` and the entropy is the von Neumann entropy
`vonNeumann` (both from the brief "Schrödinger equation is equivalent to information
conservation"). An evolution is a family `Φ t` of maps on operators, used on density operators
and for `t ≥ 0` only.

Proposition 1 (Affine pure-state correspondence):
* `affine_pure_state_correspondence`  for an affine map `T` of the density operators, bijective
  on pure states ⇔ bijective on density operators ⇔ conjugation by a unitary or an anti-unitary.
  No continuity is needed in finite dimension.

Conditions:
* `IsEvolution`  QST:H + [B]EVMIX + EVTI: `Φ t` maps density operators affinely to density
  operators, `Φ 0 = id`, `Φ (s + t) = Φ s ∘ Φ t`, and `t ↦ Φ t ρ` is continuous at `0⁺`;
* `DrSceq`  the propagator solves `U' = (iħ)⁻¹ H U` with self-adjoint `H` and `U 0 = 1`;
* `DrUnit`  `Φ t ρ = U t ρ U t†` for a norm-continuous unitary one-parameter group `U`;
* `DrEv`  `Φ t` is a bijection of the pure states;
* `DrProb`  `Φ t` maps pure states to pure states and preserves the Born rule;
* `DrInfo`  `Φ t` preserves the von Neumann entropy.

Theorem 3:
* `schrodinger_tfae`  over `IsEvolution`, the five conditions are equivalent;
* `drUnit_iff_drSceq`  DR-UNIT ⇔ DR-SCEQ (bounded Stone theorem, from physlib);
* `DrUnit.drEv`, `DrUnit.drProb`, `DrUnit.drInfo`  DR-UNIT ⇒ DR-EV, DR-PROB, DR-INFO;
* `DrEv.drUnit`  DR-EV ⇒ DR-UNIT: Proposition 1 for each `t`, then the lift of
  `ForPhyslib/QuantumMechanics/Wigner/OneParameter` (`drUnit_of_implemented`), which excludes
  anti-unitaries by `Φ t = Φ (t / 2) ∘ Φ (t / 2)` and fills the brief's "the phases can be chosen";
* `DrProb.drUnit`  DR-PROB ⇒ DR-UNIT directly by Wigner's theorem (`implemented_of_mapsPure`),
  without the brief's detour through DR-EV;
* `DrInfo.drProb`  DR-INFO ⇒ DR-PROB (brief "Schrödinger equation is equivalent to information
  conservation").
-/

public import ForPhyslib.QuantumMechanics.Wigner.OneParameter
public import UnitaryEntropy

@[expose] public noncomputable section

namespace SchroedingerEvolution

open InnerProductSpace QuantumMechanics.Wigner UnitaryEntropy Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Proposition 1 -/

/-- **Proposition 1**: for an affine map of the density operators, being bijective on the pure
states, being bijective on all density operators and being conjugation by a unitary or an
anti-unitary are equivalent. -/
theorem affine_pure_state_correspondence [FiniteDimensional ℂ E]
    {T : (E →L[ℂ] E) → E →L[ℂ] E} (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hT : AffineOnDensities T) :
    [BijOnPure T, Set.BijOn T {ρ | IsDensity ρ} {ρ | IsDensity ρ},
      ImplementedByUnitaryOrAntiunitary T].TFAE :=
  kadison_tfae hD hT

/-! ## Conditions -/

/-- **QST:H + [B]EVMIX + EVTI**: a time-independent evolution of the density operators that
preserves statistical mixtures. The brief's joint continuity is weakened to continuity of
`t ↦ Φ t ρ` at `0⁺`. -/
structure IsEvolution (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  isDensity : ∀ t ≥ 0, ∀ ρ, IsDensity ρ → IsDensity (Φ t ρ)
  affine : ∀ t ≥ 0, AffineOnDensities (Φ t)
  map_zero : ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ
  map_add : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ (s + t) ρ = Φ s (Φ t ρ)
  continuousWithinAt : ∀ ρ, IsDensity ρ → ContinuousWithinAt (fun t => Φ t ρ) (Set.Ici 0) 0

/-- `T` maps pure states to pure states. -/
def MapsPure (T : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ'

/-- `T` preserves the Born rule on pure states. -/
def PreservesBorn (T : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ ψ ϕ ψ' ϕ' : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 → ‖ψ'‖ = 1 → ‖ϕ'‖ = 1 →
    T (proj ψ) = proj ψ' → T (proj ϕ) = proj ϕ' → born ψ' ϕ' = born ψ ϕ

/-- **DR-EV**: every `Φ t` is a bijection of the pure states. -/
def DrEv (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t ≥ 0, BijOnPure (Φ t)

/-- **DR-PROB**: every `Φ t` maps pure states to pure states and preserves conditional
probability. -/
def DrProb (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t ≥ 0, MapsPure (Φ t) ∧ PreservesBorn (Φ t)

section Unit

variable [CompleteSpace E]

/-- **DR-SCEQ**: the evolution is conjugation by a propagator that solves the Schrödinger
equation `d/dt U(t) = (iħ)⁻¹ H U(t)` with a self-adjoint `H` and `U(0) = 1`. -/
def DrSceq (ħ : ℝ) (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ (H : E →L[ℂ] E) (U : ℝ → E →L[ℂ] E), IsSelfAdjoint H ∧ U 0 = 1 ∧
    (∀ t, HasDerivAt U ((I * ħ)⁻¹ • (H * U t)) t) ∧
    ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ t ρ = U t * ρ * star (U t)

/-- **DR-UNIT**: the evolution is conjugation by a norm-continuous unitary one-parameter group,
`Φ t ρ = U t ρ U t†` with `U 0 = 1` and `U (t + s) = U t U s`. -/
def DrUnit (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ U : UnitaryOneParameterGroup E, ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ t ρ = U t * ρ * star (U t)

/-! ## DR-UNIT ⇔ DR-SCEQ -/

/-- A propagator solving the Schrödinger equation with constant `H` and `U 0 = 1` is the
exponential `exp (t (iħ)⁻¹ H)`. -/
theorem eq_exp_of_schrodinger {ħ : ℝ} {H : E →L[ℂ] E} {U : ℝ → E →L[ℂ] E} (h₀ : U 0 = 1)
    (hU : ∀ t, HasDerivAt U ((I * ħ)⁻¹ • (H * U t)) t) (t : ℝ) :
    U t = NormedSpace.exp (t • (I * ħ)⁻¹ • H) := by
  set X := (I * ħ)⁻¹ • H
  have hc : ∀ s : ℝ, Commute X (NormedSpace.exp (s • -X)) := fun s =>
    ((Commute.refl X).neg_right.smul_right s).exp_right
  have hW : ∀ s, HasDerivAt (fun s : ℝ => NormedSpace.exp (s • -X) * U s) 0 s := fun s => by
    have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := E →L[ℂ] E) (-X) s).fun_mul (hU s)
    refine h.congr_deriv ?_
    rw [← smul_mul_assoc, ← mul_assoc, show (I * ħ)⁻¹ • H = X from rfl, ← (hc s).eq, neg_mul,
      neg_mul, neg_add_cancel]
  have h := is_const_of_deriv_eq_zero (fun s => (hW s).differentiableAt) (fun s => (hW s).deriv)
    t 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul, h₀] at h
  have he : NormedSpace.exp (t • X) * NormedSpace.exp (t • -X) = 1 := by
    let _ : NormedAlgebra ℚ (E →L[ℂ] E) := .restrictScalars ℚ ℂ (E →L[ℂ] E)
    rw [← NormedSpace.exp_add_of_commute (((Commute.refl X).neg_right.smul_right t).smul_left t),
      ← smul_add, add_neg_cancel, smul_zero, NormedSpace.exp_zero]
  rw [← one_mul (U t), ← he, mul_assoc, h, mul_one]

/-- **Theorem 3**, DR-UNIT ⇔ DR-SCEQ: by the bounded Stone theorem, a norm-continuous unitary
one-parameter group is `exp (t (iħ)⁻¹ H)` for a self-adjoint `H`, and conversely. -/
theorem drUnit_iff_drSceq {ħ : ℝ} (hħ : ħ ≠ 0) {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} :
    DrUnit Φ ↔ DrSceq ħ Φ := by
  constructor
  · rintro ⟨V, hV⟩
    refine ⟨(ħ : ℂ) • V.generator, V, .smul (conj_ofReal ħ) V.generator_isSelfAdjoint,
      V.toAddChar.map_zero_eq_one, fun t => ?_, hV⟩
    convert V.hasDerivAt t using 1
    rw [smul_mul_assoc, smul_smul, (V.commute_generator t).eq, mul_neg, mul_smul_comm,
      ← neg_smul, mul_inv, mul_assoc, inv_mul_cancel₀ (ofReal_ne_zero.mpr hħ), mul_one, inv_I]
  · rintro ⟨H, U, hH, hU₀, hU, hΦ⟩
    have hA : IsSelfAdjoint ((ħ⁻¹ : ℂ) • H) :=
      .smul (by rw [IsSelfAdjoint, star_inv₀, star_def, conj_ofReal]) hH
    refine ⟨UnitaryOneParameterGroup.ofSelfAdjoint hA, fun t ht ρ hρ => ?_⟩
    rw [hΦ t ht ρ hρ, UnitaryOneParameterGroup.ofSelfAdjoint_apply, eq_exp_of_schrodinger hU₀ hU,
      ← Complex.coe_smul, smul_smul, smul_smul, mul_inv, inv_I]
    ring_nf

/-! ## DR-UNIT ⇒ DR-EV, DR-PROB, DR-INFO -/

/-- Conjugation by a unitary operator as `conjOp` of the corresponding isometry. -/
lemma mul_mul_star_eq_conjOp (u : unitary (E →L[ℂ] E)) (ρ : E →L[ℂ] E) :
    (u : E →L[ℂ] E) * ρ * star (u : E →L[ℂ] E) = conjOp (Unitary.linearIsometryEquiv u) ρ := by
  rw [← adL_apply, adL_eq_mul_mul_star]
  rfl

variable [FiniteDimensional ℂ E]

/-- **DR-INFO**: every `Φ t` preserves the von Neumann entropy of density operators. -/
def DrInfo (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t ≥ 0, ∀ ρ, IsDensity ρ → vonNeumann (Φ t ρ) = vonNeumann ρ

variable {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}

/-- **Theorem 3**, DR-UNIT ⇒ DR-EV: unitary conjugation is a bijection of the pure states. -/
theorem DrUnit.drEv (hΦ : IsEvolution Φ) (h : DrUnit Φ) : DrEv Φ := by
  obtain ⟨V, hV⟩ := h
  intro t ht
  have hU : ImplementedByUnitaryOrAntiunitary (Φ t) :=
    Or.inl ⟨Unitary.linearIsometryEquiv ⟨V t, V.mem_unitary t⟩, fun ρ hρ => by
      rw [hV t ht ρ hρ]
      exact mul_mul_star_eq_conjOp ⟨V t, V.mem_unitary t⟩ ρ⟩
  exact ((affine_pure_state_correspondence (hΦ.isDensity t ht) (hΦ.affine t ht)).out 3 1).mp hU

/-- **Theorem 3**, DR-UNIT ⇒ DR-PROB: unitary conjugation maps `|ψ⟩⟨ψ|` to `|U ψ⟩⟨U ψ|`, and
`U` preserves inner products. -/
theorem DrUnit.drProb (h : DrUnit Φ) : DrProb Φ := by
  obtain ⟨V, hV⟩ := h
  intro t ht
  set W := Unitary.linearIsometryEquiv ⟨V t, V.mem_unitary t⟩
  have hP : ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (W ψ) := fun ψ hψ => by
    rw [hV t ht _ (isDensity_proj hψ), mul_mul_star_eq_conjOp ⟨V t, V.mem_unitary t⟩, conjOp_proj]
  refine ⟨fun ψ hψ => ⟨W ψ, by simp [hψ], hP ψ hψ⟩,
    fun ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂ => ?_⟩
  have h : LinearMap.trace ℂ E ((proj ψ' * proj ϕ' : E →L[ℂ] E) : E →ₗ[ℂ] E) =
      ((‖⟪W ψ, W ϕ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h₁, ← h₂, hP ψ hψ, hP ϕ hϕ]
    exact trace_rankOne_mul_rankOne _ _
  rw [trace_rankOne_mul_rankOne, ofReal_inj, LinearIsometryEquiv.inner_map_map] at h
  rw [born_of_norm hψ' hϕ', born_of_norm hψ hϕ, h]

/-- **Theorem 3**, DR-UNIT ⇒ DR-INFO: unitary conjugation preserves the eigenvalues, hence the
von Neumann entropy. -/
theorem DrUnit.drInfo (h : DrUnit Φ) : DrInfo Φ := by
  obtain ⟨V, hV⟩ := h
  intro t ht ρ hρ
  rw [hV t ht ρ hρ]
  exact vonNeumann_unitary_conj (V.mem_unitary t) ρ

/-! ## DR-EV, DR-PROB, DR-INFO ⇒ DR-UNIT -/

/-- An evolution whose every `Φ t` is conjugation by a unitary or an anti-unitary satisfies
DR-UNIT: the anti-unitary case is excluded by `Φ t = Φ (t / 2) ∘ Φ (t / 2)`, and the phase-free
conjugation group lifts to a unitary one-parameter group. -/
theorem drUnit_of_implemented (hΦ : IsEvolution Φ)
    (h : ∀ t ≥ 0, ImplementedByUnitaryOrAntiunitary (Φ t)) : DrUnit Φ :=
  exists_unitaryOneParameterGroup h hΦ.map_zero hΦ.map_add hΦ.continuousWithinAt

/-- **Theorem 3**, DR-EV ⇒ DR-UNIT: by Proposition 1 every `Φ t` is conjugation by a unitary or
an anti-unitary. -/
theorem DrEv.drUnit (hΦ : IsEvolution Φ) (h : DrEv Φ) : DrUnit Φ :=
  drUnit_of_implemented hΦ fun t ht =>
    ((affine_pure_state_correspondence (hΦ.isDensity t ht) (hΦ.affine t ht)).out 1 3).mp (h t ht)

omit [CompleteSpace E] in
/-- An affine map of the density operators that maps pure states to pure states and preserves the
Born rule is conjugation by a unitary or an anti-unitary: Wigner's theorem on the pure states and
the mixed-state extension. Neither injectivity nor surjectivity is needed. -/
theorem implemented_of_mapsPure {T : (E →L[ℂ] E) → E →L[ℂ] E} (hT : AffineOnDensities T)
    (hP : MapsPure T) (hB : PreservesBorn T) : ImplementedByUnitaryOrAntiunitary T := by
  have htr : ∀ ψ ϕ : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      LinearMap.trace ℂ E ((T (proj ψ) * T (proj ϕ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((proj ψ * proj ϕ : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    intro ψ ϕ hψ hϕ
    obtain ⟨ψ', hψ', h₁⟩ := hP ψ hψ
    obtain ⟨ϕ', hϕ', h₂⟩ := hP ϕ hϕ
    have h := hB ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂
    rw [born_of_norm hψ' hϕ', born_of_norm hψ hϕ] at h
    rw [h₁, h₂, trace_rankOne_mul_rankOne, trace_rankOne_mul_rankOne, h]
  rcases wigner_rankOne T hP htr with ⟨W, hW⟩ | ⟨W, hW⟩
  · exact Or.inl ⟨W, fun ρ hρ => hT.eq_conjOp hW hρ⟩
  · exact Or.inr ⟨W, fun ρ hρ => hT.eq_conjOp hW hρ⟩

/-- **Theorem 3**, DR-PROB ⇒ DR-UNIT, directly by Wigner's theorem rather than through DR-EV. -/
theorem DrProb.drUnit (hΦ : IsEvolution Φ) (h : DrProb Φ) : DrUnit Φ :=
  drUnit_of_implemented hΦ fun t ht =>
    implemented_of_mapsPure (hΦ.affine t ht) (h t ht).1 (h t ht).2

omit [CompleteSpace E] in
/-- **Theorem 3**, DR-INFO ⇒ DR-PROB: pure states are the states of zero entropy, and the entropy
of an equal mixture of two pure states determines their transition probability (brief
"Schrödinger equation is equivalent to information conservation"). -/
theorem DrInfo.drProb (hΦ : IsEvolution Φ) (h : DrInfo Φ) : DrProb Φ := fun t ht =>
  pure_and_born_of_preserves (Φ t) (hΦ.isDensity t ht) (h t ht)
    fun _ _ hρ hσ => (hΦ.affine t ht).map_mix hρ hσ

/-- **Theorem 3**: over QST:H + [B]EVMIX + EVTI, DR-SCEQ, DR-UNIT, DR-EV, DR-PROB and DR-INFO are
equivalent. -/
theorem schrodinger_tfae (hΦ : IsEvolution Φ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    [DrSceq ħ Φ, DrUnit Φ, DrEv Φ, DrProb Φ, DrInfo Φ].TFAE := by
  tfae_have 1 ↔ 2 := (drUnit_iff_drSceq hħ).symm
  tfae_have 2 → 3 := DrUnit.drEv hΦ
  tfae_have 3 → 2 := DrEv.drUnit hΦ
  tfae_have 2 → 4 := DrUnit.drProb
  tfae_have 4 → 2 := DrProb.drUnit hΦ
  tfae_have 2 → 5 := DrUnit.drInfo
  tfae_have 5 → 4 := DrInfo.drProb hΦ
  tfae_finish

end Unit

end SchroedingerEvolution
