/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Multiple equivalent characterizations of the Schrödinger equation: Theorem 3 without EVTI, in
finite dimension. Not part of the brief, which restricts to the time-independent case.

Setting: a finite-dimensional complex Hilbert space `E` and a two-parameter evolution
`Ψ t₀ t₁ = Φ_{t₀→t₁}`, `t₀ ≤ t₁`, as in `SchroedingerEvolution.TwoParameter.IsEvolution`
(QST:H + [B]EVMIX: affine on density operators, `Ψ t t = id`, the composition law and joint
continuity). Without EVTI there is no one-parameter group, and the conditions are restated for
the maps `Ψ t₀ t₁`:
* `DrUnit`  DR-UNIT: `Ψ t₀ t₁` is conjugation by the propagator `U t₁ U t₀†` of a family of
  unitaries `U t`;
* `DrEv`  DR-EV: every `Ψ t₀ t₁` is a bijection of the pure states;
* `DrProb`  DR-PROB: every `Ψ t₀ t₁` maps pure states to pure states and preserves the Born rule;
* DR-INFO and EVDIFF as in `UnitaryEntropy.TwoParameter` (every `Ψ t₀ t₁` preserves the von
  Neumann entropy; `t ↦ Ψ r t ρ` is differentiable at every `t > r`).

Results:
* `drUnit_of_forall`  if every `Ψ t₀ t₁` is conjugation by some unitary, the unitaries can be
  chosen as one propagator `U t₁ U t₀†`: `U t` implements `Ψ 0 t` for `t ≥ 0` and `Ψ t 0⁻¹` for
  `t < 0`, and the composition law does the rest;
* `drUnit_of_implemented`  if every `Ψ t₀ t₁` is conjugation by a unitary or an anti-unitary,
  DR-UNIT holds: the anti-unitary case is excluded by continuity and the composition law
  (`UnitaryEntropy.TwoParameter.exists_unitary_of_wigner`);
* `schrodinger_tfae`  over QST:H + [B]EVMIX, DR-UNIT, DR-EV, DR-PROB and DR-INFO are equivalent;
* `drSceq_tfae`  DR-SCEQ with a time-dependent Hamiltonian is equivalent to each of them together
  with EVDIFF. Under EVTI the differentiability is automatic, since a norm-continuous unitary group
  is smooth; without EVTI it is not, and the propagator `U t` may be continuous but not
  differentiable.
-/

public import UnitaryEntropy.TwoParameter

@[expose] public noncomputable section

namespace SchroedingerEvolution.FurtherResults

open InnerProductSpace QuantumMechanics.Wigner
open UnitaryEntropy.TwoParameter (EvDiff exists_unitary_of_wigner drSceq_iff_drInfo_and_evDiff)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

/-! ## Conditions -/

/-- **DR-UNIT** for a two-parameter evolution: `Ψ t₀ t₁` is conjugation by the propagator
`U t₁ U t₀†` of a family of unitaries `U t`. -/
def DrUnit (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ U : ℝ → E →L[ℂ] E, (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧
    ∀ t₀ t₁, t₀ ≤ t₁ → ∀ ρ, IsDensity ρ →
      Ψ t₀ t₁ ρ = U t₁ * star (U t₀) * ρ * star (U t₁ * star (U t₀))

/-- **DR-EV** for a two-parameter evolution: every `Ψ t₀ t₁` is a bijection of the pure
states. -/
def DrEv (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t₀ t₁, t₀ ≤ t₁ → BijOnPure (Ψ t₀ t₁)

/-- **DR-PROB** for a two-parameter evolution: every `Ψ t₀ t₁` maps pure states to pure states
and preserves conditional probability. -/
def DrProb (Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t₀ t₁, t₀ ≤ t₁ → MapsPure (Ψ t₀ t₁) ∧ PreservesBorn (Ψ t₀ t₁)

variable {Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E}

/-! ## Unitary conjugations -/

omit [FiniteDimensional ℂ E] in
lemma mul_mul_star_mul (u v ρ : E →L[ℂ] E) :
    u * v * ρ * star (u * v) = u * (v * ρ * star v) * star u := by
  rw [star_mul]
  simp only [mul_assoc]

omit [FiniteDimensional ℂ E] in
lemma mul_mul_star_of_star_mul {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) (ρ : E →L[ℂ] E) :
    u * (star u * ρ * star (star u)) * star u = ρ := by
  simp only [star_star, ← mul_assoc, Unitary.mul_star_self_of_mem hu, one_mul]
  rw [mul_assoc, Unitary.mul_star_self_of_mem hu, mul_one]

omit [FiniteDimensional ℂ E] in
lemma star_mul_star_of_mul {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) (ρ : E →L[ℂ] E) :
    star u * (u * ρ * star u) * star (star u) = ρ := by
  simpa using mul_mul_star_of_star_mul (Unitary.star_mem hu) ρ

lemma isDensity_mul_mul_star {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) {ρ : E →L[ℂ] E}
    (hρ : IsDensity ρ) : IsDensity (u * ρ * star u) := by
  convert hρ.conjOp (Unitary.linearIsometryEquiv ⟨u, hu⟩) using 1
  exact mul_mul_star_eq_conjOp ⟨u, hu⟩ ρ

/-- **One propagator.** If every `Ψ t₀ t₁` is conjugation by some unitary, then DR-UNIT holds:
with `U t` implementing `Ψ 0 t` for `t ≥ 0` and the inverse of `Ψ t 0` for `t < 0`, the
composition law through the time `0` gives `Ψ t₀ t₁` as conjugation by `U t₁ U t₀†`. -/
theorem drUnit_of_forall (hΨ : TwoParameter.IsEvolution Ψ)
    (h : ∀ t₀ t₁, t₀ ≤ t₁ → ∃ u ∈ unitary (E →L[ℂ] E),
      ∀ ρ, IsDensity ρ → Ψ t₀ t₁ ρ = u * ρ * star u) :
    DrUnit Ψ := by
  have h' : ∀ t₀ t₁, ∃ u ∈ unitary (E →L[ℂ] E),
      t₀ ≤ t₁ → ∀ ρ, IsDensity ρ → Ψ t₀ t₁ ρ = u * ρ * star u := fun t₀ t₁ => by
    by_cases ht : t₀ ≤ t₁
    · obtain ⟨u, hu, hΨu⟩ := h t₀ t₁ ht
      exact ⟨u, hu, fun _ => hΨu⟩
    · exact ⟨1, one_mem _, fun h => (ht h).elim⟩
  choose u hu hΨu using h'
  let U : ℝ → E →L[ℂ] E := fun t => if 0 ≤ t then u 0 t else star (u t 0)
  have hU : ∀ t, U t ∈ unitary (E →L[ℂ] E) := fun t => by
    by_cases ht : 0 ≤ t
    · simp only [U, ht, ↓reduceIte]
      exact hu 0 t
    · simp only [U, ht, ↓reduceIte]
      exact Unitary.star_mem (hu t 0)
  have hP : ∀ t, 0 ≤ t → ∀ ρ, IsDensity ρ → Ψ 0 t ρ = U t * ρ * star (U t) :=
    fun t ht ρ hρ => by
      simp only [U, ht, ↓reduceIte]
      exact hΨu 0 t ht ρ hρ
  have hN : ∀ s, s < 0 → ∀ ρ, IsDensity ρ → Ψ s 0 ρ = star (U s) * ρ * star (star (U s)) :=
    fun s hs ρ hρ => by
      simp only [U, not_le.mpr hs, ↓reduceIte, star_star]
      exact hΨu s 0 hs.le ρ hρ
  refine ⟨U, hU, fun s t hst σ hσ => ?_⟩
  rw [mul_mul_star_mul]
  have hσ' : IsDensity (star (U s) * σ * star (star (U s))) :=
    isDensity_mul_mul_star (Unitary.star_mem (hU s)) hσ
  rcases le_or_gt 0 s with hs | hs
  · -- `0 ≤ s ≤ t`: `Ψ s t ∘ Ψ 0 s = Ψ 0 t`
    have hσρ : Ψ 0 s (star (U s) * σ * star (star (U s))) = σ := by
      rw [hP s hs _ hσ']
      exact mul_mul_star_of_star_mul (hU s) σ
    conv_lhs => rw [← hσρ]
    rw [hΨ.map_comp 0 s t hs hst _ hσ', hP t (hs.trans hst) _ hσ']
  rcases le_or_gt 0 t with ht | ht
  · -- `s < 0 ≤ t`: `Ψ 0 t ∘ Ψ s 0 = Ψ s t`
    rw [← hΨ.map_comp s 0 t hs.le ht σ hσ, hN s hs σ hσ, hP t ht _ hσ']
  · -- `s ≤ t < 0`: `Ψ t 0 ∘ Ψ s t = Ψ s 0`
    have h1 := hΨ.map_comp s t 0 hst ht.le σ hσ
    rw [hN t ht _ (hΨ.isDensity s t hst σ hσ), hN s hs σ hσ] at h1
    rw [← h1, mul_mul_star_of_star_mul (hU t)]

/-- **Excluding anti-unitaries.** If every `Ψ t₀ t₁` is conjugation by a unitary or an
anti-unitary, DR-UNIT holds: the type is locally constant in time by continuity and the
composition law, and `Ψ t t = id`. -/
theorem drUnit_of_implemented (hΨ : TwoParameter.IsEvolution Ψ)
    (h : ∀ t₀ t₁, t₀ ≤ t₁ → ImplementedByUnitaryOrAntiunitary (Ψ t₀ t₁)) : DrUnit Ψ := by
  have hW : ∀ t₀ t₁, t₀ ≤ t₁ →
      (∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Ψ t₀ t₁ (proj ψ) = proj (U ψ)) ∨
        ∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Ψ t₀ t₁ (proj ψ) = proj (U ψ) :=
    fun t₀ t₁ ht => (h t₀ t₁ ht).imp
      (fun ⟨W, hW⟩ => ⟨W, fun ψ hψ => by rw [hW _ (isDensity_proj hψ), conjOp_proj]⟩)
      (fun ⟨W, hW⟩ => ⟨W, fun ψ hψ => by rw [hW _ (isDensity_proj hψ), conjOp_proj]⟩)
  refine drUnit_of_forall hΨ fun t₀ t₁ ht => ?_
  obtain ⟨W, hW'⟩ := exists_unitary_of_wigner hΨ hW ht
  have hu := linearIsometryEquiv_mem_unitary W
  refine ⟨W, hu, fun ρ hρ => ?_⟩
  have hW'' : ∀ ψ : E, ‖ψ‖ = 1 →
      Ψ t₀ t₁ (proj ψ) = proj (Unitary.linearIsometryEquiv ⟨_, hu⟩ ψ) := hW'
  rw [(hΨ.affine t₀ t₁ ht).eq_conjOp hW'' hρ]
  exact (mul_mul_star_eq_conjOp ⟨_, hu⟩ ρ).symm

/-! ## Theorem 3 without EVTI -/

/-- DR-UNIT ⇒ DR-EV: conjugation by the unitary `U t₁ U t₀†` is a bijection of the pure states
(Proposition 1). -/
theorem DrUnit.drEv (hΨ : TwoParameter.IsEvolution Ψ) (h : DrUnit Ψ) : DrEv Ψ := by
  obtain ⟨U, hU, hΨU⟩ := h
  intro t₀ t₁ ht
  have hw := mul_mem (hU t₁) (Unitary.star_mem (hU t₀))
  have hI : ImplementedByUnitaryOrAntiunitary (Ψ t₀ t₁) :=
    Or.inl ⟨Unitary.linearIsometryEquiv ⟨_, hw⟩, fun ρ hρ => by
      rw [hΨU t₀ t₁ ht ρ hρ]
      exact mul_mul_star_eq_conjOp ⟨_, hw⟩ ρ⟩
  exact ((affine_pure_state_correspondence (hΨ.isDensity t₀ t₁ ht)
    (hΨ.affine t₀ t₁ ht)).out 3 1).mp hI

/-- DR-EV ⇒ DR-UNIT: by Proposition 1 every `Ψ t₀ t₁` is conjugation by a unitary or an
anti-unitary. -/
theorem DrEv.drUnit (hΨ : TwoParameter.IsEvolution Ψ) (h : DrEv Ψ) : DrUnit Ψ :=
  drUnit_of_implemented hΨ fun t₀ t₁ ht =>
    ((affine_pure_state_correspondence (hΨ.isDensity t₀ t₁ ht)
      (hΨ.affine t₀ t₁ ht)).out 1 3).mp (h t₀ t₁ ht)

/-- DR-UNIT ⇒ DR-INFO: unitary conjugation preserves the von Neumann entropy. -/
theorem DrUnit.drInfo (h : DrUnit Ψ) : UnitaryEntropy.TwoParameter.DrInfo Ψ := by
  obtain ⟨U, hU, hΨU⟩ := h
  intro t₀ t₁ ht ρ hρ
  rw [hΨU t₀ t₁ ht ρ hρ]
  exact UnitaryEntropy.vonNeumann_unitary_conj (mul_mem (hU t₁) (Unitary.star_mem (hU t₀))) ρ

omit [CompleteSpace E] in
/-- DR-INFO ⇒ DR-PROB: pure states are the states of zero entropy, and the entropy of an equal
mixture of two pure states determines their transition probability. -/
theorem drProb_of_drInfo (hΨ : TwoParameter.IsEvolution Ψ)
    (h : UnitaryEntropy.TwoParameter.DrInfo Ψ) :
    DrProb Ψ := fun t₀ t₁ ht =>
  UnitaryEntropy.pure_and_born_of_preserves (Ψ t₀ t₁) (hΨ.isDensity t₀ t₁ ht) (h t₀ t₁ ht)
    fun _ _ hρ hσ => (hΨ.affine t₀ t₁ ht).map_mix hρ hσ

/-- DR-PROB ⇒ DR-UNIT: by Wigner's theorem every `Ψ t₀ t₁` is conjugation by a unitary or an
anti-unitary. -/
theorem DrProb.drUnit (hΨ : TwoParameter.IsEvolution Ψ) (h : DrProb Ψ) : DrUnit Ψ :=
  drUnit_of_implemented hΨ fun t₀ t₁ ht =>
    implemented_of_mapsPure (hΨ.affine t₀ t₁ ht) (h t₀ t₁ ht).1 (h t₀ t₁ ht).2

/-- **Theorem 3 without EVTI**: over QST:H + [B]EVMIX for a two-parameter evolution, DR-UNIT,
DR-EV, DR-PROB and DR-INFO are equivalent. -/
theorem schrodinger_tfae (hΨ : TwoParameter.IsEvolution Ψ) :
    [DrUnit Ψ, DrEv Ψ, DrProb Ψ, UnitaryEntropy.TwoParameter.DrInfo Ψ].TFAE := by
  tfae_have 1 → 2 := DrUnit.drEv hΨ
  tfae_have 2 → 1 := DrEv.drUnit hΨ
  tfae_have 1 → 4 := DrUnit.drInfo
  tfae_have 4 → 3 := drProb_of_drInfo hΨ
  tfae_have 3 → 1 := DrProb.drUnit hΨ
  tfae_finish

/-- **Theorem 3 without EVTI, with DR-SCEQ**: DR-SCEQ with a time-dependent Hamiltonian is
equivalent to each of DR-UNIT, DR-EV, DR-PROB and DR-INFO together with EVDIFF. -/
theorem drSceq_tfae (hΨ : TwoParameter.IsEvolution Ψ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    [TwoParameter.DrSceq ħ Ψ, DrUnit Ψ ∧ EvDiff Ψ, DrEv Ψ ∧ EvDiff Ψ, DrProb Ψ ∧ EvDiff Ψ,
      UnitaryEntropy.TwoParameter.DrInfo Ψ ∧ EvDiff Ψ].TFAE := by
  have h := schrodinger_tfae hΨ
  tfae_have 1 ↔ 5 := drSceq_iff_drInfo_and_evDiff hΨ hħ
  tfae_have 2 ↔ 5 := and_congr_left' (h.out 1 4)
  tfae_have 3 ↔ 5 := and_congr_left' (h.out 2 4)
  tfae_have 4 ↔ 5 := and_congr_left' (h.out 3 4)
  tfae_finish

end SchroedingerEvolution.FurtherResults
