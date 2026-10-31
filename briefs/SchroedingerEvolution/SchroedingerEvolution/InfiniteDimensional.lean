/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Multiple equivalent characterizations of the Schrödinger equation: Hilbert spaces of any
dimension.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a complex Hilbert space `E` of any dimension, as in QST:H; no separability is used.
Density operators are the positive trace-class operators of trace one (`IsDensityOperator`),
pure states are `proj ψ = |ψ⟩⟨ψ|` for unit `ψ`, and the entropy is the von Neumann entropy
`vonNeumannEntropy ∈ [0, ∞]` (brief "Schrödinger equation is equivalent to information
conservation", any dimension). An evolution is a family `Φ t` of maps on operators, used on
density operators and for `t ≥ 0` only.

Proposition 1 (Affine pure-state correspondence):
* `affine_pure_state_correspondence`  for a map `T` of the density operators that preserves
  convex combinations, bijective on pure states ⇔ bijective on density operators ⇔ conjugation by
  a unitary or an anti-unitary (`QuantumMechanics.AffineOnDensityOperators.tfae`). No continuity
  is needed.

Conditions:
* `IsEvolution`  QST:H + [B]EVMIX + EVTI: `Φ t` maps density operators affinely to density
  operators, `Φ 0 = id`, `Φ (s + t) = Φ s ∘ Φ t`, and `t ↦ Φ t ρ` is continuous at `0⁺` in
  operator norm;
* `DrSceq`  a propagator `U` with `U 0 = 1` solves `d/dt U t ψ = (iħ)⁻¹ H U t ψ` for `ψ` in the
  domain of a self-adjoint, possibly unbounded, `H` (`QuantumMechanics.SolvesSchrodinger`);
* `DrUnit`  `Φ t ρ = U t ρ U t†` for a strongly continuous unitary one-parameter group `U`;
* `DrEv`  `Φ t` is a bijection of the pure states;
* `DrProb`  `Φ t` maps pure states to pure states, preserves the Born rule, and every pure state
  has a pure past (`HasPurePast`);
* `DrInfo`  `Φ t` preserves the von Neumann entropy, and every density operator has a past.

Theorem 3:
* `schrodinger_tfae`  over `IsEvolution`, the five conditions are equivalent;
* `drUnit_iff_drSceq`  DR-UNIT ⇔ DR-SCEQ (Stone's theorem, `ForPhyslib/QuantumMechanics/Stone`);
* `DrUnit.drEv`, `DrUnit.drProb`, `DrUnit.drInfo`  DR-UNIT ⇒ DR-EV, DR-PROB, DR-INFO;
* `DrEv.drUnit`  DR-EV ⇒ DR-UNIT: Proposition 1 for each `t`, then Bargmann's theorem for `ℝ`
  (`QuantumMechanics.exists_stronglyContinuousUnitaryGroup`), which excludes anti-unitaries by
  `Φ t = Φ (t / 2) ∘ Φ (t / 2)` and chooses the phases;
* `DrProb.drEv`  DR-PROB ⇒ DR-EV: Born preservation gives injectivity on pure states, the pure
  past surjectivity;
* `DrInfo.drProb`  DR-INFO ⇒ DR-PROB: pure states are the states of zero entropy, and the
  entropy of an equal mixture of two pure states determines their transition probability.
-/

public import ForPhyslib.QuantumMechanics.Stone
public import SchroedingerEvolution
public import UnitaryEntropy.InfiniteDimensional

@[expose] public noncomputable section

namespace SchroedingerEvolution.InfiniteDimensional

open InnerProductSpace QuantumMechanics QuantumMechanics.Wigner UnitaryEntropy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Proposition 1 -/

/-- **Proposition 1**, any dimension: for a map of the density operators that preserves convex
combinations, being bijective on the pure states, being bijective on all density operators and
being conjugation by a unitary or an anti-unitary are equivalent. -/
theorem affine_pure_state_correspondence {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (T ρ)) (hT : AffineOnDensityOperators T) :
    [BijOnPure T, Set.BijOn T {ρ | IsDensityOperator ρ} {ρ | IsDensityOperator ρ},
      ImplementedOnDensityOperators T].TFAE :=
  hT.tfae hD

/-! ## Conditions -/

/-- **QST:H + [B]EVMIX + EVTI**: a time-independent evolution of the density operators that
preserves statistical mixtures. The brief's joint continuity is weakened to continuity of
`t ↦ Φ t ρ` at `0⁺` in operator norm, for each density operator `ρ`. -/
structure IsEvolution (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  isDensityOperator : ∀ t ≥ 0, ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ t ρ)
  affine : ∀ t ≥ 0, AffineOnDensityOperators (Φ t)
  map_zero : ∀ ρ, IsDensityOperator ρ → Φ 0 ρ = ρ
  map_add : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ρ, IsDensityOperator ρ → Φ (s + t) ρ = Φ s (Φ t ρ)
  continuousWithinAt :
    ∀ ρ, IsDensityOperator ρ → ContinuousWithinAt (fun t => Φ t ρ) (Set.Ici 0) 0

/-- Every pure state is the evolution of a pure state, its reconstructed past. -/
def HasPurePast (T : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ ϕ : E, ‖ϕ‖ = 1 → ∃ ψ : E, ‖ψ‖ = 1 ∧ T (proj ψ) = proj ϕ

/-- **DR-EV**: every `Φ t` is a bijection of the pure states. -/
def DrEv (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t ≥ 0, BijOnPure (Φ t)

/-- **DR-PROB**: every `Φ t` maps pure states to pure states and preserves conditional
probability, and every pure state has a reconstructed pure past. -/
def DrProb (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t ≥ 0, MapsPure (Φ t) ∧ PreservesBorn (Φ t) ∧ HasPurePast (Φ t)

/-- **DR-INFO**: every `Φ t` preserves the von Neumann entropy of density operators, and every
density operator has a reconstructed past. -/
def DrInfo (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ t ≥ 0, (∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ t ρ) = vonNeumannEntropy ρ) ∧
    ∀ ρ, IsDensityOperator ρ → ∃ σ, IsDensityOperator σ ∧ Φ t σ = ρ

/-- **DR-SCEQ**: the evolution is conjugation by a propagator `U` with `U 0 = 1` that solves the
Schrödinger equation `d/dt U t ψ = (iħ)⁻¹ H U t ψ` on the domain of a self-adjoint `H`. -/
def DrSceq (ħ : ℝ) (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ (H : E →ₗ.[ℂ] E) (U : ℝ → E →L[ℂ] E), IsSelfAdjoint H ∧ U 0 = 1 ∧
    SolvesSchrodinger ħ H U ∧ ∀ t ≥ 0, ∀ ρ, IsDensityOperator ρ → Φ t ρ = U t * ρ * star (U t)

/-- **DR-UNIT**: the evolution is conjugation by a strongly continuous unitary one-parameter
group, `Φ t ρ = U t ρ U t†`. -/
def DrUnit (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ U : StronglyContinuousUnitaryGroup E, ∀ t ≥ 0, ∀ ρ, IsDensityOperator ρ →
    Φ t ρ = U t * ρ * star (U t)

/-! ## DR-UNIT ⇔ DR-SCEQ -/

variable {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}

/-- **Theorem 3**, DR-UNIT ⇔ DR-SCEQ, by Stone's theorem: a strongly continuous unitary group
solves the Schrödinger equation for a self-adjoint `H`, and a solution with `U 0 = 1` is a
strongly continuous unitary group. -/
theorem drUnit_iff_drSceq {ħ : ℝ} (hħ : ħ ≠ 0) : DrUnit Φ ↔ DrSceq ħ Φ := by
  constructor
  · rintro ⟨V, hV⟩
    obtain ⟨H, hH, hS⟩ := V.exists_solvesSchrodinger hħ
    exact ⟨H, V.toFun, hH, V.map_zero, hS, hV⟩
  · rintro ⟨H, U, hH, hU0, hS, hΦ⟩
    obtain ⟨V, hVU⟩ := exists_stronglyContinuousUnitaryGroup_of_solvesSchrodinger hħ hH hU0 hS
    exact ⟨V, fun t ht ρ hρ => by rw [hΦ t ht ρ hρ, ← hVU]⟩

/-! ## DR-UNIT ⇒ DR-EV, DR-PROB, DR-INFO -/

omit [CompleteSpace E] in
/-- Pure states with equal projections have equal transition probabilities. -/
lemma norm_inner_sq_eq_of_proj_eq {a a' b b' : E} (ha : proj a = proj a')
    (hb : proj b = proj b') : ‖⟪a, b⟫_ℂ‖ ^ 2 = ‖⟪a', b'⟫_ℂ‖ ^ 2 := by
  have h1 : ‖⟪a, b⟫_ℂ‖ ^ 2 = ‖⟪a', b⟫_ℂ‖ ^ 2 := by
    have h := inner_proj_apply a b
    rw [ha, inner_proj_apply] at h
    exact_mod_cast h.symm
  have h2 : ‖⟪b, a'⟫_ℂ‖ ^ 2 = ‖⟪b', a'⟫_ℂ‖ ^ 2 := by
    have h := inner_proj_apply b a'
    rw [hb, inner_proj_apply] at h
    exact_mod_cast h.symm
  rw [h1, norm_inner_symm a' b, h2, norm_inner_symm]

/-- Under DR-UNIT every `Φ t` is conjugation by a unitary. -/
theorem DrUnit.implemented (h : DrUnit Φ) {t : ℝ} (ht : 0 ≤ t) :
    ImplementedOnDensityOperators (Φ t) := by
  obtain ⟨V, hV⟩ := h
  exact Or.inl ⟨Unitary.linearIsometryEquiv ⟨V t, V.mem_unitary t⟩, fun ρ hρ => by
    rw [hV t ht ρ hρ]
    exact mul_mul_star_eq_conjOp ⟨V t, V.mem_unitary t⟩ ρ⟩

/-- **Theorem 3**, DR-UNIT ⇒ DR-EV: unitary conjugation is a bijection of the pure states. -/
theorem DrUnit.drEv (hΦ : IsEvolution Φ) (h : DrUnit Φ) : DrEv Φ := fun t ht =>
  ((affine_pure_state_correspondence (hΦ.isDensityOperator t ht) (hΦ.affine t ht)).out 3 1).mp
    (h.implemented ht)

/-- **Theorem 3**, DR-UNIT ⇒ DR-PROB: unitary conjugation maps `|ψ⟩⟨ψ|` to `|U ψ⟩⟨U ψ|`, `U`
preserves inner products, and `U⋆ ϕ` is the past of `ϕ`. -/
theorem DrUnit.drProb (h : DrUnit Φ) : DrProb Φ := by
  obtain ⟨V, hV⟩ := h
  intro t ht
  have hu := V.mem_unitary t
  have hP : ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (V t ψ) := fun ψ hψ => by
    rw [hV t ht _ (isDensityOperator_proj hψ), mul_proj_mul_star]
  refine ⟨fun ψ hψ => ⟨V t ψ, ?_, hP ψ hψ⟩, fun ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂ => ?_,
    fun ϕ hϕ => ⟨star (V t) ϕ, ?_, ?_⟩⟩
  · rw [ContinuousLinearMap.norm_map_of_mem_unitary hu, hψ]
  · rw [born_of_norm hψ' hϕ', born_of_norm hψ hϕ, ← norm_inner_sq_eq_of_proj_eq
      ((hP ψ hψ).symm.trans h₁) ((hP ϕ hϕ).symm.trans h₂),
      ContinuousLinearMap.inner_map_map_of_mem_unitary hu]
  · rw [ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hu), hϕ]
  · rw [hP _ (by rw [ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem hu), hϕ]),
      ← mul_apply_eq_comp, Unitary.mul_star_self_of_mem hu, one_apply_eq_self]

/-- **Theorem 3**, DR-UNIT ⇒ DR-INFO: unitary conjugation preserves the entropy, and
`U⋆ ρ U` is the past of `ρ`. -/
theorem DrUnit.drInfo (h : DrUnit Φ) : DrInfo Φ := by
  obtain ⟨V, hV⟩ := h
  intro t ht
  have hu := V.mem_unitary t
  refine ⟨fun ρ hρ => ?_, fun ρ hρ => ⟨star (V t) * ρ * star (star (V t)), ?_, ?_⟩⟩
  · rw [hV t ht ρ hρ]
    exact hρ.vonNeumannEntropy_conj (Unitary.star_mul_self_of_mem hu)
  · exact hρ.conj (by rw [star_star]; exact Unitary.mul_star_self_of_mem hu)
  · rw [hV t ht _ (hρ.conj (by rw [star_star]; exact Unitary.mul_star_self_of_mem hu)), star_star]
    simp only [← mul_assoc, Unitary.mul_star_self_of_mem hu, one_mul]
    rw [mul_assoc, Unitary.mul_star_self_of_mem hu, mul_one]

/-! ## DR-EV, DR-PROB, DR-INFO ⇒ DR-UNIT -/

/-- **Theorem 3**, DR-EV ⇒ DR-UNIT: by Proposition 1 every `Φ t` is conjugation by a unitary or
an anti-unitary, and Bargmann's theorem for `ℝ` lifts the evolution to a strongly continuous
unitary group. -/
theorem DrEv.drUnit (hΦ : IsEvolution Φ) (h : DrEv Φ) : DrUnit Φ :=
  exists_stronglyContinuousUnitaryGroup
    (fun t ht => ((affine_pure_state_correspondence (hΦ.isDensityOperator t ht)
      (hΦ.affine t ht)).out 1 3).mp (h t ht))
    (fun _ hψ => hΦ.map_zero _ (isDensityOperator_proj hψ)) hΦ.map_add
    (fun _ hψ => hΦ.continuousWithinAt _ (isDensityOperator_proj hψ))

omit [CompleteSpace E] in
/-- **Theorem 3**, DR-PROB ⇒ DR-EV: if `Φ t` sends `ψ` and `ϕ` to the same pure state, their
transition probability is that of the image with itself, `1`, so `ψ` and `ϕ` are the same pure
state; the pure past gives surjectivity. -/
theorem DrProb.drEv (h : DrProb Φ) : DrEv Φ := by
  intro t ht
  obtain ⟨hP, hB, hS⟩ := h t ht
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨ψ, hψ, rfl⟩
    obtain ⟨ψ', hψ', h'⟩ := hP ψ hψ
    exact ⟨ψ', hψ', h'⟩
  · rintro _ ⟨ψ, hψ, rfl⟩ _ ⟨ϕ, hϕ, rfl⟩ heq
    obtain ⟨ψ', hψ', h₁⟩ := hP ψ hψ
    obtain ⟨ϕ', hϕ', h₂⟩ := hP ϕ hϕ
    have hb := hB ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂
    rw [born_of_norm hψ' hϕ', born_of_norm hψ hϕ,
      norm_inner_sq_eq_of_proj_eq (h₁.symm.trans (heq.trans h₂)) rfl,
      inner_self_eq_norm_sq_to_K, hϕ'] at hb
    refine proj_eq_proj_of_norm_inner_eq_one hψ hϕ ?_
    have h1 : ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2 = 1 := by rw [← hb]; simp
    nlinarith [norm_nonneg ⟪ψ, ϕ⟫_ℂ]
  · rintro _ ⟨ϕ, hϕ, rfl⟩
    obtain ⟨ψ, hψ, h'⟩ := hS ϕ hϕ
    exact ⟨proj ψ, ⟨ψ, hψ, rfl⟩, h'⟩

/-- **Theorem 3**, DR-PROB ⇒ DR-UNIT, through DR-EV. -/
theorem DrProb.drUnit (hΦ : IsEvolution Φ) (h : DrProb Φ) : DrUnit Φ :=
  h.drEv.drUnit hΦ

/-- **Theorem 3**, DR-INFO ⇒ DR-PROB: pure states are the states of zero entropy, the entropy of
an equal mixture of two pure states determines their transition probability, and the past of a
pure state is pure. -/
theorem DrInfo.drProb (hΦ : IsEvolution Φ) (h : DrInfo Φ) : DrProb Φ := fun t ht => by
  obtain ⟨hP, hB⟩ := pure_and_born_of_preserves_vonNeumannEntropy (Φ t)
    (hΦ.isDensityOperator t ht) (h t ht).1 fun _ _ hρ hσ => (hΦ.affine t ht).map_mix hρ hσ
  exact ⟨hP, hB, exists_proj_of_past (Φ t) (h t ht).1 (h t ht).2⟩

/-- **Theorem 3**, any dimension: over QST:H + [B]EVMIX + EVTI, DR-SCEQ, DR-UNIT, DR-EV,
DR-PROB and DR-INFO are equivalent. -/
theorem schrodinger_tfae (hΦ : IsEvolution Φ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    [DrSceq ħ Φ, DrUnit Φ, DrEv Φ, DrProb Φ, DrInfo Φ].TFAE := by
  tfae_have 1 ↔ 2 := (drUnit_iff_drSceq hħ).symm
  tfae_have 2 → 3 := DrUnit.drEv hΦ
  tfae_have 3 → 2 := DrEv.drUnit hΦ
  tfae_have 2 → 4 := DrUnit.drProb
  tfae_have 4 → 3 := DrProb.drEv
  tfae_have 2 → 5 := DrUnit.drInfo
  tfae_have 5 → 4 := DrInfo.drProb hΦ
  tfae_finish

end SchroedingerEvolution.InfiniteDimensional
