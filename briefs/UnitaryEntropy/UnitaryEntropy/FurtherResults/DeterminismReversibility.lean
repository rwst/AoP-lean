/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import UnitaryEntropy.TwoParameter

/-!
# Further results: entropy conservation as determinism and reversibility

Not part of the brief. This file formalizes Sec. 2 of `further-results.tex` in the brief's
directory. The brief reads DR-INFO as "an information theoretic way to characterize determinism
and reversibility". Here that reading is made precise and proved, for one evolution map and
without any continuity in time.

The base is the brief's: a finite-dimensional Hilbert space (QST:H) and a map `Φ` of the density
operators that preserves equal mixtures ([B]EVMIX). Following *Assumptions of Physics*, an
evolution is deterministic and reversible when "specifying the state of the system at a
particular time is equivalent to specifying the state at a future (determinism) or past
(reversibility) time". The states of maximal information are the pure states, so:

* deterministic: `Φ` maps every pure state to a pure state, so the initial state determines the
  final state, not only a statistical mixture of final states;
* reversible: `Φ` is injective on the pure states, so the final state determines the initial one.

`IsDetRev Φ` is the conjunction. `detRev_tfae` proves it equivalent to DR-INFO (`PreservesEntropy`,
`S(Φ ρ) = S(ρ)` for every density operator `ρ`), to `Φ` being a bijection of the pure states, to
`Φ` being a bijection of all density operators (an isomorphism of the state space), and to `Φ`
being conjugation by a unitary or an anti-unitary.

Steps:
* DR-INFO ⇒ deterministic and reversible: the brief's Steps 1 and 2
  (`UnitaryEntropy.pure_and_born_of_preserves`): pure states, the states of zero entropy, go to
  pure states, and transition probabilities are preserved, so distinct pure states have distinct
  images;
* deterministic and reversible ⇒ conjugation: Kadison's theorem for maps injective on pure states
  (`QuantumMechanics.Wigner.AffineOnDensities.implemented_of_injOn`), which needs neither
  surjectivity nor continuity;
* conjugation ⇒ DR-INFO: the entropy is invariant under unitary conjugation
  (`UnitaryEntropy.vonNeumann_conj`), and on a density operator an anti-unitary agrees with the
  unitary that maps the same orthonormal eigenbasis to the same vectors
  (`vonNeumann_conjOp`).

The anti-unitary case cannot be excluded for a single map: complex conjugation in a basis is
deterministic, reversible and preserves the entropy. Along an evolution with `Ψ t t = id` and
the composition law it is excluded by continuity
(`UnitaryEntropy.TwoParameter.exists_unitary`). `detRev_iff_drInfo` states the equivalence for
the brief's two-parameter evolutions.

In dimension `n ≥ 2` neither half of the definition can be dropped (not formalized here). The
constant map onto one pure state is
deterministic but not reversible, and it lowers the entropy of every mixed state. The
depolarizing map `ρ ↦ ρ/2 + 1/(2n)` is injective but not deterministic, and it raises the
entropy of every pure state.

## Main results

* `vonNeumann_conjOp`: conjugation by a unitary or an anti-unitary preserves the entropy of a
  density operator;
* `IsDetRev`: deterministic and reversible evolution;
* `detRev_tfae`: the five equivalent conditions;
* `isDetRev_iff_preservesEntropy`: deterministic and reversible ⇔ DR-INFO;
* `detRev_iff_drInfo`: the same for the brief's two-parameter evolutions.

The comparator lane, which certifies the main file of the brief, does not depend on this module.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy.FurtherResults

open InnerProductSpace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## Entropy under anti-unitary conjugation -/

/-- On a density operator `ρ`, conjugation by an anti-unitary `W` agrees with conjugation by the
unitary that sends an orthonormal eigenbasis `v` of `ρ` to `W ∘ v`. -/
lemma exists_conjOp_eq_conjOp (W : E ≃ₗᵢ⋆[ℂ] E) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    ∃ U : E ≃ₗᵢ[ℂ] E, conjOp W ρ = conjOp U ρ := by
  set v := hρ.isPositive.isSymmetric.eigenvectorBasis rfl
  have hon : Orthonormal ℂ (W ∘ v) :=
    (isWignerMap_conjLinearIsometryEquiv W).orthonormal_comp v.orthonormal
  let v' := OrthonormalBasis.mk hon
    (hon.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)).ge
  refine ⟨v.equiv v' (Equiv.refl _), ?_⟩
  conv_lhs => rw [hρ.eq_sum_proj]
  conv_rhs => rw [hρ.eq_sum_proj]
  simp_rw [conjOp_sum, conjOp_ofReal_smul, conjOp_proj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.equiv_apply_basis, OrthonormalBasis.coe_mk]
  rfl

/-- Conjugation by a unitary preserves the entropy. -/
lemma vonNeumann_conjOp_unitary (U : E ≃ₗᵢ[ℂ] E) (ρ : E →L[ℂ] E) :
    vonNeumann (conjOp U ρ) = vonNeumann ρ :=
  vonNeumann_conj U.toLinearEquiv (by ext; rfl)

/-- Conjugation by an anti-unitary preserves the entropy of a density operator. -/
lemma vonNeumann_conjOp_antiunitary (W : E ≃ₗᵢ⋆[ℂ] E) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    vonNeumann (conjOp W ρ) = vonNeumann ρ := by
  obtain ⟨U, hU⟩ := exists_conjOp_eq_conjOp W hρ
  rw [hU, vonNeumann_conjOp_unitary]

/-- A map that is conjugation by a unitary or an anti-unitary preserves the entropy. -/
theorem vonNeumann_conjOp {Φ : (E →L[ℂ] E) → E →L[ℂ] E}
    (h : ImplementedByUnitaryOrAntiunitary Φ) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    vonNeumann (Φ ρ) = vonNeumann ρ := by
  rcases h with ⟨W, hW⟩ | ⟨W, hW⟩
  · rw [hW ρ hρ, vonNeumann_conjOp_unitary]
  · rw [hW ρ hρ, vonNeumann_conjOp_antiunitary W hρ]

/-! ## Determinism and reversibility -/

/-- **DR-INFO** for one evolution map: it preserves the von Neumann entropy of every density
operator. -/
def PreservesEntropy (Φ : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ ρ, IsDensity ρ → vonNeumann (Φ ρ) = vonNeumann ρ

/-- **Deterministic and reversible evolution**: every pure state, a state of maximal information,
evolves into a pure state (determinism), and distinct pure states evolve into distinct pure
states, so the initial state can be reconstructed from the final one (reversibility). -/
def IsDetRev (Φ : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  Set.MapsTo Φ {ρ | IsPure ρ} {ρ | IsPure ρ} ∧ Set.InjOn Φ {ρ | IsPure ρ}

variable {Φ : (E →L[ℂ] E) → E →L[ℂ] E}

/-- DR-INFO ⇒ deterministic and reversible: zero entropy characterizes the pure states, and the
entropy of the equal mixture of two pure states determines their transition probability. -/
theorem isDetRev_of_preservesEntropy (hD : ∀ ρ, IsDensity ρ → IsDensity (Φ ρ))
    (hmix : ∀ ρ σ, IsDensity ρ → IsDensity σ → Φ (mix ρ σ) = mix (Φ ρ) (Φ σ))
    (hS : PreservesEntropy Φ) : IsDetRev Φ := by
  obtain ⟨hP, hB⟩ := pure_and_born_of_preserves Φ hD hS hmix
  refine ⟨fun ρ ⟨ψ, hψ, hρ⟩ => hρ ▸ hP ψ hψ, ?_⟩
  rintro _ ⟨ψ, hψ, rfl⟩ _ ⟨ϕ, hϕ, rfl⟩ h
  obtain ⟨ψ', hψ', h₁⟩ := hP ψ hψ
  obtain ⟨ϕ', hϕ', h₂⟩ := hP ϕ hϕ
  have hb := hB ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂
  rw [h₁, h₂] at h
  have h1 : born ψ' ϕ' = 1 := by
    rw [born_of_norm hψ' hϕ', (phaseEq_of_rankOne_self_eq hψ' hϕ' h).norm_inner_left,
      norm_inner_self_eq_one hϕ', one_pow]
  rw [h1, born_of_norm hψ hϕ, eq_comm,
    pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at hb
  exact proj_eq_of_norm_inner_eq_one hψ hϕ hb

/-- **Determinism and reversibility.** For a map `Φ` of the density operators that preserves
equal mixtures, in finite dimension, the following are equivalent: (i) `Φ` is deterministic and
reversible; (ii) `Φ` is a bijection of the pure states; (iii) `Φ` is a bijection of the density
operators; (iv) `Φ` preserves the von Neumann entropy (DR-INFO); (v) `Φ` is conjugation by a
unitary or an anti-unitary. -/
theorem detRev_tfae (hD : ∀ ρ, IsDensity ρ → IsDensity (Φ ρ))
    (hmix : ∀ ρ σ, IsDensity ρ → IsDensity σ → Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) :
    [IsDetRev Φ, BijOnPure Φ, Set.BijOn Φ {ρ | IsDensity ρ} {ρ | IsDensity ρ},
      PreservesEntropy Φ, ImplementedByUnitaryOrAntiunitary Φ].TFAE := by
  have hT := affineOnDensities_of_map_mix hD hmix
  have hK := kadison_tfae hD hT
  tfae_have 1 → 5 := fun h => hT.implemented_of_injOn hD
    (fun ψ hψ => h.1 ⟨ψ, hψ, rfl⟩) h.2
  tfae_have 2 → 1 := fun h => ⟨h.mapsTo, h.injOn⟩
  tfae_have 5 → 2 := (hK.out 3 1).mp
  tfae_have 2 ↔ 3 := hK.out 1 2
  tfae_have 5 → 4 := fun h ρ hρ => vonNeumann_conjOp h hρ
  tfae_have 4 → 1 := isDetRev_of_preservesEntropy hD hmix
  tfae_finish

/-- **DR-INFO is determinism and reversibility.** A map of the density operators that preserves
equal mixtures is deterministic and reversible if and only if it preserves the von Neumann
entropy. -/
theorem isDetRev_iff_preservesEntropy (hD : ∀ ρ, IsDensity ρ → IsDensity (Φ ρ))
    (hmix : ∀ ρ σ, IsDensity ρ → IsDensity σ → Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) :
    IsDetRev Φ ↔ PreservesEntropy Φ :=
  (detRev_tfae hD hmix).out 1 4

/-- The two-parameter form: an evolution `Ψ t₀ t₁` of the brief's kind satisfies DR-INFO if and
only if every `Ψ t₀ t₁`, `t₀ ≤ t₁`, is deterministic and reversible. -/
theorem detRev_iff_drInfo {Ψ : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (hΨ : SchroedingerEvolution.TwoParameter.IsEvolution Ψ) :
    (∀ t₀ t₁, t₀ ≤ t₁ → IsDetRev (Ψ t₀ t₁)) ↔ TwoParameter.DrInfo Ψ :=
  forall₂_congr fun t₀ t₁ => imp_congr_right fun h =>
    isDetRev_iff_preservesEntropy (hΨ.isDensity t₀ t₁ h) fun _ _ hρ hσ =>
      (hΨ.affine t₀ t₁ h).map_mix hρ hσ

end UnitaryEntropy.FurtherResults
