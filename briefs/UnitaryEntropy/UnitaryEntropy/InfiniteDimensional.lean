/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Schrödinger equation is equivalent to information conservation: Hilbert spaces of any dimension.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a complex Hilbert space `E` of any dimension, as in QST:H. Density operators are the
positive trace-class operators of trace one (`IsDensityOperator`,
`ForPhyslib/QuantumMechanics/DensityOperator`), and the von Neumann entropy is
`S(ρ) = tr η(ρ) ∈ [0, ∞]` with `η(x) = -x log x` (`vonNeumannEntropy`,
`ForPhyslib/QuantumMechanics/VonNeumannEntropy`). In finite dimension both agree with the
definitions of `UnitaryEntropy` (`isDensityOperator_iff_isDensity`,
`vonNeumannEntropy_eq_ofReal_vonNeumann`).

Corollary 1 (Born rule is entropy):
* `vonNeumannEntropy_mix_proj`  `S(½ρψ + ½ρϕ) = mixEntropy (born ψ ϕ)`. The mixture satisfies
  `ρ³ = ρ² - ((1 - p)/4) ρ`, so its spectrum lies in `{0, (1 ± √p)/2}`, `η(ρ) = α ρ + β ρ²` for
  suitable `α, β`, and the trace of the right side is computed from rank-one traces;
* `born_eq_iff_vonNeumannEntropy`  `p(ϕ|ψ) = p` iff the mixture has entropy `mixEntropy p`.

Theorem 2, DR-SCEQ ⇒ DR-INFO:
* `schrodinger_conserves_vonNeumannEntropy`  the propagator is an isometry
  (`star_mul_self_of_schrodinger`, dimension-free); `ρF = U ρ U†` is a density operator, the
  reconstructed past `U† ρF U` is `ρ`, and `S(ρF) = S(ρ)`.

Theorem 2, DR-INFO + EVDIFF ⇒ DR-SCEQ:
* `IsDensityOperator.vonNeumannEntropy_eq_zero_iff`  Step 1: pure iff entropy zero;
* `pure_and_born_of_preserves_vonNeumannEntropy`  Steps 1–2: an entropy-preserving map that
  preserves equal mixtures sends pure states to pure states and preserves transition
  probabilities;
* `exists_isWignerMap_of_preserves`  the same, as a Wigner map on unit vectors implementing it;
* `exists_isometry_of_preserves`  with Wigner's theorem
  (`IsWignerMap.exists_linearIsometry_or_conjLinearIsometry`), a linear or conjugate-linear
  isometry implements it;
* `exists_unitary_of_preserves`  a unitary or anti-unitary, if every pure state is the image of a
  pure state;
* `exists_proj_of_past`, `exists_unitary_of_preserves_of_past`  that hypothesis follows from the
  reconstructed past of DR-INFO: every density operator is `Φ σ` for a density operator `σ`;
* `eventually_exists_unitary_of_preserves`  for a family `Φ t` with `Φ t₀ = id`, continuous at
  `t₀`, the anti-unitary case is excluded near `t₀`
  (`eventually_exists_unitary_of_unitary_or_antiunitary`, through
  `⟪x, P_a P_b P_c P_a x⟫ = |⟪a, x⟫|² Δ(a, b, c)` in place of a trace);
* `shift_preserves_not_unitary`  the past cannot be dropped: conjugation by the shift on `ℓ²(ℕ)`
  satisfies the other hypotheses but is induced by no unitary and no anti-unitary;
* `exists_unitary_differentiableAt_apply`  the phases can be chosen so that `t ↦ U t ψ` is
  differentiable at `t₀` for every `ψ`;
* `schrodinger_of_preserves_vonNeumannEntropy`  Step 3 and the whole direction: by
  Banach–Steinhaus the derivative is a bounded operator (`exists_hasDerivAt_apply`), skew-adjoint
  because the `U t` are unitary, so `ψ'(t₀) = (iħ)⁻¹ H ψ(t₀)` with `H` bounded and self-adjoint.
EVDIFF on every density operator forces a bounded Hamiltonian; unbounded ones, differentiable
only on a dense set of states, are not covered.
-/

public import ForMathlib.Analysis.InnerProductSpace.StrongDerivative
public import ForPhyslib.QuantumMechanics.VonNeumannEntropy
public import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
public import UnitaryEntropy

@[expose] public noncomputable section

namespace UnitaryEntropy

open Real InnerProductSpace ComplexOrder QuantumMechanics QuantumMechanics.Wigner Polynomial
open ContinuousLinearMap (posTrace posTraceBasis re_inner_apply_nonneg)
open scoped ENNReal lp Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Corollary 1 -/

omit [CompleteSpace E] in
/-- The diagonal of `|x⟩⟨y|` in a Hilbert basis sums to `⟪y, x⟫`. -/
lemma hasSum_inner_rankOne_apply {ι : Type*} (b : HilbertBasis ι ℂ E) (x y : E) :
    HasSum (fun i => ⟪b i, rankOne ℂ x y (b i)⟫_ℂ) ⟪y, x⟫_ℂ := by
  simpa [rankOne_apply, inner_smul_right] using b.hasSum_inner_mul_inner y x

/-- **Corollary 1** (Born rule is entropy), entropy formula, in any dimension: the equal mixture
of two pure states with transition probability `p` has entropy
`-(1 + √p)/2 log ((1 + √p)/2) - (1 - √p)/2 log ((1 - √p)/2)`. -/
theorem vonNeumannEntropy_mix_proj {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    vonNeumannEntropy (mix (proj ψ) (proj ϕ)) = ENNReal.ofReal (mixEntropy (born ψ ϕ)) := by
  have hD := (isDensityOperator_proj hψ).mix (isDensityOperator_proj hϕ)
  have hsa := hD.isSelfAdjoint
  set ρ := mix (proj ψ) (proj ϕ) with hρ
  have h1 : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have h2 : ⟪ϕ, ϕ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hϕ]; simp
  set q := ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2 with hq
  have hqC : (q : ℂ) = ⟪ψ, ϕ⟫_ℂ * ⟪ϕ, ψ⟫_ℂ := by
    rw [hq, ← inner_conj_symm ϕ ψ, RCLike.mul_conj]; push_cast; rfl
  have hq0 : 0 ≤ q := by positivity
  set a := (1 + √q) / 2
  set b := (1 - √q) / 2
  have hs : √q ^ 2 = q := Real.sq_sqrt hq0
  -- the spectrum lies in `{0, a, b}`
  have hcube : ρ ^ 3 - ρ ^ 2 + algebraMap ℝ (E →L[ℂ] E) ((1 - q) / 4) * ρ = 0 := by
    ext x
    have h := mix_proj_cubic hψ hϕ x
    rw [← hρ] at h
    rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    change ρ (ρ (ρ x)) - ρ (ρ x) + ((1 - q) / 4 : ℝ) • ρ x = 0
    rw [h, ← hqC, ← Complex.coe_smul]
    push_cast
    abel
  have hroot : ∀ x ∈ spectrum ℝ ρ, x = 0 ∨ x = a ∨ x = b := by
    intro x hx
    have := hD.nontrivial
    have hmem := spectrum.subset_polynomial_aeval ρ (X ^ 3 - X ^ 2 + C ((1 - q) / 4) * X)
      ⟨x, hx, rfl⟩
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, hcube,
      spectrum.zero_eq, Set.mem_singleton_iff, eval_add, eval_sub, eval_mul, eval_pow, eval_X,
      eval_C] at hmem
    have : x * ((x - a) * (x - b)) = 0 := by
      simp only [a, b]; linear_combination hmem - (x / 4) * hs
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  -- `η(ρ) = α ρ + β ρ²`
  obtain ⟨α, β, ha, hb⟩ := exists_negMulLog_eq a b
  have hη : cfc negMulLog ρ = (α : ℂ) • ρ + (β : ℂ) • (ρ * ρ) := by
    have : cfc negMulLog ρ = cfc (fun x => α * x + β * (x * x)) ρ := by
      refine cfc_congr fun x hx => ?_
      rcases hroot x hx with h | h | h <;> rw [h]
      · simp
      · rw [ha]; ring
      · rw [hb]; ring
    rw [this, cfc_add (a := ρ) (fun x => α * x) (fun x => β * (x * x)),
      cfc_const_mul α (fun x => x) ρ, cfc_const_mul β (fun x => x * x) ρ,
      cfc_mul (fun x => x) (fun x => x) ρ, cfc_id' ℝ ρ, Complex.coe_smul, Complex.coe_smul]
  -- the diagonal of `η(ρ)` in a Hilbert basis
  set e := posTraceBasis E
  have hρd : HasSum (fun i => ⟪e i, ρ (e i)⟫_ℂ) 1 := by
    have := ((hasSum_inner_rankOne_apply e ψ ψ).mul_left 2⁻¹).add
      ((hasSum_inner_rankOne_apply e ϕ ϕ).mul_left 2⁻¹)
    convert this using 1
    · ext i
      simp [ρ, mix, proj, inner_add_right, inner_smul_right]
    · rw [h1, h2]; norm_num
  have hρ2d : HasSum (fun i => ⟪e i, (ρ * ρ) (e i)⟫_ℂ) (((1 + q) / 2 : ℝ) : ℂ) := by
    have := ((((hasSum_inner_rankOne_apply e ψ ψ).add (hasSum_inner_rankOne_apply e ϕ ϕ)).add
      ((hasSum_inner_rankOne_apply e ψ ϕ).mul_left ⟪ψ, ϕ⟫_ℂ)).add
      ((hasSum_inner_rankOne_apply e ϕ ψ).mul_left ⟪ϕ, ψ⟫_ℂ)).mul_left 4⁻¹
    convert this using 1
    · ext i
      rw [hρ, mix_proj_sq ψ ϕ hψ hϕ]
      simp [proj, inner_add_right, inner_smul_right]
      ring
    · rw [h1, h2]; push_cast; rw [hqC]; ring
  have hd : HasSum (fun i => ⟪e i, cfc negMulLog ρ (e i)⟫_ℂ)
      ((α + β * ((1 + q) / 2) : ℝ) : ℂ) := by
    have := (hρd.mul_left (α : ℂ)).add (hρ2d.mul_left (β : ℂ))
    convert this using 1
    · ext i
      rw [hη]
      simp only [add_apply, smul_apply, inner_add_right, inner_smul_right]
    · push_cast; ring
  have hd' := Complex.hasSum_re hd
  simp only [Complex.ofReal_re] at hd'
  rw [vonNeumannEntropy, posTrace, ← ENNReal.ofReal_tsum_of_nonneg
    (fun _ => re_inner_apply_nonneg hD.cfc_negMulLog_nonneg _) hd'.summable, hd'.tsum_eq,
    born_of_norm hψ hϕ, mixEntropy_eq, ← hq]
  congr 1
  change _ = negMulLog a + negMulLog b
  rw [ha, hb]
  simp only [a, b]
  linear_combination (-β / 2) * hs

lemma mixEntropy_nonneg {p : ℝ} (hp : p ∈ Set.Icc 0 1) : 0 ≤ mixEntropy p := by
  have h0 := Real.sqrt_nonneg p
  have h1 : √p ≤ 1 := Real.sqrt_le_one.mpr hp.2
  exact binEntropy_nonneg (by linarith) (by linarith)

/-- **Corollary 1** (Born rule is entropy), in any dimension: the transition probability of two
pure states is determined by the entropy of their equal mixture, and vice versa. -/
theorem born_eq_iff_vonNeumannEntropy {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) {p : ℝ}
    (hp : p ∈ Set.Icc 0 1) :
    born ψ ϕ = p ↔ vonNeumannEntropy (mix (proj ψ) (proj ϕ)) = ENNReal.ofReal (mixEntropy p) := by
  rw [vonNeumannEntropy_mix_proj hψ hϕ, ENNReal.ofReal_eq_ofReal_iff
    (mixEntropy_nonneg (born_mem_Icc hψ hϕ)) (mixEntropy_nonneg hp)]
  exact (mixEntropy_strictAntiOn.injOn.eq_iff (born_mem_Icc hψ hϕ) hp).symm

/-! ## Theorem 2 -/

/-- **Theorem 2** (⇒), DR-INFO, in any dimension: along a Schrödinger evolution the future
ensemble `ρF = U ρ U†` is a density operator, the reconstructed past `U† ρF U` is the initial
`ρ`, and both have the entropy of `ρ`. Only `U† U = 1` is used. -/
theorem schrodinger_conserves_vonNeumannEntropy {ħ : ℝ} {H U : ℝ → E →L[ℂ] E} {t₀ : ℝ}
    (hH : ∀ t, IsSelfAdjoint (H t))
    (hU : ∀ t, HasDerivAt U ((Complex.I * ħ)⁻¹ • (H t * U t)) t) (h₀ : U t₀ = 1)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (t : ℝ) :
    IsDensityOperator (U t * ρ * star (U t)) ∧ star (U t) * (U t * ρ * star (U t)) * U t = ρ ∧
      vonNeumannEntropy (U t * ρ * star (U t)) = vonNeumannEntropy ρ := by
  have hu := star_mul_self_of_schrodinger hH hU h₀ t
  refine ⟨hρ.conj hu, ?_, hρ.vonNeumannEntropy_conj hu⟩
  calc star (U t) * (U t * ρ * star (U t)) * U t
      = (star (U t) * U t) * ρ * (star (U t) * U t) := by noncomm_ring
    _ = ρ := by rw [hu, one_mul, mul_one]

/-- **Theorem 2** (⇐), Steps 1 and 2, in any dimension: a map on density operators that preserves
the entropy and equal mixtures sends pure states to pure states and preserves their transition
probabilities. -/
theorem pure_and_born_of_preserves_vonNeumannEntropy (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ))
    (hS : ∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ ρ) = vonNeumannEntropy ρ)
    (hmix : ∀ ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) :
    (∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ Φ (proj ψ) = proj ψ') ∧
    ∀ ψ ϕ ψ' ϕ' : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 → ‖ψ'‖ = 1 → ‖ϕ'‖ = 1 →
      Φ (proj ψ) = proj ψ' → Φ (proj ϕ) = proj ϕ' → born ψ' ϕ' = born ψ ϕ := by
  refine ⟨fun ψ hψ => (hD _ (isDensityOperator_proj hψ)).vonNeumannEntropy_eq_zero_iff.mp ?_, ?_⟩
  · rw [hS _ (isDensityOperator_proj hψ), vonNeumannEntropy_proj hψ]
  · intro ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂
    refine (born_eq_iff_vonNeumannEntropy hψ' hϕ' (born_mem_Icc hψ hϕ)).mpr ?_
    rw [← h₁, ← h₂, ← hmix _ _ (isDensityOperator_proj hψ) (isDensityOperator_proj hϕ),
      hS _ ((isDensityOperator_proj hψ).mix (isDensityOperator_proj hϕ)),
      vonNeumannEntropy_mix_proj hψ hϕ]

/-- **Theorem 2** (⇐), Steps 1 and 2 up to Wigner's theorem, in any dimension: the evolution of
pure states is implemented by a map on unit vectors that preserves `|⟪ψ, ϕ⟫|`. -/
theorem exists_isWignerMap_of_preserves (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ))
    (hS : ∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ ρ) = vonNeumannEntropy ρ)
    (hmix : ∀ ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) :
    ∃ f : E → E, IsWignerMap f ∧ ∀ ψ : E, ‖ψ‖ = 1 → ‖f ψ‖ = 1 ∧ Φ (proj ψ) = proj (f ψ) := by
  classical
  obtain ⟨hP, hB⟩ := pure_and_born_of_preserves_vonNeumannEntropy Φ hD hS hmix
  let f : E → E := fun ψ => if h : ‖ψ‖ = 1 then (hP ψ h).choose else 0
  have hf : ∀ ψ (h : ‖ψ‖ = 1), ‖f ψ‖ = 1 ∧ Φ (proj ψ) = proj (f ψ) := fun ψ h => by
    simpa [f, h] using (hP ψ h).choose_spec
  refine ⟨f, fun v w hv hw => ?_, hf⟩
  have h := hB v w (f v) (f w) hv hw (hf v hv).1 (hf w hw).1 (hf v hv).2 (hf w hw).2
  rw [born_of_norm (hf v hv).1 (hf w hw).1, born_of_norm hv hw] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- **Theorem 2** (⇐), Steps 1 and 2 with Wigner's theorem, in any dimension: the evolution of
pure states is implemented by a linear or a conjugate-linear isometry. -/
theorem exists_isometry_of_preserves (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ))
    (hS : ∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ ρ) = vonNeumannEntropy ρ)
    (hmix : ∀ ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) :
    (∃ U : E →ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ)) ∨
      ∃ U : E →ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ) := by
  obtain ⟨f, hf, hfΦ⟩ := exists_isWignerMap_of_preserves Φ hD hS hmix
  rcases hf.exists_linearIsometry_or_conjLinearIsometry with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun ψ hψ => (hfΦ ψ hψ).2.trans (hU ψ hψ).rankOne_self⟩
  · exact Or.inr ⟨U, fun ψ hψ => (hfΦ ψ hψ).2.trans (hU ψ hψ).rankOne_self⟩

/-- **Theorem 2** (⇐), Steps 1 and 2 with Wigner's theorem, in any dimension: if moreover every
pure state is the image of a pure state, the evolution of pure states is implemented by a unitary
or an anti-unitary. In finite dimension the extra hypothesis is automatic; in infinite dimension
it is needed, see `shift_preserves_not_unitary`. -/
theorem exists_unitary_of_preserves (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ))
    (hS : ∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ ρ) = vonNeumannEntropy ρ)
    (hmix : ∀ ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      Φ (mix ρ σ) = mix (Φ ρ) (Φ σ))
    (hsurj : ∀ ϕ : E, ‖ϕ‖ = 1 → ∃ ψ : E, ‖ψ‖ = 1 ∧ Φ (proj ψ) = proj ϕ) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ)) ∨
      ∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ) := by
  obtain ⟨f, hf, hfΦ⟩ := exists_isWignerMap_of_preserves Φ hD hS hmix
  have hs : ∀ w : E, ‖w‖ = 1 → ∃ v, ‖v‖ = 1 ∧ PhaseEq (f v) w := fun w hw => by
    obtain ⟨v, hv, h⟩ := hsurj w hw
    exact ⟨v, hv, phaseEq_of_rankOne_self_eq (hfΦ v hv).1 hw ((hfΦ v hv).2.symm.trans h)⟩
  rcases hf.exists_unitary_or_antiunitary_of_surjective hs with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun ψ hψ => (hfΦ ψ hψ).2.trans (hU ψ hψ).rankOne_self⟩
  · exact Or.inr ⟨U, fun ψ hψ => (hfΦ ψ hψ).2.trans (hU ψ hψ).rankOne_self⟩

/-- Step 1 with the reconstructed past of DR-INFO: if every density operator is the evolution of
a past density operator, then every pure state is the evolution of a pure state, because its past
has entropy zero. -/
theorem exists_proj_of_past (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hS : ∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ ρ) = vonNeumannEntropy ρ)
    (hpast : ∀ ρ, IsDensityOperator ρ → ∃ σ, IsDensityOperator σ ∧ Φ σ = ρ) :
    ∀ ϕ : E, ‖ϕ‖ = 1 → ∃ ψ : E, ‖ψ‖ = 1 ∧ Φ (proj ψ) = proj ϕ := by
  intro ϕ hϕ
  obtain ⟨σ, hσ, h⟩ := hpast _ (isDensityOperator_proj hϕ)
  obtain ⟨ψ, hψ, rfl⟩ := hσ.vonNeumannEntropy_eq_zero_iff.mp <| by
    rw [← hS σ hσ, h, vonNeumannEntropy_proj hϕ]
  exact ⟨ψ, hψ, h⟩

/-- **Theorem 2** (⇐), Steps 1 and 2 with Wigner's theorem, in any dimension, with DR-INFO in
full: the evolution preserves the entropy, and every density operator `ρ` has a reconstructed past
`σ` with `Φ σ = ρ` (then `S(σ) = S(ρ)` by the first condition). The evolution of pure states is
implemented by a unitary or an anti-unitary. -/
theorem exists_unitary_of_preserves_of_past (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ))
    (hS : ∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ ρ) = vonNeumannEntropy ρ)
    (hpast : ∀ ρ, IsDensityOperator ρ → ∃ σ, IsDensityOperator σ ∧ Φ σ = ρ)
    (hmix : ∀ ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ)) ∨
      ∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ) :=
  exists_unitary_of_preserves Φ hD hS hmix (exists_proj_of_past Φ hS hpast)

/-- **Theorem 2** (⇐), Steps 1 and 2 in any dimension, with the anti-unitary case excluded: if
moreover `Φ t₀` is the identity and `t ↦ Φ t ρ` is continuous at `t₀` in operator norm, then
near `t₀` the evolution of pure states is implemented by unitaries. -/
theorem eventually_exists_unitary_of_preserves {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {t₀ : ℝ}
    (hD : ∀ t ρ, IsDensityOperator ρ → IsDensityOperator (Φ t ρ))
    (hS : ∀ t ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ t ρ) = vonNeumannEntropy ρ)
    (hpast : ∀ t ρ, IsDensityOperator ρ → ∃ σ, IsDensityOperator σ ∧ Φ t σ = ρ)
    (hmix : ∀ t ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      Φ t (mix ρ σ) = mix (Φ t ρ) (Φ t σ))
    (h₀ : ∀ ρ, IsDensityOperator ρ → Φ t₀ ρ = ρ)
    (hc : ∀ ρ, IsDensityOperator ρ → ContinuousAt (fun t => Φ t ρ) t₀) :
    ∀ᶠ t in 𝓝 t₀, ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (U ψ) :=
  eventually_exists_unitary_of_unitary_or_antiunitary
    (fun t => exists_unitary_of_preserves_of_past (Φ t) (hD t) (hS t) (hpast t) (hmix t))
    (fun _ hψ => h₀ _ (isDensityOperator_proj hψ)) (fun _ hψ => hc _ (isDensityOperator_proj hψ))

/-- **Theorem 2** (⇐), DR-INFO + EVDIFF ⇒ DR-SCEQ, in any dimension. Let `Φ t` map density
operators to density operators, preserve the entropy and equal mixtures, give every density
operator a reconstructed past, be the identity at `t₀`, and be differentiable at `t₀` on each
density operator. Then near `t₀`, `Φ t` acts on pure states through unitaries `U t` with
`U t₀ = 1`, and each state `ψ(t) = U t ψ` solves the Schrödinger equation
`ψ'(t₀) = (iħ)⁻¹ H ψ(t₀)` for one bounded self-adjoint `H`. -/
theorem schrodinger_of_preserves_vonNeumannEntropy {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    {t₀ ħ : ℝ}
    (hD : ∀ t ρ, IsDensityOperator ρ → IsDensityOperator (Φ t ρ))
    (hS : ∀ t ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ t ρ) = vonNeumannEntropy ρ)
    (hpast : ∀ t ρ, IsDensityOperator ρ → ∃ σ, IsDensityOperator σ ∧ Φ t σ = ρ)
    (hmix : ∀ t ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      Φ t (mix ρ σ) = mix (Φ t ρ) (Φ t σ))
    (h₀ : ∀ ρ, IsDensityOperator ρ → Φ t₀ ρ = ρ)
    (hdiff : ∀ ρ, IsDensityOperator ρ → DifferentiableAt ℝ (fun t => Φ t ρ) t₀) (hħ : ħ ≠ 0) :
    ∃ (U : ℝ → E →L[ℂ] E) (H : E →L[ℂ] E), IsSelfAdjoint H ∧
      (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧ U t₀ = 1 ∧
      (∀ᶠ t in 𝓝 t₀, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (U t ψ)) ∧
      ∀ ψ : E, HasDerivAt (fun t => U t ψ) ((Complex.I * ħ)⁻¹ • H (U t₀ ψ)) t₀ := by
  obtain ⟨U, hU, hU₀, hΦ, hUd⟩ := exists_unitary_differentiableAt_apply
    (eventually_exists_unitary_of_preserves hD hS hpast hmix h₀ fun ρ hρ =>
      (hdiff ρ hρ).continuousAt)
    (fun _ hψ => h₀ _ (isDensityOperator_proj hψ))
    (fun _ hψ => hdiff _ (isDensityOperator_proj hψ))
  obtain ⟨A, hA⟩ := ContinuousLinearMap.exists_hasDerivAt_apply hUd
  obtain ⟨H, hH, rfl⟩ := exists_hamiltonian_of_star_eq_neg
    (star_eq_neg_of_hasDerivAt_apply_of_mem_unitary hU hU₀ hA) hħ
  refine ⟨U, H, hH, hU, hU₀, hΦ, fun ψ => ?_⟩
  simpa [hU₀] using hA ψ

/-! ## The shift -/

section Shift

/-- The unilateral shift `eₙ ↦ eₙ₊₁` on `ℓ²(ℕ)`, as an isometry. -/
def shiftIsometry : ℓ²(ℕ, ℂ) →ₗᵢ[ℂ] ℓ²(ℕ, ℂ) :=
  (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)).isometryOfOrthonormal
    ((default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)).orthonormal.comp _ Nat.succ_injective)

/-- The unilateral shift `eₙ ↦ eₙ₊₁` on `ℓ²(ℕ)`. -/
def shift : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  shiftIsometry.toContinuousLinearMap

lemma shift_apply_basis (k : ℕ) :
    shift ((default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)) k) =
      (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)) (k + 1) :=
  HilbertBasis.isometryOfOrthonormal_apply_basis _
    ((default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)).orthonormal.comp _ Nat.succ_injective) k

lemma star_shift_mul_shift : star shift * shift = 1 := by
  ext1 x
  refine ext_inner_left ℂ fun z => ?_
  change ⟪z, ContinuousLinearMap.adjoint shift (shift x)⟫_ℂ = ⟪z, x⟫_ℂ
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact shiftIsometry.inner_map_map z x

lemma norm_shift (x : ℓ²(ℕ, ℂ)) : ‖shift x‖ = ‖x‖ :=
  LinearIsometry.norm_map _ x

/-- The first basis vector is orthogonal to the range of the shift. -/
lemma inner_basis_zero_shift (x : ℓ²(ℕ, ℂ)) :
    ⟪(default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)) 0, shift x⟫_ℂ = 0 := by
  set b : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ) := default
  have h0 : (ContinuousLinearMap.adjoint shift) (b 0) = 0 := b.ext_inner fun k => by
    rw [ContinuousLinearMap.adjoint_inner_right, inner_zero_right, shift_apply_basis]
    exact b.orthonormal.2 (Nat.succ_ne_zero k)
  rw [← ContinuousLinearMap.adjoint_inner_left, h0, inner_zero_left]

lemma shift_mul_proj_mul_star (ψ : ℓ²(ℕ, ℂ)) : shift * proj ψ * star shift = proj (shift ψ) := by
  ext1 x
  change shift (rankOne ℂ ψ ψ (ContinuousLinearMap.adjoint shift x)) =
    rankOne ℂ (shift ψ) (shift ψ) x
  rw [rankOne_apply, rankOne_apply, map_smul, ContinuousLinearMap.adjoint_inner_right]

/-- **The extra hypothesis of `exists_unitary_of_preserves` is needed in infinite dimension.**
Conjugation by the shift on `ℓ²(ℕ)` maps density operators to density operators and preserves the
entropy and equal mixtures, but it sends no pure state to `|e₀⟩⟨e₀|`, so its action on pure
states is induced by no unitary and by no anti-unitary. -/
theorem shift_preserves_not_unitary :
    ∃ Φ : (ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) → ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
      (∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ)) ∧
      (∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ ρ) = vonNeumannEntropy ρ) ∧
      (∀ ρ σ, IsDensityOperator ρ → IsDensityOperator σ → Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) ∧
      (¬ ∃ U : ℓ²(ℕ, ℂ) ≃ₗᵢ[ℂ] ℓ²(ℕ, ℂ), ∀ ψ, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ)) ∧
      ¬ ∃ U : ℓ²(ℕ, ℂ) ≃ₗᵢ⋆[ℂ] ℓ²(ℕ, ℂ), ∀ ψ, ‖ψ‖ = 1 → Φ (proj ψ) = proj (U ψ) := by
  set e₀ := (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ)) 0
  have he₀ : ‖e₀‖ = 1 := HilbertBasis.orthonormal _ |>.1 0
  have hmiss : ∀ ψ : ℓ²(ℕ, ℂ), ‖ψ‖ = 1 → proj (shift ψ) ≠ proj e₀ := fun ψ hψ h => by
    obtain ⟨c, hc, hce⟩ := phaseEq_of_rankOne_self_eq ((norm_shift ψ).trans hψ) he₀ h
    have h0 := inner_basis_zero_shift ψ
    rw [hce, inner_smul_right, inner_self_eq_norm_sq_to_K, he₀] at h0
    norm_num at h0
    rw [h0, norm_zero] at hc
    exact zero_ne_one hc
  refine ⟨fun ρ => shift * ρ * star shift, fun ρ hρ => hρ.conj star_shift_mul_shift,
    fun ρ hρ => hρ.vonNeumannEntropy_conj star_shift_mul_shift, fun ρ σ _ _ => ?_, ?_, ?_⟩
  · change shift * ((2⁻¹ : ℂ) • ρ + (2⁻¹ : ℂ) • σ) * star shift =
      (2⁻¹ : ℂ) • (shift * ρ * star shift) + (2⁻¹ : ℂ) • (shift * σ * star shift)
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]
  · rintro ⟨U, hU⟩
    have hψ : ‖U.symm e₀‖ = 1 := (U.symm.norm_map e₀).trans he₀
    refine hmiss _ hψ ((shift_mul_proj_mul_star _).symm.trans ((hU _ hψ).trans ?_))
    rw [U.apply_symm_apply]
  · rintro ⟨U, hU⟩
    have hψ : ‖U.symm e₀‖ = 1 := (U.symm.norm_map e₀).trans he₀
    refine hmiss _ hψ ((shift_mul_proj_mul_star _).symm.trans ((hU _ hψ).trans ?_))
    rw [U.apply_symm_apply]

end Shift

/-! ## Finite dimension -/

/-- In finite dimension, the entropy in `[0, ∞]` is the eigenvalue sum `vonNeumann`. -/
theorem vonNeumannEntropy_eq_ofReal_vonNeumann [FiniteDimensional ℂ E] {ρ : E →L[ℂ] E}
    (hρ : IsDensity ρ) : vonNeumannEntropy ρ = ENNReal.ofReal (vonNeumann ρ) := by
  have hD := isDensityOperator_iff_isDensity.mpr hρ
  have hsym := hρ.isPositive.isSymmetric
  have hsa := hD.isSelfAdjoint
  set e := hsym.eigenvectorBasis rfl
  rw [vonNeumannEntropy, ContinuousLinearMap.posTrace_eq_ofReal_re_trace hD.cfc_negMulLog_nonneg,
    vonNeumann_eq_sum hsym, LinearMap.trace_eq_sum_inner _ e, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.cfc_apply_of_apply_eq_smul negMulLog
    (hsym.apply_eigenvectorBasis rfl i), inner_smul_right, e.inner_eq_one]
  simp

end UnitaryEntropy
