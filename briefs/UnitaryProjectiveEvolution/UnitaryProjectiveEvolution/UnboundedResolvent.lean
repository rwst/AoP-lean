/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Unitary evolution as infinitesimal projective processes: the resolvent of an unbounded generator.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

The remark "Unbounded generators" of Sec. 5: "Direct use of the resolvent of an unbounded
generator still gives a completely positive trace-preserving map and the resolvent exponential
formula. The bounded spectral truncations are used only to ensure that the total probability of
the selected state sequence tends to one for every Hilbert-space state, including states outside
the domain of the Hamiltonian."

Setting: as in `InfiniteDimensional`. For a strongly continuous unitary group `V`, whose generator
may be unbounded, `Ψ τ = V.resolvent τ` is the Laplace integral `∫₀^∞ e^{-s} T (τ s) ds` taken
pointwise on vectors (`ForPhyslib/QuantumMechanics/VonNeumannResolvent/Strong`); no cutoff is used.

* `isStateAdaptiveProjective_resolvent`  Proposition 2 for `Ψ τ`, `τ > 0`: it keeps density
  operators (positive and trace preserving), is affine, and is the projective measurement on an
  eigenbasis of `Ψ τ ρ`.
* `exists_completelyPositiveMap_resolvent`  `Ψ τ` is completely positive and trace preserving.
  A matrix of operators is positive exactly when its block operator on `Eᵏ` is, so complete
  positivity is a family of pointwise inequalities, which the pointwise integral keeps.
* `tendsto_resolvent_iterate`  the resolvent exponential formula `(Ψ (t / n))ⁿ ρ → V t ρ V t†` in
  trace norm, for every density operator. On the core of density operators supported in a spectral
  subspace `P_m`, `Ψ τ` agrees with the resolvent of the bounded group `W_m` and keeps the core, so
  the bounded formula applies; trace-norm contraction extends it to every density operator.
* `infinitesimal_resolvent`  eq. (26) on the same core.
* `perfectPrediction_resolvent`  perfect prediction from every pure state `|ψ⟩⟨ψ|` whose orbit is
  Lipschitz, `‖V u ψ - ψ‖ ≤ C |u|`: following the largest outcome, the branch probability is at
  least `1 - 8 C² t² / n`, and the final state tends to `V t |ψ⟩⟨ψ| V t†`.
* `perfectPrediction_resolvent_of_mem_domain`  so prediction is perfect on the domain of the
  Hamiltonian, with `C = ‖H ψ‖`.

The family `Ψ` is a projective limit of the unitary evolution in every respect except that
`PerfectPrediction` asks for every pure state; whether prediction fails outside the domain is not
settled here, and the brief does not claim it.
-/

public import ForPhyslib.QuantumMechanics.VonNeumannResolvent.Strong
public import UnitaryProjectiveEvolution.InfiniteDimensional

@[expose] public noncomputable section

namespace UnitaryProjectiveEvolution.InfiniteDimensional

open Filter Set QuantumMechanics QuantumMechanics.Wigner ProbabilisticTheory.QuantumMechanics
  ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure
open scoped Topology InnerProductSpace ComplexOrder ENNReal CStarAlgebra

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Proposition 2 and complete positivity -/

/-- **Proposition 2** for the resolvent of a possibly unbounded generator: for `τ > 0`, `Ψ τ` is
state-adaptive projective, with the projectors onto an eigenbasis of `Ψ τ ρ`. -/
theorem isStateAdaptiveProjective_resolvent (V : StronglyContinuousUnitaryGroup E) {τ : ℝ}
    (hτ : 0 < τ) : IsStateAdaptiveProjective (V.resolvent τ) where
  isDensityOperator _ hρ := V.isDensityOperator_resolvent τ hρ
  affine := affineOnDensityOperators_of_linearMap (V.resolvent τ).toLinearMap
  projective ρ hρ := by
    obtain ⟨w, b, -, -, -, -, -, hsum⟩ := V.exists_hilbertBasis_resolvent hτ hρ
    exact ⟨w, fun i => proj (b i), isProjectiveDecomposition_proj b, hsum⟩

lemma isDensityOperator_resolvent_iterate (V : StronglyContinuousUnitaryGroup E) (τ : ℝ) (n : ℕ)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) : IsDensityOperator ((V.resolvent τ)^[n] ρ) :=
  isDensityOperator_iterate (fun _ hσ => V.isDensityOperator_resolvent τ hσ) n hρ

/-- **The resolvent of an unbounded generator is completely positive and trace preserving**: `Ψ τ`
is a completely positive map that keeps density operators. -/
theorem exists_completelyPositiveMap_resolvent (V : StronglyContinuousUnitaryGroup E) (τ : ℝ) :
    ∃ Φ : (E →L[ℂ] E) →CP (E →L[ℂ] E), ⇑Φ = V.resolvent τ ∧
      ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ) :=
  ⟨V.resolventCP τ, rfl, fun _ hρ => V.isDensityOperator_resolvent τ hρ⟩

/-! ## The core of bounded spectral support -/

section Core

variable (μS : WOTSpectralMeasure ℝ E)

lemma spectralCutoffProj_mul_cutoffGroup (m M t : ℝ) :
    spectralCutoffProj μS m * cutoffGroup μS M t =
      cutoffGroup μS M t * spectralCutoffProj μS m := by
  rw [spectralCutoffProj_eq, cutoffGroup_apply, cutoffIntegral,
    ← ContinuousLinearMapWOT.toCLM_mul, ← ContinuousLinearMapWOT.toCLM_mul, ← boundedIntegral_mul,
    ← boundedIntegral_mul]
  exact congrArg _ (boundedIntegral_congr μS _ _ _ _ fun x => mul_comm _ _)

variable {V : StronglyContinuousUnitaryGroup E} (hV : ∀ t, V t = expGroup μS t)
include hV

/-- On an operator supported in `P_m`, conjugation by `V` is conjugation by the bounded group
`W_m`. -/
lemma conj_eq_unitaryChannel {m : ℝ} {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ)
    (hP : spectralCutoffProj μS m * ρ = ρ) (s : ℝ) :
    V.conj s ρ = unitaryChannel (cutoffGroup μS m) s ρ := by
  have hPs := isStarProjection_spectralCutoffProj μS m
  have hP' : ρ * spectralCutoffProj μS m = ρ := by
    have h := congrArg star hP
    rwa [star_mul, hρ.star_eq, hPs.isSelfAdjoint.star_eq] at h
  have hρPP : spectralCutoffProj μS m * ρ * spectralCutoffProj μS m = ρ := by rw [hP, hP']
  have hW := expGroup_mul_spectralCutoffProj μS m s
  have hW' : spectralCutoffProj μS m * star (expGroup μS s) =
      spectralCutoffProj μS m * star (cutoffGroup μS m s) := by
    have h := congrArg star hW
    rwa [star_mul, star_mul, hPs.isSelfAdjoint.star_eq] at h
  calc V.conj s ρ = expGroup μS s * spectralCutoffProj μS m * ρ *
        (spectralCutoffProj μS m * star (expGroup μS s)) := by
        rw [StronglyContinuousUnitaryGroup.conj, hV]
        conv_lhs => rw [← hρPP]
        simp only [mul_assoc]
    _ = cutoffGroup μS m s * spectralCutoffProj μS m * ρ *
        (spectralCutoffProj μS m * star (cutoffGroup μS m s)) := by rw [hW, hW']
    _ = unitaryChannel (cutoffGroup μS m) s ρ := by
        rw [unitaryChannel]
        conv_rhs => rw [← hρPP]
        simp only [mul_assoc]

/-- On an operator supported in `P_m`, the resolvent is that of the bounded group `W_m`. -/
lemma resolvent_eq_laplaceResolvent_cutoffGroup {m : ℝ} {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ)
    (hP : spectralCutoffProj μS m * ρ = ρ) (τ : ℝ) :
    V.resolvent τ ρ = laplaceResolvent (cutoffGroup μS m) τ ρ :=
  V.resolvent_eq_laplaceResolvent _ (conj_eq_unitaryChannel μS hV hρ hP) τ

omit hV in
/-- The resolvent of `W_m` keeps the operators supported in `P_m`. -/
lemma mul_laplaceResolvent_cutoffGroup {m : ℝ} {ρ : E →L[ℂ] E}
    (hP : spectralCutoffProj μS m * ρ = ρ) (τ : ℝ) :
    spectralCutoffProj μS m * laplaceResolvent (cutoffGroup μS m) τ ρ =
      laplaceResolvent (cutoffGroup μS m) τ ρ := by
  set P := spectralCutoffProj μS m
  rw [laplaceResolvent_apply]
  change ContinuousLinearMap.mul ℂ (E →L[ℂ] E) P (∫ s in Ioi (0 : ℝ), _) = _
  rw [← (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) P).integral_comp_comm
    (integrableOn_laplaceKernel_apply _ τ ρ)]
  congr 1
  funext s
  rw [ContinuousLinearMap.map_smul_of_tower]
  change Real.exp (-s) • (P * unitaryChannel _ _ ρ) = _
  rw [unitaryChannel, ← mul_assoc, ← mul_assoc, spectralCutoffProj_mul_cutoffGroup,
    mul_assoc _ P ρ, hP]

/-- On the core, every power of the resolvent is the power of the resolvent of `W_m`. -/
lemma resolvent_iterate_eq {m : ℝ} {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ)
    (hP : spectralCutoffProj μS m * ρ = ρ) (τ : ℝ) (n : ℕ) :
    (V.resolvent τ)^[n] ρ = (laplaceResolvent (cutoffGroup μS m) τ)^[n] ρ := by
  have key : ∀ n, (V.resolvent τ)^[n] ρ = (laplaceResolvent (cutoffGroup μS m) τ)^[n] ρ ∧
      IsSelfAdjoint ((laplaceResolvent (cutoffGroup μS m) τ)^[n] ρ) ∧
      spectralCutoffProj μS m * (laplaceResolvent (cutoffGroup μS m) τ)^[n] ρ =
        (laplaceResolvent (cutoffGroup μS m) τ)^[n] ρ := by
    intro n
    induction n with
    | zero => exact ⟨rfl, hρ, hP⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [Function.iterate_succ_apply']
      refine ⟨by rw [h1, resolvent_eq_laplaceResolvent_cutoffGroup μS hV h2 h3],
        isSelfAdjoint_laplaceResolvent _ τ h2, mul_laplaceResolvent_cutoffGroup μS h3 τ⟩
  exact (key n).1

end Core

/-! ## The resolvent exponential formula -/

/-- Convergence of contractions on a dense set of density operators extends to all of them. -/
lemma tendsto_traceENorm_of_dense {F : ℕ → (E →L[ℂ] E) → E →L[ℂ] E}
    {G : (E →L[ℂ] E) → E →L[ℂ] E}
    (hF : ∀ n ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      traceENorm (F n ρ - F n σ) ≤ traceENorm (ρ - σ))
    (hG : ∀ ρ σ, traceENorm (G ρ - G σ) ≤ traceENorm (ρ - σ)) {D : Set (E →L[ℂ] E)}
    (hD : ∀ ρ, IsDensityOperator ρ → ∀ ε : ℝ, 0 < ε →
      ∃ σ ∈ D, IsDensityOperator σ ∧ traceENorm (ρ - σ) < ENNReal.ofReal ε)
    (h : ∀ σ ∈ D, Tendsto (fun n => traceENorm (F n σ - G σ)) atTop (𝓝 0))
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    Tendsto (fun n => traceENorm (F n ρ - G ρ)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨r, -, hr, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hr0 : 0 < r := ENNReal.ofReal_pos.mp hr
  obtain ⟨σ, hσD, hσ, hd⟩ := hD ρ hρ (r / 3) (by positivity)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (h σ hσD) (ENNReal.ofReal (r / 3))
    (ENNReal.ofReal_pos.mpr (by positivity))] with n hn
  calc traceENorm (F n ρ - G ρ) ≤ traceENorm (F n ρ - F n σ) + traceENorm (F n σ - G σ) +
        traceENorm (G σ - G ρ) :=
        (traceENorm_sub_le _ (G σ) _).trans (add_le_add_left (traceENorm_sub_le _ _ _) _)
    _ ≤ ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3) + ENNReal.ofReal (r / 3) := by
        gcongr
        · exact (hF n ρ σ hρ hσ).trans hd.le
        · exact (hG σ ρ).trans (by rw [traceENorm_sub_comm]; exact hd.le)
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ε := hrε.le

/-- **The resolvent exponential formula** for a possibly unbounded generator:
`(Ψ (t / n))ⁿ ρ → V t ρ V t†` in trace norm for every density operator, without cutoffs. -/
theorem tendsto_resolvent_iterate (V : StronglyContinuousUnitaryGroup E) {t : ℝ} (ht : 0 < t)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    Tendsto (fun n : ℕ => traceENorm ((V.resolvent (t / n))^[n] ρ - V t * ρ * star (V t)))
      atTop (𝓝 0) := by
  obtain ⟨μS, hμS⟩ := V.exists_expIntegral
  have hV : ∀ t, V t = expGroup μS t := hμS
  set D := {σ | IsDensityOperator σ ∧ ∃ m, spectralCutoffProj μS m * σ = σ}
  have hF : ∀ (n : ℕ) ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
      traceENorm ((V.resolvent (t / n))^[n] ρ - (V.resolvent (t / n))^[n] σ) ≤
        traceENorm (ρ - σ) := fun n ρ σ hρ hσ =>
    ((affineOnDensityOperators_of_linearMap (V.resolvent (t / n)).toLinearMap).iterate
      (fun _ h => V.isDensityOperator_resolvent _ h) n).traceENorm_sub_le
      (fun _ h => isDensityOperator_resolvent_iterate V _ n h) hρ hσ
  have hG : ∀ ρ σ, traceENorm (V.conj t ρ - V.conj t σ) ≤ traceENorm (ρ - σ) := fun ρ σ => by
    rw [V.conj_sub]
    exact V.traceENorm_conj_le t _
  have hD : ∀ ρ, IsDensityOperator ρ → ∀ ε : ℝ, 0 < ε →
      ∃ σ ∈ D, IsDensityOperator σ ∧ traceENorm (ρ - σ) < ENNReal.ofReal ε := fun ρ hρ ε hε => by
    obtain ⟨m, σ, hσ, hPσ, hd⟩ := exists_isDensityOperator_mul_eq
      (isStarProjection_spectralCutoffProj μS) (tendsto_spectralCutoffProj_apply μS) hρ hε
    exact ⟨σ, ⟨hσ, m, hPσ⟩, hσ, hd⟩
  have hcore : ∀ σ ∈ D, Tendsto (fun n : ℕ => traceENorm ((V.resolvent (t / n))^[n] σ -
      V.conj t σ)) atTop (𝓝 0) := by
    rintro σ ⟨hσ, m, hm⟩
    have h := tendsto_laplaceResolvent_iterate (cutoffGroup μS m) ht.le hσ
    rw [← conj_eq_unitaryChannel μS hV hσ.isSelfAdjoint hm t] at h
    refine h.congr fun n => ?_
    rw [resolvent_iterate_eq μS hV hσ.isSelfAdjoint hm]
  exact tendsto_traceENorm_of_dense (F := fun n : ℕ => (V.resolvent (t / n))^[n])
    (G := V.conj t) hF hG hD hcore hρ

/-- **Eq. (26)** for the resolvent of a possibly unbounded generator, on the dense set of
density operators supported in a spectral subspace `P_m`. -/
theorem infinitesimal_resolvent (V : StronglyContinuousUnitaryGroup E) :
    ∃ D : Set (E →L[ℂ] E), (∀ ρ ∈ D, IsDensityOperator ρ) ∧
    (∀ ρ, IsDensityOperator ρ → ∀ ε : ℝ, 0 < ε → ∃ σ ∈ D, traceENorm (ρ - σ) < ENNReal.ofReal ε) ∧
    ∀ ρ ∈ D, ∃ Lρ : E →L[ℂ] E,
      Tendsto (fun τ : ℝ => traceENorm (τ⁻¹ • (V.resolvent τ ρ - ρ) - Lρ)) (𝓝[>] 0)
        (𝓝 0) := by
  obtain ⟨μS, hμS⟩ := V.exists_expIntegral
  have hV : ∀ t, V t = expGroup μS t := hμS
  refine ⟨{ρ | IsDensityOperator ρ ∧ ∃ m, spectralCutoffProj μS m * ρ = ρ}, fun ρ hρ => hρ.1,
    fun ρ hρ ε hε => ?_, fun ρ ⟨hρ, m, hm⟩ => ?_⟩
  · obtain ⟨m, σ, hσ, hPσ, hd⟩ := exists_isDensityOperator_mul_eq
      (isStarProjection_spectralCutoffProj μS) (tendsto_spectralCutoffProj_apply μS) hρ hε
    exact ⟨σ, ⟨hσ, m, hPσ⟩, hd⟩
  · refine ⟨vonNeumannGenerator (cutoffGroup μS m).generator ρ,
      (tendsto_inv_smul_laplaceResolvent_sub (cutoffGroup μS m) hρ).congr fun τ => ?_⟩
    rw [resolvent_eq_laplaceResolvent_cutoffGroup μS hV hρ.isSelfAdjoint hm]

/-! ## Perfect prediction on the domain of the Hamiltonian -/

/-- **Perfect prediction from a state with a Lipschitz orbit.** If `‖V u ψ - ψ‖ ≤ C |u|`, the
branch that follows the largest outcome at every step has probability at least
`1 - 8 C² t² / n`, and its final state tends to `V t |ψ⟩⟨ψ| V t†` in trace norm. -/
theorem perfectPrediction_resolvent (V : StronglyContinuousUnitaryGroup E) {t : ℝ} (ht : 0 < t)
    {ψ : E} (hψ : ‖ψ‖ = 1) {C : ℝ} (hC : ∀ u, ‖V u ψ - ψ‖ ≤ C * |u|) :
    ∃ (Q : ℕ → ℕ → E →L[ℂ] E) (p : ℕ → ℕ → ℝ),
      (∀ᶠ n in atTop, Q n 0 = proj ψ ∧ IsBranch (V.resolvent (t / n)) n (Q n) (p n)) ∧
      Tendsto (fun n => ∏ k ∈ Finset.range n, p n k) atTop (𝓝 1) ∧
      Tendsto (fun n => traceENorm (Q n n - V t * proj ψ * star (V t))) atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 1)
    rwa [abs_one, mul_one] at h
  -- one step: the largest outcome
  have hstep : ∀ τ : ℝ, ∀ χ : E, ∃ x : ℝ, ∃ φ : E, ‖χ‖ = 1 → 0 < τ →
      ‖φ‖ = 1 ∧ IsOutcome (V.resolvent τ) (proj χ) x (proj φ) ∧ 0 < x ∧ x ≤ 1 ∧
      ∀ D : ℝ, (∀ u, ‖V u χ - χ‖ ≤ D * |u|) →
        1 - 2 * D ^ 2 * τ ^ 2 ≤ x ∧ ∀ u, ‖V u φ - φ‖ ≤ D / x * |u| := by
    intro τ χ
    by_cases h : ‖χ‖ = 1 ∧ 0 < τ
    · obtain ⟨w, b, μ, i₀, -, -, hP, hsum, -, hq0, hq1, hD⟩ := V.exists_max_resolvent_proj h.2 h.1
      have hb : ‖b i₀‖ = 1 := b.orthonormal.1 i₀
      exact ⟨μ i₀, b i₀, fun _ _ => ⟨hb, ⟨⟨b i₀, hb, rfl⟩, w, fun i => proj (b i),
        isProjectiveDecomposition_proj b, hsum, i₀, hP i₀⟩, hq0, hq1, hD⟩⟩
    · exact ⟨0, χ, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose x φ hxφ using hstep
  set χ : ℕ → ℕ → E := fun n k => (φ (t / n))^[k] ψ
  have hsucc : ∀ n k, χ n (k + 1) = φ (t / n) (χ n k) := fun n k => by
    simp only [χ, Function.iterate_succ_apply']
  have hunit : ∀ n : ℕ, 0 < n → ∀ k, ‖χ n k‖ = 1 := fun n hn k => by
    induction k with
    | zero => exact hψ
    | succ k ih => rw [hsucc]; exact (hxφ _ _ ih (by positivity)).1
  -- for large `n`, `n δ ≤ ½` with `δ = 8 C² (t / n)²`
  have hlim : Tendsto (fun n : ℕ => 8 * C ^ 2 * t ^ 2 / n) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hlarge : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 8 * C ^ 2 * t ^ 2 / n ≤ 2⁻¹ := by
    filter_upwards [eventually_gt_atTop 0, (tendsto_order.1 hlim).2 2⁻¹ (by norm_num)] with n hn h
    exact ⟨hn, h.le⟩
  -- along the branch the Lipschitz constant stays below `2 C`, and each step loses at most `δ`
  have hgood : ∀ n : ℕ, 0 < n → 8 * C ^ 2 * t ^ 2 / n ≤ 2⁻¹ → ∀ k < n,
      1 - 8 * C ^ 2 * (t / n) ^ 2 ≤ x (t / n) (χ n k) := by
    intro n hn hsmall
    have hτ : 0 < t / n := by positivity
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set δ := 8 * C ^ 2 * (t / n) ^ 2
    set a := 1 - δ
    have hnδ : n * δ = 8 * C ^ 2 * t ^ 2 / n := by simp only [δ]; field_simp
    have hδ0 : 0 ≤ δ := by positivity
    have hδ : δ ≤ 2⁻¹ := by
      have : δ ≤ n * δ := le_mul_of_one_le_left hδ0 (by exact_mod_cast hn)
      linarith
    have ha0 : 0 < a := by simp only [a]; linarith
    have ha1 : a ≤ 1 := by simp only [a]; linarith
    have hapow : ∀ k ≤ n, 2⁻¹ ≤ a ^ k := fun k hk => by
      have h1 := one_add_mul_le_pow (a := -δ) (by linarith) n
      have h2 : a ^ n ≤ a ^ k := pow_le_pow_of_le_one ha0.le ha1 hk
      rw [← sub_eq_add_neg] at h1
      simp only [a] at h2 ⊢
      nlinarith
    -- the step bound, from a Lipschitz constant `D ≤ 2 C`
    have hstep' : ∀ k, ∀ D : ℝ, 0 ≤ D → D ≤ 2 * C → (∀ u, ‖V u (χ n k) - χ n k‖ ≤ D * |u|) →
        a ≤ x (t / n) (χ n k) ∧ ∀ u, ‖V u (χ n (k + 1)) - χ n (k + 1)‖ ≤ D / a * |u| := by
      intro k D hD0 hD2 hD
      obtain ⟨h1, h2⟩ := (hxφ _ _ (hunit n hn k) hτ).2.2.2.2 D hD
      have hx : a ≤ x (t / n) (χ n k) := by
        have : 2 * D ^ 2 * (t / n) ^ 2 ≤ δ := by
          have := pow_le_pow_left₀ hD0 hD2 2
          simp only [δ]
          nlinarith [sq_nonneg (t / n)]
        simp only [a]
        linarith
      refine ⟨hx, fun u => ?_⟩
      rw [hsucc]
      refine (h2 u).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg u))
      exact div_le_div_of_nonneg_left hD0 ha0 hx
    have hlip : ∀ k ≤ n, ∀ u, ‖V u (χ n k) - χ n k‖ ≤ C / a ^ k * |u| := by
      intro k
      induction k with
      | zero =>
        intro _ u
        change ‖V u ψ - ψ‖ ≤ C / a ^ 0 * |u|
        simpa using hC u
      | succ k ih =>
        intro hk u
        have hk' : k ≤ n := by omega
        have hD2 : C / a ^ k ≤ 2 * C := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hapow k hk']
        have h := ((hstep' k _ (by positivity) hD2 (ih hk')).2 u)
        rwa [div_div, ← pow_succ] at h
    intro k hk
    have hD2 : C / a ^ k ≤ 2 * C := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hapow k hk.le]
    exact (hstep' k _ (by positivity) hD2 (hlip k hk.le)).1
  have hbranch : ∀ n : ℕ, 0 < n → IsBranch (V.resolvent (t / n)) n (fun k => proj (χ n k))
      (fun k => x (t / n) (χ n k)) := fun n hn =>
    ⟨⟨ψ, hψ, rfl⟩, fun k _ => by
      change IsOutcome _ (proj (χ n k)) _ (proj (χ n (k + 1)))
      rw [hsucc]
      exact (hxφ _ _ (hunit n hn k) (by positivity)).2.1⟩
  -- the branch probability tends to one
  have hprob : Tendsto (fun n => ∏ k ∈ Finset.range n, x (t / n) (χ n k)) atTop (𝓝 1) := by
    have hlow : Tendsto (fun n : ℕ => 1 - 8 * C ^ 2 * t ^ 2 / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hlarge] with n ⟨hn, hsmall⟩
      have hn' : (n : ℝ) ≠ 0 := by positivity
      set δ := 8 * C ^ 2 * (t / n) ^ 2
      have hδ0 : 0 ≤ δ := by positivity
      have hδ : δ ≤ 2⁻¹ := by
        have : δ ≤ n * δ := le_mul_of_one_le_left hδ0 (by exact_mod_cast hn)
        have h' : n * δ = 8 * C ^ 2 * t ^ 2 / n := by simp only [δ]; field_simp
        linarith
      calc 1 - 8 * C ^ 2 * t ^ 2 / n = 1 + n * -δ := by simp only [δ]; field_simp; ring
        _ ≤ (1 + -δ) ^ n := one_add_mul_le_pow (by linarith) n
        _ = ∏ k ∈ Finset.range n, (1 - δ) := by
            rw [Finset.prod_const, Finset.card_range, ← sub_eq_add_neg]
        _ ≤ ∏ k ∈ Finset.range n, x (t / n) (χ n k) :=
            Finset.prod_le_prod₀ (fun _ _ => by linarith)
              fun k hk => hgood n hn hsmall k (Finset.mem_range.mp hk)
    · filter_upwards [eventually_gt_atTop 0] with n hn
      exact Finset.prod_le_one₀ (fun k _ => (hxφ _ _ (hunit n hn k) (by positivity)).2.2.1.le)
        fun k _ => (hxφ _ _ (hunit n hn k) (by positivity)).2.2.2.1
  refine ⟨fun n k => proj (χ n k), fun n k => x (t / n) (χ n k), ?_, hprob, ?_⟩
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact ⟨rfl, hbranch n hn⟩
  · -- the final state is within `2 (1 - w)` of the unconditioned output
    have h1 : Tendsto (fun n => ENNReal.ofReal (2 * (1 - ∏ k ∈ Finset.range n,
        x (t / n) (χ n k)))) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_ofReal
        (((tendsto_const_nhds (x := (1 : ℝ))).sub hprob).const_mul 2)
      rwa [sub_self, mul_zero, ENNReal.ofReal_zero] at h
    have h2 := tendsto_resolvent_iterate V ht (isDensityOperator_proj hψ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [add_zero] using h1.add h2)
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hb := traceENorm_iterate_sub_le_of_isBranch
      (isStateAdaptiveProjective_resolvent V (by positivity : 0 < t / n)) (hbranch n hn)
    refine (traceENorm_sub_le _ ((V.resolvent (t / n))^[n] (proj ψ)) _).trans
      (add_le_add ?_ le_rfl)
    rw [traceENorm_sub_comm]
    exact hb

/-- **Perfect prediction on the domain of the Hamiltonian**: from every pure state `|ψ⟩⟨ψ|` with
`ψ` in the domain of the forward Hamiltonian `H` of `V` (with `ħ = 1`), the branch probability is at
least `1 - 8 ‖H ψ‖² t² / n`. -/
theorem perfectPrediction_resolvent_of_mem_domain (V : StronglyContinuousUnitaryGroup E) {t : ℝ}
    (ht : 0 < t) (ψ : (forwardHamiltonian V.toFun 1).domain) (hψ : ‖(ψ : E)‖ = 1) :
    ∃ (Q : ℕ → ℕ → E →L[ℂ] E) (p : ℕ → ℕ → ℝ),
      (∀ᶠ n in atTop, Q n 0 = proj (ψ : E) ∧ IsBranch (V.resolvent (t / n)) n (Q n) (p n)) ∧
      Tendsto (fun n => ∏ k ∈ Finset.range n, p n k) atTop (𝓝 1) ∧
      Tendsto (fun n => traceENorm (Q n n - V t * proj (ψ : E) * star (V t))) atTop (𝓝 0) :=
  perfectPrediction_resolvent V ht hψ (V.norm_apply_sub_le_of_mem_domain ψ)

end UnitaryProjectiveEvolution.InfiniteDimensional
