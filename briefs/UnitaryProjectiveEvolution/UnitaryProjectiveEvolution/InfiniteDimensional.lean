/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Unitary evolution as infinitesimal projective processes: Hilbert spaces of any dimension.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a complex Hilbert space `E` of any dimension, as in QST:H; no separability is used.
Density operators are the positive trace-class operators of trace one (`IsDensityOperator`), pure
states are `proj ψ = |ψ⟩⟨ψ|` for unit `ψ`, and limits are in the trace norm `traceENorm`, as the
brief's remarks require. Time evolution is DR-UNIT of the brief on the Schrödinger equation in any
dimension: conjugation by a strongly continuous unitary group, whose generator may be unbounded.
For a bounded generator `K` the resolvent `Ψ τ = (1 - τ L)⁻¹` of `L ρ = -i (K ρ - ρ K)` is the
Laplace integral `∫₀^∞ e^{-s} T (τ s) ds` of eq. (7)
(`ForPhyslib/QuantumMechanics/VonNeumannResolvent/Laplace`); `ħ = 1`.

Definition 1:
* `IsProjectiveDecomposition`  orthogonal projectors `Pₐ`, pairwise orthogonal, with `∑ₐ Pₐ = 1`
  strongly; the index set is arbitrary, and in a separable space at most countably many `Pₐ` are
  nonzero;
* `IsStateAdaptiveProjective`  an affine map of the density operators acting on each `ρ` as
  `∑ₐ Pₐ ρ Pₐ`, the sum converging strongly, for a projective decomposition depending on `ρ`.

Propositions:
* `isStateAdaptiveProjective_laplaceResolvent`  Proposition 2: the resolvent of a bounded
  generator is state-adaptive projective, for every `τ`, with the projectors onto an eigenbasis of
  `Ψ τ ρ`;
* `traceENorm_laplaceResolvent_sub_unitaryChannel_le`, `exists_max_laplaceResolvent_proj`
  Proposition 13 in trace norm: `‖Ψ τ ρ - T τ ρ‖₁ ≤ 80 ‖K‖² τ²`; for a pure state the largest
  eigenvalue `q` of `Ψ τ P` has `1 - q ≤ 8 ‖K‖² τ²` and its eigenprojector is within
  `64 ‖K‖² τ²` of `T τ P`;
* `tendsto_laplaceResolvent_iterate`  eq. (20), bounded `K`, in trace norm, with error
  `80 ‖K‖² t² / n` (`traceENorm_laplaceResolvent_iterate_sub_le`).

Conditions:
* `IsOutcome`, `IsBranch`  outcomes and branches, as in finite dimension;
* `PerfectPrediction`  branches of `n` steps of duration `t / n` whose probability tends to one
  and whose final states converge in trace norm;
* `IsProjectiveLimit`  `(Ψ (t / n))ⁿ ρ → Φ t ρ` in trace norm, with perfect prediction, for a
  family `Ψ τ` of state-adaptive projective processes that is infinitesimal: `(Ψ τ ρ - ρ) / τ`
  converges in trace norm for `ρ` in a dense set of density operators (eq. (26));
* `DrProj`  DR-PROJ: a projective limit with perfect prediction and a second one that
  reconstructs the pure initial states.

Theorem 18, DR-UNIT ⇒ DR-PROJ, unbounded generator:
* `isProjectiveLimit_cutoffResolvent`  the brief's scheme (22)–(25). With `V t = ∫ e^{itx} dμS`,
  the cutoff `H_τ = c_{M_τ}(H)` at `M_τ = τ^{-1/4}` (`cutoffLevel`, so `M_τ → ∞` and
  `τ M_τ² = √τ → 0`) gives bounded groups `W_τ` with `‖H_τ‖ ≤ M_τ`, and `Ψ τ` is the resolvent of
  `W_τ` at `τ`. Proposition 13 bounds the accumulated error after `n` steps by `80 t √(t / n)`, and
  `W_{t/n} t → V t` strongly (bounded convergence) gives eq. (25). The core of eq. (26) is the
  density operators supported in a spectral subspace `P_m = μS [-m, m]`, on which `Ψ τ` agrees with
  the resolvent of the fixed bounded group `W_m` once `M_τ ≥ m`;
* `DrUnit.drProj`  prediction by the resolvents of `V`, reconstruction by those of `t ↦ V (-t)`.

Theorem 18, DR-PROJ ⇒ DR-UNIT, over `IsEvolution`:
* `traceENorm_iterate_sub_le_of_isBranch`  by affinity, the unconditioned output `Ψⁿ (Q 0)` is
  within `2 (1 - w)` in trace norm of the final state of a branch of probability `w`
  (`nonneg_iterate_sub_of_isBranch`: `Ψⁿ (Q 0) - w Q n` is positive);
* `IsProjectiveLimit.isPure`  so every `Φ t` maps pure states to pure states, as a trace-norm
  limit of pure states (`QuantumMechanics.isPure_of_tendsto_traceENorm`);
* `DrProj.drEv`, `DrProj.drUnit`  reconstruction makes `Φ t` a bijection of the pure states, and
  the brief on the Schrödinger equation (Proposition 1 = Proposition 17, then Bargmann) gives
  DR-UNIT;
* `drUnit_iff_drProj`  Theorem 18.
-/

public import ForPhyslib.QuantumMechanics.SpectralCutoff
public import ForPhyslib.QuantumMechanics.VonNeumannResolvent.Laplace
public import SchroedingerEvolution.InfiniteDimensional

@[expose] public noncomputable section

namespace UnitaryProjectiveEvolution.InfiniteDimensional

open Filter Set QuantumMechanics QuantumMechanics.Wigner SchroedingerEvolution.InfiniteDimensional
  ProbabilisticTheory.QuantumMechanics ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure
open scoped Topology InnerProductSpace ComplexOrder ENNReal
open ContinuousLinearMap (posTrace posTrace_add posTrace_smul posTrace_eq_zero_iff
  re_inner_apply_nonneg)

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Definition 1 -/

/-- A projective decomposition `{Pₐ}` of the identity: orthogonal projectors, pairwise
orthogonal, with `∑ₐ Pₐ = 1` strongly. -/
def IsProjectiveDecomposition {ι : Type u} (P : ι → E →L[ℂ] E) : Prop :=
  (∀ a, IsStarProjection (P a)) ∧ (∀ a b, a ≠ b → P a * P b = 0) ∧ ∀ x, HasSum (fun a => P a x) x

/-- **Definition 1**: a state-adaptive projective process is an affine map of the density
operators that acts on each density operator `ρ` as the projective measurement `∑ₐ Pₐ ρ Pₐ`, the
sum converging strongly, of a projective decomposition `{Pₐ}` depending on `ρ`. -/
structure IsStateAdaptiveProjective (Ψ : (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  isDensityOperator : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Ψ ρ)
  affine : AffineOnDensityOperators Ψ
  projective : ∀ ρ, IsDensityOperator ρ → ∃ (ι : Type u) (P : ι → E →L[ℂ] E),
    IsProjectiveDecomposition P ∧ ∀ x, HasSum (fun a => (P a * ρ * P a) x) (Ψ ρ x)

/-- The projectors onto a Hilbert basis form a projective decomposition. -/
lemma isProjectiveDecomposition_proj {w : Set E} (b : HilbertBasis w ℂ E) :
    IsProjectiveDecomposition fun i => proj (b i) := by
  have hb : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  refine ⟨fun i => ⟨(InnerProductSpace.isIdempotentElem_rankOne_self (hb i)),
    (proj_nonneg (b i)).isSelfAdjoint⟩, fun i j hij => ?_, fun x => ?_⟩
  · ext x
    simp [b.orthonormal.2 hij]
  · simpa [proj_apply, HilbertBasis.repr_apply_apply] using b.hasSum_repr x

/-- A linear map is affine on density operators. -/
lemma affineOnDensityOperators_of_linearMap (T : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E) :
    AffineOnDensityOperators T := fun ρ σ _ _ t _ _ => by
  rw [map_add, map_smul, map_smul]

/-- **Proposition 2**: the resolvent `(1 - τ L)⁻¹` of a bounded generator is a state-adaptive
projective process, for every `τ`. -/
theorem isStateAdaptiveProjective_laplaceResolvent (V : UnitaryOneParameterGroup E) (τ : ℝ) :
    IsStateAdaptiveProjective (laplaceResolvent V τ) where
  isDensityOperator _ hρ := isDensityOperator_laplaceResolvent V τ hρ
  affine := affineOnDensityOperators_of_linearMap (laplaceResolvent V τ).toLinearMap
  projective ρ hρ := by
    obtain ⟨w, b, -, -, -, -, -, hsum⟩ := exists_hilbertBasis_laplaceResolvent V τ hρ
    exact ⟨w, fun i => proj (b i), isProjectiveDecomposition_proj b, hsum⟩

/-! ## Outcomes and branches -/

/-- `Q` is an outcome, of probability `p`, of the projective measurement that `Ψ` performs on the
pure state `P`: for a projective decomposition `{Fₐ}` realizing `Ψ P = ∑ₐ Fₐ P Fₐ`, one term
`Fₐ P Fₐ` is `p Q` with `Q` pure. -/
def IsOutcome (Ψ : (E →L[ℂ] E) → E →L[ℂ] E) (P : E →L[ℂ] E) (p : ℝ) (Q : E →L[ℂ] E) : Prop :=
  IsPure Q ∧ ∃ (ι : Type u) (F : ι → E →L[ℂ] E), IsProjectiveDecomposition F ∧
    (∀ x, HasSum (fun a => (F a * P * F a) x) (Ψ P x)) ∧ ∃ a, F a * P * F a = (p : ℂ) • Q

/-- A branch of `n` steps of `Ψ`: a sequence of pure states `Q 0, …, Q n` in which each `Q (k + 1)`
is an outcome on `Q k`, of probability `p k`. Its probability is `∏ₖ p k`. -/
def IsBranch (Ψ : (E →L[ℂ] E) → E →L[ℂ] E) (n : ℕ) (Q : ℕ → E →L[ℂ] E) (p : ℕ → ℝ) : Prop :=
  IsPure (Q 0) ∧ ∀ k < n, IsOutcome Ψ (Q k) (p k) (Q (k + 1))

/-! ## Conditions -/

/-- Perfect prediction over the elapsed time `t`: from every pure state there is, for all large
`n`, a branch of `n` steps of the process of duration `t / n`, whose probability tends to one and
whose final state converges in trace norm. -/
def PerfectPrediction (Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) (t : ℝ) : Prop :=
  ∀ P, IsPure P → ∃ (Q : ℕ → ℕ → E →L[ℂ] E) (p : ℕ → ℕ → ℝ) (R : E →L[ℂ] E),
    (∀ᶠ n in atTop, Q n 0 = P ∧ IsBranch (Ψ (t / n)) n (Q n) (p n)) ∧
    Tendsto (fun n => ∏ k ∈ Finset.range n, p n k) atTop (𝓝 1) ∧
    Tendsto (fun n => traceENorm (Q n n - R)) atTop (𝓝 0)

/-- The evolution `Φ` is the limit of repeated applications of the infinitesimal state-adaptive
projective process `Ψ`, with perfect prediction. Every `Ψ τ` with `τ > 0` is state-adaptive
projective; the family is infinitesimal (eq. (26)): `(Ψ τ ρ - ρ) / τ` converges in trace norm as
`τ → 0⁺` for every `ρ` in a set of density operators that is dense in trace norm; `(Ψ (t / n))ⁿ ρ →
Φ t ρ` in trace norm; and prediction is perfect. -/
structure IsProjectiveLimit (Φ Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  stateAdaptive : ∀ τ > 0, IsStateAdaptiveProjective (Ψ τ)
  infinitesimal : ∃ D : Set (E →L[ℂ] E), (∀ ρ ∈ D, IsDensityOperator ρ) ∧
    (∀ ρ, IsDensityOperator ρ → ∀ ε : ℝ, 0 < ε → ∃ σ ∈ D, traceENorm (ρ - σ) < ENNReal.ofReal ε) ∧
    ∀ ρ ∈ D, ∃ Lρ : E →L[ℂ] E,
      Tendsto (fun τ : ℝ => traceENorm (τ⁻¹ • (Ψ τ ρ - ρ) - Lρ)) (𝓝[>] 0) (𝓝 0)
  tendsto : ∀ t > 0, ∀ ρ, IsDensityOperator ρ →
    Tendsto (fun n : ℕ => traceENorm ((Ψ (t / n))^[n] ρ - Φ t ρ)) atTop (𝓝 0)
  prediction : ∀ t > 0, PerfectPrediction Ψ t

/-- **DR-PROJ**: the evolution is a projective limit with perfect prediction, and also with
perfect reconstruction: a second projective limit `Φ'` runs backwards, recovering every pure
initial state from the evolved one and every pure final state from the reconstructed one. -/
def DrProj (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ Ψ, IsProjectiveLimit Φ Ψ ∧ ∃ Φ' Ψ', IsProjectiveLimit Φ' Ψ' ∧
    ∀ t > 0, ∀ P, IsPure P → Φ' t (Φ t P) = P ∧ Φ t (Φ' t P) = P

lemma IsProjectiveLimit.congr {Φ Φ' Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : IsProjectiveLimit Φ Ψ)
    (hΦ : ∀ t > 0, ∀ ρ, IsDensityOperator ρ → Φ t ρ = Φ' t ρ) : IsProjectiveLimit Φ' Ψ where
  stateAdaptive := h.stateAdaptive
  infinitesimal := h.infinitesimal
  tendsto t ht ρ hρ := by simpa only [hΦ t ht ρ hρ] using h.tendsto t ht ρ hρ
  prediction := h.prediction

/-! ## Bounded generators -/

/-- One predicted step: for a unit `χ` and `8 ‖K‖² τ² ≤ ½`, the largest outcome of `Ψ τ` on
`|χ⟩⟨χ|` is a pure state `|φ⟩⟨φ|` of probability in `[1 - 8 ‖K‖² τ², 1]`, within `64 ‖K‖² τ²` of the
unitary step in trace norm (Proposition 13). -/
lemma exists_isOutcome_laplaceResolvent (V : UnitaryOneParameterGroup E) {χ : E} (hχ : ‖χ‖ = 1)
    {τ : ℝ} (hτ : 0 ≤ τ) (hδ : 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ 2⁻¹) :
    ∃ x : ℝ, ∃ φ : E, ‖φ‖ = 1 ∧ IsOutcome (laplaceResolvent V τ) (proj χ) x (proj φ) ∧
      1 - 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ x ∧ x ≤ 1 ∧
      traceENorm (proj φ - unitaryChannel V τ (proj χ)) ≤
        ENNReal.ofReal (64 * ‖V.generator‖ ^ 2 * τ ^ 2) := by
  obtain ⟨w, b, μ, i₀, hμ0, hμ, hP, hsum, -, hx1, hF, -⟩ :=
    exists_max_laplaceResolvent_proj V hχ hτ hδ
  have hb : ‖b i₀‖ = 1 := b.orthonormal.1 i₀
  refine ⟨μ i₀, b i₀, hb, ⟨⟨b i₀, hb, rfl⟩, w, fun i => proj (b i),
    isProjectiveDecomposition_proj b, hsum, i₀, hP i₀⟩, hx1, ?_, hF⟩
  simpa using le_hasSum hμ i₀ fun j _ => hμ0 j

/-! ## Unbounded generators: the cutoff resolvents -/

/-- The cutoff level `M_τ = τ^{-1/4}`, so that `M_τ → ∞` and `τ M_τ² = √τ → 0` as `τ → 0⁺`
(eq. (22)). -/
def cutoffLevel (τ : ℝ) : ℝ := (Real.sqrt (Real.sqrt τ))⁻¹

lemma cutoffLevel_nonneg (τ : ℝ) : 0 ≤ cutoffLevel τ := inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma mul_cutoffLevel_sq {τ : ℝ} (hτ : 0 ≤ τ) : τ * cutoffLevel τ ^ 2 = Real.sqrt τ := by
  rw [cutoffLevel, inv_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
  rcases hτ.eq_or_lt with rfl | hτ
  · simp
  · have h := Real.sq_sqrt hτ.le
    have hs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    field_simp
    linarith

lemma tendsto_cutoffLevel : Tendsto cutoffLevel (𝓝[>] 0) atTop := by
  have h0 : Tendsto (fun τ : ℝ => Real.sqrt (Real.sqrt τ)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h := (Real.continuous_sqrt.comp Real.continuous_sqrt).tendsto 0
      simp only [Function.comp_apply, Real.sqrt_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hτ)
  exact tendsto_inv_nhdsGT_zero.comp h0

lemma tendsto_div_nhdsGT {t : ℝ} (ht : 0 < t) : Tendsto (fun n : ℕ => t / n) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat t,
    (eventually_gt_atTop 0).mono fun n hn => by simp only [mem_Ioi]; positivity⟩

lemma tendsto_sqrt_div {t : ℝ} : Tendsto (fun n : ℕ => Real.sqrt (t / n)) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_const_div_atTop_nhds_zero_nat t)
  rwa [Real.sqrt_zero] at h

variable (μS : WOTSpectralMeasure ℝ E)

/-- The cutoff group `W_τ = exp (it c_{M_τ}(H))` at duration `τ`. -/
def cutoffGroupAt (τ : ℝ) : UnitaryOneParameterGroup E := cutoffGroup μS (cutoffLevel τ)

/-- **The cutoff resolvents** (eq. (23)): `Ψ τ = (1 - τ L_τ)⁻¹` with `L_τ` generated by the cutoff
`H_τ = c_{M_τ}(H)`. -/
def cutoffResolvent (τ : ℝ) : (E →L[ℂ] E) → E →L[ℂ] E := laplaceResolvent (cutoffGroupAt μS τ) τ

lemma norm_cutoffGroupAt_generator_le (τ : ℝ) :
    ‖(cutoffGroupAt μS τ).generator‖ ≤ cutoffLevel τ :=
  norm_cutoffGroup_generator_le μS (cutoffLevel_nonneg τ)

/-- `‖H_τ‖² τ² ≤ τ √τ`. -/
lemma generator_sq_mul_sq_le {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖(cutoffGroupAt μS τ).generator‖ ^ 2 * τ ^ 2 ≤ τ * Real.sqrt τ := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_cutoffGroupAt_generator_le μS τ) 2
  calc ‖(cutoffGroupAt μS τ).generator‖ ^ 2 * τ ^ 2 ≤ cutoffLevel τ ^ 2 * τ ^ 2 := by gcongr
    _ = τ * (τ * cutoffLevel τ ^ 2) := by ring
    _ = τ * Real.sqrt τ := by rw [mul_cutoffLevel_sq hτ]

/-- The full unitary group `V t = ∫ e^{itx} dμS(x)`. -/
abbrev expGroup (t : ℝ) : E →L[ℂ] E := (expIntegral μS t).toCLM

lemma norm_expGroup_le (t : ℝ) : ‖expGroup μS t‖ ≤ 1 := by
  have h := Unitary.mem_iff.mp (expIntegral_mem_unitary μS t)
  have hU : expGroup μS t ∈ unitary (E →L[ℂ] E) := Unitary.mem_iff.mpr
    ⟨congrArg ContinuousLinearMapWOT.toCLM h.1, congrArg ContinuousLinearMapWOT.toCLM h.2⟩
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [ContinuousLinearMap.norm_map_of_mem_unitary hU, one_mul]

/-- **Eq. (25)**: `W_{t/n} t → V t` strongly. -/
lemma tendsto_cutoffGroupAt_apply {t : ℝ} (ht : 0 < t) (s : ℝ) (x : E) :
    Tendsto (fun n : ℕ => cutoffGroupAt μS (t / n) s x) atTop (𝓝 (expGroup μS s x)) :=
  (tendsto_cutoffGroup_apply μS s x).comp (tendsto_cutoffLevel.comp (tendsto_div_nhdsGT ht))

/-- **Eqs. (24) and (25)**: `(Ψ (t / n))ⁿ ρ → V t ρ V t†` in trace norm. -/
theorem tendsto_cutoffResolvent_iterate {t : ℝ} (ht : 0 < t) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    Tendsto (fun n : ℕ => traceENorm ((cutoffResolvent μS (t / n))^[n] ρ -
      expGroup μS t * ρ * star (expGroup μS t))) atTop (𝓝 0) := by
  set W := fun n : ℕ => cutoffGroupAt μS (t / n)
  -- the accumulated error against the cutoff group
  have h1 : Tendsto (fun n : ℕ => traceENorm ((cutoffResolvent μS (t / n))^[n] ρ -
      unitaryChannel (W n) t ρ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (80 * t * Real.sqrt (t / n))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal ((tendsto_sqrt_div (t := t)).const_mul (80 * t))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    refine (traceENorm_laplaceResolvent_iterate_sub_le (W n) ht.le hn hρ).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h := generator_sq_mul_sq_le μS (τ := t / n) (by positivity)
    have heq : 80 * ‖(W n).generator‖ ^ 2 * t ^ 2 / n =
        80 * n * (‖(W n).generator‖ ^ 2 * (t / n) ^ 2) := by field_simp
    rw [heq]
    calc 80 * n * (‖(W n).generator‖ ^ 2 * (t / n) ^ 2) ≤ 80 * n * (t / n * Real.sqrt (t / n)) := by
          gcongr
      _ = 80 * t * Real.sqrt (t / n) := by field_simp
  -- the cutoff groups converge strongly
  have h2 : Tendsto (fun n : ℕ => traceENorm (unitaryChannel (W n) t ρ -
      expGroup μS t * ρ * star (expGroup μS t))) atTop (𝓝 0) :=
    tendsto_traceENorm_conj (fun n => norm_unitaryOneParameterGroup_le (W n) t)
      (norm_expGroup_le μS t) (fun x => tendsto_cutoffGroupAt_apply μS ht t x) hρ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using h1.add h2)
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
  exact traceENorm_sub_le _ _ _

/-- **Perfect prediction** for the cutoff resolvents: following the largest outcome at every step,
the branch probability is at least `1 - 8 t √(t / n)`, and the final state is within
`64 t √(t / n)` of the cutoff evolution, which converges to the unitary evolution. -/
theorem perfectPrediction_cutoffResolvent {t : ℝ} (ht : 0 < t) :
    PerfectPrediction (cutoffResolvent μS) t := by
  rintro _ ⟨ψ, hψ, rfl⟩
  set K := fun τ : ℝ => (cutoffGroupAt μS τ).generator
  have hstep : ∀ τ : ℝ, ∀ χ : E, ∃ x : ℝ, ∃ φ : E, ‖χ‖ = 1 → 0 ≤ τ →
      8 * ‖K τ‖ ^ 2 * τ ^ 2 ≤ 2⁻¹ →
      ‖φ‖ = 1 ∧ IsOutcome (cutoffResolvent μS τ) (proj χ) x (proj φ) ∧
      1 - 8 * ‖K τ‖ ^ 2 * τ ^ 2 ≤ x ∧ x ≤ 1 ∧
      traceENorm (proj φ - unitaryChannel (cutoffGroupAt μS τ) τ (proj χ)) ≤
        ENNReal.ofReal (64 * ‖K τ‖ ^ 2 * τ ^ 2) := by
    intro τ χ
    by_cases h : ‖χ‖ = 1 ∧ 0 ≤ τ ∧ 8 * ‖K τ‖ ^ 2 * τ ^ 2 ≤ 2⁻¹
    · obtain ⟨x, φ, hφ⟩ := exists_isOutcome_laplaceResolvent (cutoffGroupAt μS τ) h.1 h.2.1 h.2.2
      exact ⟨x, φ, fun _ _ _ => hφ⟩
    · exact ⟨0, χ, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose x φ hxφ using hstep
  set χ : ℕ → ℕ → E := fun n k => (φ (t / n))^[k] ψ
  -- for large `n` every step is small
  have hδn : ∀ n : ℕ, 0 < n → 8 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2 ≤ 8 * (t / n) * Real.sqrt (t / n) :=
    fun n hn => by
      have h := generator_sq_mul_sq_le μS (τ := t / n) (by positivity)
      nlinarith
  have hsmall : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 8 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2 ≤ 2⁻¹ := by
    have h : Tendsto (fun n : ℕ => 8 * (t / n) * Real.sqrt (t / n)) atTop (𝓝 0) := by
      simpa [mul_assoc] using
        ((tendsto_const_div_atTop_nhds_zero_nat t).mul tendsto_sqrt_div).const_mul 8
    filter_upwards [eventually_gt_atTop 0, (tendsto_order.1 h).2 2⁻¹ (by norm_num)] with n hn hlt
    exact ⟨hn, (hδn n hn).trans hlt.le⟩
  have hgood : ∀ n : ℕ, 0 < n → 8 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2 ≤ 2⁻¹ → ∀ k, ‖χ n k‖ = 1 ∧
      IsOutcome (cutoffResolvent μS (t / n)) (proj (χ n k)) (x (t / n) (χ n k))
        (proj (χ n (k + 1))) ∧
      1 - 8 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2 ≤ x (t / n) (χ n k) ∧ x (t / n) (χ n k) ≤ 1 ∧
      traceENorm (proj (χ n (k + 1)) -
        unitaryChannel (cutoffGroupAt μS (t / n)) (t / n) (proj (χ n k))) ≤
        ENNReal.ofReal (64 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2) := by
    intro n hn hδ k
    have hτ : 0 ≤ t / n := by positivity
    have hunit : ∀ k, ‖χ n k‖ = 1 := by
      intro k
      induction k with
      | zero => exact hψ
      | succ k ih =>
        simp only [χ, Function.iterate_succ_apply']
        exact (hxφ _ _ ih hτ hδ).1
    have hsucc : χ n (k + 1) = φ (t / n) (χ n k) := by
      simp only [χ, Function.iterate_succ_apply']
    obtain ⟨-, h2, h3, h4, h5⟩ := hxφ (t / n) (χ n k) (hunit k) hτ hδ
    exact ⟨hunit k, hsucc ▸ h2, h3, h4, hsucc ▸ h5⟩
  refine ⟨fun n k => proj (χ n k), fun n k => x (t / n) (χ n k), proj (expGroup μS t ψ), ?_, ?_, ?_⟩
  · filter_upwards [hsmall] with n ⟨hn, hδ⟩
    exact ⟨rfl, ⟨ψ, hψ, rfl⟩, fun k _ => (hgood n hn hδ k).2.1⟩
  · -- the branch probability tends to one
    have hlow : Tendsto (fun n : ℕ => 1 - 8 * t * Real.sqrt (t / n)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_sqrt_div.const_mul (8 * t))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hsmall] with n ⟨hn, hδ⟩
      have hn' : (n : ℝ) ≠ 0 := by positivity
      set δ := 8 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2
      calc 1 - 8 * t * Real.sqrt (t / n) = 1 + n * (-(8 * (t / n) * Real.sqrt (t / n))) := by
            field_simp
            ring
        _ ≤ 1 + n * -δ := by
            have := hδn n hn
            gcongr
        _ ≤ (1 + -δ) ^ n := one_add_mul_le_pow (by linarith) n
        _ = ∏ k ∈ Finset.range n, (1 - δ) := by
            rw [Finset.prod_const, Finset.card_range, ← sub_eq_add_neg]
        _ ≤ ∏ k ∈ Finset.range n, x (t / n) (χ n k) :=
            Finset.prod_le_prod₀ (fun _ _ => by linarith) fun k _ => (hgood n hn hδ k).2.2.1
    · filter_upwards [hsmall] with n ⟨hn, hδ⟩
      refine Finset.prod_le_one₀ (fun k _ => ?_) fun k _ => (hgood n hn hδ k).2.2.2.1
      linarith [(hgood n hn hδ k).2.2.1]
  · -- the final state tends to the unitary evolution
    have h1 : Tendsto (fun n : ℕ => traceENorm (proj (χ n n) -
        unitaryChannel (cutoffGroupAt μS (t / n)) t (proj ψ))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (64 * t * Real.sqrt (t / n))) atTop
          (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal ((tendsto_sqrt_div (t := t)).const_mul (64 * t))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
        (Eventually.of_forall fun _ => zero_le) ?_
      filter_upwards [hsmall] with n ⟨hn, hδ⟩
      have hn' : (n : ℝ) ≠ 0 := by positivity
      have h := traceENorm_sub_unitaryChannel_le_of_step (cutoffGroupAt μS (t / n))
        (x := fun k => proj (χ n k)) (τ := t / n)
        (ε := ENNReal.ofReal (64 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2)) n
        fun k _ => (hgood n hn hδ k).2.2.2.2
      rw [mul_div_cancel₀ t hn'] at h
      refine h.trans ?_
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h' := generator_sq_mul_sq_le μS (τ := t / n) (by positivity)
      calc (n : ℝ) * (64 * ‖K (t / n)‖ ^ 2 * (t / n) ^ 2) ≤
            n * (64 * (t / n * Real.sqrt (t / n))) := by
            have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            nlinarith
        _ = 64 * t * Real.sqrt (t / n) := by field_simp
    have h2 : Tendsto (fun n : ℕ => traceENorm (unitaryChannel (cutoffGroupAt μS (t / n)) t
        (proj ψ) - proj (expGroup μS t ψ))) atTop (𝓝 0) := by
      have h := tendsto_traceENorm_conj (fun n => norm_unitaryOneParameterGroup_le _ t)
        (norm_expGroup_le μS t) (fun x => tendsto_cutoffGroupAt_apply μS ht t x)
        (isDensityOperator_proj hψ)
      simpa only [unitaryChannel_proj, mul_proj_mul_star] using h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using h1.add h2) (Eventually.of_forall fun _ => zero_le)
      (Eventually.of_forall fun n => traceENorm_sub_le _ _ _)

/-- On a density operator supported in `P_m`, the cutoff resolvent at levels `M ≥ m` is the
resolvent of the fixed bounded group `W_m`. -/
lemma laplaceResolvent_cutoffGroup_eq {m M : ℝ} (hm : m ≤ M) {ρ : E →L[ℂ] E}
    (hρ : IsSelfAdjoint ρ) (hP : spectralCutoffProj μS m * ρ = ρ) (τ : ℝ) :
    laplaceResolvent (cutoffGroup μS M) τ ρ = laplaceResolvent (cutoffGroup μS m) τ ρ := by
  have hPs := isStarProjection_spectralCutoffProj μS m
  have hP' : ρ * spectralCutoffProj μS m = ρ := by
    have h := congrArg star hP
    rwa [star_mul, hρ.star_eq, hPs.isSelfAdjoint.star_eq] at h
  have hρPP : spectralCutoffProj μS m * ρ * spectralCutoffProj μS m = ρ := by rw [hP, hP']
  have hT : ∀ s, unitaryChannel (cutoffGroup μS M) s ρ = unitaryChannel (cutoffGroup μS m) s ρ := by
    intro s
    have hW := cutoffGroup_mul_spectralCutoffProj μS hm s
    have hW' : spectralCutoffProj μS m * star (cutoffGroup μS M s) =
        spectralCutoffProj μS m * star (cutoffGroup μS m s) := by
      have h := congrArg star hW
      rwa [star_mul, star_mul, hPs.isSelfAdjoint.star_eq] at h
    calc unitaryChannel (cutoffGroup μS M) s ρ = cutoffGroup μS M s * spectralCutoffProj μS m * ρ *
          (spectralCutoffProj μS m * star (cutoffGroup μS M s)) := by
          rw [unitaryChannel]
          conv_lhs => rw [← hρPP]
          simp only [mul_assoc]
      _ = cutoffGroup μS m s * spectralCutoffProj μS m * ρ *
          (spectralCutoffProj μS m * star (cutoffGroup μS m s)) := by rw [hW, hW']
      _ = unitaryChannel (cutoffGroup μS m) s ρ := by
          rw [unitaryChannel]
          conv_rhs => rw [← hρPP]
          simp only [mul_assoc]
  rw [laplaceResolvent_apply, laplaceResolvent_apply]
  simp only [hT]

/-- **Eq. (26)**: the cutoff resolvents are infinitesimal on the dense set of density operators
supported in a spectral subspace `P_m`. -/
theorem infinitesimal_cutoffResolvent : ∃ D : Set (E →L[ℂ] E), (∀ ρ ∈ D, IsDensityOperator ρ) ∧
    (∀ ρ, IsDensityOperator ρ → ∀ ε : ℝ, 0 < ε → ∃ σ ∈ D, traceENorm (ρ - σ) < ENNReal.ofReal ε) ∧
    ∀ ρ ∈ D, ∃ Lρ : E →L[ℂ] E,
      Tendsto (fun τ : ℝ => traceENorm (τ⁻¹ • (cutoffResolvent μS τ ρ - ρ) - Lρ)) (𝓝[>] 0)
        (𝓝 0) := by
  refine ⟨{ρ | IsDensityOperator ρ ∧ ∃ m, spectralCutoffProj μS m * ρ = ρ}, fun ρ hρ => hρ.1,
    fun ρ hρ ε hε => ?_, fun ρ ⟨hρ, m, hm⟩ => ?_⟩
  · obtain ⟨m, σ, hσ, hPσ, hd⟩ := exists_isDensityOperator_mul_eq
      (isStarProjection_spectralCutoffProj μS) (tendsto_spectralCutoffProj_apply μS) hρ hε
    exact ⟨σ, ⟨hσ, m, hPσ⟩, hd⟩
  · refine ⟨vonNeumannGenerator (cutoffGroup μS m).generator ρ,
      (tendsto_inv_smul_laplaceResolvent_sub (cutoffGroup μS m) hρ).congr' ?_⟩
    filter_upwards [tendsto_cutoffLevel.eventually (eventually_ge_atTop m)] with τ hτ
    rw [cutoffResolvent, cutoffGroupAt, laplaceResolvent_cutoffGroup_eq μS hτ hρ.isSelfAdjoint hm]

/-- **Theorem 18**, DR-UNIT ⇒ DR-PROJ for a possibly unbounded generator: the cutoff resolvents
form a projective limit of the unitary evolution. -/
theorem isProjectiveLimit_cutoffResolvent :
    IsProjectiveLimit (fun t ρ => expGroup μS t * ρ * star (expGroup μS t))
      (cutoffResolvent μS) where
  stateAdaptive τ _ := isStateAdaptiveProjective_laplaceResolvent _ τ
  infinitesimal := infinitesimal_cutoffResolvent μS
  tendsto _ ht _ hρ := tendsto_cutoffResolvent_iterate μS ht hρ
  prediction _ ht := perfectPrediction_cutoffResolvent μS ht

/-! ## Theorem 18, DR-UNIT ⇒ DR-PROJ -/

/-- The reversed group `t ↦ V (-t)`. -/
def timeReversal (V : StronglyContinuousUnitaryGroup E) : StronglyContinuousUnitaryGroup E where
  toFun t := V (-t)
  mem_unitary t := V.mem_unitary _
  map_zero := by rw [neg_zero]; exact V.map_zero
  map_add s t := by rw [neg_add]; exact V.map_add _ _
  continuous_apply x := (V.continuous_apply x).comp continuous_neg

/-- Every strongly continuous unitary group is a projective limit of cutoff resolvents. -/
theorem exists_isProjectiveLimit (V : StronglyContinuousUnitaryGroup E) :
    ∃ Ψ, IsProjectiveLimit (fun t ρ => V t * ρ * star (V t)) Ψ := by
  obtain ⟨μS, hμS⟩ := V.exists_expIntegral
  refine ⟨_, (isProjectiveLimit_cutoffResolvent μS).congr fun t _ ρ _ => ?_⟩
  rw [hμS t]

/-- **Theorem 18**, DR-UNIT ⇒ DR-PROJ: the cutoff resolvents of `V` give prediction, and those of
the reversed group `t ↦ V (-t)` give reconstruction. -/
theorem DrUnit.drProj {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : DrUnit Φ) : DrProj Φ := by
  obtain ⟨V, hV⟩ := h
  obtain ⟨Ψ, hΨ⟩ := exists_isProjectiveLimit V
  obtain ⟨Ψ', hΨ'⟩ := exists_isProjectiveLimit (timeReversal V)
  have hinv : ∀ t, V (-t) * V t = 1 ∧ V t * V (-t) = 1 := fun t => by
    have h1 := V.map_add (-t) t
    have h2 := V.map_add t (-t)
    rw [neg_add_cancel, V.map_zero] at h1
    rw [add_neg_cancel, V.map_zero] at h2
    exact ⟨h1.symm, h2.symm⟩
  have hstar : ∀ t, star (V t) = V (-t) := fun t => by
    have hu := Unitary.mem_iff.mp (V.mem_unitary t)
    calc star (V t) = star (V t) * (V t * V (-t)) := by rw [(hinv t).2, mul_one]
      _ = V (-t) := by rw [← mul_assoc, hu.1, one_mul]
  refine ⟨Ψ, hΨ.congr fun t ht ρ hρ => (hV t ht.le ρ hρ).symm, _, Ψ', hΨ',
    fun t ht P hP => ⟨?_, ?_⟩⟩
  · have hPd : IsDensityOperator P := by obtain ⟨ψ, hψ, rfl⟩ := hP; exact isDensityOperator_proj hψ
    change V (-t) * Φ t P * star (V (-t)) = P
    rw [hV t ht.le P hPd, hstar, hstar, neg_neg]
    calc V (-t) * (V t * P * V (-t)) * V t = (V (-t) * V t) * P * (V (-t) * V t) := by
          simp only [mul_assoc]
      _ = P := by rw [(hinv t).1, one_mul, mul_one]
  · have hPd : IsDensityOperator P := by obtain ⟨ψ, hψ, rfl⟩ := hP; exact isDensityOperator_proj hψ
    have hd : IsDensityOperator (V (-t) * P * star (V (-t))) :=
      hPd.conj (Unitary.mem_iff.mp (V.mem_unitary (-t))).1
    change Φ t (V (-t) * P * star (V (-t))) = P
    rw [hV t ht.le _ hd, hstar, hstar, neg_neg]
    calc V t * (V (-t) * P * V t) * V (-t) = (V t * V (-t)) * P * (V t * V (-t)) := by
          simp only [mul_assoc]
      _ = P := by rw [(hinv t).2, one_mul, mul_one]

/-! ## Theorem 18, DR-PROJ ⇒ DR-UNIT -/

lemma isDensityOperator_of_isPure {P : E →L[ℂ] E} (hP : IsPure P) : IsDensityOperator P := by
  obtain ⟨ψ, hψ, rfl⟩ := hP
  exact isDensityOperator_proj hψ

lemma IsBranch.isPure {Ψ : (E →L[ℂ] E) → E →L[ℂ] E} {n : ℕ} {Q : ℕ → E →L[ℂ] E} {p : ℕ → ℝ}
    (h : IsBranch Ψ n Q p) : ∀ k ≤ n, IsPure (Q k)
  | 0, _ => h.1
  | k + 1, hk => (h.2 k hk).1

lemma smul_nonneg_of_nonneg {c : ℝ} (hc : 0 ≤ c) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    0 ≤ (c : ℂ) • A := by
  rw [Complex.coe_smul]
  exact smul_nonneg hc hA

/-- An outcome has a nonnegative probability `p`, and `Ψ P - p Q` is positive: the other terms of
`Ψ P = ∑ₐ Fₐ P Fₐ` are positive. -/
lemma IsOutcome.nonneg {Ψ : (E →L[ℂ] E) → E →L[ℂ] E} (hΨ : IsStateAdaptiveProjective Ψ)
    {P Q : E →L[ℂ] E} {p : ℝ} (hP : IsPure P) (h : IsOutcome Ψ P p Q) :
    0 ≤ p ∧ 0 ≤ Ψ P - (p : ℂ) • Q := by
  obtain ⟨⟨q, hq, rfl⟩, ι, F, hF, hΨP, a, ha⟩ := h
  have hpos : ∀ b, 0 ≤ F b * P * F b := fun b => by
    have h := star_right_conjugate_nonneg (isDensityOperator_of_isPure hP).nonneg (F b)
    rwa [(hF.1 b).isSelfAdjoint.star_eq] at h
  have hsum : ∀ x, HasSum (fun b => (⟪x, (F b * P * F b) x⟫_ℂ).re) (⟪x, Ψ P x⟫_ℂ).re :=
    fun x => Complex.hasSum_re ((innerSL ℂ x).hasSum (hΨP x))
  have hle : ∀ x, (⟪x, (F a * P * F a) x⟫_ℂ).re ≤ (⟪x, Ψ P x⟫_ℂ).re := fun x =>
    le_hasSum (hsum x) a fun b _ => re_inner_apply_nonneg (hpos b) x
  have hpq : (⟪q, ((p : ℂ) • proj q) q⟫_ℂ).re = p := by
    have h1 : ⟪q, q⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hq]; simp
    simp only [smul_apply, inner_smul_right, proj,
      InnerProductSpace.rankOne_apply, h1, one_smul, mul_one, Complex.ofReal_re]
  refine ⟨hpq ▸ ha ▸ re_inner_apply_nonneg (hpos a) q, ?_⟩
  rw [← ha, ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  refine ⟨((hΨ.isDensityOperator P (isDensityOperator_of_isPure hP)).isSelfAdjoint).sub
    (hpos a).isSelfAdjoint, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm, sub_apply, inner_sub_right,
    map_sub, sub_nonneg]
  exact hle x

/-- If `A - w Q` is positive for density operators `A`, `Q` and `w ≥ 0`, then `w ≤ 1`,
`tr (A - w Q) = 1 - w`, and `A - w Q = (1 - w) R` for a density operator `R`. -/
lemma exists_isDensityOperator_sub_smul {A Q : E →L[ℂ] E} (hA : IsDensityOperator A)
    (hQ : IsDensityOperator Q) {w : ℝ} (hw : 0 ≤ w) (hD : 0 ≤ A - (w : ℂ) • Q) :
    w ≤ 1 ∧ posTrace (A - (w : ℂ) • Q) = ENNReal.ofReal (1 - w) ∧
      ∃ R, IsDensityOperator R ∧ A - (w : ℂ) • Q = ((1 - w : ℝ) : ℂ) • R := by
  have htr : posTrace (A - (w : ℂ) • Q) + ENNReal.ofReal w = 1 := by
    rw [← hA.posTrace_eq_one, ← mul_one (ENNReal.ofReal w), ← hQ.posTrace_eq_one,
      ← posTrace_smul hw, ← posTrace_add hD (smul_nonneg_of_nonneg hw hQ.nonneg), sub_add_cancel]
  have hw1 : w ≤ 1 := by
    have h : ENNReal.ofReal w ≤ 1 := htr ▸ le_add_self
    exact ENNReal.ofReal_le_one.mp h
  have hD1 : posTrace (A - (w : ℂ) • Q) = ENNReal.ofReal (1 - w) := by
    rw [ENNReal.ofReal_sub _ hw, ENNReal.ofReal_one, ← htr]
    exact (ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top).symm
  refine ⟨hw1, hD1, ?_⟩
  rcases hw1.eq_or_lt with rfl | hlt
  · refine ⟨Q, hQ, ?_⟩
    rw [sub_self, Complex.ofReal_zero, zero_smul]
    exact (posTrace_eq_zero_iff hD).mp (by rw [hD1, sub_self, ENNReal.ofReal_zero])
  · have h0 : 0 < 1 - w := by linarith
    refine ⟨_, isDensityOperator_inv_smul hD h0 hD1, ?_⟩
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h0.ne', Complex.ofReal_one, one_smul]

/-- The affinity argument. Along a branch of probability `w`, the unconditioned output
`Ψⁿ (Q 0)` contains the branch's final state with weight `w`: `Ψⁿ (Q 0) - w Q n` is positive. -/
theorem nonneg_iterate_sub_of_isBranch {Ψ : (E →L[ℂ] E) → E →L[ℂ] E}
    (hΨ : IsStateAdaptiveProjective Ψ) {n : ℕ} {Q : ℕ → E →L[ℂ] E} {p : ℕ → ℝ}
    (h : IsBranch Ψ n Q p) : ∀ k ≤ n,
      IsDensityOperator (Ψ^[k] (Q 0)) ∧ 0 ≤ ∏ j ∈ Finset.range k, p j ∧
      0 ≤ Ψ^[k] (Q 0) - ((∏ j ∈ Finset.range k, p j : ℝ) : ℂ) • Q k := by
  intro k hk
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Finset.range_zero, Finset.prod_empty,
      Complex.ofReal_one, one_smul, sub_self, zero_le_one, le_refl, and_true]
    exact isDensityOperator_of_isPure h.1
  | succ k ih =>
    obtain ⟨hA, hw0, hD⟩ := ih (by omega)
    set w := ∏ j ∈ Finset.range k, p j
    set A := Ψ^[k] (Q 0)
    have hQk := isDensityOperator_of_isPure (h.isPure k (by omega))
    obtain ⟨hp0, hD'⟩ := (h.2 k (by omega)).nonneg hΨ (h.isPure k (by omega))
    obtain ⟨hw1, -, R, hR, hDR⟩ := exists_isDensityOperator_sub_smul hA hQk hw0 hD
    have hAR : A = (w : ℂ) • Q k + ((1 - w : ℝ) : ℂ) • R := by rw [← hDR]; abel
    have hΨA : Ψ^[k + 1] (Q 0) = (w : ℂ) • Ψ (Q k) + ((1 - w : ℝ) : ℂ) • Ψ R := by
      rw [Function.iterate_succ_apply', show Ψ^[k] (Q 0) = A from rfl, hAR,
        hΨ.affine _ _ hQk hR w hw0 hw1]
    rw [Finset.prod_range_succ]
    refine ⟨by rw [Function.iterate_succ_apply']; exact hΨ.isDensityOperator _ hA,
      mul_nonneg hw0 hp0, ?_⟩
    have heq : Ψ^[k + 1] (Q 0) - ((w * p k : ℝ) : ℂ) • Q (k + 1) =
        (w : ℂ) • (Ψ (Q k) - (p k : ℂ) • Q (k + 1)) + ((1 - w : ℝ) : ℂ) • Ψ R := by
      rw [hΨA, Complex.ofReal_mul, smul_sub, smul_smul]
      abel
    rw [heq]
    exact add_nonneg (by rw [Complex.coe_smul]; exact smul_nonneg hw0 hD')
      (smul_nonneg_of_nonneg (sub_nonneg.mpr hw1) (hΨ.isDensityOperator R hR).nonneg)

/-- Along a branch of probability `w`, the unconditioned output is within `2 (1 - w)` of the
branch's final state in trace norm. -/
theorem traceENorm_iterate_sub_le_of_isBranch {Ψ : (E →L[ℂ] E) → E →L[ℂ] E}
    (hΨ : IsStateAdaptiveProjective Ψ) {n : ℕ} {Q : ℕ → E →L[ℂ] E} {p : ℕ → ℝ}
    (h : IsBranch Ψ n Q p) :
    traceENorm (Ψ^[n] (Q 0) - Q n) ≤ ENNReal.ofReal (2 * (1 - ∏ k ∈ Finset.range n, p k)) := by
  obtain ⟨hA, hw0, hD⟩ := nonneg_iterate_sub_of_isBranch hΨ h n le_rfl
  set w := ∏ k ∈ Finset.range n, p k
  have hQn := isDensityOperator_of_isPure (h.isPure n le_rfl)
  obtain ⟨hw1, htr, -⟩ := exists_isDensityOperator_sub_smul hA hQn hw0 hD
  have h1w : 0 ≤ 1 - w := by linarith
  have hsplit : Ψ^[n] (Q 0) - Q n =
      (Ψ^[n] (Q 0) - (w : ℂ) • Q n) - ((1 - w : ℝ) : ℂ) • Q n := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    abel
  rw [hsplit]
  refine (traceENorm_sub_le_add _ _).trans ?_
  rw [traceENorm_of_nonneg hD, traceENorm_of_nonneg (smul_nonneg_of_nonneg h1w hQn.nonneg), htr,
    posTrace_smul h1w, hQn.posTrace_eq_one, mul_one, ← ENNReal.ofReal_add h1w h1w]
  exact le_of_eq (congrArg ENNReal.ofReal (by ring))

/-- With perfect prediction, the limit of a projective process maps pure states to pure states:
the unconditioned output is within `2 (1 - w)` of the predicted branch, whose probability `w`
tends to one, so the branch's final states converge to `Φ t P` in trace norm. -/
theorem IsProjectiveLimit.isPure {Φ Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : IsProjectiveLimit Φ Ψ)
    {t : ℝ} (ht : 0 < t) {P : E →L[ℂ] E} (hP : IsPure P) : IsPure (Φ t P) := by
  obtain ⟨Q, p, -, hb, hw, -⟩ := h.prediction t ht P hP
  have hb' : ∀ᶠ n : ℕ in atTop, Q n 0 = P ∧ IsBranch (Ψ (t / n)) n (Q n) (p n) ∧ 0 < n :=
    (hb.and (eventually_gt_atTop 0)).mono fun n hn => ⟨hn.1.1, hn.1.2, hn.2⟩
  have h2 : Tendsto (fun n => ENNReal.ofReal (2 * (1 - ∏ k ∈ Finset.range n, p n k))) atTop
      (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (((tendsto_const_nhds (x := (1 : ℝ))).sub hw).const_mul 2)
  have hsum := h2.add (h.tendsto t ht P (isDensityOperator_of_isPure hP))
  rw [add_zero] at hsum
  refine isPure_of_tendsto_traceENorm (hb'.mono fun n hn => hn.2.1.isPure n le_rfl)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => zero_le) ?_)
  filter_upwards [hb'] with n ⟨h0, hn, hpos⟩
  have hd := traceENorm_iterate_sub_le_of_isBranch (h.stateAdaptive _ (by positivity)) hn
  rw [h0, traceENorm_sub_comm] at hd
  exact (traceENorm_sub_le _ _ _).trans (add_le_add_left hd _)

/-- **Theorem 18**, DR-PROJ ⇒ DR-EV: prediction makes every `Φ t` map pure states to pure states,
and reconstruction inverts it on pure states. -/
theorem DrProj.drEv {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (hΦ : IsEvolution Φ) (h : DrProj Φ) :
    DrEv Φ := by
  obtain ⟨Ψ, hΨ, Φ', Ψ', hΨ', hinv⟩ := h
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · have hid : ∀ ρ, IsPure ρ → Φ 0 ρ = ρ := fun ρ hρ =>
      hΦ.map_zero ρ (isDensityOperator_of_isPure hρ)
    exact ⟨fun ρ hρ => (hid ρ hρ).symm ▸ hρ, fun ρ hρ σ hσ h => by rwa [hid ρ hρ, hid σ hσ] at h,
      fun ρ hρ => ⟨ρ, hρ, hid ρ hρ⟩⟩
  · refine ⟨fun ρ hρ => hΨ.isPure ht hρ, fun ρ hρ σ hσ h => ?_,
      fun ρ hρ => ⟨Φ' t ρ, hΨ'.isPure ht hρ, (hinv t ht ρ hρ).2⟩⟩
    rw [← (hinv t ht ρ hρ).1, ← (hinv t ht σ hσ).1, show Φ t ρ = Φ t σ from h]

/-- **Theorem 18**, DR-PROJ ⇒ DR-UNIT: DR-EV, then the brief on the Schrödinger equation
(Proposition 1 for each `t` and Bargmann's theorem for `ℝ`). -/
theorem DrProj.drUnit {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (hΦ : IsEvolution Φ) (h : DrProj Φ) :
    DrUnit Φ :=
  (h.drEv hΦ).drUnit hΦ

/-- **Theorem 18**, any dimension, possibly unbounded generator: over QST:H and the evolution
structure of `IsEvolution`, DR-UNIT ⇔ DR-PROJ. -/
theorem drUnit_iff_drProj {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (hΦ : IsEvolution Φ) :
    DrUnit Φ ↔ DrProj Φ :=
  ⟨DrUnit.drProj, DrProj.drUnit hΦ⟩

end UnitaryProjectiveEvolution.InfiniteDimensional
