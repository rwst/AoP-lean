/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Unitary evolution as infinitesimal projective processes.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a finite-dimensional complex Hilbert space `E`, density operators `IsDensity` and pure
states `IsPure` (`ForPhyslib/QuantumMechanics/Wigner`), and an evolution `Φ t` of the density
operators as in the brief "Multiple equivalent characterizations of the Schrödinger equation".
The unitary group is `V t = exp (-i t K)` with `ħ = 1`. Its von Neumann generator
`L ρ = -i (K ρ - ρ K)`, the unitary channel `T t ρ = V t ρ V t†` and the resolvent
`Ψ τ = (1 - τ L)⁻¹` are in `ForPhyslib/QuantumMechanics/VonNeumannResolvent`. In finite dimension
every generator is bounded, so the brief's cutoff `H_τ = f_τ(H)` is not needed.

Definition 1:
* `IsStateAdaptiveProjective`  an affine map of the density operators acting on each `ρ` as
  `∑ₐ Pₐ ρ Pₐ` for a projective decomposition `IsProjectiveDecomposition` that depends on `ρ`.

Propositions:
* `isStateAdaptiveProjective_vonNeumannResolvent`  Proposition 2, with the decomposition given
  by the spectral projectors of `Ψ τ ρ` (`pinching_vonNeumannResolvent`, eqs. (10)–(12)).
* `norm_vonNeumannResolvent_sub_unitaryChannel_le`  Proposition 13, eq. (14), in operator norm:
  `‖Ψ τ ρ - T τ ρ‖ ≤ 8 ‖K‖² τ²` on density operators.
* `exists_spectralProj_max_eq_proj`  Proposition 13, eq. (15): for a pure state `P`, the
  spectral projector `F_τ(P)` at the largest eigenvalue `q_τ(P)` is pure, `1 - q_τ(P) ≤ 8 ‖K‖² τ²`
  and `‖F_τ(P) - T τ P‖ ≤ 48 ‖K‖² τ²` once `8 ‖K‖² τ² ≤ ½`.
* `implemented_of_bijOnPure`  Proposition 17, from the brief on the Schrödinger equation.

Conditions:
* `IsOutcome`, `IsBranch`  an outcome of a state-adaptive projective process on a pure state,
  and a branch of repeated outcomes, whose probability is the product of the outcome probabilities;
* `PerfectPrediction`  for large `n`, branches of `n` steps of duration `t / n` whose
  probability tends to one and whose final states converge;
* `IsProjectiveLimit`  `Φ t ρ = lim (Ψ (t / n))ⁿ ρ` for an infinitesimal family `Ψ τ` of
  state-adaptive projective processes, with perfect prediction;
* `DrUnit`  DR-UNIT, from the brief on the Schrödinger equation;
* `DrProj`  DR-PROJ: a projective limit with perfect prediction, and a second one (perfect
  reconstruction) that inverts it on pure states.

Theorem 18:
* `drUnit_iff_drProj`  over `IsEvolution`, DR-UNIT ⇔ DR-PROJ;
* `DrUnit.drProj`  DR-UNIT ⇒ DR-PROJ: the resolvents of `V` predict and those of `t ↦ V (-t)`
  reconstruct (`perfectPrediction_vonNeumannResolvent`, `tendsto_vonNeumannResolvent_iterate`,
  eq. (20), `tendsto_inv_smul_vonNeumannResolvent_sub`);
* `DrProj.drUnit`  DR-PROJ ⇒ DR-UNIT: by affinity the unconditioned output is within
  `2 (1 - w)` of a branch of probability `w` (`norm_iterate_sub_le_of_isBranch`), so every `Φ t`
  maps pure states to pure states (`IsProjectiveLimit.isPure`); reconstruction makes it a
  bijection (`DrProj.drEv`), and the brief on the Schrödinger equation gives DR-UNIT.

The evolution structure from DR-PROJ:
* `IsProjectiveLimit.exists_eq_exp`  a projective limit is `Φ t = exp (t B)` on density
  operators for every `t > 0`: the processes agree on density operators with linear maps `T τ`
  (`AffineOnDensities.basis_constr_apply`), `(T τ - 1) / τ → B` in operator norm, and
  `(T (t / n))ⁿ → exp (t B)` (`tendsto_pow_exp_of_tendsto_smul_sub_one`). This replaces the
  brief's common refinements, which do not cover durations with irrational ratio;
* `IsProjectiveLimit.isEvolution`  with `Φ 0 = 1`, a projective limit has the evolution
  structure `IsEvolution`: affinity, continuity at `0⁺` and `Φ (s + t) = Φ s ∘ Φ t`;
* `drUnit_iff_drProj_and_map_zero`  Theorem 18 without assuming `IsEvolution`: DR-UNIT ⇔
  DR-PROJ with `Φ 0 = 1`.
-/

public import ForMathlib.Analysis.SpecialFunctions.Exponential
public import ForPhyslib.QuantumMechanics.VonNeumannResolvent
public import ForPhyslib.QuantumMechanics.Wigner.AffineExtension
public import SchroedingerEvolution

@[expose] public noncomputable section

namespace UnitaryProjectiveEvolution

open Filter Set QuantumMechanics QuantumMechanics.Wigner SchroedingerEvolution Complex
open scoped Topology InnerProductSpace ComplexOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-! ## Definition 1 -/

/-- A projective decomposition `{Pₐ}` of the identity: orthogonal projectors with `∑ₐ Pₐ = 1`. -/
def IsProjectiveDecomposition {ι : Type} [Fintype ι] (P : ι → E →L[ℂ] E) : Prop :=
  (∀ a, IsStarProjection (P a)) ∧ (∀ a b, a ≠ b → P a * P b = 0) ∧ ∑ a, P a = 1

/-- **Definition 1**: a state-adaptive projective process is an affine map of the density
operators that acts on each density operator `ρ` as the projective measurement `∑ₐ Pₐ ρ Pₐ` of a
projective decomposition `{Pₐ}` depending on `ρ`. -/
structure IsStateAdaptiveProjective (Ψ : (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  isDensity : ∀ ρ, IsDensity ρ → IsDensity (Ψ ρ)
  affine : AffineOnDensities Ψ
  projective : ∀ ρ, IsDensity ρ → ∃ (ι : Type) (_ : Fintype ι) (P : ι → E →L[ℂ] E),
    IsProjectiveDecomposition P ∧ Ψ ρ = ∑ a, P a * ρ * P a

/-- The spectral projectors of a self-adjoint operator form a projective decomposition. -/
lemma isProjectiveDecomposition_spectralProj {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) :
    IsProjectiveDecomposition fun x : spectrumFinset X => spectralProj X x := by
  refine ⟨fun x => ⟨spectralProj_mul_self X x, isSelfAdjoint_spectralProj X x⟩,
    fun x y hxy => ?_, ?_⟩
  · simp [spectralProj_mul_spectralProj, Subtype.coe_injective.ne hxy]
  · rw [Finset.sum_coe_sort (spectrumFinset X) (spectralProj X), sum_spectralProj hX]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- A linear map is affine on density operators. -/
lemma affineOnDensities_of_linearMap (T : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E) :
    AffineOnDensities T := fun ρ σ _ _ t _ _ => by
  rw [map_add, map_smul, map_smul]

/-- **Proposition 2**: the resolvent `(1 - τ L)⁻¹` of the von Neumann generator is a
state-adaptive projective process, for every `τ`. -/
theorem isStateAdaptiveProjective_vonNeumannResolvent (V : UnitaryOneParameterGroup E) (τ : ℝ) :
    IsStateAdaptiveProjective (vonNeumannResolvent V τ) where
  isDensity _ hρ := isDensity_vonNeumannResolvent V τ hρ
  affine := affineOnDensities_of_linearMap (vonNeumannResolvent V τ).toLinearMap
  projective ρ hρ := ⟨spectrumFinset (vonNeumannResolvent V τ ρ), inferInstance,
    fun x => spectralProj (vonNeumannResolvent V τ ρ) x,
    isProjectiveDecomposition_spectralProj
      (isSelfAdjoint_vonNeumannResolvent V τ hρ.isSelfAdjoint), by
    rw [Finset.sum_coe_sort (spectrumFinset _)
      (fun x => spectralProj _ x * ρ * spectralProj _ x)]
    exact (pinching_vonNeumannResolvent V τ hρ.isSelfAdjoint).symm⟩

/-! ## Outcomes and branches -/

/-- `Q` is an outcome, of probability `p`, of the projective measurement that `Ψ` performs on the
pure state `P`: for a projective decomposition `{Fₐ}` realizing `Ψ P = ∑ₐ Fₐ P Fₐ`, one term
`Fₐ P Fₐ` is `p Q` with `Q` pure. -/
def IsOutcome (Ψ : (E →L[ℂ] E) → E →L[ℂ] E) (P : E →L[ℂ] E) (p : ℝ) (Q : E →L[ℂ] E) : Prop :=
  IsPure Q ∧ ∃ (ι : Type) (_ : Fintype ι) (F : ι → E →L[ℂ] E), IsProjectiveDecomposition F ∧
    Ψ P = ∑ a, F a * P * F a ∧ ∃ a, F a * P * F a = (p : ℂ) • Q

/-- A branch of `n` steps of `Ψ`: a sequence of pure states `Q 0, …, Q n` in which each `Q (k + 1)`
is an outcome on `Q k`, of probability `p k`. Its probability is `∏ₖ p k`. -/
def IsBranch (Ψ : (E →L[ℂ] E) → E →L[ℂ] E) (n : ℕ) (Q : ℕ → E →L[ℂ] E) (p : ℕ → ℝ) : Prop :=
  IsPure (Q 0) ∧ ∀ k < n, IsOutcome Ψ (Q k) (p k) (Q (k + 1))

omit [FiniteDimensional ℂ E] in
lemma isPositive_mul_mul {F ρ : E →L[ℂ] E} (hF : IsSelfAdjoint F)
    (hρ : (ρ : E →ₗ[ℂ] E).IsPositive) : ((F * ρ * F : E →L[ℂ] E) : E →ₗ[ℂ] E).IsPositive := by
  have h := ((ContinuousLinearMap.isPositive_toLinearMap_iff ρ).mp hρ).conj_adjoint F
  rw [← ContinuousLinearMap.star_eq_adjoint, hF.star_eq] at h
  exact h.toLinearMap

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
lemma re_trace_nonneg {D : E →L[ℂ] E} (hD : (D : E →ₗ[ℂ] E).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E D).re :=
  (RCLike.nonneg_iff.mp hD.trace_nonneg).1

/-- An outcome has probability in `[0, 1]`, and `Ψ P - p Q` is positive. -/
lemma IsOutcome.isPositive {Ψ : (E →L[ℂ] E) → E →L[ℂ] E} (hΨ : IsStateAdaptiveProjective Ψ)
    {P Q : E →L[ℂ] E} {p : ℝ} (hP : IsPure P) (h : IsOutcome Ψ P p Q) :
    0 ≤ p ∧ p ≤ 1 ∧ ((Ψ P - (p : ℂ) • Q : E →L[ℂ] E) : E →ₗ[ℂ] E).IsPositive := by
  classical
  obtain ⟨hQ, ι, _, F, hF, hΨP, a, ha⟩ := h
  have hpos : ∀ b, ((F b * P * F b : E →L[ℂ] E) : E →ₗ[ℂ] E).IsPositive := fun b =>
    isPositive_mul_mul (hF.1 b).isSelfAdjoint hP.isExtremeDensity.1.isPositive
  have hrest : Ψ P - (p : ℂ) • Q = ∑ b ∈ Finset.univ.erase a, F b * P * F b := by
    rw [hΨP, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha, add_sub_cancel_left]
  have hD : ((Ψ P - (p : ℂ) • Q : E →L[ℂ] E) : E →ₗ[ℂ] E).IsPositive := by
    rw [hrest, ContinuousLinearMap.toLinearMap_sum]
    exact Finset.sum_induction _ LinearMap.IsPositive (fun _ _ ha hb => ha.add hb)
      LinearMap.isPositive_zero fun b _ => hpos b
  have htrQ : (LinearMap.trace ℂ E ((p : ℂ) • Q : E →L[ℂ] E)).re = p := by
    rw [ContinuousLinearMap.toLinearMap_smul, map_smul, hQ.isExtremeDensity.1.trace_eq_one]
    simp
  have hp0 : 0 ≤ p := by
    rw [← htrQ, ← ha]
    exact re_trace_nonneg (hpos a)
  have hp1 : p ≤ 1 := by
    have h := re_trace_nonneg hD
    rw [ContinuousLinearMap.toLinearMap_sub, map_sub, Complex.sub_re, htrQ,
      (hΨ.isDensity P hP.isExtremeDensity.1).trace_eq_one, one_re] at h
    linarith
  exact ⟨hp0, hp1, hD⟩

omit [FiniteDimensional ℂ E] in
lemma IsBranch.isPure {Ψ : (E →L[ℂ] E) → E →L[ℂ] E} {n : ℕ} {Q : ℕ → E →L[ℂ] E} {p : ℕ → ℝ}
    (h : IsBranch Ψ n Q p) : ∀ k ≤ n, IsPure (Q k)
  | 0, _ => h.1
  | k + 1, hk => (h.2 k hk).1

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
lemma re_trace_smul (c : ℝ) {Q : E →L[ℂ] E} (hQ : IsDensity Q) :
    LinearMap.trace ℂ E ((c : ℂ) • Q : E →L[ℂ] E) = c := by
  rw [ContinuousLinearMap.toLinearMap_smul, map_smul, hQ.trace_eq_one, smul_eq_mul, mul_one]

omit [CompleteSpace E] in
/-- A positive operator of trace `1 - w` is `(1 - w) R` for a density operator `R`. -/
lemma exists_isDensity_eq_smul {D R₀ : E →L[ℂ] E} (hD : (D : E →ₗ[ℂ] E).IsPositive) {w : ℝ}
    (hw : w ≤ 1) (htr : LinearMap.trace ℂ E D = ((1 - w : ℝ) : ℂ)) (hR₀ : IsDensity R₀) :
    ∃ R, IsDensity R ∧ D = ((1 - w : ℝ) : ℂ) • R := by
  rcases hw.eq_or_lt with rfl | hw
  · refine ⟨R₀, hR₀, ?_⟩
    have h := ContinuousLinearMap.norm_le_re_trace hD
    rw [htr] at h
    rw [sub_self, ofReal_zero, zero_smul]
    exact norm_le_zero_iff.mp (by simpa using h)
  · have h0 : (1 - w : ℝ) ≠ 0 := by linarith
    refine ⟨(((1 - w)⁻¹ : ℝ) : ℂ) • D, ⟨?_, ?_⟩, ?_⟩
    · rw [ContinuousLinearMap.toLinearMap_smul]
      exact hD.smul_of_nonneg (by exact_mod_cast (inv_pos.mpr (by linarith : (0 : ℝ) < 1 - w)).le)
    · rw [ContinuousLinearMap.toLinearMap_smul, map_smul, htr, smul_eq_mul, ← ofReal_mul,
        inv_mul_cancel₀ h0, ofReal_one]
    · rw [smul_smul, ← ofReal_mul, mul_inv_cancel₀ h0, ofReal_one, one_smul]

/-- The affinity argument. Along a branch of probability `w`, the unconditioned output
`Ψⁿ (Q 0)` contains the branch's final state with weight `w`: `Ψⁿ (Q 0) - w Q n` is positive. -/
theorem isPositive_iterate_sub_of_isBranch {Ψ : (E →L[ℂ] E) → E →L[ℂ] E}
    (hΨ : IsStateAdaptiveProjective Ψ) {n : ℕ} {Q : ℕ → E →L[ℂ] E} {p : ℕ → ℝ}
    (h : IsBranch Ψ n Q p) : ∀ k ≤ n,
      IsDensity (Ψ^[k] (Q 0)) ∧ 0 ≤ ∏ j ∈ Finset.range k, p j ∧ ∏ j ∈ Finset.range k, p j ≤ 1 ∧
      ((Ψ^[k] (Q 0) - ((∏ j ∈ Finset.range k, p j : ℝ) : ℂ) • Q k : E →L[ℂ] E) :
        E →ₗ[ℂ] E).IsPositive := by
  intro k hk
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Finset.range_zero, Finset.prod_empty, ofReal_one,
      one_smul, sub_self, zero_le_one, le_refl, true_and]
    exact ⟨(h.1).isExtremeDensity.1, by simp⟩
  | succ k ih =>
    obtain ⟨hA, hw0, hw1, hD⟩ := ih (by omega)
    set w := ∏ j ∈ Finset.range k, p j
    set A := Ψ^[k] (Q 0)
    have hQk := (h.isPure k (by omega)).isExtremeDensity.1
    obtain ⟨hp0, hp1, hD'⟩ := (h.2 k (by omega)).isPositive hΨ (h.isPure k (by omega))
    have htr : LinearMap.trace ℂ E (A - (w : ℂ) • Q k : E →L[ℂ] E) = ((1 - w : ℝ) : ℂ) := by
      rw [ContinuousLinearMap.toLinearMap_sub, map_sub, hA.trace_eq_one, re_trace_smul w hQk,
        ofReal_sub, ofReal_one]
    obtain ⟨R, hR, hDR⟩ := exists_isDensity_eq_smul hD hw1 htr hQk
    have hAR : A = (w : ℂ) • Q k + ((1 - w : ℝ) : ℂ) • R := by rw [← hDR]; abel
    have hΨA : Ψ^[k + 1] (Q 0) = (w : ℂ) • Ψ (Q k) + ((1 - w : ℝ) : ℂ) • Ψ R := by
      rw [Function.iterate_succ_apply', show Ψ^[k] (Q 0) = A from rfl, hAR,
        hΨ.affine _ _ hQk hR w hw0 hw1]
    rw [Finset.prod_range_succ]
    refine ⟨by rw [Function.iterate_succ_apply']; exact hΨ.isDensity _ hA, mul_nonneg hw0 hp0,
      (mul_le_of_le_one_right hw0 hp1).trans hw1, ?_⟩
    have heq : Ψ^[k + 1] (Q 0) - ((w * p k : ℝ) : ℂ) • Q (k + 1) =
        (w : ℂ) • (Ψ (Q k) - (p k : ℂ) • Q (k + 1)) + ((1 - w : ℝ) : ℂ) • Ψ R := by
      rw [hΨA, ofReal_mul, smul_sub, smul_smul]
      abel
    rw [heq, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.toLinearMap_smul]
    exact (hD'.smul_of_nonneg (by exact_mod_cast hw0)).add
      ((hΨ.isDensity R hR).isPositive.smul_of_nonneg (by exact_mod_cast (sub_nonneg.mpr hw1)))

/-- Along a branch of probability `w`, the unconditioned output is within `2 (1 - w)` of the
branch's final state. -/
theorem norm_iterate_sub_le_of_isBranch {Ψ : (E →L[ℂ] E) → E →L[ℂ] E}
    (hΨ : IsStateAdaptiveProjective Ψ) {n : ℕ} {Q : ℕ → E →L[ℂ] E} {p : ℕ → ℝ}
    (h : IsBranch Ψ n Q p) :
    ‖Ψ^[n] (Q 0) - Q n‖ ≤ 2 * (1 - ∏ k ∈ Finset.range n, p k) := by
  obtain ⟨hA, hw0, hw1, hD⟩ := isPositive_iterate_sub_of_isBranch hΨ h n le_rfl
  set w := ∏ k ∈ Finset.range n, p k
  have hQn := (h.isPure n le_rfl).isExtremeDensity.1
  have hDn : ‖Ψ^[n] (Q 0) - (w : ℂ) • Q n‖ ≤ 1 - w := by
    have h1 := ContinuousLinearMap.norm_le_re_trace hD
    rw [ContinuousLinearMap.toLinearMap_sub, map_sub, hA.trace_eq_one, re_trace_smul w hQn] at h1
    simpa using h1
  calc ‖Ψ^[n] (Q 0) - Q n‖ = ‖(Ψ^[n] (Q 0) - (w : ℂ) • Q n) - ((1 - w : ℝ) : ℂ) • Q n‖ := by
        congr 1
        rw [ofReal_sub, ofReal_one, sub_smul, one_smul]
        abel
    _ ≤ (1 - w) + (1 - w) * 1 := by
        refine (norm_sub_le _ _).trans (add_le_add hDn ?_)
        rw [norm_smul, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        gcongr
        exact hQn.norm_le_one
    _ = 2 * (1 - w) := by ring

/-! ## Proposition 17 -/

omit [CompleteSpace E] in
/-- **Proposition 17** (affine pure-state correspondence): an affine map of the density operators
that maps the pure states bijectively onto the pure states is conjugation by a unitary or an
anti-unitary. This is Proposition 1 of the brief on the Schrödinger equation. -/
theorem implemented_of_bijOnPure {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ)) (hT : AffineOnDensities T) (h : BijOnPure T) :
    ImplementedByUnitaryOrAntiunitary T :=
  ((affine_pure_state_correspondence hD hT).out 1 3).mp h

/-! ## Conditions -/

/-- Perfect prediction over the elapsed time `t`: from every pure state there is, for all large
`n`, a branch of `n` steps of the process of duration `t / n`, whose probability tends to one and
whose final state converges. -/
def PerfectPrediction (Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) (t : ℝ) : Prop :=
  ∀ P, IsPure P → ∃ (Q : ℕ → ℕ → E →L[ℂ] E) (p : ℕ → ℕ → ℝ) (R : E →L[ℂ] E),
    (∀ᶠ n in atTop, Q n 0 = P ∧ IsBranch (Ψ (t / n)) n (Q n) (p n)) ∧
    Tendsto (fun n => ∏ k ∈ Finset.range n, p n k) atTop (𝓝 1) ∧
    Tendsto (fun n => Q n n) atTop (𝓝 R)

/-- The evolution `Φ` is the limit of repeated applications of the infinitesimal state-adaptive
projective process `Ψ`, with perfect prediction: every `Ψ τ` with `τ > 0` is state-adaptive
projective, `(Ψ τ ρ - ρ) / τ` converges as `τ → 0⁺`, `(Ψ (t / n))ⁿ ρ → Φ t ρ`, and prediction is
perfect. -/
structure IsProjectiveLimit (Φ Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  stateAdaptive : ∀ τ > 0, IsStateAdaptiveProjective (Ψ τ)
  infinitesimal : ∃ L : (E →L[ℂ] E) → E →L[ℂ] E, ∀ ρ, IsDensity ρ →
    Tendsto (fun τ : ℝ => τ⁻¹ • (Ψ τ ρ - ρ)) (𝓝[>] 0) (𝓝 (L ρ))
  tendsto : ∀ t > 0, ∀ ρ, IsDensity ρ →
    Tendsto (fun n : ℕ => (Ψ (t / n))^[n] ρ) atTop (𝓝 (Φ t ρ))
  prediction : ∀ t > 0, PerfectPrediction Ψ t

/-- **DR-PROJ**: the evolution is a projective limit with perfect prediction, and also with
perfect reconstruction: a second projective limit `Φ'` runs backwards, recovering every pure
initial state from the evolved one and every pure final state from the reconstructed one. -/
def DrProj (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ Ψ, IsProjectiveLimit Φ Ψ ∧ ∃ Φ' Ψ', IsProjectiveLimit Φ' Ψ' ∧
    ∀ t > 0, ∀ P, IsPure P → Φ' t (Φ t P) = P ∧ Φ t (Φ' t P) = P

/-! ## DR-PROJ ⇒ DR-UNIT -/

omit [CompleteSpace E] in
/-- The pure states are closed: they are the image of the unit sphere. -/
lemma isClosed_setOf_isPure : IsClosed {ρ : E →L[ℂ] E | IsPure ρ} := by
  have h : {ρ : E →L[ℂ] E | IsPure ρ} = (fun ψ => proj ψ) '' Metric.sphere 0 1 := by
    ext ρ
    simp [IsPure, eq_comm]
  have : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  have hc : Continuous fun ψ : E => proj ψ := by
    simp_rw [proj, InnerProductSpace.rankOne_def']
    exact (ContinuousLinearMap.toSpanSingletonLIE ℂ E).continuous.clm_comp (innerSL ℂ).continuous
  rw [h]
  exact ((isCompact_sphere 0 1).image hc).isClosed

/-- With perfect prediction, the limit of a projective process maps pure states to pure states:
the unconditioned output is within `2 (1 - w)` of the predicted branch, whose probability `w` tends
to one. -/
theorem IsProjectiveLimit.isPure {Φ Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : IsProjectiveLimit Φ Ψ)
    {t : ℝ} (ht : 0 < t) {P : E →L[ℂ] E} (hP : IsPure P) : IsPure (Φ t P) := by
  obtain ⟨Q, p, R, hb, hw, hR⟩ := h.prediction t ht P hP
  have hb' : ∀ᶠ n : ℕ in atTop, Q n 0 = P ∧ IsBranch (Ψ (t / n)) n (Q n) (p n) ∧ 0 < n :=
    (hb.and (eventually_gt_atTop 0)).mono fun n hn => ⟨hn.1.1, hn.1.2, hn.2⟩
  have hdist : Tendsto (fun n : ℕ => (Ψ (t / n))^[n] P - Q n n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h2 : Tendsto (fun n => 2 * (1 - ∏ k ∈ Finset.range n, p n k)) atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hw).const_mul 2
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ h2
    filter_upwards [hb'] with n ⟨h0, hn, hpos⟩
    have h := norm_iterate_sub_le_of_isBranch (h.stateAdaptive _ (by positivity)) hn
    rwa [h0] at h
  have hlim : Tendsto (fun n : ℕ => (Ψ (t / n))^[n] P) atTop (𝓝 R) := by
    simpa using hdist.add hR
  rw [tendsto_nhds_unique (h.tendsto t ht P hP.isExtremeDensity.1) hlim]
  exact isClosed_setOf_isPure.mem_of_tendsto hR
    (hb'.mono fun n hn => hn.2.1.isPure n le_rfl)

/-- **Theorem 18**, DR-PROJ ⇒ DR-EV: prediction makes every `Φ t` map pure states to pure states,
and reconstruction inverts it on pure states. -/
theorem DrProj.drEv {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (hΦ : IsEvolution Φ) (h : DrProj Φ) :
    DrEv Φ := by
  obtain ⟨Ψ, hΨ, Φ', Ψ', hΨ', hinv⟩ := h
  intro t ht
  rcases ht.eq_or_lt with rfl | ht
  · have hid : ∀ ρ, IsPure ρ → Φ 0 ρ = ρ := fun ρ hρ => hΦ.map_zero ρ hρ.isExtremeDensity.1
    exact ⟨fun ρ hρ => (hid ρ hρ).symm ▸ hρ, fun ρ hρ σ hσ h => by rwa [hid ρ hρ, hid σ hσ] at h,
      fun ρ hρ => ⟨ρ, hρ, hid ρ hρ⟩⟩
  · refine ⟨fun ρ hρ => hΨ.isPure ht hρ, fun ρ hρ σ hσ h => ?_,
      fun ρ hρ => ⟨Φ' t ρ, hΨ'.isPure ht hρ, (hinv t ht ρ hρ).2⟩⟩
    rw [← (hinv t ht ρ hρ).1, ← (hinv t ht σ hσ).1, show Φ t ρ = Φ t σ from h]

/-- **Theorem 18**, DR-PROJ ⇒ DR-UNIT. -/
theorem DrProj.drUnit {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (hΦ : IsEvolution Φ) (h : DrProj Φ) :
    DrUnit Φ :=
  (h.drEv hΦ).drUnit hΦ

/-! ## DR-UNIT ⇒ DR-PROJ -/

section Forward

variable (V : UnitaryOneParameterGroup E)

/-- One predicted step: for a unit `χ` and `8 ‖K‖² τ² ≤ ½`, the largest outcome of `Ψ τ` on
`|χ⟩⟨χ|` is a pure state `|φ⟩⟨φ|` of probability at least `1 - 8 ‖K‖² τ²`, within `48 ‖K‖² τ²` of
the unitary step (Proposition 13). -/
lemma exists_isOutcome_vonNeumannResolvent {χ : E} (hχ : ‖χ‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hδ : 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ 2⁻¹) :
    ∃ x : ℝ, ∃ φ : E, ‖φ‖ = 1 ∧ IsOutcome (vonNeumannResolvent V τ) (proj χ) x (proj φ) ∧
      1 - 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ x ∧
      ‖proj φ - unitaryChannel V τ (proj χ)‖ ≤ 48 * ‖V.generator‖ ^ 2 * τ ^ 2 := by
  obtain ⟨x, hx, -, hx1, φ, hφ, hPφ, hdist⟩ := exists_spectralProj_max_eq_proj V hχ hτ hδ
  have hs := (isDensity_proj hχ).isSelfAdjoint
  obtain ⟨-, -, -, hdec, hsum⟩ := (isStateAdaptiveProjective_vonNeumannResolvent V τ).projective _
    (isDensity_proj hχ)
  refine ⟨x, φ, hφ, ⟨⟨φ, hφ, rfl⟩, spectrumFinset (vonNeumannResolvent V τ (proj χ)),
    inferInstance, fun y => spectralProj (vonNeumannResolvent V τ (proj χ)) y,
    isProjectiveDecomposition_spectralProj (isSelfAdjoint_vonNeumannResolvent V τ hs), ?_,
    ⟨x, hx⟩, ?_⟩, hx1, hdist⟩
  · rw [Finset.sum_coe_sort (spectrumFinset _)
      (fun y => spectralProj _ y * proj χ * spectralProj _ y)]
    exact (pinching_vonNeumannResolvent V τ hs).symm
  · rw [spectralProj_mul_mul_vonNeumannResolvent V τ hs, hPφ, Complex.coe_smul]

/-- Perfect prediction for the resolvent: following the largest outcome at every step, the branch
probability is at least `1 - 8 ‖K‖² t² / n` and the final state is within `48 ‖K‖² t² / n` of the
unitary evolution. -/
theorem perfectPrediction_vonNeumannResolvent {t : ℝ} (ht : 0 < t) :
    PerfectPrediction (fun τ => vonNeumannResolvent V τ) t := by
  rintro _ ⟨ψ, hψ, rfl⟩
  set M := ‖V.generator‖
  have hstep : ∀ τ : ℝ, ∀ χ : E, ∃ x : ℝ, ∃ φ : E, ‖χ‖ = 1 → 0 ≤ τ →
      8 * M ^ 2 * τ ^ 2 ≤ 2⁻¹ →
      ‖φ‖ = 1 ∧ IsOutcome (vonNeumannResolvent V τ) (proj χ) x (proj φ) ∧
      1 - 8 * M ^ 2 * τ ^ 2 ≤ x ∧ ‖proj φ - unitaryChannel V τ (proj χ)‖ ≤ 48 * M ^ 2 * τ ^ 2 := by
    intro τ χ
    by_cases h : ‖χ‖ = 1 ∧ 0 ≤ τ ∧ 8 * M ^ 2 * τ ^ 2 ≤ 2⁻¹
    · obtain ⟨x, φ, hφ⟩ := exists_isOutcome_vonNeumannResolvent V h.1 h.2.1 h.2.2
      exact ⟨x, φ, fun _ _ _ => hφ⟩
    · exact ⟨0, χ, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose x φ hxφ using hstep
  set χ : ℕ → ℕ → E := fun n k => (φ (t / n))^[k] ψ
  have hsmall : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 8 * M ^ 2 * (t / n) ^ 2 ≤ 2⁻¹ := by
    have h : Tendsto (fun n : ℕ => 8 * M ^ 2 * (t / n) ^ 2) atTop (𝓝 0) := by
      simpa using ((tendsto_const_div_atTop_nhds_zero_nat t).pow 2).const_mul (8 * M ^ 2)
    exact (eventually_gt_atTop 0).and
      (((tendsto_order.1 h).2 2⁻¹ (by norm_num)).mono fun _ h => h.le)
  -- along the branch, every vector is a unit vector and every step is controlled
  have hgood : ∀ n : ℕ, 0 < n → 8 * M ^ 2 * (t / n) ^ 2 ≤ 2⁻¹ → ∀ k, ‖χ n k‖ = 1 ∧
      ‖φ (t / n) (χ n k)‖ = 1 ∧
      IsOutcome (vonNeumannResolvent V (t / n)) (proj (χ n k)) (x (t / n) (χ n k))
        (proj (χ n (k + 1))) ∧
      1 - 8 * M ^ 2 * (t / n) ^ 2 ≤ x (t / n) (χ n k) ∧
      ‖proj (χ n (k + 1)) - unitaryChannel V (t / n) (proj (χ n k))‖ ≤
        48 * M ^ 2 * (t / n) ^ 2 := by
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
    obtain ⟨h1, h2, h3, h4⟩ := hxφ (t / n) (χ n k) (hunit k) hτ hδ
    exact ⟨hunit k, h1, hsucc ▸ h2, h3, hsucc ▸ h4⟩
  have hbranch : ∀ᶠ n : ℕ in atTop, (fun k => proj (χ n k)) 0 = proj ψ ∧
      IsBranch (vonNeumannResolvent V (t / n)) n (fun k => proj (χ n k))
        (fun k => x (t / n) (χ n k)) := by
    filter_upwards [hsmall] with n ⟨hn, hδ⟩
    exact ⟨rfl, ⟨ψ, hψ, rfl⟩, fun k _ => (hgood n hn hδ k).2.2.1⟩
  refine ⟨fun n k => proj (χ n k), fun n k => x (t / n) (χ n k),
    unitaryChannel V t (proj ψ), hbranch, ?_, ?_⟩
  · -- the branch probability tends to one
    have hlow : Tendsto (fun n : ℕ => 1 - 8 * M ^ 2 * t ^ 2 / n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
        (tendsto_const_div_atTop_nhds_zero_nat (8 * M ^ 2 * t ^ 2))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hsmall] with n ⟨hn, hδ⟩
      have hn' : (n : ℝ) ≠ 0 := by positivity
      calc 1 - 8 * M ^ 2 * t ^ 2 / n = 1 + n * (-(8 * M ^ 2 * (t / n) ^ 2)) := by
            field_simp
            ring
        _ ≤ (1 + -(8 * M ^ 2 * (t / n) ^ 2)) ^ n := one_add_mul_le_pow (by linarith) n
        _ = ∏ k ∈ Finset.range n, (1 - 8 * M ^ 2 * (t / n) ^ 2) := by
            rw [Finset.prod_const, Finset.card_range, ← sub_eq_add_neg]
        _ ≤ ∏ k ∈ Finset.range n, x (t / n) (χ n k) :=
            Finset.prod_le_prod₀ (fun _ _ => by linarith) fun k _ => (hgood n hn hδ k).2.2.2.1
    · filter_upwards [hsmall] with n ⟨hn, hδ⟩
      refine Finset.prod_le_one₀ (fun k _ => ?_) fun k _ => ?_
      · exact ((hgood n hn hδ k).2.2.1.isPositive
          (isStateAdaptiveProjective_vonNeumannResolvent V _) ⟨_, (hgood n hn hδ k).1, rfl⟩).1
      · exact ((hgood n hn hδ k).2.2.1.isPositive
          (isStateAdaptiveProjective_vonNeumannResolvent V _) ⟨_, (hgood n hn hδ k).1, rfl⟩).2.1
  · -- the final state tends to the unitary evolution
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (48 * M ^ 2 * t ^ 2))
    filter_upwards [hsmall] with n ⟨hn, hδ⟩
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have h := norm_sub_unitaryChannel_le_of_step V (x := fun k => proj (χ n k)) (τ := t / n)
      (ε := 48 * M ^ 2 * (t / n) ^ 2) n fun k _ => (hgood n hn hδ k).2.2.2.2
    rw [mul_div_cancel₀ t hn'] at h
    refine h.trans_eq ?_
    field_simp

/-- The resolvents of a unitary group form a projective limit of its unitary channel. -/
theorem isProjectiveLimit_vonNeumannResolvent {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (hΦ : ∀ t > 0, ∀ ρ, IsDensity ρ → Φ t ρ = unitaryChannel V t ρ) :
    IsProjectiveLimit Φ fun τ => vonNeumannResolvent V τ where
  stateAdaptive τ _ := isStateAdaptiveProjective_vonNeumannResolvent V τ
  infinitesimal := ⟨vonNeumannGenerator V.generator, fun _ hρ =>
    tendsto_inv_smul_vonNeumannResolvent_sub V hρ⟩
  tendsto t ht ρ hρ := by
    rw [hΦ t ht ρ hρ]
    exact tendsto_vonNeumannResolvent_iterate V ht.le hρ
  prediction _ ht := perfectPrediction_vonNeumannResolvent V ht

end Forward

/-- **Theorem 18**, DR-UNIT ⇒ DR-PROJ: the resolvents `(1 - τ L)⁻¹` give prediction, and the
resolvents `(1 + τ L)⁻¹` of the reversed group give reconstruction. -/
theorem DrUnit.drProj {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : DrUnit Φ) : DrProj Φ := by
  obtain ⟨V, hV⟩ := h
  refine ⟨_, isProjectiveLimit_vonNeumannResolvent V fun t ht => hV t ht.le,
    fun t => unitaryChannel (timeReversal V) t, _,
    isProjectiveLimit_vonNeumannResolvent (timeReversal V) fun _ _ _ _ => rfl,
    fun t ht P hP => ⟨?_, ?_⟩⟩
  · rw [hV t ht.le P hP.isExtremeDensity.1]
    show unitaryChannel (timeReversal V) t (unitaryChannel V t P) = P
    rw [unitaryChannel_timeReversal, ← unitaryChannel_add, neg_add_cancel, unitaryChannel_zero]
  · rw [hV t ht.le _ (isDensity_unitaryChannel _ t hP.isExtremeDensity.1)]
    show unitaryChannel V t (unitaryChannel (timeReversal V) t P) = P
    rw [unitaryChannel_timeReversal, ← unitaryChannel_add, add_neg_cancel, unitaryChannel_zero]

/-- **Theorem 18**: over QST:H and the evolution structure of `IsEvolution`, DR-UNIT ⇔ DR-PROJ. -/
theorem drUnit_iff_drProj {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (hΦ : IsEvolution Φ) :
    DrUnit Φ ↔ DrProj Φ :=
  ⟨DrUnit.drProj, DrProj.drUnit hΦ⟩

/-! ## The evolution structure from DR-PROJ

DR-PROJ defines `Φ t` only through steps of duration exactly `t / n`, so the brief's common
refinements do not prove `Φ (s + t) = Φ s ∘ Φ t` when `s / t` is irrational. In finite dimension
the processes are linear on density operators, the family is differentiable at `0` in operator
norm, and `Φ t = exp (t B)` on density operators for every `t > 0`; composition follows for all
durations. DR-PROJ says nothing about `Φ 0`, which is taken to be the identity. -/

section Structure

open NormedSpace

/-- The operators on the operators, as their values on a basis of the operators. -/
def basisEquiv {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E →L[ℂ] E)) :
    (ι → E →L[ℂ] E) ≃L[ℂ] ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) :=
  ((b.constr ℂ).trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

lemma basisEquiv_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E →L[ℂ] E))
    (w : ι → E →L[ℂ] E) (ρ : E →L[ℂ] E) : basisEquiv b w ρ = b.constr ℂ w ρ :=
  rfl

lemma basisEquiv_apply_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E →L[ℂ] E))
    (w : ι → E →L[ℂ] E) (i : ι) : basisEquiv b w (b i) = w i := by
  rw [basisEquiv_apply, Module.Basis.constr_basis]

/-- Convergence on a basis is convergence in operator norm. -/
lemma tendsto_of_tendsto_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E →L[ℂ] E))
    {α : Type*} {l : Filter α} {F : α → (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E} {w : ι → E →L[ℂ] E}
    (h : ∀ i, Tendsto (fun a => F a (b i)) l (𝓝 (w i))) :
    Tendsto F l (𝓝 (basisEquiv b w)) := by
  refine (((basisEquiv b).continuous.tendsto _).comp (tendsto_pi_nhds.mpr h)).congr fun a => ?_
  refine ContinuousLinearMap.coe_injective (b.ext fun i => ?_)
  simp [basisEquiv_apply_basis]

omit [FiniteDimensional ℂ E] in
/-- Repeated state-adaptive projective processes preserve density operators. -/
lemma IsStateAdaptiveProjective.isDensity_iterate {Ψ : (E →L[ℂ] E) → E →L[ℂ] E}
    (hΨ : IsStateAdaptiveProjective Ψ) (n : ℕ) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    IsDensity (Ψ^[n] ρ) := by
  induction n with
  | zero => exact hρ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hΨ.isDensity _ ih

/-- **A projective limit is an exponential**: on density operators, `Φ t = exp (t B)` for every
`t > 0`, with `B` the operator-norm derivative at `0` of the linear maps that extend the processes
`Ψ τ`. -/
theorem IsProjectiveLimit.exists_eq_exp {Φ Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (h : IsProjectiveLimit Φ Ψ) : ∃ B : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E,
      ∀ t > 0, ∀ ρ, IsDensity ρ → Φ t ρ = exp (algebraMap ℝ _ t * B) ρ := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine ⟨0, fun t _ ρ hρ => absurd hρ.trace_eq_one ?_⟩
    rw [Subsingleton.elim ρ 0]
    simp
  obtain ⟨s, _, b, hb⟩ := exists_basis_isDensity (E := E)
  obtain ⟨L, hL⟩ := h.infinitesimal
  set T : ℝ → (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E := fun τ => basisEquiv b fun i => Ψ τ (b i)
  have hT : ∀ τ > 0, ∀ ρ, IsDensity ρ → T τ ρ = Ψ τ ρ := fun τ hτ ρ hρ =>
    (h.stateAdaptive τ hτ).affine.basis_constr_apply b hb hρ
  have hiter : ∀ τ > 0, ∀ n : ℕ, ∀ ρ, IsDensity ρ → (Ψ τ)^[n] ρ = (T τ ^ n) ρ := by
    intro τ hτ n
    induction n with
    | zero => intro ρ _; simp
    | succ n ih =>
      intro ρ hρ
      rw [Function.iterate_succ_apply, ih _ ((h.stateAdaptive τ hτ).isDensity ρ hρ),
        ← hT τ hτ ρ hρ, pow_succ]
      rfl
  have hB : Tendsto (fun τ : ℝ => τ⁻¹ • (T τ - 1)) (𝓝[>] 0)
      (𝓝 (basisEquiv b fun i => L (b i))) := by
    refine tendsto_of_tendsto_basis b fun i => ?_
    refine (hL (b i) (hb i)).congr fun τ => ?_
    simp [T, basisEquiv_apply_basis]
  refine ⟨basisEquiv b fun i => L (b i), fun t ht ρ hρ => ?_⟩
  have hl := tendsto_pow_exp_of_tendsto_smul_sub_one hB ht
  rw [Algebra.smul_def] at hl
  have h2 : Tendsto (fun n : ℕ => (Ψ (t / n))^[n] ρ) atTop
      (𝓝 (exp (algebraMap ℝ _ t * basisEquiv b fun i => L (b i)) ρ)) := by
    refine (((ContinuousLinearMap.apply ℂ (E →L[ℂ] E) ρ).continuous.tendsto _).comp hl).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
    exact (hiter _ (div_pos ht (Nat.cast_pos.mpr hn)) n ρ hρ).symm
  exact tendsto_nhds_unique (h.tendsto t ht ρ hρ) h2

/-- **The evolution structure from DR-PROJ**: a projective limit with `Φ 0 = 1` maps density
operators to density operators, is affine, satisfies `Φ (s + t) = Φ s ∘ Φ t` for all durations,
and is continuous at `0⁺`. -/
theorem IsProjectiveLimit.isEvolution {Φ Ψ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (h : IsProjectiveLimit Φ Ψ) (h0 : ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ) : IsEvolution Φ := by
  let _ : NormedAlgebra ℚ ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) :=
    NormedAlgebra.restrictScalars ℚ ℂ ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E)
  obtain ⟨B, hB⟩ := h.exists_eq_exp
  have hexp : ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ t ρ = exp (algebraMap ℝ _ t * B) ρ := by
    intro t ht ρ hρ
    rcases ht.eq_or_lt with rfl | ht
    · rw [h0 ρ hρ, map_zero, zero_mul, NormedSpace.exp_zero, one_apply_eq_self]
    · exact hB t ht ρ hρ
  have hD : ∀ t ≥ 0, ∀ ρ, IsDensity ρ → IsDensity (Φ t ρ) := by
    intro t ht ρ hρ
    rcases ht.eq_or_lt with rfl | ht
    · rwa [h0 ρ hρ]
    · refine isClosed_setOf_isDensity.mem_of_tendsto (h.tendsto t ht ρ hρ) ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      exact (h.stateAdaptive _ (div_pos ht (Nat.cast_pos.mpr hn))).isDensity_iterate n hρ
  refine ⟨hD, fun t ht ρ σ hρ hσ c hc0 hc1 => ?_, h0, fun s hs t ht ρ hρ => ?_, fun ρ hρ => ?_⟩
  · rw [hexp t ht _ (hρ.smul_add_smul hσ hc0 hc1), hexp t ht ρ hρ, hexp t ht σ hσ, map_add,
      map_smul, map_smul]
  · rw [hexp (s + t) (add_nonneg hs ht) ρ hρ, hexp s hs _ (hD t ht ρ hρ), hexp t ht ρ hρ,
      map_add, add_mul, exp_add_of_commute ((Algebra.commute_algebraMap_left s _).mul_left
        ((Algebra.commute_algebraMap_right t B).mul_right (Commute.refl B)))]
    rfl
  · have hc : Continuous fun t : ℝ => exp (algebraMap ℝ _ t * B) ρ :=
      (exp_continuous.comp ((continuous_algebraMap ℝ _).mul continuous_const)).clm_apply
        continuous_const
    exact hc.continuousWithinAt.congr (fun t ht => hexp t ht ρ hρ) (hexp 0 le_rfl ρ hρ)

/-- DR-PROJ with `Φ 0 = 1` gives the evolution structure. -/
theorem DrProj.isEvolution {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : DrProj Φ)
    (h0 : ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ) : IsEvolution Φ :=
  let ⟨_, hΨ, _⟩ := h
  hΨ.isEvolution h0

/-- **Theorem 18**, DR-PROJ ⇒ DR-UNIT, without assuming `IsEvolution`. -/
theorem DrProj.drUnit_of_map_zero {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : DrProj Φ)
    (h0 : ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ) : DrUnit Φ :=
  h.drUnit (h.isEvolution h0)

omit [FiniteDimensional ℂ E] in
/-- A unitary evolution is the identity at `t = 0`. -/
theorem DrUnit.map_zero {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (h : DrUnit Φ) :
    ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ := by
  obtain ⟨U, hU⟩ := h
  intro ρ hρ
  rw [hU 0 le_rfl ρ hρ]
  exact unitaryChannel_zero U ρ

/-- **Theorem 18** without assuming `IsEvolution`: DR-UNIT ⇔ DR-PROJ with `Φ 0 = 1`. -/
theorem drUnit_iff_drProj_and_map_zero {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} :
    DrUnit Φ ↔ DrProj Φ ∧ ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ :=
  ⟨fun h => ⟨DrUnit.drProj h, DrUnit.map_zero h⟩, fun h => h.1.drUnit_of_map_zero h.2⟩

end Structure

end UnitaryProjectiveEvolution
