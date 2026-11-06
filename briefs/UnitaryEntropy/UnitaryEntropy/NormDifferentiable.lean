/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Schrödinger equation is equivalent to information conservation: EVDIFF does not make the
propagator differentiable in operator norm.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

In any dimension, `schrodinger_of_preserves_vonNeumannEntropy` chooses the phases of the unitaries
`U t` so that `t ↦ U t ψ` is differentiable at `t₀` for every `ψ`. In finite dimension the same
choice makes `t ↦ U t` differentiable in operator norm. In infinite dimension no choice does: on
`ℓ²(ℕ)` let `U t` multiply the component along `e_{k(t)}`, `k(t) = ⌈1/|t|⌉ + 1`, by `e^{it}`.
Conjugation by `U t` satisfies all hypotheses of `schrodinger_of_preserves_vonNeumannEntropy` at
`t₀ = 0`, even with derivative `0` in operator norm on each density operator, because
`‖ρ e_k‖ → 0`. But every unitary `V t` inducing it is a phase times `U t`, and
`‖U t - 1‖ = |e^{it} - 1|` is not `o(t)`.
* `phaseOp`  `1 + (z - 1) |e⟩⟨e|`, unitary for `|z| = 1` (`phaseOp_mem_unitary`), with
  `‖U ρ U† - ρ‖ ≤ (2|z - 1| + |z - 1|²) ‖ρ e‖` for self-adjoint `ρ`
  (`norm_phaseOp_mul_mul_star_sub_le`);
* `tendsto_norm_apply_hilbertBasis`  `‖ρ eₙ‖ → 0`, as `∑ ‖√ρ eₙ‖² = 1`;
* `movingPhase`  the family `U t`;
* `hasDerivAt_movingPhase_conj`  EVDIFF at `0` in operator norm, with derivative `0`;
* `not_exists_differentiableAt_movingPhase`  no unitary family inducing it near `0` is
  differentiable at `0`: its derivative would vanish on every `eₙ`, hence be `0`;
* `movingPhase_counterexample`  all of it.
-/

public import ForPhyslib.QuantumMechanics.Kadison
public import ForPhyslib.QuantumMechanics.VonNeumannEntropy
public import ForPhyslib.QuantumMechanics.Wigner.Propagator

@[expose] public noncomputable section

namespace UnitaryEntropy

open Filter InnerProductSpace QuantumMechanics QuantumMechanics.Wigner
open ContinuousLinearMap (posTrace)
open scoped lp Topology

/-! ## A phase on one vector -/

section PhaseOp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

lemma star_proj (e : E) : star (proj e) = proj e :=
  (proj_nonneg e).isSelfAdjoint.star_eq

omit [CompleteSpace E] in
lemma one_add_smul_proj_mul {e : E} (he : ‖e‖ = 1) (w v : ℂ) :
    (1 + w • proj e) * (1 + v • proj e) = 1 + (w + v + w * v) • proj e := by
  simp only [mul_add, add_mul, one_mul, mul_one, smul_mul_smul_comm, proj_mul_proj_self he]
  module

/-- `1 + (z - 1) |e⟩⟨e|`: for a unit vector `e`, it multiplies the component along `e` by `z`. -/
def phaseOp (z : ℂ) (e : E) : E →L[ℂ] E := 1 + (z - 1) • proj e

omit [CompleteSpace E] in
lemma phaseOp_apply (z : ℂ) (e x : E) : phaseOp z e x = x + ((z - 1) * ⟪e, x⟫_ℂ) • e := by
  simp [phaseOp, smul_smul]

omit [CompleteSpace E] in
lemma phaseOp_apply_self (z : ℂ) {e : E} (he : ‖e‖ = 1) : phaseOp z e e = z • e := by
  rw [phaseOp_apply, inner_self_eq_norm_sq_to_K, he]
  module

omit [CompleteSpace E] in
lemma phaseOp_apply_of_inner_eq_zero (z : ℂ) {e x : E} (h : ⟪e, x⟫_ℂ = 0) : phaseOp z e x = x := by
  rw [phaseOp_apply, h, mul_zero, zero_smul, add_zero]

lemma star_phaseOp (z : ℂ) (e : E) : star (phaseOp z e) = phaseOp (star z) e := by
  rw [phaseOp, phaseOp, star_add, star_one, star_smul, star_proj, star_sub, star_one]

omit [CompleteSpace E] in
lemma phaseOp_mul {e : E} (he : ‖e‖ = 1) (z w : ℂ) :
    phaseOp z e * phaseOp w e = phaseOp (z * w) e := by
  rw [phaseOp, phaseOp, phaseOp, one_add_smul_proj_mul he]
  congr 2
  ring

lemma phaseOp_mem_unitary {z : ℂ} (hz : ‖z‖ = 1) {e : E} (he : ‖e‖ = 1) :
    phaseOp z e ∈ unitary (E →L[ℂ] E) := by
  have hzz : star z * z = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hz]
    simp
  have h1 : phaseOp 1 e = 1 := by simp [phaseOp]
  rw [Unitary.mem_iff, star_phaseOp, phaseOp_mul he, phaseOp_mul he, mul_comm z, hzz, h1]
  exact ⟨rfl, rfl⟩

/-- `U ρ U† - ρ` for `U = 1 + (z - 1) |e⟩⟨e|`. -/
lemma phaseOp_mul_mul_star_sub (z : ℂ) (e : E) (ρ : E →L[ℂ] E) :
    phaseOp z e * ρ * star (phaseOp z e) - ρ = (z - 1) • (proj e * ρ) +
      star (z - 1) • (ρ * proj e) + ((z - 1) * star (z - 1)) • (proj e * ρ * proj e) := by
  rw [star_phaseOp]
  simp only [phaseOp, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm,
    star_sub, star_one]
  module

omit [CompleteSpace E] in
lemma norm_mul_proj {e : E} (he : ‖e‖ = 1) (ρ : E →L[ℂ] E) : ‖ρ * proj e‖ = ‖ρ e‖ := by
  rw [ContinuousLinearMap.mul_def, comp_rankOne, norm_rankOne, he, mul_one]

lemma norm_proj_mul {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) {e : E} (he : ‖e‖ = 1) :
    ‖proj e * ρ‖ = ‖ρ e‖ := by
  rw [← norm_mul_proj he, ← norm_star (ρ * proj e), star_mul, star_proj, hρ.star_eq]

omit [CompleteSpace E] in
lemma norm_proj_mul_mul_proj_le {e : E} (he : ‖e‖ = 1) (ρ : E →L[ℂ] E) :
    ‖proj e * ρ * proj e‖ ≤ ‖ρ e‖ := by
  rw [mul_assoc, ← norm_mul_proj he ρ]
  refine (norm_mul_le _ _).trans ?_
  rw [norm_rankOne, he, mul_one, one_mul]

/-- Conjugation by `1 + (z - 1) |e⟩⟨e|` moves a self-adjoint `ρ` by at most
`(2|z - 1| + |z - 1|²) ‖ρ e‖`. -/
lemma norm_phaseOp_mul_mul_star_sub_le {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) (z : ℂ) {e : E}
    (he : ‖e‖ = 1) :
    ‖phaseOp z e * ρ * star (phaseOp z e) - ρ‖ ≤ (2 * ‖z - 1‖ + ‖z - 1‖ ^ 2) * ‖ρ e‖ := by
  rw [phaseOp_mul_mul_star_sub]
  refine (norm_add₃_le).trans ?_
  rw [norm_smul, norm_smul, norm_smul, norm_mul (z - 1), norm_star, norm_proj_mul hρ he,
    norm_mul_proj he]
  have h := mul_le_mul_of_nonneg_left (norm_proj_mul_mul_proj_le he ρ) (sq_nonneg ‖z - 1‖)
  nlinarith

end PhaseOp

/-- A density operator is small on the tail of a Hilbert basis: `‖ρ eₙ‖ → 0`, since
`‖ρ eₙ‖ ≤ ‖√ρ‖ ‖√ρ eₙ‖` and `∑ ‖√ρ eₙ‖² = tr ρ = 1`. -/
theorem tendsto_norm_apply_hilbertBasis {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (b : HilbertBasis ℕ ℂ E) : Tendsto (fun n => ‖ρ (b n)‖) atTop (𝓝 0) := by
  have hs : Summable fun n => ‖CFC.sqrt ρ (b n)‖ ^ 2 := by
    rw [summable_iff_tsum_ofReal_ne_top fun _ => by positivity,
      ← ContinuousLinearMap.posTrace_eq_tsum_norm_sqrt_sq hρ.nonneg b, hρ.posTrace_eq_one]
    exact ENNReal.one_ne_top
  have h := hs.tendsto_atTop_zero.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (by simpa using h.const_mul ‖CFC.sqrt ρ‖)
  conv_lhs => rw [← CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
  exact (CFC.sqrt ρ).le_opNorm _

/-! ## The moving phase on `ℓ²(ℕ)` -/

section MovingPhase

/-- The standard Hilbert basis `e₀, e₁, …` of `ℓ²(ℕ)`. -/
local notation "𝐞" => (default : HilbertBasis ℕ ℂ ℓ²(ℕ, ℂ))

/-- The basis vector carrying the phase at time `t`: `k(t) = ⌈1/|t|⌉ + 1`. -/
def movingIndex (t : ℝ) : ℕ := ⌈|t|⁻¹⌉₊ + 1

/-- The moving phase: `U t` multiplies the component along `e_{k(t)}` by `e^{it}`. -/
def movingPhase (t : ℝ) : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ) :=
  phaseOp (Complex.exp (t * Complex.I)) (𝐞 (movingIndex t))

lemma movingPhase_mem_unitary (t : ℝ) : movingPhase t ∈ unitary (ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) :=
  phaseOp_mem_unitary (Complex.norm_exp_ofReal_mul_I t) ((𝐞).orthonormal.1 _)

lemma movingPhase_zero : movingPhase 0 = 1 := by
  simp [movingPhase, phaseOp]

lemma tendsto_movingIndex : Tendsto movingIndex (𝓝[≠] 0) atTop :=
  (tendsto_add_atTop_nat 1).comp
    (tendsto_nat_ceil_atTop.comp (tendsto_inv_nhdsGT_zero.comp tendsto_abs_nhdsNE_zero))

/-- Away from `e_{k(t)}` the moving phase is the identity; in particular `U t e₀ = e₀`. -/
lemma movingPhase_apply_basis {t : ℝ} {n : ℕ} (h : movingIndex t ≠ n) :
    movingPhase t (𝐞 n) = 𝐞 n :=
  phaseOp_apply_of_inner_eq_zero _ ((𝐞).orthonormal.2 h)

lemma hasDerivAt_exp_mul_I :
    HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I)) Complex.I 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp

/-- **EVDIFF at `0`, in operator norm**: `t ↦ U t ρ U t†` has derivative `0` at `0` for every
density operator `ρ`. -/
theorem hasDerivAt_movingPhase_conj {ρ : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)} (hρ : IsDensityOperator ρ) :
    HasDerivAt (fun t => movingPhase t * ρ * star (movingPhase t)) 0 0 := by
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hasDerivAt_exp_mul_I).norm
  have hsmall : Tendsto (fun t : ℝ => ‖Complex.exp (t * Complex.I) - 1‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((hasDerivAt_exp_mul_I.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).sub_const 1).norm
  have hρe := (tendsto_norm_apply_hilbertBasis hρ 𝐞).comp tendsto_movingIndex
  rw [hasDerivAt_iff_tendsto_slope]
  refine squeeze_zero_norm (fun t => ?_)
    (by simpa using hslope.mul ((hsmall.const_add 2).mul hρe))
  have hb := norm_phaseOp_mul_mul_star_sub_le hρ.isSelfAdjoint (Complex.exp (t * Complex.I))
    ((𝐞).orthonormal.1 (movingIndex t))
  simp only [slope_def_module, norm_smul, movingPhase_zero, star_one, mul_one, one_mul,
    Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  calc _ ≤ ‖(t - 0)⁻¹‖ * ((2 * ‖Complex.exp (t * Complex.I) - 1‖ +
        ‖Complex.exp (t * Complex.I) - 1‖ ^ 2) * ‖ρ (𝐞 (movingIndex t))‖) := by
        gcongr
        exact hb
    _ = _ := by ring

/-- **No differentiable choice of phases**: no family of unitaries `V t` inducing the moving
phase on pure states near `0` is differentiable at `0` in operator norm. -/
theorem not_exists_differentiableAt_movingPhase :
    ¬ ∃ V : ℝ → ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
      (∀ᶠ t in 𝓝 0, V t ∈ unitary (ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) ∧ ∀ ψ : ℓ²(ℕ, ℂ), ‖ψ‖ = 1 →
        movingPhase t * proj ψ * star (movingPhase t) = proj (V t ψ)) ∧
      DifferentiableAt ℝ V 0 := by
  rintro ⟨V, hV, hVd⟩
  have he₀ : ‖𝐞 0‖ = 1 := (𝐞).orthonormal.1 0
  -- `V t = c t • U t` with `c t = ⟪e₀, V t e₀⟫` of modulus one
  set c : ℝ → ℂ := fun t => ⟪𝐞 0, V t (𝐞 0)⟫_ℂ with hc_def
  have hVc : ∀ᶠ t in 𝓝 0, ‖c t‖ = 1 ∧ V t = c t • movingPhase t := hV.mono fun t ⟨hu, h⟩ => by
    have hU := movingPhase_mem_unitary t
    have h' := eq_inner_smul_of_proj_eq hU hu
      (fun ψ hψ => (mul_proj_mul_star_of_mem_unitary hU ψ).symm.trans (h ψ hψ)) he₀
    rw [movingPhase_apply_basis (Nat.add_one_ne_zero _)] at h'
    refine ⟨?_, h'⟩
    have hn := (Unitary.linearIsometryEquiv ⟨V t, hu⟩).norm_map (𝐞 0)
    change ‖V t (𝐞 0)‖ = _ at hn
    rw [h', smul_apply, movingPhase_apply_basis (Nat.add_one_ne_zero _), norm_smul, he₀,
      mul_one] at hn
    exact hn
  have hcd : DifferentiableAt ℝ c 0 :=
    (((innerSL ℂ (𝐞 0)).comp (ContinuousLinearMap.apply ℂ _ (𝐞 0))).restrictScalars
      ℝ).differentiableAt.comp 0 hVd
  have hc0 : c 0 ≠ 0 := fun h => by
    have := hVc.self_of_nhds.1
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hUd : DifferentiableAt ℝ movingPhase 0 :=
    ((hcd.inv hc0).smul hVd).congr_of_eventuallyEq (hVc.mono fun t ⟨hn, h⟩ => by
      have hct : c t ≠ 0 := fun h0 => by rw [h0, norm_zero] at hn; exact zero_ne_one hn
      change movingPhase t = (c t)⁻¹ • V t
      rw [h, inv_smul_smul₀ hct])
  -- its derivative vanishes on every basis vector, hence is `0`
  have hD := hUd.hasDerivAt
  have hD0 : deriv movingPhase 0 = 0 := by
    refine ContinuousLinearMap.ext_on (s := Set.range 𝐞)
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr (𝐞).dense_span) ?_
    rintro _ ⟨n, rfl⟩
    have h1 := ((ContinuousLinearMap.apply ℂ ℓ²(ℕ, ℂ) (𝐞 n)).restrictScalars
      ℝ).hasFDerivAt.comp_hasDerivAt 0 hD
    have hev : (fun t => movingPhase t (𝐞 n)) =ᶠ[𝓝 0] fun _ => 𝐞 n := by
      have h := (tendsto_movingIndex.eventually_ne_atTop n)
      rw [eventually_nhdsWithin_iff] at h
      refine h.mono fun t ht => ?_
      by_cases h0 : t = 0
      · subst h0
        show movingPhase 0 (𝐞 n) = 𝐞 n
        rw [movingPhase_zero]
        rfl
      · exact movingPhase_apply_basis (ht h0)
    exact h1.unique ((hasDerivAt_const 0 (𝐞 n)).congr_of_eventuallyEq hev)
  rw [hD0] at hD
  -- but `‖U t - 1‖ ≥ |e^{it} - 1|`, whose slope tends to `|i| = 1`
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hasDerivAt_exp_mul_I).norm
  rw [Complex.norm_I] at hslope
  have hzero : Tendsto (fun t => ‖slope (fun t : ℝ => Complex.exp (t * Complex.I)) 0 t‖)
      (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_)
      (by simpa using (hasDerivAt_iff_tendsto_slope.mp hD).norm)
    have hk : ‖𝐞 (movingIndex t)‖ = 1 := (𝐞).orthonormal.1 _
    calc ‖slope (fun t : ℝ => Complex.exp (t * Complex.I)) 0 t‖
        = ‖slope movingPhase 0 t (𝐞 (movingIndex t))‖ := by
          simp only [slope_def_module, smul_apply, sub_apply, movingPhase_zero, one_apply_eq_self]
          rw [movingPhase, phaseOp_apply_self _ hk, norm_smul, norm_smul]
          conv_rhs => rw [show ∀ (z : ℂ) (x : ℓ²(ℕ, ℂ)), z • x - x = (z - 1) • x from
            fun z x => by rw [sub_smul, one_smul]]
          rw [norm_smul, hk, mul_one]
          simp
      _ ≤ ‖slope movingPhase 0 t‖ * ‖𝐞 (movingIndex t)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖slope movingPhase 0 t‖ := by rw [hk, mul_one]
  exact one_ne_zero (tendsto_nhds_unique hslope hzero)

/-- **EVDIFF does not give a norm-differentiable propagator in infinite dimension.** On `ℓ²(ℕ)`,
`Φ t ρ = U t ρ U t†` with the moving phase `U t` satisfies every hypothesis of
`schrodinger_of_preserves_vonNeumannEntropy` at `t₀ = 0`, with EVDIFF in operator norm, but no
family of unitaries inducing `Φ t` on pure states near `0` is differentiable at `0` in operator
norm. -/
theorem movingPhase_counterexample :
    ∃ Φ : ℝ → (ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) → ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
      (∀ t ρ, IsDensityOperator ρ → IsDensityOperator (Φ t ρ)) ∧
      (∀ t ρ, IsDensityOperator ρ → vonNeumannEntropy (Φ t ρ) = vonNeumannEntropy ρ) ∧
      (∀ t ρ, IsDensityOperator ρ → ∃ σ, IsDensityOperator σ ∧ Φ t σ = ρ) ∧
      (∀ t ρ σ, IsDensityOperator ρ → IsDensityOperator σ →
        Φ t (mix ρ σ) = mix (Φ t ρ) (Φ t σ)) ∧
      (∀ ρ, Φ 0 ρ = ρ) ∧
      (∀ ρ, IsDensityOperator ρ → HasDerivAt (fun t => Φ t ρ) 0 0) ∧
      ¬ ∃ V : ℝ → ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ),
        (∀ᶠ t in 𝓝 0, V t ∈ unitary (ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℕ, ℂ)) ∧
          ∀ ψ : ℓ²(ℕ, ℂ), ‖ψ‖ = 1 → Φ t (proj ψ) = proj (V t ψ)) ∧
        DifferentiableAt ℝ V 0 := by
  have hU := fun t => Unitary.mem_iff.mp (movingPhase_mem_unitary t)
  refine ⟨fun t ρ => movingPhase t * ρ * star (movingPhase t),
    fun t ρ hρ => hρ.conj (hU t).1, fun t ρ hρ => hρ.vonNeumannEntropy_conj (hU t).1,
    fun t ρ hρ => ⟨_, hρ.conj (U := star (movingPhase t)) (by rw [star_star]; exact (hU t).2),
      ?_⟩, fun t ρ σ _ _ => ?_, fun ρ => by simp [movingPhase_zero],
    fun ρ hρ => hasDerivAt_movingPhase_conj hρ, not_exists_differentiableAt_movingPhase⟩
  · simp only [star_star, ← mul_assoc, (hU t).2, one_mul]
    rw [mul_assoc, (hU t).2, mul_one]
  · change movingPhase t * ((2⁻¹ : ℂ) • ρ + (2⁻¹ : ℂ) • σ) * star (movingPhase t) =
      (2⁻¹ : ℂ) • (movingPhase t * ρ * star (movingPhase t)) +
        (2⁻¹ : ℂ) • (movingPhase t * σ * star (movingPhase t))
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_mul_assoc]

end MovingPhase

end UnitaryEntropy
