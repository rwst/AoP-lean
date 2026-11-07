/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.ForwardHamiltonian
public import ForPhyslib.QuantumMechanics.Howland

/-!
# The Howland generator on compactly supported functions

Howland's group `(W σ f)(t) = U t (t - σ) f(t - σ)` on `L²(ℝ; E)` is `e^{-iσK/ħ}` for a
self-adjoint `K`. Here `K` is made concrete as the forward Hamiltonian of `W`, and computed on
compactly supported continuous `f` whose moving orbit `σ ↦ U t (t - σ) f(t - σ)` is
differentiable, with derivative `G σ t` jointly continuous: `K f = iħ G 0`.

When `U` and `f` are differentiable, `G 0 t = (iħ)⁻¹ H(t) f(t) - f'(t)`, with
`H(t) x = -iħ ∂ₛ U t s x` at `s = t`, so this is `K = H(t) - iħ ∂ₜ`. For a time-independent
evolution `U t s = e^{-i(t-s)H/ħ}` this is the generator `H - iħ ∂ₜ` of `e^{-iσH/ħ}` combined with
translation.

## i. Overview

`K` is the forward Hamiltonian of `W`, which is tangent to its own unitary group, so by the local
Stone theorem it is self-adjoint and equal to the generator of Stone's theorem. On `f` as above,
the difference quotient `(W σ f - f) / σ - G 0` vanishes outside the compact set
`tsupport f + [0, 1]` for `σ ∈ [0, 1]`, and on it is uniformly small by the mean value theorem and
uniform continuity of `G` near `σ = 0`. So it tends to `0` in `L²`.

## ii. Key results

- `QuantumMechanics.UnitaryPropagator.howlandGenerator`: the forward Hamiltonian of `W`.
- `QuantumMechanics.UnitaryPropagator.isSelfAdjoint_howlandGenerator`: it is self-adjoint, and
  `W σ = e^{-iσK/ħ}` (`howland_eq_schrodingerPropagator`).
- `QuantumMechanics.UnitaryPropagator.howlandGenerator_toLp`: `K f = iħ ∂_σ (W σ f)` at `0`,
  computed pointwise, for compactly supported continuous `f`.

## iii. References

- J. S. Howland, *Stationary scattering theory for time-dependent Hamiltonians*, Math. Ann. 207
  (1974), 315–335.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Set Asymptotics
open scoped ENNReal InnerProductSpace Pointwise

namespace QuantumMechanics.UnitaryPropagator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (U : UnitaryPropagator E)

/-- **The Howland generator** `K`, the forward Hamiltonian `iħ ∂₊ W σ f` at `σ = 0` of Howland's
group. -/
def howlandGenerator (ħ : ℝ) : Lp E 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp E 2 (volume : Measure ℝ) :=
  forwardHamiltonian U.howland ħ

/-- A self-adjoint `K` with `W σ = e^{-iσK/ħ}` is the Howland generator. -/
theorem howlandGenerator_eq {ħ : ℝ} (hħ : ħ ≠ 0)
    {K : Lp E 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp E 2 (volume : Measure ℝ)} (hK : IsSelfAdjoint K)
    (hU : ∀ σ, U.howland σ = schrodingerPropagator hħ hK σ) : U.howlandGenerator ħ = K :=
  forwardHamiltonian_eq_of_isLittleO hħ U.howland_zero
    (fun σ _ => ContinuousLinearMap.inner_map_map_of_mem_unitary (U.howland_mem_unitary σ)) hK
    fun ψ _ => by
      simp only [hU, sub_self]
      exact isLittleO_zero _ _

/-- **The Howland generator is self-adjoint.** -/
theorem isSelfAdjoint_howlandGenerator {ħ : ℝ} (hħ : ħ ≠ 0) :
    IsSelfAdjoint (U.howlandGenerator ħ) := by
  obtain ⟨K, hK, -, hU⟩ := U.exists_howlandGenerator hħ
  rw [U.howlandGenerator_eq hħ hK hU]
  exact hK

/-- Howland's group is `e^{-iσK/ħ}` for the Howland generator `K`. -/
theorem howland_eq_schrodingerPropagator {ħ : ℝ} (hħ : ħ ≠ 0) (σ : ℝ) :
    U.howland σ = schrodingerPropagator hħ (U.isSelfAdjoint_howlandGenerator hħ) σ := by
  obtain ⟨K, hK, -, hU⟩ := U.exists_howlandGenerator hħ
  have h := U.howlandGenerator_eq hħ hK hU
  subst h
  exact hU σ

variable {U} {f : ℝ → E} {G : ℝ → ℝ → E}

/-- Where `f` vanishes near `t`, so does the moving orbit, and its derivative at `0` is `0`. -/
lemma deriv_eq_zero_of_notMem_tsupport
    (hG : ∀ σ t, HasDerivAt (fun σ => U t (t - σ) (f (t - σ))) (G σ t) σ) {t : ℝ}
    (ht : t ∉ tsupport f) : G 0 t = 0 := by
  have hf : ∀ᶠ s in 𝓝 t, f s = 0 := notMem_tsupport_iff_eventuallyEq.mp ht
  have hlim : Tendsto (fun σ : ℝ => t - σ) (𝓝 0) (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
  have h0 : (fun _ : ℝ => (0 : E)) =ᶠ[𝓝 0] fun σ => U t (t - σ) (f (t - σ)) := by
    filter_upwards [hlim.eventually hf] with σ hσ
    rw [hσ, map_zero]
  exact ((hG 0 t).congr_of_eventuallyEq h0).unique (hasDerivAt_const 0 0)

lemma hasCompactSupport_deriv (hfs : HasCompactSupport f)
    (hG : ∀ σ t, HasDerivAt (fun σ => U t (t - σ) (f (t - σ))) (G σ t) σ) :
    HasCompactSupport (G 0) :=
  hfs.mono' fun t ht => by
    by_contra h
    exact ht (deriv_eq_zero_of_notMem_tsupport hG h)

lemma memLp_deriv (hfs : HasCompactSupport f)
    (hG : ∀ σ t, HasDerivAt (fun σ => U t (t - σ) (f (t - σ))) (G σ t) σ)
    (hGc : Continuous (Function.uncurry G)) : MemLp (G 0) 2 (volume : Measure ℝ) :=
  (hGc.comp (continuous_const.prodMk continuous_id) :).memLp_of_hasCompactSupport
    (hasCompactSupport_deriv hfs hG)

/-- **The Howland generator on compactly supported functions.** Let `f` be continuous with
compact support, and let the moving orbit `σ ↦ U t (t - σ) f(t - σ)` have derivative `G σ t`,
jointly continuous in `(σ, t)`. Then `f` is in the domain of `K`, and `K f = iħ G 0`. -/
theorem howlandGenerator_toLp (ħ : ℝ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (hG : ∀ σ t, HasDerivAt (fun σ => U t (t - σ) (f (t - σ))) (G σ t) σ)
    (hGc : Continuous (Function.uncurry G)) :
    ∃ h : (hf.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs).toLp f ∈
        (U.howlandGenerator ħ).domain,
      U.howlandGenerator ħ ⟨_, h⟩ = (Complex.I * ħ) • (memLp_deriv hfs hG hGc).toLp (G 0) := by
  set fL := (hf.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs).toLp f
  set gL := (memLp_deriv hfs hG hGc).toLp (G 0)
  -- The compact set outside which the difference quotient vanishes for `σ ∈ [0, 1]`.
  set S := tsupport f + Icc (0 : ℝ) 1
  have hS : IsCompact S := hfs.isCompact.add isCompact_Icc
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hSf : volume S ≠ ∞ := hS.measure_lt_top.ne
  set m := (volume : Measure ℝ).real S ^ (1 / (2 : ℝ≥0∞).toReal)
  have hm : 0 ≤ m := Real.rpow_nonneg measureReal_nonneg _
  -- The pointwise estimate.
  have hpt : ∀ ε > 0, ∃ δ > 0, δ ≤ 1 ∧ ∀ σ ∈ Icc 0 δ, ∀ t,
      ‖U t (t - σ) (f (t - σ)) - f t - σ • G 0 t‖ ≤ S.indicator (fun _ => ε * σ) t := by
    intro ε hε
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ t ∈ S, ‖G s t - G 0 t‖ < ε := by
      refine hS.eventually_forall_of_forall_eventually fun t _ => ?_
      have hc : Continuous fun z : ℝ × ℝ => G z.1 z.2 - G 0 z.2 :=
        hGc.sub (hGc.comp (continuous_const.prodMk continuous_snd))
      have hlim : Tendsto (fun z : ℝ × ℝ => ‖G z.1 z.2 - G 0 z.2‖) (𝓝 (0, t)) (𝓝 0) := by
        simpa using (hc.tendsto (0, t)).norm
      exact hlim.eventually_lt_const hε
    obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.eventually_nhds_iff.mp hev
    refine ⟨min (δ₀ / 2) 1, by positivity, min_le_right _ _, fun σ hσ t => ?_⟩
    by_cases ht : t ∈ S
    · rw [indicator_of_mem ht]
      have hd : ∀ s ∈ Icc 0 σ, HasDerivWithinAt
          (fun s => U t (t - s) (f (t - s)) - s • G 0 t) (G s t - G 0 t) (Icc 0 σ) s :=
        fun s _ => by
          have h := (hG s t).fun_sub ((hasDerivAt_id s).smul_const (G 0 t))
          refine h.hasDerivWithinAt.congr_deriv ?_
          simp
      have hb : ∀ s ∈ Ico 0 σ, ‖G s t - G 0 t‖ ≤ ε := by
        intro s hs
        refine (hδ ?_ t ht).le
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
        linarith [hs.2, hσ.2, min_le_left (δ₀ / 2) 1]
      have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb σ (right_mem_Icc.mpr hσ.1)
      calc ‖U t (t - σ) (f (t - σ)) - f t - σ • G 0 t‖
          = ‖(U t (t - σ) (f (t - σ)) - σ • G 0 t) -
              (U t (t - 0) (f (t - 0)) - (0 : ℝ) • G 0 t)‖ := by
            rw [sub_zero, U.self_apply, zero_smul, sub_zero]
            congr 1
            abel
        _ ≤ ε * (σ - 0) := h
        _ = ε * σ := by ring
    · rw [indicator_of_notMem ht]
      have hz : ∀ s ∈ Icc (0 : ℝ) 1, f (t - s) = 0 := fun s hs => by
        refine image_eq_zero_of_notMem_tsupport fun h => ht ?_
        exact ⟨t - s, h, s, hs, by ring⟩
      have hG0 : G 0 t = 0 := deriv_eq_zero_of_notMem_tsupport hG fun h => ht ⟨t, h, 0, by simp⟩
      have hσ1 : σ ∈ Icc (0 : ℝ) 1 := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
      have hft : f t = 0 := by simpa using hz 0 (by simp)
      rw [hz σ hσ1, hft, hG0, map_zero]
      simp
  -- The `L²` estimate.
  have ho : (fun σ : ℝ => U.howland σ fL - fL - σ • gL) =o[𝓝[≥] 0] fun σ => σ := by
    refine isLittleO_iff.mpr fun c hc => ?_
    obtain ⟨δ, hδ, -, hpt'⟩ := hpt (c / (m + 1)) (by positivity)
    filter_upwards [Icc_mem_nhdsGE hδ] with σ hσ
    have hle : ‖U.howland σ fL - fL - σ • gL‖ ≤
        ‖indicatorConstLp 2 hSm hSf (c / (m + 1) * σ)‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      have hshift := (measurePreserving_sub_right volume σ).quasiMeasurePreserving.ae_eq_comp
        (MemLp.coeFn_toLp (hf.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs))
      filter_upwards [Lp.coeFn_sub (U.howland σ fL - fL) (σ • gL),
        Lp.coeFn_sub (U.howland σ fL) fL, Lp.coeFn_smul σ gL, U.coeFn_howland σ fL, hshift,
        MemLp.coeFn_toLp (hf.memLp_of_hasCompactSupport (p := 2) (μ := volume) hfs),
        MemLp.coeFn_toLp (memLp_deriv hfs hG hGc),
        indicatorConstLp_coeFn (p := 2) (hs := hSm) (hμs := hSf) (c := c / (m + 1) * σ)] with
        t h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
      simp only [Function.comp_apply] at h₅
      rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₃, Pi.smul_apply, h₄, h₅, h₆, h₇, h₈]
      refine (hpt' σ hσ t).trans (le_of_eq ?_)
      by_cases ht : t ∈ S
      · rw [indicator_of_mem ht, Real.norm_of_nonneg (by
          have := hσ.1; positivity)]
      · rw [indicator_of_notMem ht, norm_zero]
    refine hle.trans ?_
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, Real.norm_of_nonneg (by
      have := hσ.1; positivity), Real.norm_of_nonneg hσ.1]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hc.le hσ.1]
  have hd : HasDerivWithinAt (fun σ => U.howland σ fL) gL (Ici 0) 0 := by
    rw [hasDerivWithinAt_iff_isLittleO]
    simpa [U.howland_zero] using ho
  exact forwardHamiltonian_of_hasDerivWithinAt ħ hd

omit [CompleteSpace E] in
lemma memLp_smul_const {χ : ℝ → ℝ} (hχ : Continuous χ) (hχs : HasCompactSupport χ) (x : E) :
    MemLp (fun t => χ t • x) 2 (volume : Measure ℝ) :=
  (hχ.smul continuous_const).memLp_of_hasCompactSupport (hχs.smul_right (f' := fun _ => x))

/-- **Time-independent case: `K = H - iħ ∂ₜ`.** For the propagator `U t s = V (t - s)` of a
strongly continuous unitary group that solves the Schrödinger equation for `H`, a compactly
supported `C¹` function `χ` and `x` in the domain of `H`, `K (χ x) = χ H x - iħ χ' x`. The
moving orbit is `χ(t - σ) V σ x`, with derivative `χ(t - σ) V σ v - χ'(t - σ) V σ x` for
`v = (iħ)⁻¹ H x`, by the group law. -/
theorem howlandGenerator_smul_of_group {ħ : ℝ} (hħ : ħ ≠ 0) (V : StronglyContinuousUnitaryGroup E)
    {H : E →ₗ.[ℂ] E} (hV : SolvesSchrodinger ħ H V.toFun) {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχs : HasCompactSupport χ) {x : E} (hx : x ∈ H.domain) :
    ∃ h : (memLp_smul_const hχ.continuous hχs x).toLp (fun t => χ t • x) ∈
        (V.toUnitaryPropagator.howlandGenerator ħ).domain,
      V.toUnitaryPropagator.howlandGenerator ħ ⟨_, h⟩ =ᵐ[volume]
        fun t => χ t • H ⟨x, hx⟩ - (Complex.I * ħ * deriv χ t) • x := by
  have hV0 : ∀ y, V.toFun 0 y = y := fun y => by
    rw [V.map_zero]
    rfl
  obtain ⟨hmem, hd0⟩ := hV ⟨x, hx⟩ 0
  set v := (Complex.I * ħ)⁻¹ • H ⟨V.toFun 0 x, hmem⟩
  have hv : v = (Complex.I * ħ)⁻¹ • H ⟨x, hx⟩ := by
    have : (⟨V.toFun 0 x, hmem⟩ : H.domain) = ⟨x, hx⟩ := Subtype.ext (hV0 x)
    simp only [v, this]
  -- The orbit of `x`, by the group law `V s = V σ V (s - σ)`.
  have horb : ∀ σ, HasDerivAt (fun s => V.toFun s x) (V.toFun σ v) σ := by
    intro σ
    have h1 : HasDerivAt (fun s => V.toFun (s - σ) x) v σ :=
      HasDerivAt.comp_sub_const σ σ (by simpa using hd0)
    have h2 := ((V.toFun σ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt σ h1
    refine h2.congr_of_eventuallyEq (.of_forall fun s => ?_)
    change V.toFun s x = V.toFun σ (V.toFun (s - σ) x)
    rw [← mul_apply_eq_comp, ← V.map_add, add_sub_cancel]
  have hdχ : Continuous (deriv χ) := hχ.continuous_deriv le_rfl
  set G : ℝ → ℝ → E := fun σ t => χ (t - σ) • V.toFun σ v - deriv χ (t - σ) • V.toFun σ x
  have hG : ∀ σ t, HasDerivAt
      (fun σ => V.toUnitaryPropagator t (t - σ) ((fun t => χ t • x) (t - σ))) (G σ t) σ := by
    intro σ t
    have hc : HasDerivAt (fun σ => χ (t - σ)) (deriv χ (t - σ) * -1) σ :=
      (hχ.differentiable one_ne_zero (t - σ)).hasDerivAt.comp σ ((hasDerivAt_id σ).const_sub t)
    have h := hc.smul (horb σ)
    refine (h.congr_of_eventuallyEq (.of_forall fun s => ?_)).congr_deriv ?_
    · change V.toFun (t - (t - s)) (χ (t - s) • x) = χ (t - s) • V.toFun s x
      rw [sub_sub_cancel, ContinuousLinearMap.map_smul_of_tower]
    · simp only [G, mul_neg_one, neg_smul, sub_eq_add_neg]
  have hGc : Continuous (Function.uncurry G) := by
    have hs : Continuous fun z : ℝ × ℝ => z.2 - z.1 := continuous_snd.sub continuous_fst
    exact ((hχ.continuous.comp hs).smul ((V.continuous_apply v).comp continuous_fst)).sub
      ((hdχ.comp hs).smul ((V.continuous_apply x).comp continuous_fst))
  obtain ⟨h, hK⟩ := V.toUnitaryPropagator.howlandGenerator_toLp (f := fun t => χ t • x) ħ
    (hχ.continuous.smul continuous_const) (hχs.smul_right (f' := fun _ => x)) hG hGc
  refine ⟨h, ?_⟩
  rw [hK]
  have hIħ : Complex.I * ħ ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)
  have hmG := memLp_deriv (U := V.toUnitaryPropagator) (f := fun t => χ t • x)
    (hχs.smul_right (f' := fun _ => x)) hG hGc
  filter_upwards [Lp.coeFn_smul (Complex.I * ħ) (hmG.toLp (G 0)), MemLp.coeFn_toLp hmG]
    with t h₁ h₂
  rw [h₁, Pi.smul_apply, h₂]
  simp only [G, sub_zero, hV0, hv]
  rw [smul_sub, smul_comm (Complex.I * ħ) (χ t), smul_smul, mul_inv_cancel₀ hIħ, one_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ) (deriv χ t) x, smul_smul]
  rfl

end QuantumMechanics.UnitaryPropagator
