/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.MeasureTheory.Function.LpSpace.Multiplication
public import UnitaryEntropy.Propagator

/-!
# A strongly continuous Hamiltonian without a norm-differentiable propagator

On `L²[0, 1]` let `H(t)` multiply by the indicator of `[0, t]`. Each `H(t)` is self-adjoint with
`‖H(t)‖ ≤ 1`, and `t ↦ H(t) ψ` is continuous, since `‖(H(t) - H(s)) ψ‖² = ∫_s^t |ψ|²`. But
`‖H(t) - H(s)‖ = 1` for `s ≠ t` in `[0, 1]`, so `H` is nowhere norm-continuous on `(0, 1)`.

The propagator from time `0` multiplies by `exp (-i (t - x)₊ / ħ)`. It solves the Schrödinger
equation `d/dt U(t) ψ = (iħ)⁻¹ H(t) U(t) ψ` for every `ψ`, but it is nowhere differentiable in
operator norm on `(0, 1)`: for `s > t` and `x ∈ (t, (t + s) / 2)`, the difference quotient
`(U(s) - U(t)) / (s - t)` multiplies by about `-i (s - x) / (ħ (s - t))`, while
`(iħ)⁻¹ H(t) U(t)` multiplies by `0`. By uniqueness of the propagator, the same holds for
every propagator `V` with `V(t₀) = 1`.

## Main results

* `indicatorHamiltonian`, `indicatorPropagator`: `H(t)` and `U(t)`.
* `continuous_indicatorHamiltonian_apply`: `H` is strongly continuous.
* `norm_indicatorHamiltonian_sub`: `‖H(t) - H(s)‖ = 1` for `s ≠ t` in `[0, 1]`.
* `hasDerivAt_indicatorPropagator_apply`: `U` solves the Schrödinger equation strongly.
* `not_differentiableAt_indicatorPropagator`: `U` is not norm-differentiable on `(0, 1)`.
* `indicatorHamiltonian_counterexample`: `H` satisfies the hypotheses of
  `exists_propagator_of_continuous_apply`, and no propagator is norm-differentiable on `(0, 1)`.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Lebesgue measure on `[0, 1]`. -/
local notation "μ₁" => (volume.restrict (Icc (0 : ℝ) 1))

/-- `L²[0, 1]`. -/
local notation "L²" => Lp ℂ 2 μ₁

/-- `H(t)` on `L²[0, 1]`: multiplication by the indicator of `[0, t]`. -/
def indicatorHamiltonian (t : ℝ) : L² →L[ℂ] L² := Lp.mulL ((Iic t).indicator 1)

/-- The phase `exp (-i (t - x)₊ / ħ)`. -/
def indicatorPhase (ħ t x : ℝ) : ℂ := Complex.exp (Complex.I * ((-max (t - x) 0 / ħ : ℝ) : ℂ))

/-- The propagator of `indicatorHamiltonian` from time `0`: multiplication by
`exp (-i (t - x)₊ / ħ)`. -/
def indicatorPropagator (ħ t : ℝ) : L² →L[ℂ] L² := Lp.mulL (indicatorPhase ħ t)

/-- The multiplier of `(iħ)⁻¹ H(t) U(t)`. -/
def indicatorGenerator (ħ t x : ℝ) : ℂ :=
  (Complex.I * ħ)⁻¹ * ((Iic t).indicator 1 x * indicatorPhase ħ t x)

local notation "H" => indicatorHamiltonian

local notation "U" => indicatorPropagator

lemma aestronglyMeasurable_indicator_Iic (t : ℝ) :
    AEStronglyMeasurable ((Iic t).indicator (1 : ℝ → ℂ)) μ₁ :=
  (stronglyMeasurable_const.indicator measurableSet_Iic).aestronglyMeasurable

lemma norm_indicator_Iic_le (t x : ℝ) : ‖(Iic t).indicator (1 : ℝ → ℂ) x‖ ≤ 1 := by
  by_cases hx : x ∈ Iic t <;> simp [hx]

lemma memLp_indicator_Iic (t : ℝ) : MemLp ((Iic t).indicator (1 : ℝ → ℂ)) ∞ μ₁ :=
  memLp_top_of_bound (aestronglyMeasurable_indicator_Iic t) 1
    (.of_forall (norm_indicator_Iic_le t))

lemma continuous_indicatorPhase (ħ t : ℝ) : Continuous (indicatorPhase ħ t) := by
  unfold indicatorPhase
  fun_prop

lemma norm_indicatorPhase (ħ t x : ℝ) : ‖indicatorPhase ħ t x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

lemma indicatorPhase_ne_zero (ħ t x : ℝ) : indicatorPhase ħ t x ≠ 0 :=
  Complex.exp_ne_zero _

lemma norm_indicatorPhase_sub_le (ħ s t x : ℝ) :
    ‖indicatorPhase ħ s x - indicatorPhase ħ t x‖ ≤ |s - t| * |ħ|⁻¹ := by
  have h : indicatorPhase ħ s x - indicatorPhase ħ t x = indicatorPhase ħ t x *
      (Complex.exp (Complex.I * ((-max (s - x) 0 / ħ - -max (t - x) 0 / ħ : ℝ) : ℂ)) - 1) := by
    simp only [indicatorPhase, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, norm_indicatorPhase, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, ← sub_div, neg_sub_neg, abs_div, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (abs_nonneg _))
  exact (abs_max_sub_max_le_abs _ _ _).trans_eq (by rw [abs_sub_comm]; ring_nf)

lemma norm_slope_indicatorPhase_le (ħ s t x : ℝ) :
    ‖slope (indicatorPhase ħ · x) t s‖ ≤ |ħ|⁻¹ := by
  rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs]
  rcases eq_or_ne s t with rfl | hst
  · simp [inv_nonneg]
  have hpos : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
  rw [inv_mul_le_iff₀ hpos]
  exact norm_indicatorPhase_sub_le ħ s t x

lemma norm_indicatorGenerator_le (ħ t x : ℝ) : ‖indicatorGenerator ħ t x‖ ≤ |ħ|⁻¹ := by
  rw [indicatorGenerator, norm_mul, norm_mul, norm_indicatorPhase, mul_one, norm_inv, norm_mul,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (inv_nonneg.mpr (abs_nonneg _)) (norm_indicator_Iic_le t x)

lemma aestronglyMeasurable_indicatorGenerator (ħ t : ℝ) :
    AEStronglyMeasurable (indicatorGenerator ħ t) μ₁ :=
  aestronglyMeasurable_const.mul ((aestronglyMeasurable_indicator_Iic t).mul
    (continuous_indicatorPhase ħ t).aestronglyMeasurable)

lemma aestronglyMeasurable_slope_indicatorPhase (ħ s t : ℝ) :
    AEStronglyMeasurable (fun x => slope (indicatorPhase ħ · x) t s) μ₁ := by
  simp only [slope_def_module]
  exact (((continuous_indicatorPhase ħ s).sub
    (continuous_indicatorPhase ħ t)).const_smul _).aestronglyMeasurable

lemma memLp_indicatorPhase (ħ t : ℝ) : MemLp (indicatorPhase ħ t) ∞ μ₁ :=
  memLp_top_of_bound (continuous_indicatorPhase ħ t).aestronglyMeasurable 1
    (.of_forall fun x => (norm_indicatorPhase ħ t x).le)

lemma memLp_indicatorGenerator (ħ t : ℝ) : MemLp (indicatorGenerator ħ t) ∞ μ₁ :=
  memLp_top_of_bound (aestronglyMeasurable_indicatorGenerator ħ t) _
    (.of_forall (norm_indicatorGenerator_le ħ t))

lemma memLp_slope_indicatorPhase (ħ s t : ℝ) :
    MemLp (fun x => slope (indicatorPhase ħ · x) t s) ∞ μ₁ :=
  memLp_top_of_bound (aestronglyMeasurable_slope_indicatorPhase ħ s t) _
    (.of_forall fun x => norm_slope_indicatorPhase_le ħ s t x)

lemma coeFn_indicatorHamiltonian (t : ℝ) (f : L²) :
    H t f =ᵐ[μ₁] fun x => (Iic t).indicator 1 x * f x :=
  Lp.coeFn_mulL (memLp_indicator_Iic t) f

lemma coeFn_indicatorPropagator (ħ t : ℝ) (f : L²) :
    U ħ t f =ᵐ[μ₁] fun x => indicatorPhase ħ t x * f x :=
  Lp.coeFn_mulL (memLp_indicatorPhase ħ t) f

lemma ae_ne (t : ℝ) : ∀ᵐ x ∂μ₁, x ≠ t :=
  ae_restrict_of_ae (by simp [ae_iff])

/-- Each `H(t)` is self-adjoint. -/
theorem isSelfAdjoint_indicatorHamiltonian (t : ℝ) : IsSelfAdjoint (H t) :=
  Lp.isSelfAdjoint_mulL (memLp_indicator_Iic t)
    (.of_forall fun x => by by_cases hx : x ∈ Iic t <;> simp [hx])

theorem norm_indicatorHamiltonian_le (t : ℝ) : ‖H t‖ ≤ 1 :=
  Lp.norm_mulL_le (aestronglyMeasurable_indicator_Iic t) zero_le_one
    (.of_forall (norm_indicator_Iic_le t))

/-- **`H` is strongly continuous.** -/
theorem continuous_indicatorHamiltonian_apply (ψ : L²) : Continuous (H · ψ) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  refine Lp.tendsto_mulL_apply ENNReal.ofNat_ne_top
    (.of_forall aestronglyMeasurable_indicator_Iic) (aestronglyMeasurable_indicator_Iic t)
    (.of_forall fun s => .of_forall (norm_indicator_Iic_le s))
    (.of_forall (norm_indicator_Iic_le t)) ?_ ψ
  filter_upwards [ae_ne t] with x hx
  rcases hx.lt_or_gt with h | h
  · rw [indicator_of_mem (mem_Iic.mpr h.le)]
    exact tendsto_const_nhds.congr' ((lt_mem_nhds h).mono fun s hs =>
      (indicator_of_mem (mem_Iic.mpr hs.le) _).symm)
  · rw [indicator_of_notMem (by simpa using h)]
    exact tendsto_const_nhds.congr' ((gt_mem_nhds h).mono fun s hs =>
      (indicator_of_notMem (by simpa using hs) _).symm)

lemma norm_indicatorHamiltonian_sub_of_lt {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 1) (hst : s < t) :
    ‖H t - H s‖ = 1 := by
  set d : ℝ → ℂ := fun x => (Iic t).indicator 1 x - (Iic s).indicator 1 x
  have hd : MemLp d ∞ μ₁ := (memLp_indicator_Iic t).sub (memLp_indicator_Iic s)
  have hHd : H t - H s = Lp.mulL d := Lp.eq_mulL hd fun f => by
    filter_upwards [Lp.coeFn_sub (H t f) (H s f), coeFn_indicatorHamiltonian t f,
      coeFn_indicatorHamiltonian s f] with x h h₁ h₂
    rw [sub_apply, h, Pi.sub_apply, h₁, h₂, sub_mul]
  rw [hHd]
  refine le_antisymm (Lp.norm_mulL_le hd.aestronglyMeasurable zero_le_one (.of_forall fun x => ?_))
    (Lp.le_norm_mulL ENNReal.ofNat_ne_top hd (s := Ioc s t) measurableSet_Ioc ?_ ?_
      (.of_forall fun x (hx : x ∈ Ioc s t) => ?_))
  · by_cases h₁ : x ≤ s <;> by_cases h₂ : x ≤ t <;> simp [d, h₁, h₂]
  · rw [Measure.restrict_apply measurableSet_Ioc]
    exact measure_ne_top_of_subset inter_subset_left (by simp)
  · rw [Measure.restrict_apply measurableSet_Ioc,
      inter_eq_left.mpr (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs ht))]
    rw [Real.volume_Ioc, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
    exact hst
  · simp [d, hx.2, not_le.mpr hx.1]

/-- **`H` is not norm-continuous:** `‖H(t) - H(s)‖ = 1` for `s ≠ t` in `[0, 1]`. -/
theorem norm_indicatorHamiltonian_sub {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1)
    (hst : s ≠ t) : ‖H t - H s‖ = 1 := by
  rcases hst.lt_or_gt with h | h
  · exact norm_indicatorHamiltonian_sub_of_lt hs.1 ht.2 h
  · rw [norm_sub_rev]
    exact norm_indicatorHamiltonian_sub_of_lt ht.1 hs.2 h

theorem not_continuousAt_indicatorHamiltonian {t : ℝ} (ht : t ∈ Ioo 0 1) :
    ¬ ContinuousAt H t := by
  intro h
  have h₀ := (tendsto_iff_norm_sub_tendsto_zero.mp h).mono_left
    (nhdsWithin_le_nhds (s := Ioi t))
  have h₁ : ∀ᶠ s in 𝓝[>] t, ‖H s - H t‖ = 1 := by
    filter_upwards [Ioo_mem_nhdsGT ht.2] with s hs
    exact norm_indicatorHamiltonian_sub (Ioo_subset_Icc_self ht)
      ⟨(ht.1.trans hs.1).le, hs.2.le⟩ hs.1.ne
  obtain ⟨s, h₂, h₃⟩ := ((h₀.eventually (gt_mem_nhds one_pos)).and h₁).exists
  exact h₂.ne h₃

theorem indicatorPropagator_zero (ħ : ℝ) : U ħ 0 = 1 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  change U ħ 0 f =ᵐ[μ₁] f
  filter_upwards [coeFn_indicatorPropagator ħ 0 f, ae_restrict_mem measurableSet_Icc]
    with x hx hx01
  rw [hx]
  simp [indicatorPhase, max_eq_right (neg_nonpos.mpr hx01.1)]

lemma hasDerivAt_indicatorPhase (ħ : ℝ) {t x : ℝ} (hx : x ≠ t) :
    HasDerivAt (indicatorPhase ħ · x) (indicatorGenerator ħ t x) t := by
  rcases hx.lt_or_gt with h | h
  · have heq : (indicatorPhase ħ · x) =ᶠ[𝓝 t]
        fun s => Complex.exp (Complex.I * ((-(s - x) / ħ : ℝ) : ℂ)) :=
      (lt_mem_nhds h).mono fun s hs => by
        simp only [indicatorPhase, max_eq_left (sub_nonneg.mpr hs.le)]
    have hd : HasDerivAt (fun s => Complex.exp (Complex.I * ((-(s - x) / ħ : ℝ) : ℂ)))
        (Complex.exp (Complex.I * ((-(t - x) / ħ : ℝ) : ℂ)) * (Complex.I * ((-1 / ħ : ℝ) : ℂ)))
        t :=
      ((((hasDerivAt_id' t).sub_const x).neg.div_const ħ).ofReal_comp.const_mul Complex.I).cexp
    refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [indicatorGenerator, indicatorPhase, indicator_of_mem (mem_Iic.mpr h.le), Pi.one_apply,
      one_mul, max_eq_left (sub_nonneg.mpr h.le), mul_inv, Complex.inv_I]
    push_cast
    ring
  · have heq : (indicatorPhase ħ · x) =ᶠ[𝓝 t] fun _ => 1 :=
      (gt_mem_nhds h).mono fun s hs => by
        simp [indicatorPhase, max_eq_right (sub_nonpos.mpr hs.le)]
    refine ((hasDerivAt_const t (1 : ℂ)).congr_of_eventuallyEq heq).congr_deriv ?_
    simp [indicatorGenerator, indicator_of_notMem (show x ∉ Iic t by simpa using h)]

lemma indicatorGenerator_apply (ħ t : ℝ) (ψ : L²) :
    (Complex.I * ħ)⁻¹ • H t (U ħ t ψ) = Lp.mulL (indicatorGenerator ħ t) ψ := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_smul (Complex.I * ħ)⁻¹ (H t (U ħ t ψ)),
    coeFn_indicatorHamiltonian t (U ħ t ψ), coeFn_indicatorPropagator ħ t ψ,
    Lp.coeFn_mulL (memLp_indicatorGenerator ħ t) ψ] with x h₁ h₂ h₃ h₄
  rw [h₁, h₄, Pi.smul_apply, h₂, h₃, smul_eq_mul, indicatorGenerator]
  ring

lemma slope_indicatorPropagator (ħ t s : ℝ) :
    slope (U ħ) t s = Lp.mulL (fun x => slope (indicatorPhase ħ · x) t s) :=
  Lp.eq_mulL (memLp_slope_indicatorPhase ħ s t) fun f => by
    rw [slope_def_module]
    filter_upwards [Lp.coeFn_smul (s - t)⁻¹ (U ħ s f - U ħ t f),
      Lp.coeFn_sub (U ħ s f) (U ħ t f), coeFn_indicatorPropagator ħ s f,
      coeFn_indicatorPropagator ħ t f] with x h₁ h₂ h₃ h₄
    rw [smul_apply, sub_apply, h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, h₄, slope_def_module,
      ← sub_mul, smul_mul_assoc]

/-- **The propagator solves the Schrödinger equation strongly:**
`d/dt U(t) ψ = (iħ)⁻¹ H(t) U(t) ψ`. -/
theorem hasDerivAt_indicatorPropagator_apply (ħ : ℝ) (ψ : L²) (t : ℝ) :
    HasDerivAt (U ħ · ψ) ((Complex.I * ħ)⁻¹ • H t (U ħ t ψ)) t := by
  rw [hasDerivAt_iff_tendsto_slope, indicatorGenerator_apply]
  have h : slope (U ħ · ψ) t = fun s => Lp.mulL (fun x => slope (indicatorPhase ħ · x) t s) ψ :=
    funext fun s => by
      rw [← slope_indicatorPropagator]
      simp only [slope_def_module, smul_apply, sub_apply]
  rw [h]
  refine Lp.tendsto_mulL_apply ENNReal.ofNat_ne_top
    (.of_forall fun s => aestronglyMeasurable_slope_indicatorPhase ħ s t)
    (aestronglyMeasurable_indicatorGenerator ħ t)
    (.of_forall fun s => .of_forall fun x => norm_slope_indicatorPhase_le ħ s t x)
    (.of_forall (norm_indicatorGenerator_le ħ t)) ?_ ψ
  filter_upwards [ae_ne t] with x hx
  exact (hasDerivAt_indicatorPhase ħ hx).tendsto_slope

/-- **The propagator is not norm-differentiable** at any `t ∈ (0, 1)`. -/
theorem not_differentiableAt_indicatorPropagator {ħ : ℝ} (hħ : 0 < ħ) {t : ℝ}
    (ht : t ∈ Ioo 0 1) : ¬ DifferentiableAt ℝ (U ħ) t := by
  intro hd
  set e := Lp.mulL (indicatorGenerator ħ t) (μ := μ₁) (p := 2)
  have hD : HasDerivAt (U ħ) e t := by
    convert hd.hasDerivAt using 1
    refine ContinuousLinearMap.ext fun ψ => ?_
    rw [← indicatorGenerator_apply]
    exact (hasDerivAt_indicatorPropagator_apply ħ ψ t).unique (hd.hasDerivAt.clm_apply_const ψ)
  have h₀ := (tendsto_iff_norm_sub_tendsto_zero.mp (hasDerivAt_iff_tendsto_slope.mp hD)).mono_left
    (nhdsWithin_mono t (show Ioi t ⊆ {t}ᶜ from fun s hs => ne_of_gt hs))
  set c := 1 / (Real.pi * ħ)
  have hc : 0 < c := by positivity
  have hlow : ∀ᶠ s in 𝓝[>] t, c ≤ ‖slope (U ħ) t s - e‖ := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min (by linarith : t < t + ħ) ht.2)] with s hs
    have hts : t < s := hs.1
    have hsħ : s - t ≤ ħ := by linarith [hs.2.trans_le (min_le_left (t + ħ) 1)]
    have hs1 : s < 1 := hs.2.trans_le (min_le_right _ _)
    set q : ℝ → ℂ := fun x => slope (indicatorPhase ħ · x) t s - indicatorGenerator ħ t x
    have hq : MemLp q ∞ μ₁ :=
      (memLp_slope_indicatorPhase ħ s t).sub (memLp_indicatorGenerator ħ t)
    have heq : slope (U ħ) t s - e = Lp.mulL q := Lp.eq_mulL hq fun f => by
      rw [slope_indicatorPropagator]
      filter_upwards [Lp.coeFn_sub (Lp.mulL (fun x => slope (indicatorPhase ħ · x) t s) f) (e f),
        Lp.coeFn_mulL (memLp_slope_indicatorPhase ħ s t) f,
        Lp.coeFn_mulL (memLp_indicatorGenerator ħ t) f] with x h₁ h₂ h₃
      rw [sub_apply, h₁, Pi.sub_apply, h₂, h₃, sub_mul]
    rw [heq]
    refine Lp.le_norm_mulL ENNReal.ofNat_ne_top hq (s := Ioo t ((t + s) / 2)) measurableSet_Ioo
      ?_ ?_ (.of_forall fun x (hx : x ∈ Ioo t ((t + s) / 2)) => ?_)
    · rw [Measure.restrict_apply measurableSet_Ioo]
      exact measure_ne_top_of_subset inter_subset_left (by simp)
    · rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.mpr
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc ht.1.le (by linarith))), Real.volume_Ioo,
        ne_eq, ENNReal.ofReal_eq_zero, not_le]
      linarith
    have hφt : indicatorPhase ħ t x = 1 := by
      simp [indicatorPhase, max_eq_right (by linarith [hx.1] : t - x ≤ 0)]
    have hφs : indicatorPhase ħ s x = Complex.exp (Complex.I * ((-(s - x) / ħ : ℝ) : ℂ)) := by
      simp only [indicatorPhase, max_eq_left (by linarith [hx.2] : 0 ≤ s - x)]
    have hg : indicatorGenerator ħ t x = 0 := by
      simp [indicatorGenerator, not_le.mpr hx.1]
    show c ≤ ‖slope (indicatorPhase ħ · x) t s - indicatorGenerator ħ t x‖
    rw [hg, sub_zero, slope_def_module]
    rw [hφt, hφs, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hts),
      Complex.norm_exp_I_mul_ofReal_sub_one]
    set z := (s - x) / (2 * ħ)
    have hz : -(s - x) / ħ / 2 = -z := by
      simp only [z]
      field_simp
    rw [hz, Real.sin_neg, mul_neg, norm_neg, norm_mul, Real.norm_two, Real.norm_eq_abs]
    have hz1 : (s - t) / (4 * ħ) ≤ z := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hx.2]
    have hz2 : z ≤ Real.pi / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.two_le_pi, hx.1]
    have hsin := Real.mul_le_sin ((div_pos (sub_pos.mpr hts) (by positivity)).le.trans hz1) hz2
    calc c = (s - t)⁻¹ * (2 * (2 / Real.pi * ((s - t) / (4 * ħ)))) := by
          simp only [c]
          field_simp
          ring
      _ ≤ (s - t)⁻¹ * (2 * |Real.sin z|) := by
          gcongr
          exact (mul_le_mul_of_nonneg_left hz1 (by positivity)).trans
            (hsin.trans (le_abs_self _))
  obtain ⟨s, h₁, h₂⟩ := ((h₀.eventually (gt_mem_nhds hc)).and hlow).exists
  exact h₂.not_gt h₁

/-- **A strongly continuous Hamiltonian without a norm-differentiable propagator.** `H(t)` is
self-adjoint, bounded by `1` and strongly continuous, so it satisfies the hypotheses of
`exists_propagator_of_continuous_apply`, but `‖H(t) - H(s)‖ = 1` for `s ≠ t` in `[0, 1]`. Every
propagator `V` with `V(t₀) = 1` is nowhere differentiable in operator norm on `(0, 1)`. -/
theorem indicatorHamiltonian_counterexample {ħ : ℝ} (hħ : 0 < ħ) (t₀ : ℝ) :
    (∀ t, IsSelfAdjoint (H t)) ∧ (∀ t, ‖H t‖ ≤ 1) ∧ (∀ ψ, Continuous (H · ψ)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, s ≠ t → ‖H t - H s‖ = 1) ∧
      ∀ V : ℝ → L² →L[ℂ] L², V t₀ = 1 →
        (∀ ψ t, HasDerivAt (V · ψ) ((Complex.I * ħ)⁻¹ • H t (V t ψ)) t) →
        ∀ t ∈ Ioo (0 : ℝ) 1, ¬ DifferentiableAt ℝ V t := by
  refine ⟨isSelfAdjoint_indicatorHamiltonian, norm_indicatorHamiltonian_le,
    continuous_indicatorHamiltonian_apply, fun s hs t ht => norm_indicatorHamiltonian_sub hs ht,
    fun V hV₀ hV t ht hd => ?_⟩
  have hX : MemLp (fun x => (indicatorPhase ħ t₀ x)⁻¹) ∞ μ₁ :=
    memLp_top_of_bound ((continuous_indicatorPhase ħ t₀).inv₀
      (indicatorPhase_ne_zero ħ t₀)).aestronglyMeasurable 1
      (.of_forall fun x => by rw [norm_inv, norm_indicatorPhase, inv_one])
  set X : L² →L[ℂ] L² := Lp.mulL fun x => (indicatorPhase ħ t₀ x)⁻¹
  have hUX : U ħ t₀ * X = 1 := ContinuousLinearMap.ext fun f => Lp.ext <| by
    change U ħ t₀ (X f) =ᵐ[μ₁] f
    filter_upwards [coeFn_indicatorPropagator ħ t₀ (X f), Lp.coeFn_mulL hX f] with x h₁ h₂
    rw [h₁, h₂, ← mul_assoc, mul_inv_cancel₀ (indicatorPhase_ne_zero ħ t₀ x), one_mul]
  have hXU : X * U ħ t₀ = 1 := ContinuousLinearMap.ext fun f => Lp.ext <| by
    change X (U ħ t₀ f) =ᵐ[μ₁] f
    filter_upwards [coeFn_indicatorPropagator ħ t₀ f, Lp.coeFn_mulL hX (U ħ t₀ f)]
      with x h₁ h₂
    rw [h₂, h₁, ← mul_assoc, inv_mul_cancel₀ (indicatorPhase_ne_zero ħ t₀ x), one_mul]
  have hW : (fun s => U ħ s * X) = V :=
    propagator_unique_of_continuous_apply continuous_indicatorHamiltonian_apply
      (fun ψ s => hasDerivAt_indicatorPropagator_apply ħ (X ψ) s) hV (by rw [hUX, hV₀])
  refine not_differentiableAt_indicatorPropagator hħ ht ?_
  have hUV : U ħ = fun s => V s * U ħ t₀ := funext fun s => by
    rw [← hW, mul_assoc, hXU, mul_one]
  rw [hUV]
  exact hd.mul_const _

end UnitaryEntropy
