/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Multiplication operators on `Lp`

For an essentially bounded `g : α → 𝕜`, `MeasureTheory.Lp.mulL g` is the operator `f ↦ g f` on
`Lp 𝕜 p μ`, built from `ContinuousLinearMap.holderL`. Its norm is at most an a.e. bound of `‖g‖`,
and at least `c` if `‖g‖ ≥ c` on a set of positive finite measure. A family of multiplication
operators converges strongly when the multipliers are uniformly bounded and converge a.e.
(dominated convergence).

## Main results

* `MeasureTheory.tendsto_eLpNorm_of_dominated`: dominated convergence for `eLpNorm`, `p ≠ ∞`.
* `MeasureTheory.Lp.coeFn_mulL`, `MeasureTheory.Lp.eq_mulL`: `mulL g f = g f` a.e.
* `MeasureTheory.Lp.norm_mulL_le`, `MeasureTheory.Lp.le_norm_mulL`: upper and lower bounds.
* `MeasureTheory.Lp.tendsto_mulL_apply`: strong convergence of `mulL (g i)`.
* `MeasureTheory.Lp.isSelfAdjoint_mulL`: on `L²`, a real multiplier gives a self-adjoint operator.
-/

@[expose] public noncomputable section

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}

/-- **Dominated convergence in `Lp`**, for `p ≠ ∞`: if `‖f i‖ ≤ F` a.e. with `F ∈ Lp` and
`f i → 0` a.e., then `‖f i‖_p → 0`. -/
theorem tendsto_eLpNorm_of_dominated {E ι : Type*} [NormedAddCommGroup E] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → α → E} {F : α → ℝ} (hp : p ≠ ∞)
    (hf : ∀ᶠ i in l, AEStronglyMeasurable (f i) μ) (hF : MemLp F p μ)
    (hle : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖f i x‖ ≤ F x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact tendsto_const_nhds.congr' (hf.mono fun i hi => (eLpNorm_exponent_zero hi).symm)
  have hpos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine Tendsto.congr' (hf.mono fun i hi =>
    (eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hi).symm) ?_
  have h : Tendsto (fun i => ∫⁻ x, ‖f i x‖ₑ ^ p.toReal ∂μ) l (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence'
      (fun x => ‖F x‖ₑ ^ p.toReal) (hf.mono fun i hi => (hi.enorm.pow_const _))
      (hle.mono fun i hi => hi.mono fun x hx =>
        ENNReal.rpow_le_rpow
          (enorm_le_iff_norm_le.mpr (hx.trans (Real.le_norm_self _))) hpos.le) ?_
      (hlim.mono fun x hx => (ENNReal.continuous_rpow_const.tendsto 0).comp
        (by simpa [Function.comp_def] using (continuous_enorm.tendsto 0).comp hx))
    · simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hpos] using this
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hF.eLpNorm_lt_top).ne
  have h2 := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp h
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hpos)] using h2

namespace Lp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Fact (1 ≤ p)]

open Classical in
/-- Multiplication by `g` on `Lp 𝕜 p μ`; zero unless `g` is essentially bounded. -/
def mulL (g : α → 𝕜) : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ :=
  if hg : MemLp g ∞ μ then (ContinuousLinearMap.mul 𝕜 𝕜).holderL μ ∞ p p (hg.toLp g) else 0

theorem coeFn_mulL {g : α → 𝕜} (hg : MemLp g ∞ μ) (f : Lp 𝕜 p μ) :
    mulL g f =ᵐ[μ] fun x => g x * f x := by
  simp only [mulL, hg, ↓reduceDIte, ContinuousLinearMap.holderL_apply_apply]
  filter_upwards [ContinuousLinearMap.coeFn_holder (r := p) (ContinuousLinearMap.mul 𝕜 𝕜)
    (hg.toLp g) f, hg.coeFn_toLp] with x hx hgx
  rw [hx, ContinuousLinearMap.mul_apply', hgx]

/-- An operator that acts as multiplication by `g` is `mulL g`. -/
theorem eq_mulL {g : α → 𝕜} (hg : MemLp g ∞ μ) {T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}
    (h : ∀ f, T f =ᵐ[μ] fun x => g x * f x) : T = mulL g :=
  ContinuousLinearMap.ext fun f => Lp.ext ((h f).trans (coeFn_mulL hg f).symm)

theorem norm_mulL_le {g : α → 𝕜} (hg : AEStronglyMeasurable g μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ x ∂μ, ‖g x‖ ≤ C) : ‖(mulL g : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun f => norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coeFn_mulL (memLp_top_of_bound hg C h) f, h] with x hx hgx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right hgx (norm_nonneg _)

/-- If `‖g‖ ≥ c` on a set of positive finite measure, then `‖mulL g‖ ≥ c`. -/
theorem le_norm_mulL (hp : p ≠ ∞) {g : α → 𝕜} (hg : MemLp g ∞ μ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hμs₀ : μ s ≠ 0) {c : ℝ}
    (h : ∀ᵐ x ∂μ, x ∈ s → c ≤ ‖g x‖) : c ≤ ‖(mulL g : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)‖ := by
  rcases le_or_gt c 0 with hc | hc
  · exact hc.trans (norm_nonneg _)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  set f : Lp 𝕜 p μ := indicatorConstLp p hs hμs 1
  have hf : 0 < ‖f‖ := by
    rw [norm_indicatorConstLp hp0 hp, norm_one, one_mul]
    exact Real.rpow_pos_of_pos (ENNReal.toReal_pos hμs₀ hμs) _
  have hle : ‖f‖ ≤ c⁻¹ * ‖mulL g f‖ := by
    refine norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [coeFn_mulL hg f, indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs)
      (c := (1 : 𝕜)), h] with x hx hfx hgx
    rw [hx, hfx, norm_mul]
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs, norm_one, mul_one]
      rw [← div_eq_inv_mul, le_div_iff₀ hc, one_mul]
      exact hgx hxs
    · simp [Set.indicator_of_notMem hxs]
  have := hle.trans (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ f)
    (inv_nonneg.mpr hc.le))
  rw [← mul_assoc, le_mul_iff_one_le_left hf, ← div_eq_inv_mul, one_le_div hc] at this
  exact this

/-- **Strong convergence of multiplication operators**: if the multipliers `g i` are bounded by
`C` and converge a.e. to `g₀`, then `mulL (g i) f → mulL g₀ f` for every `f`. -/
theorem tendsto_mulL_apply (hp : p ≠ ∞) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {g : ι → α → 𝕜} {g₀ : α → 𝕜} {C : ℝ} (hg : ∀ᶠ i in l, AEStronglyMeasurable (g i) μ)
    (hg₀ : AEStronglyMeasurable g₀ μ) (hC : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖g i x‖ ≤ C)
    (hC₀ : ∀ᵐ x ∂μ, ‖g₀ x‖ ≤ C) (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => g i x) l (𝓝 (g₀ x)))
    (f : Lp 𝕜 p μ) : Tendsto (fun i => mulL (g i) f) l (𝓝 (mulL g₀ f)) := by
  rw [tendsto_Lp_iff_tendsto_eLpNorm']
  have hm₀ := memLp_top_of_bound hg₀ C hC₀
  have key := tendsto_eLpNorm_of_dominated (μ := μ) (p := p)
    (f := fun i x => (g i x - g₀ x) * f x) (F := fun x => (C + C) * ‖f x‖) hp
    (hg.mono fun i hi => (hi.sub hg₀).mul (Lp.aestronglyMeasurable f))
    ((Lp.memLp f).norm.const_mul _)
    ((hg.and hC).mono fun i hi => by
      filter_upwards [hi.2, hC₀] with x hx hx₀
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add hx hx₀))
        (norm_nonneg _))
    (hlim.mono fun x hx => by
      simpa using (hx.sub_const (g₀ x)).mul_const (f x))
  refine key.congr' ((hg.and hC).mono fun i hi => eLpNorm_congr_ae ?_)
  filter_upwards [coeFn_mulL (memLp_top_of_bound hi.1 C hi.2) f, coeFn_mulL hm₀ f]
    with x hx hx₀
  simp only [Pi.sub_apply, hx, hx₀, sub_mul]

/-- On `L²`, multiplication by a real-valued `g` is self-adjoint. -/
theorem isSelfAdjoint_mulL {𝕜 : Type*} [RCLike 𝕜] {g : α → 𝕜} (hg : MemLp g ∞ μ)
    (hr : ∀ᵐ x ∂μ, star (g x) = g x) : IsSelfAdjoint (mulL g : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f h
  simp only [ContinuousLinearMap.coe_coe, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_mulL hg f, coeFn_mulL hg h, hr] with x hf hh hx
  rw [hf, hh, RCLike.inner_apply, RCLike.inner_apply, map_mul, ← RCLike.star_def, hx]
  ring

end Lp

end MeasureTheory
