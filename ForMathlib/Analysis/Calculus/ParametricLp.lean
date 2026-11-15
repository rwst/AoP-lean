/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Derivatives of `Lᵖ`-valued maps under a dominated derivative

Let `G q` be a family of `Lᵖ` functions depending on a parameter `q` of a normed space. If
`q ↦ G q x` has the derivative `G' q x` for every `x`, and `‖G' q x‖ ≤ B x` near `q₀` for some
`B ∈ Lᵖ`, `p < ∞`, then `q ↦ G q` is differentiable at `q₀` as a map into `Lᵖ`, with derivative
`v ↦ G' q₀ · v`. This is the `Lᵖ` analogue of `hasFDerivAt_integral_of_dominated_of_fderiv_le`.

The proof: by the mean value inequality the difference quotient is bounded by `2 B`, and it tends
to `0` pointwise, so its `Lᵖ` norm tends to `0` by dominated convergence.

## Main results

* `MeasureTheory.hasFDerivAt_toLp_of_dominated`
-/

@[expose] public section

open Filter Metric Set
open scoped Topology ENNReal

namespace MeasureTheory

variable {α P F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup P]
  [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Differentiation under the `Lᵖ` norm.** If `q ↦ G q x` has the derivative `G' q x`, bounded
by `B x` for `q` near `q₀` with `B ∈ Lᵖ`, `p < ∞`, then `q ↦ G q ∈ Lᵖ` has at `q₀` the derivative
`L` with `L v = G' q₀ · v`. -/
theorem hasFDerivAt_toLp_of_dominated (hp : p ≠ ∞) {G : P → α → F} {G' : P → α → P →L[ℝ] F}
    {q₀ : P} {r : ℝ} (hr : 0 < r) {B : α → ℝ} (hG : ∀ q, MemLp (G q) p μ) (hB : MemLp B p μ)
    (hderiv : ∀ x, ∀ q ∈ ball q₀ r, HasFDerivAt (G · x) (G' q x) q)
    (hbound : ∀ x, ∀ q ∈ ball q₀ r, ‖G' q x‖ ≤ B x) {L : P →L[ℝ] Lp F p μ}
    (hL : ∀ v, L v =ᵐ[μ] fun x => G' q₀ x v) :
    HasFDerivAt (fun q => (hG q).toLp (G q)) L q₀ := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  -- The remainder and the difference quotient.
  set D : P → α → F := fun q x => G q x - G q₀ x - G' q₀ x (q - q₀)
  set Q : P → α → F := fun q => ‖q - q₀‖⁻¹ • D q
  have hDm : ∀ q, AEStronglyMeasurable (D q) μ := fun q =>
    ((hG q).aestronglyMeasurable.sub (hG q₀).aestronglyMeasurable).sub
      ((Lp.aestronglyMeasurable (L (q - q₀))).congr (hL _))
  have hQm : ∀ q, AEStronglyMeasurable (Q q) μ := fun q => (hDm q).const_smul _
  have hnorm : ∀ q, ‖q - q₀‖⁻¹ * ‖(hG q).toLp (G q) - (hG q₀).toLp (G q₀) - L (q - q₀)‖ =
      (eLpNorm (Q q) p μ).toReal := by
    intro q
    have hae : (hG q).toLp (G q) - (hG q₀).toLp (G q₀) - L (q - q₀) =ᵐ[μ] D q := by
      filter_upwards [Lp.coeFn_sub ((hG q).toLp (G q) - (hG q₀).toLp (G q₀)) (L (q - q₀)),
        Lp.coeFn_sub ((hG q).toLp (G q)) ((hG q₀).toLp (G q₀)), (hG q).coeFn_toLp,
        (hG q₀).coeFn_toLp, hL (q - q₀)] with x h1 h2 h3 h4 h5
      rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, h4, h5]
    rw [Lp.norm_def, eLpNorm_congr_ae hae, eLpNorm_const_smul, ENNReal.toReal_mul,
      toReal_enorm, norm_inv, norm_norm]
  rw [hasFDerivAt_iff_tendsto]
  simp_rw [hnorm]
  rw [← ENNReal.toReal_zero]
  refine (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ?_
  -- Dominated convergence for `∫ ‖Q q‖ᵖ`.
  have hbound' : ∀ x, ∀ q ∈ ball q₀ r, ‖Q q x‖ ≤ 2 * B x := by
    intro x q hq
    have hB0 : 0 ≤ B x := (norm_nonneg _).trans (hbound x q₀ (mem_ball_self hr))
    have hmv : ‖D q x‖ ≤ 2 * B x * ‖q - q₀‖ :=
      (convex_ball q₀ r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun q' hq' => (hderiv x q' hq').hasFDerivWithinAt)
        (fun q' hq' => (norm_sub_le _ _).trans (by
          linarith [hbound x q' hq', hbound x q₀ (mem_ball_self hr)]))
        (mem_ball_self hr) hq
    simp only [Q, Pi.smul_apply, norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖q - q₀‖ 0 with h0 | h0
    · rw [h0, inv_zero, zero_mul]
      positivity
    · rw [inv_mul_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)), mul_comm]
      exact hmv
  have hlim : ∀ x, Tendsto (fun q => ‖Q q x‖ₑ ^ p.toReal) (𝓝 q₀) (𝓝 0) := by
    intro x
    have h := hasFDerivAt_iff_tendsto.1 (hderiv x q₀ (mem_ball_self hr))
    have h' : Tendsto (fun q => ‖Q q x‖) (𝓝 q₀) (𝓝 0) := by
      refine h.congr fun q => ?_
      simp only [Q, D, Pi.smul_apply, norm_smul, norm_inv, norm_norm]
    have h'' : Tendsto (fun q => ‖Q q x‖ₑ) (𝓝 q₀) (𝓝 0) := by
      have := ENNReal.tendsto_ofReal h'
      simp only [ofReal_norm, ENNReal.ofReal_zero] at this
      exact this
    have := ((ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0).comp h''
    rwa [ENNReal.zero_rpow_of_pos hpr] at this
  have hfin : ∫⁻ x, ‖2 * B x‖ₑ ^ p.toReal ∂μ ≠ ∞ :=
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp
      (hB.const_mul 2).eLpNorm_lt_top).ne
  have hint : Tendsto (fun q => ∫⁻ x, ‖Q q x‖ₑ ^ p.toReal ∂μ) (𝓝 q₀) (𝓝 0) := by
    have := tendsto_lintegral_filter_of_dominated_convergence' (μ := μ) (l := 𝓝 q₀)
      (F := fun q x => ‖Q q x‖ₑ ^ p.toReal) (f := fun _ => 0)
      (fun x => ‖2 * B x‖ₑ ^ p.toReal)
      (Eventually.of_forall fun q => ((hQm q).enorm.pow_const _))
      (eventually_of_mem (ball_mem_nhds q₀ hr) fun q hq => ae_of_all _ fun x => by
        gcongr
        rw [← ofReal_norm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ((hbound' x q hq).trans (le_abs_self _)) |>.trans_eq ?_
        rw [Real.norm_eq_abs])
      hfin (ae_of_all _ hlim)
    simpa using this
  have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp hint
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at this
  refine this.congr fun q => ?_
  rw [Function.comp_apply, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hQm q)]

end MeasureTheory
