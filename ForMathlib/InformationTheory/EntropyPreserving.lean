/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.InformationTheory.ChangeOfVariables

/-!
# Maps that preserve the differential entropy

Let `Φ : E → E` be injective with derivative `Φ' x` at every `x`, all invertible, on a
finite-dimensional real space with an additive Haar measure. By
`MeasureTheory.integral_negMulLog_pushDensity`, a density `ρ` and its push-forward
`pushDensity Φ Φ' ρ` differ in differential entropy by `∫ ρ log |det Φ'|`. So `Φ` preserves the
entropy of every density if `|det Φ'| = 1`; this file proves the converse, for continuous `Φ'`:
if `Φ` preserves the entropy of every probability density, then `|det Φ'| = 1`. Where
`log |det Φ'|` has a sign, the uniform density on a small ball changes its entropy.

## Main results

* `MeasureTheory.integral_negMulLog_pushDensity_of_abs_det_eq_one`: `|det Φ'| = 1` preserves the
  entropy of every density;
* `MeasureTheory.abs_det_eq_one_of_integral_negMulLog_pushDensity`: the converse.
-/

open Real Set Function Metric

public section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Φ : E → E}
  {Φ' : E → E →L[ℝ] E}

/-- A map with `|det Φ'| = 1` preserves the differential entropy of every density. -/
theorem integral_negMulLog_pushDensity_of_abs_det_eq_one (hd : ∀ x, HasFDerivAt Φ (Φ' x) x)
    (hΦ : Injective Φ) (h1 : ∀ x, |(Φ' x).det| = 1) (ρ : E → ℝ) :
    ∫ u, negMulLog (pushDensity Φ Φ' ρ u) ∂μ = ∫ x, negMulLog (ρ x) ∂μ := by
  have hdet : ∀ x, (Φ' x).det ≠ 0 := fun x h => by simpa [h] using h1 x
  rw [integral_negMulLog_pushDensity hd hΦ hdet]
  simp [h1]

/-- A map that preserves the differential entropy of every probability density has
`|det Φ'| = 1`. -/
theorem abs_det_eq_one_of_integral_negMulLog_pushDensity (hd : ∀ x, HasFDerivAt Φ (Φ' x) x)
    (hΦ : Injective Φ) (hdet : ∀ x, (Φ' x).det ≠ 0) (hc : Continuous Φ')
    (h : ∀ ρ : E → ℝ, (∀ x, 0 ≤ ρ x) → Integrable ρ μ → ∫ x, ρ x ∂μ = 1 →
      ∫ u, negMulLog (pushDensity Φ Φ' ρ u) ∂μ = ∫ x, negMulLog (ρ x) ∂μ)
    (x₀ : E) : |(Φ' x₀).det| = 1 := by
  set g : E → ℝ := fun x => log |(Φ' x).det| with hg_def
  have hg : Continuous g :=
    (ContinuousLinearMap.continuous_det.comp hc).abs.log fun x => abs_ne_zero.2 (hdet x)
  by_contra hne
  have ha : g x₀ ≠ 0 := by
    simp only [hg_def, ne_eq, log_eq_zero, not_or]
    exact ⟨abs_ne_zero.2 (hdet x₀), hne, by linarith [abs_nonneg (Φ' x₀).det]⟩
  set a := g x₀
  -- `a * g > a ^ 2 / 2` on a ball around `x₀`.
  have hpos : 0 < a ^ 2 := by positivity
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ y ∈ ball x₀ r, a ^ 2 / 2 ≤ a * g y := by
    have hk : Continuous fun y => a * g y := continuous_const.mul hg
    have : ∀ᶠ y in nhds x₀, a ^ 2 / 2 < a * g y :=
      continuousAt_const.eventually_lt hk.continuousAt (by change a ^ 2 / 2 < a * a; nlinarith)
    obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff_ball.1 this
    exact ⟨r, hr, fun y hy => (hr' y hy).le⟩
  set B := ball x₀ r
  have hBm : MeasurableSet B := measurableSet_ball
  have hBfin : μ B ≠ ⊤ := measure_ball_lt_top.ne
  have hBpos : 0 < μ.real B := ENNReal.toReal_pos (measure_ball_pos μ x₀ hr).ne' hBfin
  set c := (μ.real B)⁻¹
  have hc0 : 0 < c := inv_pos.2 hBpos
  -- The uniform density on `B`.
  set ρ : E → ℝ := B.indicator fun _ => c
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => indicator_nonneg (fun _ _ => hc0.le) x
  have hρi : Integrable ρ μ := (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  have hρ1 : ∫ x, ρ x ∂μ = 1 := by
    rw [integral_indicator_const _ hBm, smul_eq_mul, mul_inv_cancel₀ hBpos.ne']
  have hgB : IntegrableOn g B μ :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x₀ r)).mono_set
      ball_subset_closedBall
  have hneg : ∀ x, negMulLog (ρ x) = B.indicator (fun _ => negMulLog c) x := fun x => by
    by_cases hx : x ∈ B <;> simp [ρ, hx]
  have hρg : ∀ x, ρ x * g x = B.indicator (fun x => c * g x) x := fun x => by
    by_cases hx : x ∈ B <;> simp [ρ, hx]
  have hI1 : Integrable (fun x => negMulLog (ρ x)) μ := by
    simp_rw [hneg]
    exact (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  have hI2 : Integrable (fun x => ρ x * g x) μ := by
    simp_rw [hρg]
    exact (integrable_indicator_iff hBm).2 (hgB.const_mul c)
  have key := h ρ hρ0 hρi hρ1
  rw [integral_negMulLog_pushDensity hd hΦ hdet, integral_add hI1 hI2] at key
  have h0 : ∫ x in B, g x ∂μ = 0 := by
    have : ∫ x, ρ x * g x ∂μ = 0 := by linarith
    simp_rw [hρg] at this
    rw [integral_indicator hBm, integral_const_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hc0.ne'
  have hlow : a ^ 2 / 2 * μ.real B ≤ ∫ x in B, a * g x ∂μ :=
    setIntegral_ge_of_const_le_real hBm hBfin hball (hgB.const_mul a)
  rw [integral_const_mul, h0, mul_zero] at hlow
  have : 0 < a ^ 2 / 2 * μ.real B := by positivity
  linarith

end MeasureTheory
