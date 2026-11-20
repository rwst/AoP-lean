/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Probability.Distributions.Gaussian.Real

import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Transport of a positive density on the plane to a Gaussian

For a positive `C¹` probability density `ρ` on `ℝ × ℝ` and `v > 0`, the map
`PolarTransport.transport ρ v` is a `C¹` bijection `T` of the plane with
`ρ x = G (T x) |det DT x|`, where `G` is the centred isotropic Gaussian density of variance `v`
in each coordinate. It is a Knothe–Rosenblatt map in polar coordinates: in `(r, θ)`,

* the radius is sent to `R r = √(-2 v log (1 - M r))`, where `M r` is the `ρ`-mass of the disc of
  radius `r`, so that discs go to discs of the same Gaussian mass `1 - exp (-R² / 2v)`;
* on each circle the angle is sent to `Θ r θ = 2π (∫₀^θ ρ(r, φ) dφ) / m r`, where `m r` is the
  integral of `ρ` over the circle, so that arcs go to arcs of the same conditional mass.

The fibres are circles, which are compact, so `M`, `m` and `Θ` inherit the regularity of `ρ`;
a Cartesian Knothe–Rosenblatt map can fail to be `C¹` because a marginal of a smooth positive
density can be discontinuous. The map is smooth away from the origin and `C¹` at the origin,
where its derivative is `√(2π v ρ 0) • id`.

## Main definitions

* `PolarTransport.circleMass`, `PolarTransport.discMass`: `m r` and `M r`.
* `PolarTransport.radius`, `PolarTransport.angle`: `R` and `Θ`.
* `PolarTransport.transport`: the map `T`.

## Main results

* `PolarTransport.contDiff_transport`, `PolarTransport.bijective_transport`;
* `PolarTransport.eq_gaussian_mul_abs_det`: `ρ x = G (T x) |det DT x|`.
-/

open Real MeasureTheory ProbabilityTheory Set Filter Topology

open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace PolarTransport

variable {ρ : ℝ × ℝ → ℝ}

/-! ### Masses of circles and discs -/

/-- `ρ` in polar coordinates. -/
def polar (ρ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := ρ (p.1 * cos p.2, p.1 * sin p.2)

/-- `m r = ∫_{-π}^{π} ρ(r cos θ, r sin θ) dθ`, the integral of `ρ` over the circle of radius `r`
with respect to the angle. -/
def circleMass (ρ : ℝ × ℝ → ℝ) (r : ℝ) : ℝ := ∫ θ in (-π)..π, polar ρ (r, θ)

/-- `M r = ∫₀^r s m s ds`, the `ρ`-mass of the disc of radius `r ≥ 0`. -/
def discMass (ρ : ℝ × ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in (0 : ℝ)..r, s * circleMass ρ s

lemma continuous_polar (hρ : Continuous ρ) : Continuous (polar ρ) := by
  unfold polar; fun_prop

lemma contDiff_polar {n : ℕ∞} (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (polar ρ) :=
  hρ.comp (by fun_prop)

lemma polar_zero_left (θ : ℝ) : polar ρ (0, θ) = ρ 0 := by
  simp [polar]; rfl

lemma polar_add_two_pi (r θ : ℝ) : polar ρ (r, θ + 2 * π) = polar ρ (r, θ) := by
  simp [polar]

lemma continuous_circleMass (hρ : Continuous ρ) : Continuous (circleMass ρ) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun r θ => polar ρ (r, θ)) (continuous_polar hρ) _ _

lemma contDiff_circleMass {n : ℕ∞} (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (circleMass ρ) :=
  (contDiff_polar hρ).parametric_intervalIntegral

lemma circleMass_pos (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (r : ℝ) :
    0 < circleMass ρ r :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    (((continuous_polar hρ).comp (Continuous.prodMk_right r)).intervalIntegrable _ _)
    (fun _ _ => hpos _) (by linarith [pi_pos])

lemma circleMass_zero : circleMass ρ 0 = 2 * π * ρ 0 := by
  simp only [circleMass, polar_zero_left, intervalIntegral.integral_const, smul_eq_mul]
  ring

lemma hasDerivAt_discMass (hρ : Continuous ρ) (r : ℝ) :
    HasDerivAt (discMass ρ) (r * circleMass ρ r) r :=
  (continuous_id.mul (continuous_circleMass hρ)).integral_hasStrictDerivAt 0 r |>.hasDerivAt

lemma continuous_discMass (hρ : Continuous ρ) : Continuous (discMass ρ) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_discMass hρ r).continuousAt

lemma discMass_zero : discMass ρ 0 = 0 := intervalIntegral.integral_same

lemma discMass_pos (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) {r : ℝ} (hr : 0 < r) :
    0 < discMass ρ r :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_id.mul (continuous_circleMass hρ)).intervalIntegrable _ _)
    (fun s hs => mul_pos hs.1 (circleMass_pos hρ hpos s)) hr

lemma strictMonoOn_discMass (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) :
    StrictMonoOn (discMass ρ) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_discMass hρ).continuousOn
    fun r hr => ?_
  rw [interior_Ici] at hr
  rw [(hasDerivAt_discMass hρ r).deriv]
  exact mul_pos hr (circleMass_pos hρ hpos r)

/-- The total mass in polar coordinates: `∫_{r > 0} r m r dr = ∫ ρ = 1`. -/
lemma integrableOn_and_integral_Ioi (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (hint : ∫ x, ρ x = 1) :
    IntegrableOn (fun s => s * circleMass ρ s) (Ioi 0) ∧
      ∫ s in Ioi 0, s * circleMass ρ s = 1 := by
  have hρi : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hint]; norm_num)
  have h1 : ∫⁻ x, ENNReal.ofReal (ρ x) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ fun x => (hpos x).le), hint,
      ENNReal.ofReal_one]
  rw [← lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
    ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)] at h1
  have hinner : ∀ r ∈ Ioi (0 : ℝ), ∫⁻ θ in Ioo (-π) π,
      ENNReal.ofReal (r, θ).1 • ENNReal.ofReal (ρ (polarCoord.symm (r, θ))) =
        ENNReal.ofReal (r * circleMass ρ r) := by
    intro r hr
    have hc : Continuous fun θ => r * polar ρ (r, θ) :=
      continuous_const.mul ((continuous_polar hρ).comp (Continuous.prodMk_right r))
    rw [circleMass, ← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal ((hc.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
        (ae_of_all _ fun θ => (mul_pos hr (hpos _)).le)]
    refine setLIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
    simp only [smul_eq_mul, polarCoord_symm_apply, polar]
    rw [ENNReal.ofReal_mul hr.le]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner] at h1
  have hc : Continuous fun s => s * circleMass ρ s := continuous_id.mul (continuous_circleMass hρ)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun s => s * circleMass ρ s :=
    (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun s hs =>
      (mul_pos hs (circleMass_pos hρ hpos s)).le)
  have hi : IntegrableOn (fun s => s * circleMass ρ s) (Ioi 0) :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable hnn).1 (by simp [h1])
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hc.aestronglyMeasurable, h1, ENNReal.toReal_one]

lemma tendsto_discMass (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (hint : ∫ x, ρ x = 1) :
    Tendsto (discMass ρ) atTop (𝓝 1) := by
  obtain ⟨hi, he⟩ := integrableOn_and_integral_Ioi hρ hpos hint
  rw [← he]
  exact intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id

lemma discMass_lt_one (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (hint : ∫ x, ρ x = 1)
    {r : ℝ} (hr : 0 ≤ r) : discMass ρ r < 1 := by
  have hm := strictMonoOn_discMass hρ hpos
  have hlt : discMass ρ r < discMass ρ (r + 1) := hm hr (by simp; linarith) (by linarith)
  have hle : discMass ρ (r + 1) ≤ 1 := by
    refine ge_of_tendsto (tendsto_discMass hρ hpos hint) ?_
    filter_upwards [eventually_ge_atTop (r + 1)] with t ht
    exact hm.monotoneOn (by simp; linarith) (by simp; linarith) ht
  linarith

/-! ### The radial map -/

/-- The hypotheses on `ρ`: a positive continuous probability density. -/
structure IsPosDensity (ρ : ℝ × ℝ → ℝ) : Prop where
  continuous : Continuous ρ
  pos : ∀ x, 0 < ρ x
  integral_eq_one : ∫ x, ρ x = 1

/-- `R r = √(-2 v log (1 - M r))`: the Gaussian disc of radius `R r` has the `ρ`-mass of the disc
of radius `r`. -/
def radius (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (r : ℝ) : ℝ := √(-2 * v * log (1 - discMass ρ r))

/-- The derivative of `radius ρ v` at `r > 0`. -/
def radiusDeriv (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (r : ℝ) : ℝ :=
  v * (r * circleMass ρ r) / (radius ρ v r * (1 - discMass ρ r))

/-- `K r = ∫₀¹ t m(r t) dt`, so that `M r = r² K r`. -/
def discMassQuot (ρ : ℝ × ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, t * circleMass ρ (r * t)

lemma discMass_eq_sq_mul (r : ℝ) : discMass ρ r = r ^ 2 * discMassQuot ρ r := by
  have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1)
    (fun s => s * circleMass ρ s) r
  simp only [mul_zero, mul_one, smul_eq_mul] at this
  rw [discMass, ← this, discMassQuot, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  congr 1
  ext t
  ring

lemma continuous_discMassQuot (hρ : Continuous ρ) : Continuous (discMassQuot ρ) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun r t => t * circleMass ρ (r * t))
    (continuous_snd.mul ((continuous_circleMass hρ).comp (continuous_fst.mul continuous_snd)))
    _ _

lemma discMassQuot_zero : discMassQuot ρ 0 = circleMass ρ 0 / 2 := by
  simp only [discMassQuot, zero_mul, intervalIntegral.integral_mul_const, integral_id]
  ring

namespace IsPosDensity

variable (hρ : IsPosDensity ρ) {v : ℝ≥0} {r : ℝ}
include hρ

lemma discMass_nonneg (hr : 0 ≤ r) : 0 ≤ discMass ρ r := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [discMass_zero]
  · exact (discMass_pos hρ.1 hρ.2 hr).le

lemma one_sub_discMass_pos (hr : 0 ≤ r) : 0 < 1 - discMass ρ r :=
  sub_pos.2 (discMass_lt_one hρ.1 hρ.2 hρ.3 hr)

lemma log_one_sub_discMass_nonpos (hr : 0 ≤ r) : log (1 - discMass ρ r) ≤ 0 :=
  log_nonpos (hρ.one_sub_discMass_pos hr).le (by linarith [hρ.discMass_nonneg hr])

lemma log_one_sub_discMass_neg (hr : 0 < r) : log (1 - discMass ρ r) < 0 :=
  log_neg (hρ.one_sub_discMass_pos hr.le) (by linarith [discMass_pos hρ.1 hρ.2 hr])

lemma radius_sq (hr : 0 ≤ r) : radius ρ v r ^ 2 = -2 * v * log (1 - discMass ρ r) :=
  sq_sqrt (mul_nonneg_of_nonpos_of_nonpos (by have := v.coe_nonneg; linarith)
    (hρ.log_one_sub_discMass_nonpos hr))

lemma radius_pos (hv : v ≠ 0) (hr : 0 < r) : 0 < radius ρ v r := by
  have : (0 : ℝ) < v := by positivity
  exact sqrt_pos.2 (mul_pos_of_neg_of_neg (by linarith) (hρ.log_one_sub_discMass_neg hr))

/-- The Gaussian mass outside the disc of radius `R r` is `1 - M r`. -/
lemma exp_neg_radius_sq (hv : v ≠ 0) (hr : 0 ≤ r) :
    exp (-radius ρ v r ^ 2 / (2 * v)) = 1 - discMass ρ r := by
  have : (0 : ℝ) < v := by positivity
  rw [hρ.radius_sq hr, show -(-2 * (v : ℝ) * log (1 - discMass ρ r)) / (2 * v) =
    log (1 - discMass ρ r) by field_simp, exp_log (hρ.one_sub_discMass_pos hr)]

lemma hasDerivAt_radius (hv : v ≠ 0) (hr : 0 < r) :
    HasDerivAt (radius ρ v) (radiusDeriv ρ v r) r := by
  have hv' : (0 : ℝ) < v := by positivity
  have h1 := hρ.one_sub_discMass_pos hr.le
  have hR := hρ.radius_pos hv hr
  have h2 := (((hasDerivAt_discMass hρ.1 r).const_sub 1).log h1.ne').const_mul (-2 * (v : ℝ))
  have h3 := h2.sqrt (mul_pos_of_neg_of_neg (by linarith)
    (hρ.log_one_sub_discMass_neg hr)).ne'
  have h4 : HasDerivAt (radius ρ v) _ r := h3
  convert h4 using 1
  rw [radiusDeriv, show √(-2 * (v : ℝ) * log (1 - discMass ρ r)) = radius ρ v r from rfl]
  field_simp

lemma radiusDeriv_pos (hv : v ≠ 0) (hr : 0 < r) : 0 < radiusDeriv ρ v r := by
  have : (0 : ℝ) < v := by positivity
  exact div_pos (mul_pos this (mul_pos hr (circleMass_pos hρ.1 hρ.2 r)))
    (mul_pos (hρ.radius_pos hv hr) (hρ.one_sub_discMass_pos hr.le))

lemma continuousOn_radius : ContinuousOn (radius ρ v) (Ici 0) := fun _ hr =>
  (ContinuousAt.sqrt (continuousAt_const.mul (ContinuousAt.log
    (continuousAt_const.sub (continuous_discMass hρ.1).continuousAt)
    (hρ.one_sub_discMass_pos hr).ne'))).continuousWithinAt

lemma strictMonoOn_radius (hv : v ≠ 0) : StrictMonoOn (radius ρ v) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) hρ.continuousOn_radius fun r hr => ?_
  rw [interior_Ici] at hr
  rw [(hρ.hasDerivAt_radius hv hr).deriv]
  exact hρ.radiusDeriv_pos hv hr

lemma tendsto_radius_atTop (hv : v ≠ 0) : Tendsto (radius ρ v) atTop atTop := by
  have hv' : (0 : ℝ) < v := by positivity
  have h1 : Tendsto (fun r => 1 - discMass ρ r) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa using (tendsto_discMass hρ.1 hρ.2 hρ.3).const_sub 1
    · filter_upwards [eventually_ge_atTop 0] with r hr
      exact hρ.one_sub_discMass_pos hr
  exact tendsto_sqrt_atTop.comp
    ((tendsto_log_nhdsGT_zero.comp h1).const_mul_atBot_of_neg (by linarith))

lemma exists_radius_eq (hv : v ≠ 0) {a : ℝ} (ha : 0 < a) : ∃ r, 0 < r ∧ radius ρ v r = a := by
  obtain ⟨N, hN, hN0⟩ :=
    (((hρ.tendsto_radius_atTop hv).eventually_ge_atTop a).and (eventually_ge_atTop 0)).exists
  have hR0 : radius ρ v 0 = 0 := by simp [radius, discMass_zero]
  obtain ⟨r, hr, hra⟩ :=
    intermediate_value_Icc hN0 (hρ.continuousOn_radius.mono Icc_subset_Ici_self)
    ⟨by rw [hR0]; exact ha.le, hN⟩
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, hra⟩
  rintro rfl
  rw [hR0] at hra
  exact ha.ne hra

/-- `R r / r → c = √(v m 0)` as `r → 0⁺`. -/
lemma tendsto_radius_div (hv : v ≠ 0) :
    Tendsto (fun r => radius ρ v r / r) (𝓝[>] 0) (𝓝 √(v * circleMass ρ 0)) := by
  -- `-log (1 - u) / u → 1` as `u → 0`
  have hlog : Tendsto (fun u : ℝ => -(u⁻¹ * log (1 - u))) (𝓝[≠] 0) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope_zero.1
      (((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num))
    simp only [zero_add, smul_eq_mul] at h
    simpa using h.neg
  have hM : Tendsto (discMass ρ) (𝓝[>] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have := ((continuous_discMass hρ.1).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rwa [discMass_zero] at this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact (discMass_pos hρ.1 hρ.2 hr).ne'
  have hK : Tendsto (discMassQuot ρ) (𝓝[>] 0) (𝓝 (circleMass ρ 0 / 2)) := by
    rw [← discMassQuot_zero]
    exact (continuous_discMassQuot hρ.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := ((hK.const_mul (2 * (v : ℝ))).mul (hlog.comp hM)).sqrt
  rw [show √(2 * (v : ℝ) * (circleMass ρ 0 / 2) * 1) = √(v * circleMass ρ 0) by ring_nf] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have hM0 := (discMass_pos hρ.1 hρ.2 hr).ne'
  have hsq := hρ.radius_sq (v := v) hr.le
  rw [discMass_eq_sq_mul] at hsq hM0
  rw [Function.comp_apply, discMass_eq_sq_mul,
    ← sqrt_sq (div_nonneg (sqrt_nonneg _) hr.le : 0 ≤ radius ρ v r / r), div_pow, hsq]
  have hK0 : discMassQuot ρ r ≠ 0 := right_ne_zero_of_mul hM0
  congr 1
  field_simp

/-- `R' r → c` as `r → 0⁺`. -/
lemma tendsto_radiusDeriv (hv : v ≠ 0) :
    Tendsto (radiusDeriv ρ v) (𝓝[>] 0) (𝓝 √(v * circleMass ρ 0)) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hc : 0 < √(v * circleMass ρ 0) :=
    sqrt_pos.2 (mul_pos hv' (circleMass_pos hρ.1 hρ.2 0))
  have h1 : Tendsto (fun r => 1 - discMass ρ r) (𝓝[>] 0) (𝓝 1) := by
    have := (((continuous_discMass hρ.1).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))).const_sub 1
    rwa [discMass_zero, sub_zero] at this
  have hm : Tendsto (circleMass ρ) (𝓝[>] 0) (𝓝 (circleMass ρ 0)) :=
    (continuous_circleMass hρ.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hm.const_mul (v : ℝ)).div ((hρ.tendsto_radius_div hv).mul h1)
    (by rw [mul_one]; exact hc.ne')
  rw [mul_one, show (v : ℝ) * circleMass ρ 0 / √(v * circleMass ρ 0) = √(v * circleMass ρ 0) by
    rw [div_eq_iff hc.ne', mul_self_sqrt (mul_pos hv' (circleMass_pos hρ.1 hρ.2 0)).le]] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  have := hr.ne'
  simp only [Pi.div_apply]
  rw [radiusDeriv]
  field_simp

end IsPosDensity

/-! ### The angular map -/

/-- `Θ r θ = 2π (∫₀^θ ρ(r cos φ, r sin φ) dφ) / m r`: the arc from angle `0` to `Θ r θ` has the
conditional mass on the circle of radius `r` of the arc from `0` to `θ`. -/
def angle (ρ : ℝ × ℝ → ℝ) (r θ : ℝ) : ℝ :=
  2 * π / circleMass ρ r * ∫ φ in (0 : ℝ)..θ, polar ρ (r, φ)

lemma angle_zero_right (r : ℝ) : angle ρ r 0 = 0 := by
  simp [angle]

lemma hasDerivAt_angle (hρ : Continuous ρ) (r θ : ℝ) :
    HasDerivAt (angle ρ r) (2 * π / circleMass ρ r * polar ρ (r, θ)) θ :=
  (((continuous_polar hρ).comp (Continuous.prodMk_right r)).integral_hasStrictDerivAt 0 θ
    |>.hasDerivAt).const_mul _

lemma continuous_angle_right (hρ : Continuous ρ) (r : ℝ) : Continuous (angle ρ r) :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_angle hρ r θ).continuousAt

lemma strictMono_angle (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (r : ℝ) :
    StrictMono (angle ρ r) := by
  refine strictMonoOn_univ.1 (strictMonoOn_of_deriv_pos convex_univ
    (continuous_angle_right hρ r).continuousOn fun θ _ => ?_)
  rw [(hasDerivAt_angle hρ r θ).deriv]
  exact mul_pos (div_pos (by positivity) (circleMass_pos hρ hpos r)) (hpos _)

lemma angle_add_two_pi (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (r θ : ℝ) :
    angle ρ r (θ + 2 * π) = angle ρ r θ + 2 * π := by
  have hc : Continuous fun φ => polar ρ (r, φ) :=
    (continuous_polar hρ).comp (Continuous.prodMk_right r)
  have hper : Function.Periodic (fun φ => polar ρ (r, φ)) (2 * π) := fun φ =>
    polar_add_two_pi r φ
  have h := hper.intervalIntegral_add_eq θ (-π)
  rw [show -π + 2 * π = π by ring] at h
  have hm := (circleMass_pos hρ hpos r).ne'
  rw [angle, angle, ← intervalIntegral.integral_add_adjacent_intervals (b := θ)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), h,
    show (∫ φ in (-π)..π, polar ρ (r, φ)) = circleMass ρ r from rfl]
  field_simp

lemma angle_add_int_mul (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (r θ : ℝ) (k : ℤ) :
    angle ρ r (θ + k * (2 * π)) = angle ρ r θ + k * (2 * π) := by
  have hper : Function.Periodic (fun θ => angle ρ r θ - θ) (2 * π) := fun θ => by
    simp only [angle_add_two_pi hρ hpos]; ring
  have := hper.int_mul k θ
  linarith

/-- `∫₀^θ g = θ ∫₀¹ g(θ t) dt`. -/
lemma integral_zero_eq_mul (g : ℝ → ℝ) (θ : ℝ) :
    ∫ φ in (0 : ℝ)..θ, g φ = θ * ∫ t in (0 : ℝ)..1, g (θ * t) := by
  have := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 1) g θ
  simp only [mul_zero, mul_one, smul_eq_mul] at this
  exact this.symm

lemma contDiff_angle {n : ℕ∞} (hρ : ContDiff ℝ n ρ) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ n fun p : ℝ × ℝ => angle ρ p.1 p.2 := by
  have hc : Continuous ρ := hρ.continuous
  have hI : ContDiff ℝ n fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, polar ρ (p.1, p.2 * t) :=
    ((contDiff_polar hρ).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2 * q.2))
      (by fun_prop)).parametric_intervalIntegral
  have hm : ContDiff ℝ n fun p : ℝ × ℝ => circleMass ρ p.1 :=
    (contDiff_circleMass hρ).comp contDiff_fst
  have : (fun p : ℝ × ℝ => angle ρ p.1 p.2) = fun p =>
      2 * π / circleMass ρ p.1 * (p.2 * ∫ t in (0 : ℝ)..1, polar ρ (p.1, p.2 * t)) := by
    ext p
    rw [angle, integral_zero_eq_mul]
  rw [this]
  exact (contDiff_const.div hm fun p => (circleMass_pos hc hpos p.1).ne').mul
    (contDiff_snd.mul hI)

/-- `|Θ r θ - θ| ≤ 4π |θ| ε / m r` if `ρ` is within `ε` of `ρ 0` on the circle of radius `r`. -/
lemma abs_angle_sub_le (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) {r θ ε : ℝ}
    (hε : ∀ φ, |polar ρ (r, φ) - ρ 0| ≤ ε) :
    |angle ρ r θ - θ| ≤ 4 * π * |θ| * ε / circleMass ρ r := by
  have hc : Continuous fun φ => polar ρ (r, φ) :=
    (continuous_polar hρ).comp (Continuous.prodMk_right r)
  have hm := circleMass_pos hρ hpos r
  have hb : ∀ a b : ℝ, |(∫ φ in a..b, polar ρ (r, φ)) - (b - a) * ρ 0| ≤ ε * |b - a| := by
    intro a b
    rw [show (b - a) * ρ 0 = ∫ _ in a..b, ρ 0 by simp,
      ← intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun φ => polar ρ (r, φ) - ρ 0) (C := ε) fun φ _ => by
        rw [Real.norm_eq_abs]; exact hε φ
  have h1 := hb 0 θ
  have h2 := hb (-π) π
  rw [sub_zero] at h1
  rw [show π - -π = 2 * π by ring, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h2
  change |circleMass ρ r - 2 * π * ρ 0| ≤ ε * (2 * π) at h2
  rw [angle, show 2 * π / circleMass ρ r * (∫ φ in (0 : ℝ)..θ, polar ρ (r, φ)) - θ =
    (2 * π * ((∫ φ in (0 : ℝ)..θ, polar ρ (r, φ)) - θ * ρ 0) -
      θ * (circleMass ρ r - 2 * π * ρ 0)) / circleMass ρ r by field_simp; ring,
    abs_div, abs_of_pos hm]
  gcongr
  calc |2 * π * ((∫ φ in (0 : ℝ)..θ, polar ρ (r, φ)) - θ * ρ 0) -
        θ * (circleMass ρ r - 2 * π * ρ 0)|
      ≤ 2 * π * |(∫ φ in (0 : ℝ)..θ, polar ρ (r, φ)) - θ * ρ 0| +
        |θ| * |circleMass ρ r - 2 * π * ρ 0| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul (2 * π), abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_mul θ]
    _ ≤ 2 * π * (ε * |θ|) + |θ| * (ε * (2 * π)) := by gcongr
    _ = 4 * π * |θ| * ε := by ring

/-! ### Polar coordinates on the whole plane -/

/-- `polarCoord.symm ∘ polarCoord = id` on the whole plane, including the cut `(-∞, 0]`. -/
lemma polarCoord_symm_polarCoord (x : ℝ × ℝ) : polarCoord.symm (polarCoord x) = x := by
  have A : √(x.1 ^ 2 + x.2 ^ 2) = ‖Complex.equivRealProd.symm x‖ := by
    rw [Complex.norm_def, Complex.equivRealProd_symm_apply, Complex.normSq_add_mul_I]
  ext
  · simp only [polarCoord_symm_apply, polarCoord_apply, A, Complex.norm_mul_cos_arg]
    simp [Complex.equivRealProd_symm_apply]
  · simp only [polarCoord_symm_apply, polarCoord_apply, A, Complex.norm_mul_sin_arg]
    simp [Complex.equivRealProd_symm_apply]

lemma polarCoord_fst_nonneg (x : ℝ × ℝ) : 0 ≤ (polarCoord x).1 := sqrt_nonneg _

lemma polarCoord_fst_pos {x : ℝ × ℝ} (hx : x ≠ 0) : 0 < (polarCoord x).1 := by
  refine lt_of_le_of_ne (polarCoord_fst_nonneg x) fun h => hx ?_
  rw [← polarCoord_symm_polarCoord x, ← Prod.mk.eta (p := polarCoord x), ← h]
  simp

lemma polarCoord_snd_mem (x : ℝ × ℝ) : (polarCoord x).2 ∈ Ioc (-π) π :=
  ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩

lemma polarCoord_fst_polarCoord_symm {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    (polarCoord (polarCoord.symm (r, θ))).1 = r := by
  simp only [polarCoord_apply, polarCoord_symm_apply]
  rw [show (r * cos θ) ^ 2 + (r * sin θ) ^ 2 = r ^ 2 by
    rw [mul_pow, mul_pow, ← mul_add, cos_sq_add_sin_sq, mul_one], sqrt_sq hr]

lemma polarCoord_symm_add_int_mul (a α : ℝ) (k : ℤ) :
    polarCoord.symm (a, α + k * (2 * π)) = polarCoord.symm (a, α) := by
  simp [cos_add_int_mul_two_pi, sin_add_int_mul_two_pi]

/-- Points with the same positive radius have angles that differ by a multiple of `2π`. -/
lemma exists_eq_add_int_mul {a α β : ℝ} (ha : 0 < a)
    (h : polarCoord.symm (a, α) = polarCoord.symm (a, β)) : ∃ k : ℤ, α = β + k * (2 * π) := by
  simp only [polarCoord_symm_apply, Prod.mk.injEq] at h
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1
    (Real.Angle.cos_sin_inj (mul_left_cancel₀ ha.ne' h.1) (mul_left_cancel₀ ha.ne' h.2))
  exact ⟨k, by linarith⟩

/-! ### The transport map -/

/-- The transport map `T`: `(r, θ) ↦ (R r, Θ r θ)` in polar coordinates. -/
def transport (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (x : ℝ × ℝ) : ℝ × ℝ :=
  polarCoord.symm (radius ρ v (polarCoord x).1, angle ρ (polarCoord x).1 (polarCoord x).2)

lemma radius_zero {v : ℝ≥0} : radius ρ v 0 = 0 := by simp [radius, discMass_zero]

lemma radius_nonneg {v : ℝ≥0} (r : ℝ) : 0 ≤ radius ρ v r := sqrt_nonneg _

lemma transport_zero {v : ℝ≥0} : transport ρ v 0 = 0 := by
  simp [transport, radius_zero]

lemma polarCoord_fst_transport {v : ℝ≥0} (x : ℝ × ℝ) :
    (polarCoord (transport ρ v x)).1 = radius ρ v (polarCoord x).1 :=
  polarCoord_fst_polarCoord_symm (radius_nonneg _) _

namespace IsPosDensity

variable (hρ : IsPosDensity ρ) {v : ℝ≥0}
include hρ

/-- `T (r, θ) = (R r, Θ r θ)` in polar coordinates, for every angle `θ`. -/
lemma transport_polarCoord_symm {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    transport ρ v (polarCoord.symm (r, θ)) = polarCoord.symm (radius ρ v r, angle ρ r θ) := by
  have h1 := polarCoord_fst_polarCoord_symm hr θ
  rw [transport, h1]
  rcases hr.eq_or_lt with rfl | hr
  · simp [radius_zero]
  · have h2 := polarCoord_symm_polarCoord (polarCoord.symm (0 + r, θ))
    rw [zero_add] at h2
    nth_rw 1 [← Prod.mk.eta (p := polarCoord (polarCoord.symm (r, θ))), h1] at h2
    obtain ⟨k, hk⟩ := exists_eq_add_int_mul hr h2
    rw [hk, angle_add_int_mul hρ.1 hρ.2, polarCoord_symm_add_int_mul]

lemma injective_transport (hv : v ≠ 0) : Function.Injective (transport ρ v) := by
  intro x y h
  have hr : radius ρ v (polarCoord x).1 = radius ρ v (polarCoord y).1 := by
    rw [← polarCoord_fst_transport, ← polarCoord_fst_transport, h]
  have hr' := (hρ.strictMonoOn_radius hv).injOn (polarCoord_fst_nonneg x)
    (polarCoord_fst_nonneg y) hr
  rw [← polarCoord_symm_polarCoord x, ← polarCoord_symm_polarCoord y,
    ← Prod.mk.eta (p := polarCoord x), ← Prod.mk.eta (p := polarCoord y), hr']
  rcases (polarCoord_fst_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · have h' : polarCoord.symm (radius ρ v (polarCoord y).1,
        angle ρ (polarCoord y).1 (polarCoord x).2) =
        polarCoord.symm (radius ρ v (polarCoord y).1,
        angle ρ (polarCoord y).1 (polarCoord y).2) := by
      have := h
      rw [transport, transport, hr'] at this
      exact this
    obtain ⟨k, hk⟩ := exists_eq_add_int_mul (hρ.radius_pos hv hpos) h'
    rw [← angle_add_int_mul hρ.1 hρ.2] at hk
    rw [(strictMono_angle hρ.1 hρ.2 _).injective hk, polarCoord_symm_add_int_mul]

lemma surjective_transport (hv : v ≠ 0) : Function.Surjective (transport ρ v) := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, transport_zero⟩
  obtain ⟨r, hr, hRr⟩ := hρ.exists_radius_eq hv (polarCoord_fst_pos hz)
  have hm2 : angle ρ r (-2 * π) = -2 * π := by
    have := angle_add_int_mul hρ.1 hρ.2 r 0 (-1)
    rw [angle_zero_right] at this
    convert this using 2 <;> push_cast <;> ring
  have hp2 : angle ρ r (2 * π) = 2 * π := by
    have := angle_add_two_pi hρ.1 hρ.2 r 0
    rwa [zero_add, angle_zero_right, zero_add] at this
  have hz2 := polarCoord_snd_mem z
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc (by linarith [pi_pos] : -2 * π ≤ 2 * π)
    (continuous_angle_right hρ.1 r).continuousOn
    (show (polarCoord z).2 ∈ Icc (angle ρ r (-2 * π)) (angle ρ r (2 * π)) by
      rw [hm2, hp2]; constructor <;> linarith [hz2.1, hz2.2, pi_pos])
  refine ⟨polarCoord.symm (r, θ), ?_⟩
  rw [hρ.transport_polarCoord_symm hr.le, hRr, hθ, Prod.mk.eta, polarCoord_symm_polarCoord]

lemma bijective_transport (hv : v ≠ 0) : Function.Bijective (transport ρ v) :=
  ⟨hρ.injective_transport hv, hρ.surjective_transport hv⟩

end IsPosDensity

/-! ### Derivatives away from the origin -/

lemma fderivPolarCoordSymm_apply (p v : ℝ × ℝ) :
    fderivPolarCoordSymm p v =
      (cos p.2 * v.1 + -p.1 * sin p.2 * v.2, sin p.2 * v.1 + p.1 * cos p.2 * v.2) := by
  rw [fderivPolarCoordSymm, Matrix.toLin_finTwoProd_toContinuousLinearMap]
  simp

/-- The derivative of `polarCoord` at `polarCoord.symm p`, for `p.1 ≠ 0`. -/
def fderivPolarCoord (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (cos p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ + sin p.2 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    ((-sin p.2 / p.1) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (cos p.2 / p.1) • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma fderivPolarCoord_apply (p v : ℝ × ℝ) :
    fderivPolarCoord p v =
      (cos p.2 * v.1 + sin p.2 * v.2, -sin p.2 / p.1 * v.1 + cos p.2 / p.1 * v.2) := by
  simp [fderivPolarCoord]

/-- `fderivPolarCoordSymm p` as an equivalence, for `p.1 ≠ 0`. -/
def fderivPolarCoordSymmEquiv (p : ℝ × ℝ) (hp : p.1 ≠ 0) : (ℝ × ℝ) ≃L[ℝ] ℝ × ℝ :=
  ContinuousLinearEquiv.equivOfInverse (fderivPolarCoordSymm p) (fderivPolarCoord p)
    (fun v => by
      have hr : p.1 * p.1⁻¹ = 1 := mul_inv_cancel₀ hp
      simp only [fderivPolarCoordSymm_apply, fderivPolarCoord_apply, div_eq_mul_inv]
      ext
      · linear_combination v.1 * sin_sq_add_cos_sq p.2
      · linear_combination (p.1 * p.1⁻¹ * v.2) * sin_sq_add_cos_sq p.2 + v.2 * hr)
    (fun v => by
      have hr : p.1 * p.1⁻¹ = 1 := mul_inv_cancel₀ hp
      simp only [fderivPolarCoordSymm_apply, fderivPolarCoord_apply, div_eq_mul_inv]
      ext
      · linear_combination v.1 * sin_sq_add_cos_sq p.2 +
          (sin p.2 ^ 2 * v.1 - sin p.2 * cos p.2 * v.2) * hr
      · linear_combination v.2 * sin_sq_add_cos_sq p.2 +
          (cos p.2 ^ 2 * v.2 - cos p.2 * sin p.2 * v.1) * hr)

lemma contDiff_polarCoord_symm {n : WithTop ℕ∞} : ContDiff ℝ n polarCoord.symm := by
  have : ⇑polarCoord.symm = fun p : ℝ × ℝ => (p.1 * cos p.2, p.1 * sin p.2) :=
    funext polarCoord_symm_apply
  rw [this]
  fun_prop

lemma zero_notMem_polarCoord_source : (0 : ℝ × ℝ) ∉ polarCoord.source := by
  simp [polarCoord_source]

lemma contDiffAt_polarCoord {n : WithTop ℕ∞} {x : ℝ × ℝ} (hx : x ∈ polarCoord.source) :
    ContDiffAt ℝ n polarCoord x := by
  have hx0 : x ≠ 0 := fun h => zero_notMem_polarCoord_source (h ▸ hx)
  have := polarCoord.symm.contDiffAt_symm (n := n)
    (f₀' := fderivPolarCoordSymmEquiv (polarCoord x) (polarCoord_fst_pos hx0).ne') (a := x)
    (by rw [OpenPartialHomeomorph.symm_target]; exact hx)
    (by rw [OpenPartialHomeomorph.symm_symm]; exact hasFDerivAt_polarCoord_symm (polarCoord x))
    contDiff_polarCoord_symm.contDiffAt
  rwa [OpenPartialHomeomorph.symm_symm] at this

lemma polarCoord_symm_add_pi (a α : ℝ) :
    polarCoord.symm (a, α + π) = -polarCoord.symm (a, α) := by
  simp [cos_add_pi, sin_add_pi]

lemma neg_mem_polarCoord_source {y : ℝ × ℝ} (hy : y ≠ 0) (h : y ∉ polarCoord.source) :
    -y ∈ polarCoord.source := by
  simp only [polarCoord_source, mem_union, mem_ofPred_eq, not_or, not_lt, ne_eq,
    not_not] at h ⊢
  left
  rcases h.1.lt_or_eq with h1 | h1
  · simpa using h1
  · exact absurd (Prod.ext h1 h.2) hy

/-- A polar chart at `y ≠ 0`: `polarCoord` if `y` is off the cut `(-∞, 0]`, and
`z ↦ polarCoord (-z) + (0, π)`, with angles in `(0, 2π]`, otherwise. -/
def chart (y : ℝ × ℝ) : ℝ × ℝ → ℝ × ℝ :=
  open scoped Classical in
  if y ∈ polarCoord.source then polarCoord else fun z => polarCoord (-z) + (0, π)

lemma polarCoord_symm_chart (y z : ℝ × ℝ) : polarCoord.symm (chart y z) = z := by
  unfold chart
  split_ifs
  · exact polarCoord_symm_polarCoord z
  · change polarCoord.symm (polarCoord (-z) + (0, π)) = z
    rw [← Prod.mk.eta (p := polarCoord (-z)), Prod.mk_add_mk, add_zero, polarCoord_symm_add_pi,
      Prod.mk.eta, polarCoord_symm_polarCoord, neg_neg]

lemma chart_fst (y z : ℝ × ℝ) : (chart y z).1 = (polarCoord z).1 := by
  unfold chart
  split_ifs
  · rfl
  · simp [polarCoord_apply]

lemma chart_snd_mem (y z : ℝ × ℝ) : (chart y z).2 ∈ Icc (-π) (2 * π) := by
  have h := polarCoord_snd_mem z
  have h' := polarCoord_snd_mem (-z)
  unfold chart
  split_ifs
  · exact ⟨h.1.le, by linarith [pi_pos, h.2]⟩
  · change (polarCoord (-z)).2 + π ∈ _
    exact ⟨by linarith [pi_pos, h'.1], by linarith [h'.2]⟩

lemma continuousAt_chart {y : ℝ × ℝ} (hy : y ≠ 0) : ContinuousAt (chart y) y := by
  unfold chart
  split_ifs with h
  · exact polarCoord.continuousAt h
  · exact ((polarCoord.continuousAt (neg_mem_polarCoord_source hy h)).comp
      continuous_neg.continuousAt).add continuousAt_const

lemma contDiffAt_chart {n : WithTop ℕ∞} {y : ℝ × ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ n (chart y) y := by
  unfold chart
  split_ifs with h
  · exact contDiffAt_polarCoord h
  · exact ((contDiffAt_polarCoord (neg_mem_polarCoord_source hy h)).comp y
      contDiff_neg.contDiffAt).add contDiffAt_const

lemma chart_self_fst_pos {y : ℝ × ℝ} (hy : y ≠ 0) : 0 < (chart y y).1 := by
  rw [chart_fst]; exact polarCoord_fst_pos hy

lemma hasFDerivAt_chart {y : ℝ × ℝ} (hy : y ≠ 0) :
    HasFDerivAt (chart y) (fderivPolarCoord (chart y y)) y :=
  HasFDerivAt.of_local_left_inverse (f := polarCoord.symm)
    (f' := fderivPolarCoordSymmEquiv (chart y y) (chart_self_fst_pos hy).ne')
    (continuousAt_chart hy) (hasFDerivAt_polarCoord_symm _)
    (Eventually.of_forall fun z => polarCoord_symm_chart y z)

/-- `(r, θ) ↦ (R r, Θ r θ)`. -/
def polarMap (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (q : ℝ × ℝ) : ℝ × ℝ := (radius ρ v q.1, angle ρ q.1 q.2)

/-- The derivative of `polarMap ρ v` at `q` with `q.1 > 0`. -/
def fderivPolarMap (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (radiusDeriv ρ v q.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) q)

/-- The derivative of the transport map at `polarCoord.symm q`. -/
def fderivTransport (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (fderivPolarCoordSymm (polarMap ρ v q)).comp ((fderivPolarMap ρ v q).comp (fderivPolarCoord q))

lemma contDiff_discMass (hρ : Continuous ρ) : ContDiff ℝ 1 (discMass ρ) := by
  refine contDiff_one_iff_deriv.2 ⟨fun r => (hasDerivAt_discMass hρ r).differentiableAt, ?_⟩
  rw [show deriv (discMass ρ) = fun r => r * circleMass ρ r from
    funext fun r => (hasDerivAt_discMass hρ r).deriv]
  exact continuous_id.mul (continuous_circleMass hρ)

lemma det_comp (f g : ℝ × ℝ →L[ℝ] ℝ × ℝ) : (f.comp g).det = f.det * g.det :=
  LinearMap.det_comp (f : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) g

lemma det_prod (f g : ℝ × ℝ →L[ℝ] ℝ) :
    (f.prod g).det = f (1, 0) * g (0, 1) - f (0, 1) * g (1, 0) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

namespace IsPosDensity

variable (hρ : IsPosDensity ρ) {v : ℝ≥0}
include hρ

lemma contDiffAt_radius (hv : v ≠ 0) {r : ℝ} (hr : 0 < r) : ContDiffAt ℝ 1 (radius ρ v) r :=
  (contDiffAt_const.mul ((contDiffAt_const.sub (contDiff_discMass hρ.1).contDiffAt).log
    (hρ.one_sub_discMass_pos hr.le).ne')).sqrt
    (mul_pos_of_neg_of_neg (by have h : (0 : ℝ) < v := (by positivity); linarith)
      (hρ.log_one_sub_discMass_neg hr)).ne'

lemma transport_eq_comp (y : ℝ × ℝ) :
    transport ρ v = polarCoord.symm ∘ polarMap ρ v ∘ chart y := by
  ext1 z
  conv_lhs => rw [← polarCoord_symm_chart y z, ← Prod.mk.eta (p := chart y z)]
  rw [hρ.transport_polarCoord_symm (by rw [chart_fst]; exact polarCoord_fst_nonneg z)]
  rfl

variable (hρ1 : ContDiff ℝ 1 ρ)
include hρ1

lemma hasFDerivAt_polarMap (hv : v ≠ 0) {q : ℝ × ℝ} (hq : 0 < q.1) :
    HasFDerivAt (polarMap ρ v) (fderivPolarMap ρ v q) q :=
  ((hρ.hasDerivAt_radius hv hq).comp_hasFDerivAt q (hasFDerivAt_fst)).prodMk
    ((contDiff_angle hρ1 hρ.2).differentiable one_ne_zero q).hasFDerivAt

lemma hasFDerivAt_transport (hv : v ≠ 0) {y : ℝ × ℝ} (hy : y ≠ 0) :
    HasFDerivAt (transport ρ v) (fderivTransport ρ v (chart y y)) y := by
  rw [hρ.transport_eq_comp y]
  exact (hasFDerivAt_polarCoord_symm _).comp y
    ((hρ.hasFDerivAt_polarMap hρ1 hv (chart_self_fst_pos hy)).comp y (hasFDerivAt_chart hy))

lemma contDiffAt_transport (hv : v ≠ 0) {y : ℝ × ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (transport ρ v) y := by
  rw [hρ.transport_eq_comp y]
  exact contDiff_polarCoord_symm.contDiffAt.comp y
    ((((hρ.contDiffAt_radius hv (chart_self_fst_pos hy)).comp _ contDiffAt_fst).prodMk
      (contDiff_angle hρ1 hρ.2).contDiffAt).comp y (contDiffAt_chart hy))

/-- `∂Θ/∂θ = 2π ρ / m`. -/
lemma fderiv_angle_snd (q : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) q (0, 1) =
      2 * π / circleMass ρ q.1 * polar ρ q := by
  have h1 := ((contDiff_angle hρ1 hρ.2).differentiable one_ne_zero q).hasFDerivAt
  have h2 : HasDerivAt (fun θ => ((q.1, θ) : ℝ × ℝ)) (0, 1) q.2 :=
    (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
  have h3 := h1.comp_hasDerivAt q.2 h2
  exact h3.unique (hasDerivAt_angle hρ.1 q.1 q.2)

lemma det_fderivTransport {q : ℝ × ℝ} (hq : 0 < q.1) :
    (fderivTransport ρ v q).det =
      radius ρ v q.1 * (radiusDeriv ρ v q.1 * (2 * π / circleMass ρ q.1 * polar ρ q)) *
        q.1⁻¹ := by
  have hinv : fderivPolarCoord q =
      ((fderivPolarCoordSymmEquiv q hq.ne').symm : ℝ × ℝ →L[ℝ] ℝ × ℝ) := rfl
  rw [fderivTransport, det_comp, det_comp, det_fderivPolarCoordSymm, hinv,
    ContinuousLinearEquiv.det_coe_symm, show ((fderivPolarCoordSymmEquiv q hq.ne' :
      ℝ × ℝ →L[ℝ] ℝ × ℝ)) = fderivPolarCoordSymm q from rfl, det_fderivPolarCoordSymm,
    fderivPolarMap, det_prod, hρ.fderiv_angle_snd hρ1]
  simp [polarMap]
  ring

end IsPosDensity

/-! ### The density identity away from the origin -/

/-- The centred isotropic Gaussian density of variance `v` in each coordinate. -/
def gauss (v : ℝ≥0) (y : ℝ × ℝ) : ℝ := gaussianPDFReal 0 v y.1 * gaussianPDFReal 0 v y.2

lemma gauss_polarCoord_symm {v : ℝ≥0} (hv : v ≠ 0) (a α : ℝ) :
    gauss v (polarCoord.symm (a, α)) = (2 * π * v)⁻¹ * exp (-a ^ 2 / (2 * v)) := by
  have hv' : (0 : ℝ) < v := by positivity
  simp only [gauss, gaussianPDFReal, polarCoord_symm_apply, sub_zero]
  rw [mul_mul_mul_comm, ← mul_inv, mul_self_sqrt (by positivity), ← exp_add, ← add_div]
  congr 3
  linear_combination (-a ^ 2) * cos_sq_add_sin_sq α

namespace IsPosDensity

variable (hρ : IsPosDensity ρ) (hρ1 : ContDiff ℝ 1 ρ) {v : ℝ≥0}
include hρ hρ1

/-- **The density identity** at `y ≠ 0`: `ρ y = G (T y) |det DT y|`. -/
lemma eq_gauss_mul_abs_det_of_ne (hv : v ≠ 0) {y : ℝ × ℝ} (hy : y ≠ 0) :
    ρ y = gauss v (transport ρ v y) * |(fderivTransport ρ v (chart y y)).det| := by
  set q := chart y y with hq_def
  have hq : 0 < q.1 := chart_self_fst_pos hy
  have hv' : (0 : ℝ) < v := by positivity
  have hT : transport ρ v y = polarCoord.symm (polarMap ρ v q) := by
    rw [hρ.transport_eq_comp y]; rfl
  have hpolar : polar ρ q = ρ y := by
    change ρ (polarCoord.symm q) = ρ y
    rw [hq_def, polarCoord_symm_chart]
  have hR := hρ.radius_pos hv hq
  have hm := circleMass_pos hρ.1 hρ.2 q.1
  have h1 := hρ.one_sub_discMass_pos hq.le
  have hy0 := hρ.2 y
  rw [hT, polarMap, gauss_polarCoord_symm hv, hρ.exp_neg_radius_sq hv hq.le,
    hρ.det_fderivTransport hρ1 hq, hpolar, radiusDeriv]
  rw [abs_of_pos (mul_pos (mul_pos hR (mul_pos (div_pos (mul_pos hv' (mul_pos hq hm))
    (mul_pos hR h1)) (mul_pos (div_pos (by positivity) hm) hy0))) (inv_pos.2 hq))]
  field_simp

end IsPosDensity

/-! ### Estimates for the derivative near the origin -/

lemma apply_pair (L : ℝ × ℝ →L[ℝ] ℝ) (x y : ℝ) : L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have : ((x, y) : ℝ × ℝ) = x • ((1, 0) : ℝ × ℝ) + y • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

lemma norm_le_apply_add_apply (B : ℝ × ℝ →L[ℝ] ℝ × ℝ) : ‖B‖ ≤ ‖B (1, 0)‖ + ‖B (0, 1)‖ := by
  refine B.opNorm_le_bound (by positivity) fun u => ?_
  have : B u = u.1 • B (1, 0) + u.2 • B (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  rw [this]
  calc ‖u.1 • B (1, 0) + u.2 • B (0, 1)‖ ≤ ‖u.1‖ * ‖B (1, 0)‖ + ‖u.2‖ * ‖B (0, 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ ‖u‖ * ‖B (1, 0)‖ + ‖u‖ * ‖B (0, 1)‖ := by
        gcongr
        exacts [norm_fst_le u, norm_snd_le u]
    _ = (‖B (1, 0)‖ + ‖B (0, 1)‖) * ‖u‖ := by ring

lemma norm_pair_le {a b E : ℝ} (ha : |a| ≤ E) (hb : |b| ≤ E) : ‖((a, b) : ℝ × ℝ)‖ ≤ E := by
  rw [Prod.norm_def]
  exact max_le ha hb

lemma abs_comb_le {A B C c t₁ t₂ t₃ t₄ d : ℝ} (h₁ : |t₁| ≤ 1) (h₂ : |t₂| ≤ 1) (h₃ : |t₃| ≤ 1)
    (h₄ : |t₄| ≤ d) (hc : 0 ≤ c) :
    |A * t₁ + B * t₂ + C * t₃ + c * t₄| ≤ |A| + |B| + |C| + c * d := by
  have e₁ : |A * t₁| ≤ |A| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h₁
  have e₂ : |B * t₂| ≤ |B| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h₂
  have e₃ : |C * t₃| ≤ |C| := by rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) h₃
  have e₄ : |c * t₄| ≤ c * d := by rw [abs_mul, abs_of_nonneg hc]; gcongr
  calc _ ≤ |A * t₁| + |B * t₂| + |C * t₃| + |c * t₄| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ ≤ _ := by gcongr

lemma abs_trig_mul_le (a b : ℝ) : |cos a * cos b| ≤ 1 ∧ |cos a * sin b| ≤ 1 ∧
    |sin a * cos b| ≤ 1 ∧ |sin a * sin b| ≤ 1 := by
  simp only [abs_mul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    exact (mul_le_mul (by first | exact abs_cos_le_one _ | exact abs_sin_le_one _)
      (by first | exact abs_cos_le_one _ | exact abs_sin_le_one _) (abs_nonneg _)
      zero_le_one).trans (by norm_num)

/-- The error term `E q = |R' - c| + |R a| + |R b / r - c| + c |Θ - θ|`, where `a, b` are the
partial derivatives of `Θ`. -/
def errorTerm (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (c : ℝ) (q : ℝ × ℝ) : ℝ :=
  |radiusDeriv ρ v q.1 - c| +
    |radius ρ v q.1 * fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) q (1, 0)| +
    |radius ρ v q.1 * fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) q (0, 1) / q.1 - c| +
    c * |angle ρ q.1 q.2 - q.2|

lemma norm_fderivTransport_sub_le {v : ℝ≥0} {c : ℝ} (hc : 0 ≤ c) (q : ℝ × ℝ) :
    ‖fderivTransport ρ v q - c • ContinuousLinearMap.id ℝ (ℝ × ℝ)‖ ≤ 2 * errorTerm ρ v c q := by
  set R := radius ρ v q.1
  set R' := radiusDeriv ρ v q.1
  set Θ := angle ρ q.1 q.2
  set L := fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) q
  set a := L (1, 0)
  set b := L (0, 1)
  set θ := q.2
  set r := q.1
  have happ : ∀ x y : ℝ, fderivTransport ρ v q (x, y) =
      (cos Θ * (R' * (cos θ * x + sin θ * y)) + -R * sin Θ *
          ((cos θ * x + sin θ * y) * a + (-sin θ / r * x + cos θ / r * y) * b),
        sin Θ * (R' * (cos θ * x + sin θ * y)) + R * cos Θ *
          ((cos θ * x + sin θ * y) * a + (-sin θ / r * x + cos θ / r * y) * b)) := by
    intro x y
    simp only [fderivTransport, ContinuousLinearMap.comp_apply, fderivPolarCoord_apply,
      fderivPolarMap, ContinuousLinearMap.prod_apply, smul_apply,
      ContinuousLinearMap.coe_fst', smul_eq_mul, fderivPolarCoordSymm_apply, polarMap]
    rw [apply_pair L]
  have hδ₁ : |cos (Θ - θ) - 1| ≤ |Θ - θ| := by
    simpa [cos_zero] using abs_cos_sub_cos_le (Θ - θ) 0
  have hδ₂ : |sin (Θ - θ)| ≤ |Θ - θ| := by
    simpa [sin_zero] using abs_sin_sub_sin_le (Θ - θ) 0
  have hδ₃ : |-sin (Θ - θ)| ≤ |Θ - θ| := by rwa [abs_neg]
  obtain ⟨t₁, t₂, t₃, t₄⟩ := abs_trig_mul_le Θ θ
  have hneg : ∀ {t : ℝ}, |t| ≤ 1 → |-t| ≤ 1 := fun h => by rwa [abs_neg]
  have hRa : |R * a| = |R * a| := rfl
  refine (norm_le_apply_add_apply _).trans ?_
  rw [two_mul]
  simp only [errorTerm]
  gcongr
  · rw [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, happ, Prod.smul_mk, Prod.mk_sub_mk]
    refine norm_pair_le ?_ ?_
    · have : cos Θ * (R' * (cos θ * 1 + sin θ * 0)) + -R * sin Θ *
          ((cos θ * 1 + sin θ * 0) * a + (-sin θ / r * 1 + cos θ / r * 0) * b) - c • (1 : ℝ) =
          (R' - c) * (cos Θ * cos θ) + R * a * (-(sin Θ * cos θ)) +
            (R * b / r - c) * (sin Θ * sin θ) + c * (cos (Θ - θ) - 1) := by
        rw [cos_sub, smul_eq_mul]; ring
      rw [this]
      exact abs_comb_le t₁ (hneg t₃) t₄ hδ₁ hc
    · have : sin Θ * (R' * (cos θ * 1 + sin θ * 0)) + R * cos Θ *
          ((cos θ * 1 + sin θ * 0) * a + (-sin θ / r * 1 + cos θ / r * 0) * b) - c • (0 : ℝ) =
          (R' - c) * (sin Θ * cos θ) + R * a * (cos Θ * cos θ) +
            (R * b / r - c) * (-(cos Θ * sin θ)) + c * sin (Θ - θ) := by
        rw [sin_sub, smul_eq_mul]; ring
      rw [this]
      exact abs_comb_le t₃ t₁ (hneg t₂) hδ₂ hc
  · rw [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, happ, Prod.smul_mk, Prod.mk_sub_mk]
    refine norm_pair_le ?_ ?_
    · have : cos Θ * (R' * (cos θ * 0 + sin θ * 1)) + -R * sin Θ *
          ((cos θ * 0 + sin θ * 1) * a + (-sin θ / r * 0 + cos θ / r * 1) * b) - c • (0 : ℝ) =
          (R' - c) * (cos Θ * sin θ) + R * a * (-(sin Θ * sin θ)) +
            (R * b / r - c) * (-(sin Θ * cos θ)) + c * (-sin (Θ - θ)) := by
        rw [sin_sub, smul_eq_mul]; ring
      rw [this]
      exact abs_comb_le t₂ (hneg t₄) (hneg t₃) hδ₃ hc
    · have : sin Θ * (R' * (cos θ * 0 + sin θ * 1)) + R * cos Θ *
          ((cos θ * 0 + sin θ * 1) * a + (-sin θ / r * 0 + cos θ / r * 1) * b) - c • (1 : ℝ) =
          (R' - c) * (sin Θ * sin θ) + R * a * (cos Θ * sin θ) +
            (R * b / r - c) * (cos Θ * cos θ) + c * (cos (Θ - θ) - 1) := by
        rw [cos_sub, smul_eq_mul]; ring
      rw [this]
      exact abs_comb_le t₄ t₂ t₁ hδ₁ hc

/-- `‖P(A, α) - P(B, β)‖ ≤ |A - B| + |B| |α - β|`. -/
lemma norm_polarCoord_symm_sub_le (A α B β : ℝ) :
    ‖polarCoord.symm (A, α) - polarCoord.symm (B, β)‖ ≤ |A - B| + |B| * |α - β| := by
  simp only [polarCoord_symm_apply, Prod.mk_sub_mk]
  refine norm_pair_le ?_ ?_
  · rw [show A * cos α - B * cos β = (A - B) * cos α + B * (cos α - cos β) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
      (mul_le_mul_of_nonneg_left (abs_cos_sub_cos_le _ _) (abs_nonneg _))
  · rw [show A * sin α - B * sin β = (A - B) * sin α + B * (sin α - sin β) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _))
      (mul_le_mul_of_nonneg_left (abs_sin_sub_sin_le _ _) (abs_nonneg _))

lemma norm_polarCoord_symm_le {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) : ‖polarCoord.symm (r, θ)‖ ≤ r := by
  simp only [polarCoord_symm_apply]
  refine norm_pair_le ?_ ?_
  · rw [abs_mul, abs_of_nonneg hr]; exact mul_le_of_le_one_right hr (abs_cos_le_one _)
  · rw [abs_mul, abs_of_nonneg hr]; exact mul_le_of_le_one_right hr (abs_sin_le_one _)

lemma polarCoord_fst_le (x : ℝ × ℝ) : (polarCoord x).1 ≤ 2 * ‖x‖ := by
  have h1 : |x.1| ≤ ‖x‖ := norm_fst_le x
  have h2 : |x.2| ≤ ‖x‖ := norm_snd_le x
  simp only [polarCoord_apply]
  refine sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [sq_abs x.1, sq_abs x.2, abs_nonneg x.1, abs_nonneg x.2]

/-! ### The origin -/

/-- The derivative of the transport map at the origin is `slope ρ v • id`, where
`slope ρ v = √(v m 0) = √(2π v ρ 0)`. -/
def slope (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) : ℝ := √(v * circleMass ρ 0)

lemma tendsto_polarCoord_fst :
    Tendsto (fun y : ℝ × ℝ => (polarCoord y).1) (𝓝[≠] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun y : ℝ × ℝ => (polarCoord y).1 := by
      simp only [polarCoord_apply]; fun_prop
    simpa [polarCoord_apply] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact polarCoord_fst_pos hy

namespace IsPosDensity

variable (hρ : IsPosDensity ρ) {v : ℝ≥0}
include hρ

/-- `Θ r θ - θ → 0` as `r → 0`, uniformly for `|θ| ≤ 2π`. -/
lemma exists_abs_angle_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ r θ : ℝ, 0 ≤ r → r < δ → |θ| ≤ 2 * π → |angle ρ r θ - θ| ≤ ε := by
  have hm0 : 0 < circleMass ρ 0 := circleMass_pos hρ.1 hρ.2 0
  set ε' := ε * circleMass ρ 0 / (16 * π ^ 2) with hε'_def
  have hε' : 0 < ε' := by positivity
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuous_iff.1 hρ.1 0 ε' hε'
  obtain ⟨δ₂, hδ₂, h₂⟩ :=
    Metric.continuous_iff.1 (continuous_circleMass hρ.1) 0 (circleMass ρ 0 / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun r θ hr hrδ hθ => ?_⟩
  have hcirc : ∀ φ, |polar ρ (r, φ) - ρ 0| ≤ ε' := fun φ => by
    have := h₁ (polarCoord.symm (r, φ)) (by
      rw [dist_zero_right]
      exact (norm_polarCoord_symm_le hr φ).trans_lt (hrδ.trans_le (min_le_left _ _)))
    rw [Real.dist_eq] at this
    exact this.le
  have hm : circleMass ρ 0 / 2 ≤ circleMass ρ r := by
    have := h₂ r (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hr]
      exact hrδ.trans_le (min_le_right _ _))
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).1]
  calc |angle ρ r θ - θ| ≤ 4 * π * |θ| * ε' / circleMass ρ r := abs_angle_sub_le hρ.1 hρ.2 hcirc
    _ ≤ 4 * π * (2 * π) * ε' / (circleMass ρ 0 / 2) := by gcongr
    _ = ε := by rw [hε'_def]; field_simp; ring

lemma tendsto_angle_sub {α : Type*} {l : Filter α} {r θ : α → ℝ} (hr0 : ∀ᶠ x in l, 0 ≤ r x)
    (hr : Tendsto r l (𝓝 0)) (hθ : ∀ᶠ x in l, |θ x| ≤ 2 * π) :
    Tendsto (fun x => angle ρ (r x) (θ x) - θ x) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hρ.exists_abs_angle_sub_le (half_pos hε)
  filter_upwards [hr0, hθ, Metric.tendsto_nhds.1 hr δ hδ] with x h0 h1 h2
  rw [Real.dist_eq, sub_zero] at h2 ⊢
  rw [abs_of_nonneg h0] at h2
  exact (h _ _ h0 h2 h1).trans_lt (half_lt_self hε)

lemma tendsto_radius_zero (hv : v ≠ 0) : Tendsto (radius ρ v) (𝓝[>] 0) (𝓝 0) := by
  have := ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto id (𝓝[>] (0 : ℝ)) (𝓝 0)).mul
    (hρ.tendsto_radius_div hv))
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [id]
  field_simp

lemma hasFDerivAt_transport_zero (hv : v ≠ 0) :
    HasFDerivAt (transport ρ v) (slope ρ v • ContinuousLinearMap.id ℝ (ℝ × ℝ)) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  set c := slope ρ v
  have hc : 0 ≤ c := sqrt_nonneg _
  have hr := tendsto_polarCoord_fst
  have e1 : ∀ᶠ y in 𝓝[≠] (0 : ℝ × ℝ),
      |radius ρ v (polarCoord y).1 / (polarCoord y).1 - c| ≤ ε / 4 := by
    refine (Metric.tendsto_nhds.1 ((hρ.tendsto_radius_div hv).comp hr) (ε / 4)
      (by positivity)).mono fun y hy => ?_
    rw [Real.dist_eq] at hy
    exact hy.le
  have e2 : ∀ᶠ y in 𝓝[≠] (0 : ℝ × ℝ),
      c * |angle ρ (polarCoord y).1 (polarCoord y).2 - (polarCoord y).2| ≤ ε / 4 := by
    have h := (hρ.tendsto_angle_sub (r := fun y => (polarCoord y).1)
      (θ := fun y => (polarCoord y).2) (Eventually.of_forall fun y => polarCoord_fst_nonneg y)
      (hr.mono_right nhdsWithin_le_nhds) (Eventually.of_forall fun y => by
        have := polarCoord_snd_mem y
        rw [abs_le]; constructor <;> linarith [pi_pos, this.1, this.2])).const_mul c
    rw [mul_zero] at h
    refine (Metric.tendsto_nhds.1 h (ε / 4) (by positivity)).mono fun y hy => ?_
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hc] at hy
    exact hy.le
  have := e1.and e2
  rw [eventually_nhdsWithin_iff] at this
  filter_upwards [this] with y hy
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [transport_zero]
  obtain ⟨h1, h2⟩ := hy hy0
  have hr0 : 0 < (polarCoord y).1 := polarCoord_fst_pos hy0
  have hcy : c • y = polarCoord.symm (c * (polarCoord y).1, (polarCoord y).2) := by
    conv_lhs => rw [← polarCoord_symm_polarCoord y]
    simp [mul_assoc]
  rw [zero_add, transport_zero, sub_zero, smul_apply, ContinuousLinearMap.id_apply, hcy]
  calc ‖transport ρ v y - polarCoord.symm (c * (polarCoord y).1, (polarCoord y).2)‖
      ≤ |radius ρ v (polarCoord y).1 - c * (polarCoord y).1| +
        |c * (polarCoord y).1| *
          |angle ρ (polarCoord y).1 (polarCoord y).2 - (polarCoord y).2| :=
        norm_polarCoord_symm_sub_le _ _ _ _
    _ = (polarCoord y).1 * |radius ρ v (polarCoord y).1 / (polarCoord y).1 - c| +
        (polarCoord y).1 *
          (c * |angle ρ (polarCoord y).1 (polarCoord y).2 - (polarCoord y).2|) := by
        rw [show radius ρ v (polarCoord y).1 - c * (polarCoord y).1 =
          (polarCoord y).1 * (radius ρ v (polarCoord y).1 / (polarCoord y).1 - c) by
          field_simp, abs_mul, abs_of_pos hr0, abs_mul, abs_of_nonneg hc, abs_of_pos hr0]
        ring
    _ ≤ (polarCoord y).1 * (ε / 4) + (polarCoord y).1 * (ε / 4) := by gcongr
    _ = ε / 2 * (polarCoord y).1 := by ring
    _ ≤ ε / 2 * (2 * ‖y‖) := by gcongr; exact polarCoord_fst_le y
    _ = ε * ‖y‖ := by ring

variable (hρ1 : ContDiff ℝ 1 ρ)
include hρ1

lemma tendsto_errorTerm (hv : v ≠ 0) :
    Tendsto (fun y => errorTerm ρ v (slope ρ v) (chart y y)) (𝓝[≠] 0) (𝓝 0) := by
  set c := slope ρ v
  have hr := tendsto_polarCoord_fst
  have hr' : Tendsto (fun y : ℝ × ℝ => (chart y y).1) (𝓝[≠] 0) (𝓝[>] 0) := by
    simpa only [chart_fst] using hr
  have hm0 : 0 < circleMass ρ 0 := circleMass_pos hρ.1 hρ.2 0
  have hθ : ∀ y : ℝ × ℝ, |(chart y y).2| ≤ 2 * π := fun y => by
    have := chart_snd_mem y y
    rw [abs_le]; constructor <;> linarith [pi_pos, this.1, this.2]
  -- the first term
  have T1 : Tendsto (fun y : ℝ × ℝ => |radiusDeriv ρ v (chart y y).1 - c|) (𝓝[≠] 0) (𝓝 0) := by
    have := (((hρ.tendsto_radiusDeriv hv).comp hr').sub_const c).abs
    rwa [show √((v : ℝ) * circleMass ρ 0) - c = 0 from sub_self _, abs_zero] at this
  -- the second term: `∂Θ/∂r` is bounded near the origin
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_Icc (a := -π) (b := 2 * π))).exists_bound_of_continuousOn
    (((contDiff_angle hρ1 hρ.2).continuous_fderiv one_ne_zero).continuousOn
      (s := Icc (0 : ℝ) 1 ×ˢ Icc (-π) (2 * π)))
  have T2 : Tendsto (fun y : ℝ × ℝ => |radius ρ v (chart y y).1 *
      fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) (chart y y) (1, 0)|) (𝓝[≠] 0) (𝓝 0) := by
    have hR := ((hρ.tendsto_radius_zero hv).comp hr').const_mul C
    rw [mul_zero] at hR
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hR
    have h1 : ∀ᶠ y in 𝓝[≠] (0 : ℝ × ℝ), (chart y y).1 < 1 :=
      (hr'.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds one_pos)
    filter_upwards [h1] with y hy
    have hmem : chart y y ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-π) (2 * π) :=
      ⟨⟨by rw [chart_fst]; exact polarCoord_fst_nonneg y, hy.le⟩, chart_snd_mem y y⟩
    simp only [Function.comp_apply]
    rw [abs_mul, abs_of_nonneg (radius_nonneg _), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (radius_nonneg _)
    set L := fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) (chart y y)
    have hn : ‖((1, 0) : ℝ × ℝ)‖ ≤ 1 := by rw [Prod.norm_def]; simp
    calc |L (1, 0)| = ‖L (1, 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖L‖ * ‖((1, 0) : ℝ × ℝ)‖ := L.le_opNorm _
      _ ≤ C * 1 := mul_le_mul (hC _ hmem) hn (norm_nonneg _) ((norm_nonneg _).trans (hC _ hmem))
      _ = C := mul_one C
  -- the third term: `R ∂Θ/∂θ / r = (R / r) 2π ρ / m → c`
  have T3 : Tendsto (fun y : ℝ × ℝ => |radius ρ v (chart y y).1 *
      fderiv ℝ (fun p : ℝ × ℝ => angle ρ p.1 p.2) (chart y y) (0, 1) / (chart y y).1 - c|)
      (𝓝[≠] 0) (𝓝 0) := by
    have hρy : Tendsto ρ (𝓝[≠] (0 : ℝ × ℝ)) (𝓝 (ρ 0)) :=
      (hρ.1.tendsto 0).mono_left nhdsWithin_le_nhds
    have hm : Tendsto (fun y : ℝ × ℝ => circleMass ρ (chart y y).1) (𝓝[≠] 0)
        (𝓝 (circleMass ρ 0)) :=
      ((continuous_circleMass hρ.1).tendsto 0).comp (hr'.mono_right nhdsWithin_le_nhds)
    have hlim := ((hρ.tendsto_radius_div hv).comp hr').mul
      ((tendsto_const_nhds (x := 2 * π)).div hm hm0.ne' |>.mul hρy)
    have hval : √((v : ℝ) * (2 * π * ρ 0)) * (2 * π / (2 * π * ρ 0) * ρ 0) = c := by
      rw [show c = √((v : ℝ) * (2 * π * ρ 0)) by simp only [c, slope, circleMass_zero]]
      have := (hρ.2 0).ne'
      field_simp
    rw [circleMass_zero, hval] at hlim
    have := (hlim.sub_const c).abs
    rw [sub_self, abs_zero] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y (hy : y ≠ 0)
    have hq := chart_self_fst_pos hy
    have hpolar : polar ρ (chart y y) = ρ y := by
      change ρ (polarCoord.symm (chart y y)) = ρ y
      rw [polarCoord_symm_chart]
    simp only [Function.comp_apply]
    rw [hρ.fderiv_angle_snd hρ1, hpolar]
    congr 2
    simp only [Pi.div_apply]
    field_simp
  -- the fourth term
  have T4 : Tendsto (fun y : ℝ × ℝ => c * |angle ρ (chart y y).1 (chart y y).2 - (chart y y).2|)
      (𝓝[≠] 0) (𝓝 0) := by
    have := (hρ.tendsto_angle_sub
      (Eventually.of_forall fun y => by rw [chart_fst]; exact polarCoord_fst_nonneg y)
      (hr'.mono_right nhdsWithin_le_nhds) (Eventually.of_forall hθ)).abs.const_mul c
    simpa using this
  simpa [errorTerm] using ((T1.add T2).add T3).add T4

lemma tendsto_fderivTransport (hv : v ≠ 0) :
    Tendsto (fun y => fderivTransport ρ v (chart y y)) (𝓝[≠] 0)
      (𝓝 (slope ρ v • ContinuousLinearMap.id ℝ (ℝ × ℝ))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun y => norm_fderivTransport_sub_le (sqrt_nonneg _) _) ?_
  have := (hρ.tendsto_errorTerm hρ1 hv).const_mul 2
  rwa [mul_zero] at this

/-! ### Main results -/

lemma fderiv_transport_of_ne (hv : v ≠ 0) {y : ℝ × ℝ} (hy : y ≠ 0) :
    fderiv ℝ (transport ρ v) y = fderivTransport ρ v (chart y y) :=
  (hρ.hasFDerivAt_transport hρ1 hv hy).fderiv

/-- The transport map is `C¹`. -/
theorem contDiff_transport (hv : v ≠ 0) : ContDiff ℝ 1 (transport ρ v) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun y => ?_, continuous_iff_continuousAt.2 fun y => ?_⟩
  · rcases eq_or_ne y 0 with rfl | hy
    · exact (hρ.hasFDerivAt_transport_zero hv).differentiableAt
    · exact (hρ.contDiffAt_transport hρ1 hv hy).differentiableAt one_ne_zero
  · rcases eq_or_ne y 0 with rfl | hy
    · refine continuousWithinAt_compl_self.1 ?_
      rw [ContinuousWithinAt, (hρ.hasFDerivAt_transport_zero hv).fderiv]
      refine (hρ.tendsto_fderivTransport hρ1 hv).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z (hz : z ≠ 0)
      exact (hρ.fderiv_transport_of_ne hρ1 hv hz).symm
    · exact (hρ.contDiffAt_transport hρ1 hv hy).continuousAt_fderiv one_ne_zero

/-- **The density identity**: `ρ x = G (T x) |det DT x|` for the isotropic Gaussian `G` of
variance `v`. -/
theorem eq_gauss_mul_abs_det (hv : v ≠ 0) (x : ℝ × ℝ) :
    ρ x = gauss v (transport ρ v x) * |(fderiv ℝ (transport ρ v) x).det| := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hv' : (0 : ℝ) < v := by positivity
    have hg : gauss v (0 : ℝ × ℝ) = (2 * π * v)⁻¹ := by
      have h := gauss_polarCoord_symm hv 0 0
      simp only [polarCoord_symm_apply, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, neg_zero, zero_div, exp_zero, mul_one] at h
      exact h
    have hdet : (slope ρ v • ContinuousLinearMap.id ℝ (ℝ × ℝ)).det = slope ρ v ^ 2 := by
      rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
        ContinuousLinearMap.coe_id, LinearMap.det_id, Module.finrank_prod, Module.finrank_self,
        mul_one]
    rw [(hρ.hasFDerivAt_transport_zero hv).fderiv, transport_zero, hg, hdet, slope,
      sq_sqrt (mul_pos hv' (circleMass_pos hρ.1 hρ.2 0)).le, circleMass_zero,
      abs_of_pos (by have := hρ.2 0; positivity)]
    field_simp
  · rw [hρ.fderiv_transport_of_ne hρ1 hv hx]
    exact hρ.eq_gauss_mul_abs_det_of_ne hρ1 hv hx

end IsPosDensity

/-- **Transport of a positive `C¹` density on the plane to a Gaussian.** For a positive `C¹`
probability density `ρ` on `ℝ × ℝ` and `v > 0` there is a `C¹` bijection `T` of the plane with
`ρ x = G (T x) |det DT x|`, where `G` is the product of two centred Gaussian densities of
variance `v`. -/
theorem exists_transport_gaussian {ρ : ℝ × ℝ → ℝ} (hρ1 : ContDiff ℝ 1 ρ) (hpos : ∀ x, 0 < ρ x)
    (hint : ∫ x, ρ x = 1) {v : ℝ≥0} (hv : v ≠ 0) :
    ∃ T : ℝ × ℝ → ℝ × ℝ, ContDiff ℝ 1 T ∧ Function.Bijective T ∧
      ∀ x, ρ x = gaussianPDFReal 0 v (T x).1 * gaussianPDFReal 0 v (T x).2 *
        |(fderiv ℝ T x).det| := by
  have hρ : IsPosDensity ρ := ⟨hρ1.continuous, hpos, hint⟩
  exact ⟨transport ρ v, hρ.contDiff_transport hρ1 hv, hρ.bijective_transport hv,
    hρ.eq_gauss_mul_abs_det hρ1 hv⟩

end PolarTransport
