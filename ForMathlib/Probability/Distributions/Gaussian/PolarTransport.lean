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
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Transport of a positive density on the plane to a Gaussian

For a positive `Cⁿ` probability density `ρ` on `ℝ × ℝ`, `n ≥ 1`, and `v > 0`, the map
`PolarTransport.transport ρ v` is a `Cⁿ` bijection `T` of the plane with
`ρ x = G (T x) |det DT x|`, where `G` is the centred isotropic Gaussian density of variance `v`
in each coordinate. It is a Knothe–Rosenblatt map in polar coordinates: in `(r, θ)`,

* the radius is sent to `R r = √(-2 v log (1 - M r))`, where `M r` is the `ρ`-mass of the disc of
  radius `r`, so that discs go to discs of the same Gaussian mass `1 - exp (-R² / 2v)`;
* on each circle the angle is sent to `Θ r θ = 2π (∫₀^θ ρ(r, φ) dφ) / m r + c r`, where `m r` is
  the integral of `ρ` over the circle, so that arcs go to arcs of the same conditional mass; the
  rotation `c r` gives the displacement `Θ r θ - θ` mean zero on each circle.

The fibres are circles, which are compact, so `M`, `m` and `Θ` inherit the regularity of `ρ`;
a Cartesian Knothe–Rosenblatt map can fail to be `C¹` because a marginal of a smooth positive
density can be discontinuous. At the origin, polar coordinates are singular. There `T` is
handled in Cartesian form, `T y = a y • rot (D y) y` (`transport_eq_smul_rot`), where
`a y = R |y| / |y|` and the displacement `D y` are built from integrals, over compact sets, of
expressions smooth in `y`:

* `a y = √(2 v K(y) L(|y|² K(y)))`, with `K(y) = ∫₀¹ t m(t |y|) dt = M |y| / |y|²` and
  `L u = -log (1 - u) / u`, analytic on `u < 1`;
* `D y = (1/2π) ∫_{-π}^{π} ∫_s^0 (2π ρ(rot u y) / m |y| - 1) du ds`, the primitive with mean zero
  of the angular density on the circle through `y` (`angle_sub_eq_angleDisp`).

The rotation `c r` is what makes `D` smooth: measured from the fixed angle `0`, the displacement
has a part of order `r` that is constant on each circle, and `T` is then `C¹` but not `C²` at the
origin whenever `∂ρ/∂p (0) ≠ 0`. The density identity at the origin follows from the one elsewhere
by continuity.

## Main definitions

* `PolarTransport.circleMass`, `PolarTransport.discMass`: `m r` and `M r`.
* `PolarTransport.radius`, `PolarTransport.angle`: `R` and `Θ`.
* `PolarTransport.transport`: the map `T`.
* `PolarTransport.radiusQuot`, `PolarTransport.angleDisp`: `a` and `D`.

## Main results

* `PolarTransport.IsPosDensity.transport_eq_smul_rot`: the Cartesian form of `T`;
* `PolarTransport.IsPosDensity.contDiff_transport`: `T` is as smooth as `ρ`;
* `PolarTransport.IsPosDensity.bijective_transport`;
* `PolarTransport.IsPosDensity.eq_gauss_mul_abs_det`: `ρ x = G (T x) |det DT x|`;
* `PolarTransport.exists_transport_gaussian`: the three together.
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

end IsPosDensity

/-! ### The angular map -/

/-- `Θ₀ r θ = 2π (∫₀^θ ρ(r cos φ, r sin φ) dφ) / m r`: the arc from angle `0` to `Θ₀ r θ` has the
conditional mass on the circle of radius `r` of the arc from `0` to `θ`. -/
def angle₀ (ρ : ℝ × ℝ → ℝ) (r θ : ℝ) : ℝ :=
  2 * π / circleMass ρ r * ∫ φ in (0 : ℝ)..θ, polar ρ (r, φ)

/-- `c r = -(1/2π) ∫_{-π}^{π} (Θ₀ r s - s) ds`, the rotation that gives the displacement
`Θ₀ r θ + c r - θ` mean zero on each circle. -/
def angleShift (ρ : ℝ × ℝ → ℝ) (r : ℝ) : ℝ :=
  -((2 * π)⁻¹ * ∫ s in (-π)..π, (angle₀ ρ r s - s))

/-- `Θ r θ = Θ₀ r θ + c r`: arcs go to arcs of the same conditional mass, and the displacement
`Θ r θ - θ` has mean zero on each circle. Measured from the fixed angle `0` instead, the
displacement has a part of order `r` that is constant on each circle, and the transport map is
then `C¹` but not `C²` at the origin; with mean zero it is as smooth as `ρ`
(`angle_sub_eq_angleDisp`). -/
def angle (ρ : ℝ × ℝ → ℝ) (r θ : ℝ) : ℝ := angle₀ ρ r θ + angleShift ρ r

lemma hasDerivAt_angle₀ (hρ : Continuous ρ) (r θ : ℝ) :
    HasDerivAt (angle₀ ρ r) (2 * π / circleMass ρ r * polar ρ (r, θ)) θ :=
  (((continuous_polar hρ).comp (Continuous.prodMk_right r)).integral_hasStrictDerivAt 0 θ
    |>.hasDerivAt).const_mul _

lemma hasDerivAt_angle (hρ : Continuous ρ) (r θ : ℝ) :
    HasDerivAt (angle ρ r) (2 * π / circleMass ρ r * polar ρ (r, θ)) θ :=
  (hasDerivAt_angle₀ hρ r θ).add_const _

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
  rw [angle, angle, angle₀, angle₀, ← intervalIntegral.integral_add_adjacent_intervals (b := θ)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), h,
    show (∫ φ in (-π)..π, polar ρ (r, φ)) = circleMass ρ r from rfl]
  field_simp
  ring

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

lemma contDiff_angle₀ {n : ℕ∞} (hρ : ContDiff ℝ n ρ) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ n fun p : ℝ × ℝ => angle₀ ρ p.1 p.2 := by
  have hc : Continuous ρ := hρ.continuous
  have hI : ContDiff ℝ n fun p : ℝ × ℝ => ∫ t in (0 : ℝ)..1, polar ρ (p.1, p.2 * t) :=
    ((contDiff_polar hρ).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2 * q.2))
      (by fun_prop)).parametric_intervalIntegral
  have hm : ContDiff ℝ n fun p : ℝ × ℝ => circleMass ρ p.1 :=
    (contDiff_circleMass hρ).comp contDiff_fst
  have : (fun p : ℝ × ℝ => angle₀ ρ p.1 p.2) = fun p =>
      2 * π / circleMass ρ p.1 * (p.2 * ∫ t in (0 : ℝ)..1, polar ρ (p.1, p.2 * t)) := by
    ext p
    rw [angle₀, integral_zero_eq_mul]
  rw [this]
  exact (contDiff_const.div hm fun p => (circleMass_pos hc hpos p.1).ne').mul
    (contDiff_snd.mul hI)

lemma contDiff_angleShift {n : ℕ∞} (hρ : ContDiff ℝ n ρ) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ n (angleShift ρ) :=
  (contDiff_const.mul ((contDiff_angle₀ hρ hpos).sub contDiff_snd).parametric_intervalIntegral).neg

lemma contDiff_angle {n : ℕ∞} (hρ : ContDiff ℝ n ρ) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ n fun p : ℝ × ℝ => angle ρ p.1 p.2 :=
  (contDiff_angle₀ hρ hpos).add ((contDiff_angleShift hρ hpos).comp contDiff_fst)
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
  obtain ⟨N, hN⟩ := exists_nat_ge (|(polarCoord z).2 - angle ρ r 0| / (2 * π))
  rw [div_le_iff₀ (by positivity)] at hN
  have hm : angle ρ r (-N * (2 * π)) = angle ρ r 0 - N * (2 * π) := by
    have := angle_add_int_mul hρ.1 hρ.2 r 0 (-N)
    push_cast at this
    rw [zero_add] at this
    rw [this]; ring
  have hp : angle ρ r (N * (2 * π)) = angle ρ r 0 + N * (2 * π) := by
    have := angle_add_int_mul hρ.1 hρ.2 r 0 N
    push_cast at this
    rwa [zero_add] at this
  have hN0 : (0 : ℝ) ≤ N * (2 * π) := by positivity
  obtain ⟨θ, -, hθ⟩ := intermediate_value_Icc (by linarith : -N * (2 * π) ≤ N * (2 * π))
    (continuous_angle_right hρ.1 r).continuousOn
    (show (polarCoord z).2 ∈ Icc (angle ρ r (-N * (2 * π))) (angle ρ r (N * (2 * π))) by
      rw [hm, hp]; constructor <;> linarith [(abs_le.1 hN).1, (abs_le.1 hN).2])
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

/-! ### The transport map in Cartesian form -/

/-- The rotation of the plane by the angle `α`. -/
def rot (α : ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (cos α * y.1 - sin α * y.2, sin α * y.1 + cos α * y.2)

lemma rot_polarCoord_symm (α r θ : ℝ) :
    rot α (polarCoord.symm (r, θ)) = polarCoord.symm (r, θ + α) := by
  simp only [rot, polarCoord_symm_apply, cos_add, sin_add, Prod.mk.injEq]
  constructor <;> ring

lemma smul_polarCoord_symm (t r θ : ℝ) :
    t • polarCoord.symm (r, θ) = polarCoord.symm (t * r, θ) := by
  simp only [polarCoord_symm_apply, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

lemma sq_add_sq_polarCoord_symm (r θ : ℝ) :
    (polarCoord.symm (r, θ)).1 ^ 2 + (polarCoord.symm (r, θ)).2 ^ 2 = r ^ 2 := by
  simp only [polarCoord_symm_apply]
  linear_combination r ^ 2 * cos_sq_add_sin_sq θ

lemma contDiff_rot {n : WithTop ℕ∞} : ContDiff ℝ n fun p : ℝ × (ℝ × ℝ) => rot p.1 p.2 := by
  unfold rot; fun_prop

/-- Every point is `polarCoord.symm (r, θ)` with `r ≥ 0`. -/
lemma exists_polarCoord_symm_eq (x : ℝ × ℝ) : ∃ r θ, 0 ≤ r ∧ polarCoord.symm (r, θ) = x :=
  ⟨_, _, polarCoord_fst_nonneg x, polarCoord_symm_polarCoord x⟩

/-- `m` in Cartesian form: `circleMassC ρ y = ∫_{-π}^{π} ρ (rot u y) du = m |y|`. -/
def circleMassC (ρ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ := ∫ u in (-π)..π, ρ (rot u y)

lemma circleMassC_polarCoord_symm (r θ : ℝ) :
    circleMassC ρ (polarCoord.symm (r, θ)) = circleMass ρ r := by
  have hper : Function.Periodic (fun φ => polar ρ (r, φ)) (2 * π) := fun φ =>
    polar_add_two_pi r φ
  have h1 : circleMassC ρ (polarCoord.symm (r, θ)) = ∫ u in (-π)..π, polar ρ (r, θ + u) := by
    simp only [circleMassC, rot_polarCoord_symm]; rfl
  rw [h1, intervalIntegral.integral_comp_add_left (fun φ => polar ρ (r, φ)) θ,
    show θ + π = θ + -π + 2 * π by ring, hper.intervalIntegral_add_eq (θ + -π) (-π),
    show -π + 2 * π = π by ring]
  rfl

lemma circleMassC_pos (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (y : ℝ × ℝ) :
    0 < circleMassC ρ y := by
  obtain ⟨r, θ, -, rfl⟩ := exists_polarCoord_symm_eq y
  rw [circleMassC_polarCoord_symm]
  exact circleMass_pos hρ hpos r

lemma contDiff_circleMassC {n : ℕ∞} (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (circleMassC ρ) := by
  have : ContDiff ℝ n fun q : (ℝ × ℝ) × ℝ => ρ (rot q.2 q.1) :=
    hρ.comp (contDiff_rot.comp (contDiff_snd.prodMk contDiff_fst))
  exact this.parametric_intervalIntegral

/-- `K` in Cartesian form: `discMassQuotC ρ y = ∫₀¹ t m(t |y|) dt = K |y|`. -/
def discMassQuotC (ρ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ := ∫ t in (0 : ℝ)..1, t * circleMassC ρ (t • y)

lemma discMassQuotC_polarCoord_symm (r θ : ℝ) :
    discMassQuotC ρ (polarCoord.symm (r, θ)) = discMassQuot ρ r := by
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [smul_polarCoord_symm, circleMassC_polarCoord_symm, mul_comm t r]

lemma contDiff_discMassQuotC {n : ℕ∞} (hρ : ContDiff ℝ n ρ) : ContDiff ℝ n (discMassQuotC ρ) := by
  have : ContDiff ℝ n fun q : (ℝ × ℝ) × ℝ => q.2 * circleMassC ρ (q.2 • q.1) :=
    contDiff_snd.mul ((contDiff_circleMassC hρ).comp (contDiff_snd.smul contDiff_fst))
  exact this.parametric_intervalIntegral

lemma discMassQuot_pos (hρ : Continuous ρ) (hpos : ∀ x, 0 < ρ x) (r : ℝ) :
    0 < discMassQuot ρ r :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_id.mul ((continuous_circleMass hρ).comp
      (continuous_const.mul continuous_id))).intervalIntegrable _ _)
    (fun _ ht => mul_pos ht.1 (circleMass_pos hρ hpos _)) one_pos

/-- `L u = -log (1 - u) / u`, extended by `L 0 = 1`; it is analytic on `u < 1`. -/
def logQuot (u : ℝ) : ℝ := -dslope (fun u => log (1 - u)) 0 u

lemma logQuot_of_ne {u : ℝ} (hu : u ≠ 0) : logQuot u = -log (1 - u) / u := by
  rw [logQuot, dslope_of_ne _ hu, slope_def_field]
  simp [neg_div]

lemma logQuot_zero : logQuot 0 = 1 := by
  have h : HasDerivAt (fun u : ℝ => log (1 - u)) (-1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_sub 1).log (by norm_num)
  rw [logQuot, dslope_same, h.deriv, neg_neg]

lemma logQuot_pos {u : ℝ} (hu : u < 1) : 0 < logQuot u := by
  rcases lt_trichotomy u 0 with h | rfl | h
  · rw [logQuot_of_ne h.ne]
    exact div_pos_of_neg_of_neg (neg_neg_of_pos (log_pos (by linarith))) h
  · rw [logQuot_zero]; exact one_pos
  · rw [logQuot_of_ne h.ne']
    exact div_pos (neg_pos.2 (log_neg (by linarith) (by linarith))) h

lemma contDiffOn_logQuot {n : WithTop ℕ∞} : ContDiffOn ℝ n logQuot (Iio 1) := fun u hu =>
  (((analyticAt_const.sub analyticAt_id).log
    (by simp only [mem_Iio] at hu; simp only [Pi.sub_apply, id]; linarith)).dslope
    0).neg.contDiffAt.contDiffWithinAt

/-- `a y = R |y| / |y|` in Cartesian form: `a y = √(2 v K L(|y|² K))` with `K = discMassQuotC ρ y`
(`radius_eq_mul_radiusQuot`). -/
def radiusQuot (ρ : ℝ × ℝ → ℝ) (v : ℝ≥0) (y : ℝ × ℝ) : ℝ :=
  √(2 * v * discMassQuotC ρ y * logQuot ((y.1 ^ 2 + y.2 ^ 2) * discMassQuotC ρ y))

/-- The angular displacement `Θ r θ - θ` in Cartesian form
(`angle_sub_eq_angleDisp`): `D y = (1/2π) ∫_{-π}^{π} ∫_s^0 (2π ρ(rot u y) / m - 1) du ds`. -/
def angleDisp (ρ : ℝ × ℝ → ℝ) (y : ℝ × ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ s in (-π)..π, ∫ u in s..0, (2 * π * ρ (rot u y) / circleMassC ρ y - 1)

lemma contDiff_angleDisp {n : ℕ∞} (hρ : ContDiff ℝ n ρ) (hpos : ∀ x, 0 < ρ x) :
    ContDiff ℝ n (angleDisp ρ) := by
  set h : (ℝ × ℝ) × ℝ → ℝ := fun q => 2 * π * ρ (rot q.2 q.1) / circleMassC ρ q.1 - 1 with hh_def
  have hh : ContDiff ℝ n h :=
    ((contDiff_const.mul (hρ.comp (contDiff_rot.comp (contDiff_snd.prodMk contDiff_fst)))).div
      ((contDiff_circleMassC hρ).comp contDiff_fst)
      fun q => (circleMassC_pos hρ.continuous hpos q.1).ne').sub contDiff_const
  have hin : ContDiff ℝ n fun q : (ℝ × ℝ) × ℝ => -(q.2 * ∫ t in (0 : ℝ)..1, h (q.1, q.2 * t)) :=
    (contDiff_snd.mul (hh.comp (f := fun p : ((ℝ × ℝ) × ℝ) × ℝ => (p.1.1, p.1.2 * p.2))
      (by fun_prop)).parametric_intervalIntegral).neg
  have : angleDisp ρ = fun y =>
      (2 * π)⁻¹ * ∫ s in (-π)..π, -(s * ∫ t in (0 : ℝ)..1, h (y, s * t)) := by
    funext y
    rw [angleDisp]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [intervalIntegral.integral_symm, integral_zero_eq_mul]
  rw [this]
  exact contDiff_const.mul hin.parametric_intervalIntegral

namespace IsPosDensity

variable (hρ : IsPosDensity ρ) {v : ℝ≥0}
include hρ

lemma radius_eq_mul_radiusQuot {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    radius ρ v r = r * radiusQuot ρ v (polarCoord.symm (r, θ)) := by
  rcases hr.eq_or_lt with rfl | hr
  · simp [radius_zero]
  have hM := discMass_pos hρ.1 hρ.2 hr
  have hMK := discMass_eq_sq_mul (ρ := ρ) r
  have hK := discMassQuot_pos hρ.1 hρ.2 r
  rw [radiusQuot, sq_add_sq_polarCoord_symm, discMassQuotC_polarCoord_symm, ← hMK,
    logQuot_of_ne hM.ne', radius, show ∀ X, r * √X = √(r ^ 2 * X) from fun X => by
      rw [sqrt_mul (sq_nonneg r), sqrt_sq hr.le]]
  congr 1
  rw [hMK]
  field_simp

lemma sq_mul_discMassQuotC_lt_one (y : ℝ × ℝ) :
    (y.1 ^ 2 + y.2 ^ 2) * discMassQuotC ρ y < 1 := by
  obtain ⟨r, θ, hr, rfl⟩ := exists_polarCoord_symm_eq y
  rw [sq_add_sq_polarCoord_symm, discMassQuotC_polarCoord_symm, ← discMass_eq_sq_mul]
  exact discMass_lt_one hρ.1 hρ.2 hρ.3 hr

lemma contDiff_radiusQuot {n : ℕ∞} (hv : v ≠ 0) (hρn : ContDiff ℝ n ρ) :
    ContDiff ℝ n (radiusQuot ρ v) := by
  have hv' : (0 : ℝ) < v := by positivity
  have hK := contDiff_discMassQuotC hρn
  have hu : ContDiff ℝ n fun y : ℝ × ℝ => (y.1 ^ 2 + y.2 ^ 2) * discMassQuotC ρ y :=
    (by fun_prop : ContDiff ℝ n fun y : ℝ × ℝ => y.1 ^ 2 + y.2 ^ 2).mul hK
  have hL : ContDiff ℝ n fun y : ℝ × ℝ => logQuot ((y.1 ^ 2 + y.2 ^ 2) * discMassQuotC ρ y) :=
    contDiffOn_logQuot.comp_contDiff hu fun y => hρ.sq_mul_discMassQuotC_lt_one y
  refine ((contDiff_const.mul hK).mul hL).sqrt fun y => ?_
  have hK0 : 0 < discMassQuotC ρ y := by
    obtain ⟨r, θ, -, rfl⟩ := exists_polarCoord_symm_eq y
    rw [discMassQuotC_polarCoord_symm]
    exact discMassQuot_pos hρ.1 hρ.2 r
  exact (mul_pos (mul_pos (by positivity) hK0)
    (logQuot_pos (hρ.sq_mul_discMassQuotC_lt_one y))).ne'

/-- The displacement `Θ r θ - θ` is `D` at `(r cos θ, r sin θ)`. -/
lemma angle_sub_eq_angleDisp (r θ : ℝ) :
    angle ρ r θ - θ = angleDisp ρ (polarCoord.symm (r, θ)) := by
  have hm := (circleMass_pos hρ.1 hρ.2 r).ne'
  set g : ℝ → ℝ := fun φ => 2 * π * polar ρ (r, φ) / circleMass ρ r - 1 with hg
  have hpc : Continuous fun φ => polar ρ (r, φ) :=
    (continuous_polar hρ.1).comp (Continuous.prodMk_right r)
  have hgc : Continuous g := ((continuous_const.mul hpc).div_const _).sub continuous_const
  have hgi : ∀ a b, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable a b
  have hper : Function.Periodic g (2 * π) := fun φ => by simp only [hg, polar_add_two_pi]
  have hint : ∀ a b : ℝ, ∫ φ in a..b, g φ =
      2 * π / circleMass ρ r * (∫ φ in a..b, polar ρ (r, φ)) - (b - a) := by
    intro a b
    have hc : Continuous fun φ => 2 * π * polar ρ (r, φ) / circleMass ρ r :=
      (continuous_const.mul hpc).div_const _
    show ∫ φ in a..b, (2 * π * polar ρ (r, φ) / circleMass ρ r - 1) = _
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable a b) intervalIntegrable_const,
      intervalIntegral.integral_div,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  set G : ℝ → ℝ := fun s => ∫ φ in (0 : ℝ)..s, g φ with hG_def
  have hG : ∀ s, angle₀ ρ r s - s = G s := fun s => by
    show angle₀ ρ r s - s = ∫ φ in (0 : ℝ)..s, g φ
    rw [hint, angle₀, sub_zero]
  have hGc : Continuous G := intervalIntegral.continuous_primitive hgi 0
  have hmean : ∫ φ in (-π)..π, g φ = 0 := by
    rw [hint, show (∫ φ in (-π)..π, polar ρ (r, φ)) = circleMass ρ r from rfl]
    field_simp
    ring
  have hGper : Function.Periodic G (2 * π) := fun s => by
    simp only [hG_def]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hgi 0 s) (hgi s (s + 2 * π)),
      hper.intervalIntegral_add_eq s (-π), show -π + 2 * π = π by ring, hmean, add_zero]
  -- the right side
  have hin : ∀ s, ∫ u in s..0, (2 * π * ρ (rot u (polarCoord.symm (r, θ))) /
      circleMassC ρ (polarCoord.symm (r, θ)) - 1) = G θ - G (θ + s) := by
    intro s
    have : ∀ u, 2 * π * ρ (rot u (polarCoord.symm (r, θ))) /
        circleMassC ρ (polarCoord.symm (r, θ)) - 1 = g (θ + u) := fun u => by
      rw [rot_polarCoord_symm, circleMassC_polarCoord_symm]; rfl
    simp only [this]
    rw [intervalIntegral.integral_comp_add_left g θ, add_zero, hG_def,
      intervalIntegral.integral_interval_sub_left (hgi 0 θ) (hgi 0 (θ + s))]
  have hshift : ∫ s in (-π)..π, G (θ + s) = ∫ s in (-π)..π, G s := by
    rw [intervalIntegral.integral_comp_add_left G θ, show θ + π = θ + -π + 2 * π by ring,
      hGper.intervalIntegral_add_eq (θ + -π) (-π), show -π + 2 * π = π by ring]
  rw [angleDisp]
  simp only [hin]
  have hGi : IntervalIntegrable (fun s => G (θ + s)) volume (-π) π :=
    (hGc.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub intervalIntegrable_const hGi, hshift,
    intervalIntegral.integral_const, smul_eq_mul, angle, angleShift, add_sub_right_comm, hG θ]
  simp only [hG]
  field_simp
  ring

/-- **The transport map in Cartesian form**: `T y = a y • rot (D y) y`. -/
lemma transport_eq_smul_rot (x : ℝ × ℝ) :
    transport ρ v x = radiusQuot ρ v x • rot (angleDisp ρ x) x := by
  obtain ⟨r, θ, hr, rfl⟩ := exists_polarCoord_symm_eq x
  rw [hρ.transport_polarCoord_symm hr, rot_polarCoord_symm, smul_polarCoord_symm,
    ← hρ.angle_sub_eq_angleDisp, add_sub_cancel, mul_comm, ← hρ.radius_eq_mul_radiusQuot hr]

/-- The transport map is as smooth as `ρ`. -/
theorem contDiff_transport {n : ℕ∞} (hv : v ≠ 0) (hρn : ContDiff ℝ n ρ) :
    ContDiff ℝ n (transport ρ v) := by
  rw [show transport ρ v = fun x => radiusQuot ρ v x • rot (angleDisp ρ x) x from
    funext hρ.transport_eq_smul_rot]
  exact (hρ.contDiff_radiusQuot hv hρn).smul
    (contDiff_rot.comp ((contDiff_angleDisp hρn hρ.2).prodMk contDiff_id))

end IsPosDensity

/-! ### Main results -/

lemma continuous_gauss (v : ℝ≥0) : Continuous (gauss v) := by
  unfold gauss gaussianPDFReal
  fun_prop

namespace IsPosDensity

variable (hρ : IsPosDensity ρ) (hρ1 : ContDiff ℝ 1 ρ) {v : ℝ≥0}
include hρ hρ1

lemma fderiv_transport_of_ne (hv : v ≠ 0) {y : ℝ × ℝ} (hy : y ≠ 0) :
    fderiv ℝ (transport ρ v) y = fderivTransport ρ v (chart y y) :=
  (hρ.hasFDerivAt_transport hρ1 hv hy).fderiv

/-- **The density identity**: `ρ x = G (T x) |det DT x|` for the isotropic Gaussian `G` of
variance `v`. At the origin it follows from the identity elsewhere by continuity. -/
theorem eq_gauss_mul_abs_det (hv : v ≠ 0) (x : ℝ × ℝ) :
    ρ x = gauss v (transport ρ v x) * |(fderiv ℝ (transport ρ v) x).det| := by
  have hT := hρ.contDiff_transport hv hρ1
  have hc : Continuous fun x => gauss v (transport ρ v x) * |(fderiv ℝ (transport ρ v) x).det| :=
    ((continuous_gauss v).comp hT.continuous).mul
      (ContinuousLinearMap.continuous_det.comp (hT.continuous_fderiv one_ne_zero)).abs
  refine congrFun (Continuous.ext_on (dense_compl_singleton 0) hρ.1 hc fun y hy => ?_) x
  rw [hρ.fderiv_transport_of_ne hρ1 hv hy]
  exact hρ.eq_gauss_mul_abs_det_of_ne hρ1 hv hy

end IsPosDensity

/-- **Transport of a positive density on the plane to a Gaussian.** For a positive `Cⁿ`
probability density `ρ` on `ℝ × ℝ`, `n ≥ 1`, and `v > 0` there is a `Cⁿ` bijection `T` of the
plane with `ρ x = G (T x) |det DT x|`, where `G` is the product of two centred Gaussian densities
of variance `v`. -/
theorem exists_transport_gaussian {ρ : ℝ × ℝ → ℝ} {n : ℕ∞} (hρn : ContDiff ℝ n ρ) (hn : 1 ≤ n)
    (hpos : ∀ x, 0 < ρ x) (hint : ∫ x, ρ x = 1) {v : ℝ≥0} (hv : v ≠ 0) :
    ∃ T : ℝ × ℝ → ℝ × ℝ, ContDiff ℝ n T ∧ Function.Bijective T ∧
      ∀ x, ρ x = gaussianPDFReal 0 v (T x).1 * gaussianPDFReal 0 v (T x).2 *
        |(fderiv ℝ T x).det| := by
  have hρ1 : ContDiff ℝ 1 ρ := hρn.of_le (by exact_mod_cast hn)
  have hρ : IsPosDensity ρ := ⟨hρ1.continuous, hpos, hint⟩
  exact ⟨transport ρ v, hρ.contDiff_transport hv hρn, hρ.bijective_transport hv,
    hρ.eq_gauss_mul_abs_det hρ1 hv⟩

end PolarTransport
