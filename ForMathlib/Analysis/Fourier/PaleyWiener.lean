/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Complex.CauchyIntegral
import TauCeti.Analysis.Fourier.SineSeries

/-!
# A function and its Fourier transform cannot both have bounded support

The uniqueness half of the Paley–Wiener theorem on `ℝ`: if `f ∈ L²(ℝ)` vanishes outside a bounded
interval, then its Fourier transform `𝓕 f` is the restriction to `ℝ` of an entire function, so
`𝓕 f` cannot vanish on a nonempty open set unless `f = 0` almost everywhere.

The proof: for `f` supported in `(a, b]`, the function
`G z = ∫ x in (a, b], exp (-2 π i x z) f x` is differentiable on all of `ℂ` (differentiation
under the integral sign), and `G ξ = 𝓕 f ξ` for real `ξ`. If `𝓕 f` vanishes on an open set, so
does `G` on a set accumulating in `ℂ`, and the identity theorem gives `G = 0`. In particular all
Fourier coefficients of `f` on `[a, b]`, which are values of `G` at real points, vanish, and
`f = 0` almost everywhere on `(a, b]` by Parseval's identity
(`TauCeti.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero`).

## Main results

* `Real.ae_eq_zero_of_fourier_eqOn_zero`: if `f ∈ L²(a, b]` vanishes outside `(a, b]` and `𝓕 f`
  vanishes on a nonempty open set, then `f = 0` almost everywhere;
* `Real.ae_eq_zero_of_fourier_eq_zero_of_lt_abs`: if `f ∈ L²(ℝ)` vanishes almost everywhere
  outside `[-R, R]` and `𝓕 f` vanishes outside `[-S, S]`, then `f = 0` almost everywhere.

## References

* W. Rudin, *Real and Complex Analysis*, Theorem 19.3 (Paley–Wiener).
-/

open MeasureTheory Set Complex Filter Topology
open scoped Real FourierTransform

public section

namespace Real

variable {f : ℝ → ℂ} {a b : ℝ}

private theorem norm_cexp_le {x B : ℝ} (hx : |x| ≤ B) (z : ℂ) :
    ‖cexp (-2 * π * I * x * z)‖ ≤ Real.exp (2 * π * B * ‖z‖) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have hre : (-2 * π * I * x * z).re = 2 * π * (x * z.im) := by simp; ring
  have h1 : x * z.im ≤ B * ‖z‖ :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul hx (abs_im_le_norm z) (abs_nonneg _) ((abs_nonneg x).trans hx))
  rw [hre, mul_assoc (2 * π) B]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)

/-- For `f` integrable on `(a, b]`, `z ↦ ∫ x in (a, b], exp (-2 π i x z) f x` is entire. -/
private theorem differentiable_integral_cexp_mul (hf : IntegrableOn f (Ioc a b)) :
    Differentiable ℂ fun z : ℂ => ∫ x in Ioc a b, cexp (-2 * π * I * x * z) * f x := by
  intro z₀
  set B := max |a| |b|
  have hB : ∀ᵐ x ∂(volume.restrict (Ioc a b)), |x| ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact abs_le_max_abs_abs hx.1.le hx.2
  set C := 2 * π * B * Real.exp (2 * π * B * (‖z₀‖ + 1))
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun x : ℝ => cexp (-2 * π * I * x * z) * f x)
      (volume.restrict (Ioc a b)) := fun z =>
    (Continuous.aestronglyMeasurable (by fun_prop)).mul hf.aestronglyMeasurable
  have hint : Integrable (fun x : ℝ => cexp (-2 * π * I * x * z₀) * f x)
      (volume.restrict (Ioc a b)) := by
    refine (hf.norm.const_mul (Real.exp (2 * π * B * ‖z₀‖))).mono' (hmeas z₀) ?_
    filter_upwards [hB] with x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_cexp_le hx z₀) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioc a b))
    (F := fun z x => cexp (-2 * π * I * x * z) * f x)
    (F' := fun z x => -2 * π * I * x * cexp (-2 * π * I * x * z) * f x)
    (x₀ := z₀) (bound := fun x => C * ‖f x‖) (Metric.ball_mem_nhds z₀ zero_lt_one)
    (Eventually.of_forall hmeas) hint
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul hf.aestronglyMeasurable) ?_
    (hf.norm.const_mul C) ?_
  · exact key.2.differentiableAt
  · filter_upwards [hB] with x hx z hz
    have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    have h1 : ‖cexp (-2 * π * I * x * z)‖ ≤ Real.exp (2 * π * B * (‖z₀‖ + 1)) :=
      (norm_cexp_le hx z).trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz'
        (by have := (abs_nonneg x).trans hx; positivity)))
    have h2 : ‖-2 * π * I * (x : ℂ)‖ = 2 * π * |x| := by
      simp [abs_of_pos Real.pi_pos]
    rw [norm_mul, norm_mul, h2]
    have h3 : 2 * π * |x| ≤ 2 * π * B := mul_le_mul_of_nonneg_left hx (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul h3 h1 (norm_nonneg _) (by positivity))
      (norm_nonneg _)
  · refine Eventually.of_forall fun x z _ => ?_
    have := (((hasDerivAt_id z).const_mul (-2 * π * I * x)).cexp).mul_const (f x)
    simp only [id_eq] at this
    convert this using 1
    ring

/-- **Paley–Wiener uniqueness.** If `f` is square integrable on `(a, b]` and zero almost
everywhere outside it, and its Fourier transform vanishes on a nonempty open set, then `f = 0`
almost everywhere. -/
theorem ae_eq_zero_of_fourier_eqOn_zero (hab : a < b) (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hsupp : ∀ᵐ x, x ∉ Ioc a b → f x = 0) {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ ξ ∈ U, 𝓕 f ξ = 0) : f =ᵐ[volume] 0 := by
  have hint : IntegrableOn f (Ioc a b) := by
    have : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    exact hf.integrable one_le_two
  set G : ℂ → ℂ := fun z => ∫ x in Ioc a b, cexp (-2 * π * I * x * z) * f x with hGdef
  have hG : ∀ ξ : ℝ, 𝓕 f ξ = G ξ := by
    intro ξ
    rw [fourier_real_eq_integral_exp_smul, ← setIntegral_eq_integral_of_ae_compl_eq_zero
      (s := Ioc a b) (by filter_upwards [hsupp] with x hx hx'; rw [hx hx', smul_zero])]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  have hGa : AnalyticOnNhd ℂ G univ := fun z _ =>
    (differentiable_integral_cexp_mul hint).analyticAt z
  obtain ⟨ξ₀, hξ₀⟩ := hne
  have hfreq : ∃ᶠ z in 𝓝[≠] (ξ₀ : ℂ), G z = 0 := by
    have h1 : ∀ᶠ ξ : ℝ in 𝓝[≠] ξ₀, G ξ = 0 :=
      nhdsWithin_le_nhds (eventually_of_mem (hU.mem_nhds hξ₀) fun ξ hξ => (hG ξ) ▸ h ξ hξ)
    have h2 : Tendsto (fun ξ : ℝ => (ξ : ℂ)) (𝓝[≠] ξ₀) (𝓝[≠] (ξ₀ : ℂ)) :=
      continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun ξ hξ => by
        simpa using hξ
    exact h2.frequently h1.frequently
  have hG0 := hGa.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (mem_univ _) hfreq
  have hc : ∀ n : ℤ, fourierCoeffOn hab f n = 0 := by
    intro n
    have : Fact (0 < b - a) := ⟨sub_pos.2 hab⟩
    rw [fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le hab.le]
    have : ∫ x in Ioc a b, fourier (-n) (x : AddCircle (b - a)) • f x
        = G ((n / (b - a) : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
      rw [fourier_coe_apply, smul_eq_mul]
      have hba : (b : ℂ) - a ≠ 0 := by exact_mod_cast (sub_pos.2 hab).ne'
      congr 2
      push_cast
      field_simp
    rw [this, hG0 (mem_univ _), Pi.zero_apply, smul_zero]
  have h0 := TauCeti.ae_eq_zero_of_forall_fourierCoeffOn_eq_zero hab hf hc
  filter_upwards [hsupp, ae_imp_of_ae_restrict h0] with x h1 h2
  by_cases hx : x ∈ Ioc a b
  · exact h2 hx
  · exact h1 hx

/-- **A function and its Fourier transform cannot both have bounded support.** If `f ∈ L²(ℝ)`
vanishes almost everywhere outside `[-R, R]` and `𝓕 f` vanishes outside `[-S, S]`, then `f = 0`
almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero_of_lt_abs (hf : MemLp f 2) {R S : ℝ}
    (hR : ∀ᵐ x, R < |x| → f x = 0) (hS : ∀ ξ, S < |ξ| → 𝓕 f ξ = 0) : f =ᵐ[volume] 0 := by
  have hab : -|R| - 1 < |R| + 1 := by linarith [abs_nonneg R]
  refine ae_eq_zero_of_fourier_eqOn_zero hab (hf.restrict _) ?_ (isOpen_Ioi (a := |S|))
    ⟨|S| + 1, by simp⟩ fun ξ hξ => hS ξ ?_
  · filter_upwards [hR] with x hx hxI
    refine hx ?_
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at hxI
    rcases hxI with hxI | hxI
    · rw [abs_of_neg (by linarith [abs_nonneg R])]
      linarith [le_abs_self R]
    · rw [abs_of_pos (by linarith [abs_nonneg R])]
      linarith [le_abs_self R]
  · have : |S| < ξ := hξ
    rw [abs_of_pos ((abs_nonneg S).trans_lt this)]
    exact (le_abs_self S).trans_lt this

end Real
