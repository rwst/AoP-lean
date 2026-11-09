/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Densities and entropy under a change of variables

Let `Φ : E → E` be injective with derivative `Φ' x` at every `x`, all invertible, on a
finite-dimensional real space with an additive Haar measure. A density `ρ` in the variables `x`
becomes the density `pushDensity Φ Φ' ρ` in the variables `u = Φ(x)`: `ρ(x) / |det Φ'(x)|` at
`u = Φ(x)`, and `0` off the range of `Φ`. Then `∫ g(u) ρ_Φ(u) du = ∫ g(Φ x) ρ(x) dx`, and the
differential entropy changes by the expected log-Jacobian,

  `-∫ ρ_Φ log ρ_Φ = -∫ ρ log ρ + ∫ ρ log |det Φ'|`.

`Φ` need not be onto, nor preserve orientation.

## Main results

* `MeasureTheory.integral_mul_pushDensity`: moments of `ρ_Φ` are moments of `ρ`;
* `MeasureTheory.integral_negMulLog_pushDensity`: the change of the entropy.
-/

open Real Set Function

public section

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → E}
  {Φ' : E → E →L[ℝ] E} {ρ g : E → ℝ}

/-- The density in the variables `u = Φ(x)` of a density `ρ` in the variables `x`:
`ρ(x) / |det Φ'(x)|` at `Φ(x)`, and `0` off the range of `Φ`. -/
noncomputable def pushDensity (Φ : E → E) (Φ' : E → E →L[ℝ] E) (ρ : E → ℝ) : E → ℝ :=
  Function.extend Φ (fun x => ρ x / |(Φ' x).det|) 0

theorem pushDensity_apply (hΦ : Injective Φ) (x : E) :
    pushDensity Φ Φ' ρ (Φ x) = ρ x / |(Φ' x).det| :=
  hΦ.extend_apply _ _ x

theorem pushDensity_of_notMem_range {u : E} (hu : u ∉ range Φ) : pushDensity Φ Φ' ρ u = 0 := by
  rw [pushDensity, Function.extend_apply' _ _ _ fun ⟨x, hx⟩ => hu ⟨x, hx⟩, Pi.zero_apply]

theorem abs_det_mul_pushDensity (hΦ : Injective Φ) (hdet : ∀ x, (Φ' x).det ≠ 0) (x : E) :
    |(Φ' x).det| * pushDensity Φ Φ' ρ (Φ x) = ρ x := by
  rw [pushDensity_apply hΦ, mul_div_cancel₀ _ (abs_ne_zero.2 (hdet x))]

lemma abs_det_mul_negMulLog_pushDensity (hΦ : Injective Φ) (hdet : ∀ x, (Φ' x).det ≠ 0)
    (x : E) :
    |(Φ' x).det| * negMulLog (pushDensity Φ Φ' ρ (Φ x)) =
      negMulLog (ρ x) + ρ x * log |(Φ' x).det| := by
  have hJ : |(Φ' x).det| ≠ 0 := abs_ne_zero.2 (hdet x)
  rw [pushDensity_apply hΦ]
  rcases eq_or_ne (ρ x) 0 with h0 | h0
  · simp [h0]
  rw [negMulLog, negMulLog, log_div h0 hJ]
  field_simp
  ring

section Transfer

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
  [μ.IsAddHaarMeasure] (hd : ∀ x, HasFDerivAt Φ (Φ' x) x) (hΦ : Injective Φ)
include hd hΦ

/-- Change of variables for a function that vanishes off the range of `Φ`. -/
theorem integrable_iff_of_eq_zero_off_range (hg : ∀ u ∉ range Φ, g u = 0) :
    Integrable g μ ↔ Integrable (fun x => |(Φ' x).det| * g (Φ x)) μ := by
  have hF : ∀ x ∈ univ, HasFDerivWithinAt Φ (Φ' x) univ x := fun x _ =>
    (hd x).hasFDerivWithinAt
  rw [← integrableOn_iff_integrable_of_support_subset (s := range Φ)
      fun u hu => by_contra fun h => hu (hg u h), ← image_univ,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ MeasurableSet.univ hF hΦ.injOn,
    integrableOn_univ]
  rfl

theorem integral_eq_of_eq_zero_off_range (hg : ∀ u ∉ range Φ, g u = 0) :
    ∫ u, g u ∂μ = ∫ x, |(Φ' x).det| * g (Φ x) ∂μ := by
  have hF : ∀ x ∈ univ, HasFDerivWithinAt Φ (Φ' x) univ x := fun x _ =>
    (hd x).hasFDerivWithinAt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := range Φ) hg, ← image_univ,
    integral_image_eq_integral_abs_det_fderiv_smul μ MeasurableSet.univ hF hΦ.injOn,
    setIntegral_univ]
  rfl

variable (hdet : ∀ x, (Φ' x).det ≠ 0)
include hdet

theorem integrable_mul_pushDensity_iff :
    Integrable (fun u => g u * pushDensity Φ Φ' ρ u) μ ↔ Integrable (fun x => g (Φ x) * ρ x) μ := by
  rw [integrable_iff_of_eq_zero_off_range hd hΦ fun u hu => by
    rw [pushDensity_of_notMem_range hu, mul_zero]]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  simp only
  rw [mul_left_comm, abs_det_mul_pushDensity hΦ hdet]

/-- Moments of `ρ_Φ` are moments of `ρ`: `∫ g(u) ρ_Φ(u) du = ∫ g(Φ x) ρ(x) dx`. -/
theorem integral_mul_pushDensity :
    ∫ u, g u * pushDensity Φ Φ' ρ u ∂μ = ∫ x, g (Φ x) * ρ x ∂μ := by
  rw [integral_eq_of_eq_zero_off_range hd hΦ fun u hu => by
    rw [pushDensity_of_notMem_range hu, mul_zero]]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [mul_left_comm, abs_det_mul_pushDensity hΦ hdet]

/-- **The entropy in new variables.** `-∫ ρ_Φ log ρ_Φ = ∫ (-ρ log ρ + ρ log |det Φ'|)`. -/
theorem integral_negMulLog_pushDensity :
    ∫ u, negMulLog (pushDensity Φ Φ' ρ u) ∂μ =
      ∫ x, (negMulLog (ρ x) + ρ x * log |(Φ' x).det|) ∂μ := by
  rw [integral_eq_of_eq_zero_off_range hd hΦ fun u hu => by
    rw [pushDensity_of_notMem_range hu, negMulLog_zero]]
  simp_rw [abs_det_mul_negMulLog_pushDensity hΦ hdet]

theorem integrable_negMulLog_pushDensity_iff
    (hlog : Integrable (fun x => ρ x * log |(Φ' x).det|) μ) :
    Integrable (fun u => negMulLog (pushDensity Φ Φ' ρ u)) μ ↔
      Integrable (fun x => negMulLog (ρ x)) μ := by
  rw [integrable_iff_of_eq_zero_off_range hd hΦ fun u hu => by
    rw [pushDensity_of_notMem_range hu, negMulLog_zero]]
  simp_rw [abs_det_mul_negMulLog_pushDensity hΦ hdet]
  refine ⟨fun h => (h.sub hlog).congr (ae_of_all _ fun x => ?_), fun h => h.add hlog⟩
  simp only [Pi.sub_apply, add_sub_cancel_right]

end Transfer

end MeasureTheory
