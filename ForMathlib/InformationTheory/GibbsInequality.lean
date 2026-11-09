/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Gibbs' inequality for densities

For a probability density `ρ` and a positive function `G` with `∫ G ≤ 1` on a measure space,

  `-∫ ρ log ρ ≤ -∫ ρ log G`,

with equality only if `ρ = G` almost everywhere. The proof integrates the pointwise bound
`-a log a ≤ -a log b + b - a` (from `log t ≤ t - 1`), so no Radon–Nikodym derivative is needed.

## Main results

* `Real.negMulLog_le_neg_mul_log_add_sub`, `Real.negMulLog_eq_neg_mul_log_add_sub_iff`: the
  pointwise bound and its equality case;
* `MeasureTheory.integral_negMulLog_le`: Gibbs' inequality;
* `MeasureTheory.integral_negMulLog_le_of_imp_pos`: the same for `G ≥ 0` positive where `ρ` is;
* `MeasureTheory.ae_eq_of_integral_negMulLog_eq`: its equality case.
-/

open Real

@[expose] public section

namespace Real

/-- `-a log a ≤ -a log b + b - a` for `a ≥ 0`, `b > 0`. -/
theorem negMulLog_le_neg_mul_log_add_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    negMulLog a ≤ -(a * log b) + b - a := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using hb.le
  have h := log_le_sub_one_of_pos (div_pos hb ha)
  rw [log_div hb.ne' ha.ne', le_sub_iff_add_le, ← mul_le_mul_iff_right₀ ha] at h
  rw [negMulLog]
  have : a * (b / a) = b := by field_simp
  nlinarith

/-- Equality in `negMulLog_le_neg_mul_log_add_sub` holds only for `a = b`. -/
theorem negMulLog_eq_neg_mul_log_add_sub_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    negMulLog a = -(a * log b) + b - a ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by subst h; simp [negMulLog]⟩
  rcases ha.eq_or_lt with rfl | ha
  · simp at h
    exact absurd h.symm hb.ne'
  by_contra hab
  have hlt := log_lt_sub_one_of_pos (div_pos hb ha) (by
    rw [Ne, div_eq_one_iff_eq ha.ne']; exact fun h => hab h.symm)
  rw [log_div hb.ne' ha.ne', lt_sub_iff_add_lt, ← mul_lt_mul_iff_right₀ ha] at hlt
  rw [negMulLog] at h
  have : a * (b / a) = b := by field_simp
  nlinarith

end Real

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ G : X → ℝ}

/-- The nonnegative integrand `-ρ log G + G - ρ - (-ρ log ρ)` of Gibbs' inequality. -/
private lemma integral_gibbsGap (hρ1 : ∫ x, ρ x ∂μ = 1) (hGi : Integrable G μ)
    (hρρ : Integrable (fun x => negMulLog (ρ x)) μ)
    (hρG : Integrable (fun x => ρ x * log (G x)) μ) :
    ∫ x, (-(ρ x * log (G x)) + G x - ρ x - negMulLog (ρ x)) ∂μ =
      -∫ x, ρ x * log (G x) ∂μ + ∫ x, G x ∂μ - 1 - ∫ x, negMulLog (ρ x) ∂μ := by
  have hρi : Integrable ρ μ := Integrable.of_integral_ne_zero (by rw [hρ1]; norm_num)
  have h1 : Integrable (fun x => -(ρ x * log (G x)) + G x) μ := hρG.neg.add hGi
  have h2 : Integrable (fun x => -(ρ x * log (G x)) + G x - ρ x) μ := h1.sub hρi
  rw [integral_sub h2 hρρ, integral_sub h1 hρi,
    integral_add (f := fun x => -(ρ x * log (G x))) hρG.neg hGi, integral_neg, hρ1]

/-- **Gibbs' inequality**, for a reference `G ≥ 0` that is positive wherever `ρ` is: for a
probability density `ρ` and `∫ G ≤ 1`, `-∫ ρ log ρ ≤ -∫ ρ log G`. -/
theorem integral_negMulLog_le_of_imp_pos (hρ0 : 0 ≤ᵐ[μ] ρ) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hG0 : 0 ≤ᵐ[μ] G) (hG : ∀ᵐ x ∂μ, 0 < ρ x → 0 < G x) (hGi : Integrable G μ)
    (hG1 : ∫ x, G x ∂μ ≤ 1) (hρρ : Integrable (fun x => negMulLog (ρ x)) μ)
    (hρG : Integrable (fun x => ρ x * log (G x)) μ) :
    ∫ x, negMulLog (ρ x) ∂μ ≤ -∫ x, ρ x * log (G x) ∂μ := by
  have h0 : 0 ≤ ∫ x, (-(ρ x * log (G x)) + G x - ρ x - negMulLog (ρ x)) ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hρ0, hG0, hG] with x hx hG0x hGx
    simp only [Pi.zero_apply] at hx hG0x ⊢
    rcases hx.eq_or_lt with h | h
    · simpa [← h] using hG0x
    · have := negMulLog_le_neg_mul_log_add_sub hx (hGx h)
      linarith
  rw [integral_gibbsGap hρ1 hGi hρρ hρG] at h0
  linarith

/-- **Gibbs' inequality.** For a probability density `ρ` and a positive `G` with `∫ G ≤ 1`,
`-∫ ρ log ρ ≤ -∫ ρ log G`. -/
theorem integral_negMulLog_le (hρ0 : 0 ≤ᵐ[μ] ρ) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hG : ∀ᵐ x ∂μ, 0 < G x) (hGi : Integrable G μ) (hG1 : ∫ x, G x ∂μ ≤ 1)
    (hρρ : Integrable (fun x => negMulLog (ρ x)) μ)
    (hρG : Integrable (fun x => ρ x * log (G x)) μ) :
    ∫ x, negMulLog (ρ x) ∂μ ≤ -∫ x, ρ x * log (G x) ∂μ :=
  integral_negMulLog_le_of_imp_pos hρ0 hρ1 (hG.mono fun _ hx => hx.le)
    (hG.mono fun _ hx _ => hx) hGi hG1 hρρ hρG

/-- The equality case of Gibbs' inequality: `ρ = G` almost everywhere. -/
theorem ae_eq_of_integral_negMulLog_eq (hρ0 : 0 ≤ᵐ[μ] ρ) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hG : ∀ᵐ x ∂μ, 0 < G x) (hGi : Integrable G μ) (hG1 : ∫ x, G x ∂μ ≤ 1)
    (hρρ : Integrable (fun x => negMulLog (ρ x)) μ)
    (hρG : Integrable (fun x => ρ x * log (G x)) μ)
    (heq : ∫ x, negMulLog (ρ x) ∂μ = -∫ x, ρ x * log (G x) ∂μ) : ρ =ᵐ[μ] G := by
  have hρi : Integrable ρ μ := Integrable.of_integral_ne_zero (by rw [hρ1]; norm_num)
  have hnn : 0 ≤ᵐ[μ] fun x => -(ρ x * log (G x)) + G x - ρ x - negMulLog (ρ x) := by
    filter_upwards [hρ0, hG] with x hx hGx
    have := negMulLog_le_neg_mul_log_add_sub hx hGx
    simp only [Pi.zero_apply]
    linarith
  have hint := integral_gibbsGap hρ1 hGi hρρ hρG
  have hzero : ∫ x, (-(ρ x * log (G x)) + G x - ρ x - negMulLog (ρ x)) ∂μ = 0 :=
    le_antisymm (by rw [hint]; linarith) (integral_nonneg_of_ae hnn)
  have hi : Integrable (fun x => -(ρ x * log (G x)) + G x - ρ x - negMulLog (ρ x)) μ :=
    ((hρG.neg.add hGi).sub hρi).sub hρρ
  rw [integral_eq_zero_iff_of_nonneg_ae hnn hi] at hzero
  filter_upwards [hzero, hρ0, hG] with x hx hρx hGx
  simp only [Pi.zero_apply] at hx
  exact (negMulLog_eq_neg_mul_log_add_sub_iff hρx hGx).1 (by linarith)

end MeasureTheory
