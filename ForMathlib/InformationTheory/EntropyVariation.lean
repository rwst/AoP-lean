/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The first variation of the Shannon entropy

Let `ρ` be a function with `ρ` and `ρ log ρ` integrable, and `φ` a bounded measurable function.
Along the variation `ρ_t = ρ (1 + t φ)`, `ρ_t log ρ_t` stays integrable for every `t`, and

  `d/dt ∫ -ρ_t log ρ_t |_{t = 0} = -∫ ρ φ (log ρ + 1)`

when `ρ ≥ 0`. The variation `ρ φ` vanishes where `ρ` does. Other directions are excluded on
purpose: `negMulLog` has slope `+∞` at `0`, so moving mass to where `ρ = 0` gives no
derivative.

## Main results

* `MeasureTheory.integrable_negMulLog_mul_one_add`: `ρ_t log ρ_t` is integrable;
* `MeasureTheory.hasDerivAt_integral_negMulLog_mul_one_add`: the first variation.
-/

open Real Set Metric

public section

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ φ : α → ℝ} {C : ℝ}

theorem integrable_negMulLog_mul_one_add (hρ : Integrable ρ μ)
    (hρl : Integrable (fun x => negMulLog (ρ x)) μ) (hφ : AEStronglyMeasurable φ μ)
    (hC : ∀ x, |φ x| ≤ C) (t : ℝ) :
    Integrable (fun x => negMulLog (ρ x * (1 + t * φ x))) μ := by
  set M := 1 + |t| * C
  have hy : ∀ x, |1 + t * φ x| ≤ M := fun x =>
    calc |1 + t * φ x| ≤ |1| + |t * φ x| := abs_add_le _ _
      _ ≤ M := by
        rw [abs_one, abs_mul]
        exact add_le_add_right (mul_le_mul_of_nonneg_left (hC x) (abs_nonneg t)) 1
  have hym : AEStronglyMeasurable (fun x => 1 + t * φ x) μ :=
    aestronglyMeasurable_const.add (hφ.const_mul t)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    continuous_negMulLog.continuousOn
  simp_rw [negMulLog_mul]
  exact (hρl.bdd_mul hym (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hy x))).add
    (hρ.mul_bdd (continuous_negMulLog.comp_aestronglyMeasurable hym)
      (ae_of_all _ fun x => hB _ (abs_le.1 (hy x))))

/-- **The first variation of the Shannon entropy** along `ρ (1 + t φ)`, for bounded `φ`. -/
theorem hasDerivAt_integral_negMulLog_mul_one_add (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ μ)
    (hρl : Integrable (fun x => negMulLog (ρ x)) μ) (hφ : AEStronglyMeasurable φ μ)
    (hC : ∀ x, |φ x| ≤ C) :
    HasDerivAt (fun t => ∫ x, negMulLog (ρ x * (1 + t * φ x)) ∂μ)
      (∫ x, -(ρ x * φ x * (log (ρ x) + 1)) ∂μ) 0 := by
  set ε := (2 * (|C| + 1))⁻¹
  have hε : 0 < ε := by positivity
  have hsmall : ∀ t ∈ ball (0 : ℝ) ε, ∀ x, 2⁻¹ ≤ 1 + t * φ x ∧ 1 + t * φ x ≤ 3 / 2 := by
    intro t ht x
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    have h : |t * φ x| ≤ 2⁻¹ := by
      rw [abs_mul]
      calc |t| * |φ x| ≤ ε * (|C| + 1) :=
            mul_le_mul ht.le ((hC x).trans ((le_abs_self C).trans (by linarith)))
              (abs_nonneg _) hε.le
        _ = 2⁻¹ := by simp only [ε]; field_simp
    constructor <;> linarith [abs_le.1 h]
  have hlog : ∀ y : ℝ, 2⁻¹ ≤ y → y ≤ 3 / 2 → |log y| ≤ 1 := fun y h1 h2 => by
    have hy : 0 < y := by linarith
    have hl := one_sub_inv_le_log_of_pos hy
    have hu := log_le_sub_one_of_pos hy
    have : y⁻¹ ≤ 2 := by rw [inv_le_comm₀ hy two_pos]; linarith
    rw [abs_le]
    constructor <;> linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := 0)
    (F := fun t x => negMulLog (ρ x * (1 + t * φ x)))
    (F' := fun t x => (-log (ρ x * (1 + t * φ x)) - 1) * (ρ x * φ x))
    (bound := fun x => |C| * (|negMulLog (ρ x)| + 2 * ρ x)) (ball_mem_nhds 0 hε)
    (Filter.Eventually.of_forall fun t =>
      (integrable_negMulLog_mul_one_add hρ hρl hφ hC t).aestronglyMeasurable)
    (integrable_negMulLog_mul_one_add hρ hρl hφ hC 0)
    (((measurable_log.comp_aemeasurable (hρ.aemeasurable.mul
      (aemeasurable_const.add (aemeasurable_const.mul hφ.aemeasurable)))).neg.sub_const 1).mul
        (hρ.aemeasurable.mul hφ.aemeasurable)).aestronglyMeasurable
    (ae_of_all _ fun x t ht => ?_) ((hρl.abs.add (hρ.const_mul 2)).const_mul |C|)
    (ae_of_all _ fun x t ht => ?_)
  · refine key.2.congr_deriv (integral_congr_ae (ae_of_all _ fun x => ?_))
    simp only [zero_mul, add_zero, mul_one]
    ring
  · rcases (hρ0 x).eq_or_lt with h0 | hpos
    · simp only [← h0, zero_mul, mul_zero, norm_zero, negMulLog_zero, abs_zero, zero_add]
      rfl
    obtain ⟨h1, h2⟩ := hsmall t ht x
    have hy : 0 < 1 + t * φ x := by linarith
    have hl := hlog _ h1 h2
    have hφC : |φ x| ≤ |C| := (hC x).trans (le_abs_self C)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, log_mul hpos.ne' hy.ne', abs_mul,
      abs_of_pos hpos, negMulLog, abs_mul, abs_neg, abs_of_pos hpos]
    have hb : |-(log (ρ x) + log (1 + t * φ x)) - 1| ≤ |log (ρ x)| + 2 := by
      rw [abs_le] at hl ⊢
      constructor <;> linarith [neg_abs_le (log (ρ x)), le_abs_self (log (ρ x))]
    calc |-(log (ρ x) + log (1 + t * φ x)) - 1| * (ρ x * |φ x|)
        ≤ (|log (ρ x)| + 2) * (ρ x * |C|) :=
          mul_le_mul hb (mul_le_mul_of_nonneg_left hφC hpos.le) (by positivity)
            (by positivity)
      _ = |C| * (ρ x * |log (ρ x)| + 2 * ρ x) := by ring
  · rcases (hρ0 x).eq_or_lt with h0 | hpos
    · simp only [← h0, zero_mul, mul_zero, negMulLog_zero]
      exact hasDerivAt_const _ _
    have hy : 0 < 1 + t * φ x := by linarith [(hsmall t ht x).1]
    have hu : HasDerivAt (fun t => ρ x * (1 + t * φ x)) (ρ x * φ x) t := by
      simpa using (((hasDerivAt_id t).mul_const (φ x)).const_add 1).const_mul (ρ x)
    exact (hasDerivAt_negMulLog (mul_pos hpos hy).ne').comp t hu

end MeasureTheory
