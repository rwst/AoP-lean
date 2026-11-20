/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Young's inequality for `x log x` and moments under a relative-entropy bound

The convex conjugate of `a ↦ a log a - a` is `exp`, so
  `a b ≤ a log a - a + exp b`   for `a ≥ 0`.
With `a = ρ / η` and `b = ψ`, multiplied by `η > 0`,
  `ρ ψ ≤ ρ log (ρ / η) - ρ + η exp ψ`.
Integrated, a finite relative entropy `D(ρ ‖ η) = ∫ ρ log (ρ / η)` turns a finite exponential
moment of `ψ` under `η` into a finite moment of `ψ` under `ρ`:
  `∫ ρ ψ ≤ D(ρ ‖ η) - ∫ ρ + ∫ η exp ψ`,
a weak form of the Donsker–Varadhan variational inequality that needs no Radon–Nikodym derivative.

## Main results

* `Real.mul_le_mul_log_sub_add_exp`: Young's inequality;
* `Real.mul_le_mul_log_div_sub_add_mul_exp`: the weighted form;
* `MeasureTheory.integrable_mul_of_integrable_mul_log_div`: the moment bound.
-/

open Real

public section

namespace Real

/-- **Young's inequality** for `a log a - a` and its conjugate `exp`: `a b ≤ a log a - a + exp b`
for `a ≥ 0`. -/
theorem mul_le_mul_log_sub_add_exp {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    a * b ≤ a * log a - a + exp b := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using (exp_pos b).le
  · have h := add_one_le_exp (b - log a)
    rw [exp_sub, exp_log ha, le_div_iff₀ ha] at h
    linarith

/-- The weighted form of Young's inequality: `a b ≤ a log (a / c) - a + c exp b` for `a ≥ 0`,
`c > 0`. -/
theorem mul_le_mul_log_div_sub_add_mul_exp {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (b : ℝ) :
    a * b ≤ a * log (a / c) - a + c * exp b := by
  have h := mul_le_mul_log_sub_add_exp (div_nonneg ha hc.le) b
  have h' := mul_le_mul_of_nonneg_left h hc.le
  have e1 : c * (a / c * b) = a * b := by field_simp
  have e2 : c * (a / c * log (a / c) - a / c + exp b) = a * log (a / c) - a + c * exp b := by
    field_simp
  linarith

end Real

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ρ η ψ : α → ℝ}

/-- **Moments under a relative-entropy bound.** If `ρ log (ρ / η)` and `η exp ψ` are integrable
with `ρ ≥ 0`, `η > 0` and `ψ ≥ 0`, then `ρ ψ` is integrable, and
`∫ ρ ψ ≤ ∫ ρ log (ρ / η) - ∫ ρ + ∫ η exp ψ`. -/
theorem integrable_mul_of_integrable_mul_log_div (hρ0 : ∀ x, 0 ≤ ρ x) (hη : ∀ x, 0 < η x)
    (hψ0 : ∀ x, 0 ≤ ψ x) (hm : AEStronglyMeasurable (fun x => ρ x * ψ x) μ)
    (hρ : Integrable ρ μ) (hd : Integrable (fun x => ρ x * log (ρ x / η x)) μ)
    (he : Integrable (fun x => η x * exp (ψ x)) μ) :
    Integrable (fun x => ρ x * ψ x) μ ∧
      ∫ x, ρ x * ψ x ∂μ ≤
        ∫ x, ρ x * log (ρ x / η x) ∂μ - ∫ x, ρ x ∂μ + ∫ x, η x * exp (ψ x) ∂μ := by
  have hle : ∀ x, ρ x * ψ x ≤ ρ x * log (ρ x / η x) - ρ x + η x * exp (ψ x) := fun x =>
    mul_le_mul_log_div_sub_add_mul_exp (hρ0 x) (hη x) (ψ x)
  have hu : Integrable (fun x => ρ x * log (ρ x / η x) - ρ x + η x * exp (ψ x)) μ :=
    (hd.sub hρ).add he
  have hi : Integrable (fun x => ρ x * ψ x) μ :=
    integrable_of_le_of_le hm (ae_of_all _ fun x => mul_nonneg (hρ0 x) (hψ0 x))
      (ae_of_all _ hle) (integrable_zero _ _ μ) hu
  refine ⟨hi, ?_⟩
  have hd' : Integrable (fun x => ρ x * log (ρ x / η x) - ρ x) μ := hd.sub hρ
  rw [← integral_sub hd hρ, ← integral_add hd' he]
  exact integral_mono hi hu hle

end MeasureTheory
