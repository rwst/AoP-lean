/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.InformationTheory.GibbsInequality
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite entropy of marginals

Let `ρ ≥ 0` be a density on `X × Y` with `ρ` and `ρ log ρ` integrable, and `ρ_X(x) = ∫ ρ(x, y) dy`
its marginal. Finite entropy of `ρ` alone does not give finite entropy of `ρ_X`: `-t log t` is
positive for `t < 1`, and the marginal may spread out. With positive reference functions
`γ` on `Y` and `γ'` on `X` of integral at most `1`, such that `ρ log γ(y)` and `ρ log γ'(x)` are
integrable (finite second moments, for Gaussians `γ, γ'`), `ρ_X log ρ_X` is integrable. It is
squeezed between

  `∫ -ρ(x, y) log ρ(x, y) dy + ∫ ρ(x, y) log γ(y) dy ≤ -ρ_X(x) log ρ_X(x)`

(Gibbs' inequality in `y`, against `ρ_X(x) γ`) and the pointwise bound
`-ρ_X log ρ_X ≤ -ρ_X log γ' + γ' - ρ_X`.

## Main results

* `MeasureTheory.integral_mul_integral_prod`: moments of the marginal are moments of `ρ`;
* `MeasureTheory.integral_negMulLog_add_integral_mul_log_le`: the lower bound, for one `x`;
* `MeasureTheory.integrable_negMulLog_integral_prod`: the marginal has finite entropy.
-/

open Real

public section

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

section Moments

variable [SFinite ν] {ρ : X × Y → ℝ} {g : X → ℝ}

theorem integrable_mul_integral_prod (hg : Integrable (fun z => g z.1 * ρ z) (μ.prod ν)) :
    Integrable (fun x => g x * ∫ y, ρ (x, y) ∂ν) μ := by
  simpa only [← integral_const_mul] using hg.integral_prod_left

/-- Moments of the marginal `∫ ρ(x, y) dν(y)` are moments of `ρ`. -/
theorem integral_mul_integral_prod [SFinite μ] (hg : Integrable (fun z => g z.1 * ρ z) (μ.prod ν)) :
    ∫ x, g x * ∫ y, ρ (x, y) ∂ν ∂μ = ∫ z, g z.1 * ρ z ∂(μ.prod ν) := by
  rw [integral_prod _ hg]
  simp_rw [integral_const_mul]

end Moments

/-- Gibbs' inequality against `(∫ σ) γ`: `∫ -σ log σ + ∫ σ log γ ≤ -(∫ σ) log (∫ σ)` for a
positive `γ` with `∫ γ ≤ 1`. -/
theorem integral_negMulLog_add_integral_mul_log_le {σ γ : Y → ℝ} (hσ0 : ∀ y, 0 ≤ σ y)
    (hσ : Integrable σ ν) (hσσ : Integrable (fun y => negMulLog (σ y)) ν)
    (hσγ : Integrable (fun y => σ y * log (γ y)) ν) (hγ0 : ∀ y, 0 < γ y)
    (hγ : Integrable γ ν) (hγ1 : ∫ y, γ y ∂ν ≤ 1) :
    ∫ y, negMulLog (σ y) ∂ν + ∫ y, σ y * log (γ y) ∂ν ≤ negMulLog (∫ y, σ y ∂ν) := by
  set m := ∫ y, σ y ∂ν
  rcases (integral_nonneg hσ0 : 0 ≤ m).eq_or_lt with hm | hm
  · have h0 : σ =ᵐ[ν] 0 := (integral_eq_zero_iff_of_nonneg hσ0 hσ).1 hm.symm
    have h1 : ∫ y, negMulLog (σ y) ∂ν = 0 := by
      rw [integral_congr_ae (g := fun _ => 0) (h0.mono fun y hy => by simp [hy]), integral_zero]
    have h2 : ∫ y, σ y * log (γ y) ∂ν = 0 := by
      rw [integral_congr_ae (g := fun _ => 0) (h0.mono fun y hy => by simp [hy]), integral_zero]
    rw [show m = 0 from hm.symm, h1, h2]
    simp
  have hpt : ∀ y, negMulLog (σ y) + σ y * log (γ y) ≤
      -(log m * σ y) + m * γ y - σ y := fun y => by
    have := Real.negMulLog_le_neg_mul_log_add_sub (hσ0 y) (mul_pos hm (hγ0 y))
    rw [log_mul hm.ne' (hγ0 y).ne'] at this
    linarith
  have hR : Integrable (fun y => -(log m * σ y) + m * γ y - σ y) ν :=
    ((hσ.const_mul _).neg.add (hγ.const_mul m)).sub hσ
  calc ∫ y, negMulLog (σ y) ∂ν + ∫ y, σ y * log (γ y) ∂ν
      = ∫ y, (negMulLog (σ y) + σ y * log (γ y)) ∂ν := (integral_add hσσ hσγ).symm
    _ ≤ ∫ y, (-(log m * σ y) + m * γ y - σ y) ∂ν := integral_mono (hσσ.add hσγ) hR hpt
    _ = -(log m * m) + m * ∫ y, γ y ∂ν - m := by
      rw [integral_sub _ hσ, integral_add, integral_neg, integral_const_mul, integral_const_mul]
      all_goals first
        | exact (hσ.const_mul _).neg
        | exact hγ.const_mul m
        | exact (hσ.const_mul _).neg.add (hγ.const_mul m)
    _ ≤ negMulLog m := by
      rw [negMulLog]
      nlinarith [mul_le_mul_of_nonneg_left hγ1 hm.le]

variable [SFinite μ] [SFinite ν] {ρ : X × Y → ℝ}

/-- **The marginal has finite entropy.** If `ρ ≥ 0` and `ρ log ρ` are integrable on `X × Y`,
and `ρ log γ(y)`, `ρ log γ'(x)` are integrable for positive `γ, γ'` of integral at most `1`, then
the marginal `ρ_X(x) = ∫ ρ(x, y) dν(y)` has `ρ_X log ρ_X` integrable. -/
theorem integrable_negMulLog_integral_prod (hρ0 : ∀ z, 0 ≤ ρ z) (hρ : Integrable ρ (μ.prod ν))
    (hρρ : Integrable (fun z => negMulLog (ρ z)) (μ.prod ν)) {γ : Y → ℝ} (hγ0 : ∀ y, 0 < γ y)
    (hγ : Integrable γ ν) (hγ1 : ∫ y, γ y ∂ν ≤ 1)
    (hργ : Integrable (fun z => ρ z * log (γ z.2)) (μ.prod ν)) {γ' : X → ℝ}
    (hγ'0 : ∀ x, 0 < γ' x) (hγ' : Integrable γ' μ)
    (hργ' : Integrable (fun z => ρ z * log (γ' z.1)) (μ.prod ν)) :
    Integrable (fun x => negMulLog (∫ y, ρ (x, y) ∂ν)) μ := by
  have hu := hργ'.integral_prod_left
  simp_rw [integral_mul_const] at hu
  refine integrable_of_le_of_le
    (g₁ := fun x => ∫ y, negMulLog (ρ (x, y)) ∂ν + ∫ y, ρ (x, y) * log (γ y) ∂ν)
    (g₂ := fun x => -((∫ y, ρ (x, y) ∂ν) * log (γ' x)) + γ' x - ∫ y, ρ (x, y) ∂ν)
    (continuous_negMulLog.comp_aestronglyMeasurable hρ.integral_prod_left.aestronglyMeasurable)
    ?_ (ae_of_all _ fun x => Real.negMulLog_le_neg_mul_log_add_sub
      (integral_nonneg fun y => hρ0 _) (hγ'0 x))
    (hρρ.integral_prod_left.add hργ.integral_prod_left)
    ((hu.neg.add hγ').sub hρ.integral_prod_left)
  filter_upwards [hρ.prod_right_ae, hρρ.prod_right_ae, hργ.prod_right_ae] with x h1 h2 h3
  exact integral_negMulLog_add_integral_mul_log_le (fun y => hρ0 _) h1 h2 h3 hγ0 hγ hγ1

end MeasureTheory
