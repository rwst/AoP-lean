/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Moments of the real Gaussian density

Mathlib computes the mean and variance of the measure `gaussianReal μ v`. This file restates
them as Lebesgue integrals against the density `gaussianPDFReal μ v`, and adds its logarithm.

## Main results

* `ProbabilityTheory.log_gaussianPDFReal`:
  `log (gaussianPDFReal μ v x) = -log (2πv) / 2 - (x - μ)² / (2v)`;
* `ProbabilityTheory.integrable_gaussianPDFReal_smul_iff`;
* `ProbabilityTheory.integral_mul_gaussianPDFReal`: `∫ x g(x) dx = μ`;
* `ProbabilityTheory.integral_sub_sq_mul_gaussianPDFReal`: `∫ (x - μ)² g(x) dx = v`.
-/

open Real MeasureTheory

open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {μ : ℝ} {v : ℝ≥0}

theorem log_gaussianPDFReal (hv : v ≠ 0) (x : ℝ) :
    log (gaussianPDFReal μ v x) = -log (2 * π * v) / 2 - (x - μ) ^ 2 / (2 * v) := by
  have hv' : (0 : ℝ) < v := by positivity
  rw [gaussianPDFReal, log_mul (by positivity) (exp_pos _).ne', log_exp, log_inv,
    log_sqrt (by positivity)]
  ring

theorem integrable_gaussianPDFReal_smul_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hv : v ≠ 0) {f : ℝ → E} :
    Integrable (fun x => gaussianPDFReal μ v x • f x) ↔ Integrable f (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF μ v) (ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp_rw [toReal_gaussianPDF]

theorem integrable_sub_sq_mul_gaussianPDFReal (hv : v ≠ 0) (c : ℝ) :
    Integrable fun x => (x - c) ^ 2 * gaussianPDFReal μ v x := by
  have h : Integrable (fun x : ℝ => (x - c) ^ 2) (gaussianReal μ v) :=
    ((memLp_id_gaussianReal 2).sub (memLp_const c)).integrable_sq
  simpa [mul_comm] using (integrable_gaussianPDFReal_smul_iff hv).2 h

theorem integrable_mul_gaussianPDFReal (hv : v ≠ 0) :
    Integrable fun x => x * gaussianPDFReal μ v x := by
  have h : Integrable (fun x : ℝ => x) (gaussianReal μ v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  simpa [mul_comm] using (integrable_gaussianPDFReal_smul_iff hv).2 h

theorem integral_mul_gaussianPDFReal (hv : v ≠ 0) :
    ∫ x, x * gaussianPDFReal μ v x = μ := by
  simp_rw [mul_comm _ (gaussianPDFReal μ v _), ← smul_eq_mul,
    ← integral_gaussianReal_eq_integral_smul hv]
  exact integral_id_gaussianReal

theorem integral_sub_sq_mul_gaussianPDFReal (hv : v ≠ 0) :
    ∫ x, (x - μ) ^ 2 * gaussianPDFReal μ v x = v := by
  simp_rw [mul_comm _ (gaussianPDFReal μ v _), ← smul_eq_mul,
    ← integral_gaussianReal_eq_integral_smul hv]
  have h := variance_fun_id_gaussianReal (μ := μ) (v := v)
  rw [variance_eq_integral measurable_id'.aemeasurable, integral_id_gaussianReal] at h
  exact h

end ProbabilityTheory
