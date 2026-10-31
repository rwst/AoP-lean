/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.InformationTheory.GibbsInequality
public import ForMathlib.Probability.Distributions.Gaussian.Real

/-!
# Classical uncertainty principle

## i. Overview

Formalization of the technical brief *Classical uncertainty principle* (G. Carcassi,
Assumptions of Physics). A statistical ensemble on a measure space `(X, μ)` is a probability
density `ρ` with finite entropy, and its entropy relative to a cell of size `c` is the
Gibbs/Shannon entropy `S_c[ρ] = -∫ ρ log (c ρ) dμ`, in nats. On the phase space `ℝ²` of one
degree of freedom (DOF) the cell is `h`, and `ħ = h / 2π`.

**Corollary 1.** The uniform distribution on `U` has entropy `log (μ(U) / c)`, which is zero
exactly when `μ(U) = c`; for `n` DOFs, `c = hⁿ`.

**Theorem 2.** The lower entropic bound ZENT (`S_h[ρ] ≥ 0`) implies the classical uncertainty
principle CUP (`σ_q σ_p ≥ ħ / e`), with equality exactly for products of Gaussians in `q` and
`p` with `σ_q σ_p = ħ / e`. For variables `f, g` such that `(q, p) ↦ (f, g)` is injective, the
bound becomes `σ_f σ_g ≥ (ħ / e) e^{E[log |{f, g}|]}` (eq. (5)).

The brief finds the Gaussian as a critical point of a Lagrangian, which does not show that it
is a minimum. Here the minimality comes from Gibbs' inequality instead: for any density `G`,
`-∫ ρ log ρ ≤ -∫ ρ log G`. With `G` the product of Gaussians in `(f, g)` having the means and
variances of `f, g` under `ρ`, pulled back to phase space with the Jacobian `|{f, g}|`, the
right side is `log (2π e σ_f σ_g) - E[log |{f, g}|]`. So for every ensemble

  `σ_f σ_g ≥ (ħ / e) e^{S_h[ρ] + E[log |{f, g}|]}`,

and for `(f, g) = (q, p)` equality holds exactly when `ρ` is that product of Gaussians. ZENT
then gives Theorem 2. The final remark of the brief, that CUP does not imply ZENT, holds too:
a uniform distribution on two small squares far apart has negative entropy and large spread.

## ii. Key results

- `ClassicalUncertaintyPrinciple.entropy_uniform`,
  `ClassicalUncertaintyPrinciple.entropy_uniform_eq_zero_iff`: Corollary 1.
- `ClassicalUncertaintyPrinciple.LowerEntropicBound`,
  `ClassicalUncertaintyPrinciple.UncertaintyPrinciple`: the conditions ZENT and CUP.
- `ClassicalUncertaintyPrinciple.Hyp.hbar_div_exp_mul_exp_le`: the Gaussian bound
  `σ_f σ_g ≥ (ħ/e) e^{S + E[log J]}` on any measure space, for any Gaussian weight `J`.
- `ClassicalUncertaintyPrinciple.hbar_div_exp_mul_exp_entropy_le`: `σ_q σ_p ≥ (ħ/e) e^S`.
- `ClassicalUncertaintyPrinciple.sd_mul_sd_eq_iff`: equality in it holds exactly for Gaussians.
- `ClassicalUncertaintyPrinciple.uncertaintyPrinciple_of_lowerEntropicBound`,
  `ClassicalUncertaintyPrinciple.sd_mul_sd_eq_hbar_div_exp_iff`: Theorem 2, eq. (3).
- `ClassicalUncertaintyPrinciple.det_prod`: eq. (4), the Poisson bracket is the Jacobian.
- `ClassicalUncertaintyPrinciple.hbar_div_exp_mul_exp_entropy_add_le`,
  `ClassicalUncertaintyPrinciple.hbar_div_exp_mul_exp_le_sd_mul_sd`: Theorem 2, eq. (5).
- `ClassicalUncertaintyPrinciple.exists_not_lowerEntropicBound`: the final remark.

## iii. Table of contents

- A. Ensembles, entropy and moments
- B. Gibbs' inequality against Gaussians
- C. Canonical variables: Theorem 2, eq. (3)
- D. Non-conjugate variables: Theorem 2, eq. (5)
- E. CUP does not imply ZENT
-/

open Real MeasureTheory ProbabilityTheory Set

open scoped NNReal

@[expose] public noncomputable section

namespace ClassicalUncertaintyPrinciple

/-! ### A. Ensembles, entropy and moments -/

section Ensembles

variable {X : Type*} [MeasurableSpace X]

/-- A statistical ensemble: a probability density with finite entropy. -/
structure IsEnsemble (ρ : X → ℝ) (μ : Measure X := by volume_tac) : Prop where
  nonneg : ∀ x, 0 ≤ ρ x
  integral_eq_one : ∫ x, ρ x ∂μ = 1
  integrable_negMulLog : Integrable (fun x => negMulLog (ρ x)) μ

/-- The Gibbs/Shannon entropy `S_c[ρ] = -∫ ρ log (c ρ) dμ` relative to a cell of size `c`. -/
def entropy (c : ℝ) (ρ : X → ℝ) (μ : Measure X := by volume_tac) : ℝ :=
  ∫ x, -(ρ x * log (c * ρ x)) ∂μ

/-- The mean `E[f] = ∫ f ρ dμ` of a variable `f`. -/
def mean (ρ f : X → ℝ) (μ : Measure X := by volume_tac) : ℝ := ∫ x, f x * ρ x ∂μ

/-- The variance `σ_f² = ∫ (f - E[f])² ρ dμ`. -/
def var (ρ f : X → ℝ) (μ : Measure X := by volume_tac) : ℝ :=
  ∫ x, (f x - mean ρ f μ) ^ 2 * ρ x ∂μ

/-- The standard deviation `σ_f`. -/
def sd (ρ f : X → ℝ) (μ : Measure X := by volume_tac) : ℝ := √(var ρ f μ)

/-- `ħ = h / 2π`. -/
def hbar (h : ℝ) : ℝ := h / (2 * π)

variable {μ : Measure X} {ρ f : X → ℝ} {c : ℝ}

lemma IsEnsemble.integrable (hρ : IsEnsemble ρ μ) : Integrable ρ μ :=
  Integrable.of_integral_ne_zero (by rw [hρ.integral_eq_one]; norm_num)

lemma IsEnsemble.integrable_mul (hρ : IsEnsemble ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) : Integrable (fun x => f x * ρ x) μ := by
  refine (hf2.add hρ.integrable).mono' (hf.aestronglyMeasurable.mul hρ.integrable.1)
    (ae_of_all _ fun x => ?_)
  have hx : ‖f x‖ ≤ f x ^ 2 + 1 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (f x), abs_nonneg (f x)]
  rw [norm_mul, Real.norm_of_nonneg (hρ.nonneg x), Pi.add_apply, ← add_one_mul]
  exact mul_le_mul_of_nonneg_right hx (hρ.nonneg x)

lemma IsEnsemble.integrable_sub_sq_mul (hρ : IsEnsemble ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) (a : ℝ) :
    Integrable (fun x => (f x - a) ^ 2 * ρ x) μ := by
  have h := (hf2.sub ((hρ.integrable_mul hf hf2).const_mul (2 * a))).add
    (hρ.integrable.const_mul (a ^ 2))
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

lemma var_nonneg (hρ : IsEnsemble ρ μ) : 0 ≤ var ρ f μ :=
  integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hρ.nonneg x)

/-- `S_c[ρ] = -∫ ρ log ρ - log c`. -/
lemma entropy_eq (hρ : IsEnsemble ρ μ) (hc : 0 < c) :
    entropy c ρ μ = ∫ x, negMulLog (ρ x) ∂μ - log c := by
  have h : ∀ x, -(ρ x * log (c * ρ x)) = negMulLog (ρ x) - log c * ρ x := fun x => by
    rcases (hρ.nonneg x).eq_or_lt with h | h
    · simp [← h]
    · rw [log_mul hc.ne' h.ne', negMulLog]
      ring
  simp_rw [entropy, h]
  rw [integral_sub hρ.integrable_negMulLog (hρ.integrable.const_mul _), integral_const_mul,
    hρ.integral_eq_one, mul_one]

/-- The uniform distribution on `U`. -/
def uniform (μ : Measure X) (U : Set X) : X → ℝ := U.indicator fun _ => (μ.real U)⁻¹

variable {U : Set X}

lemma isEnsemble_uniform (hU : MeasurableSet U) (hpos : 0 < μ.real U) :
    IsEnsemble (uniform μ U) μ where
  nonneg x := indicator_nonneg (fun _ _ => inv_nonneg.2 hpos.le) x
  integral_eq_one := by
    rw [uniform, integral_indicator hU, setIntegral_const, smul_eq_mul, mul_inv_cancel₀ hpos.ne']
  integrable_negMulLog := by
    have hfin : μ U ≠ ⊤ := fun h => by simp [measureReal_def, h] at hpos
    have h : (fun x => negMulLog (uniform μ U x)) =
        U.indicator fun _ => negMulLog (μ.real U)⁻¹ := by
      ext x
      by_cases hx : x ∈ U <;> simp [uniform, hx]
    rw [h]
    exact (integrableOn_const hfin).integrable_indicator hU

/-- **Corollary 1.** The uniform distribution on `U` has entropy `log (μ(U) / c)`. -/
theorem entropy_uniform (hU : MeasurableSet U) (hpos : 0 < μ.real U) (hc : 0 < c) :
    entropy c (uniform μ U) μ = log (μ.real U / c) := by
  have h : (fun x => -(uniform μ U x * log (c * uniform μ U x))) =
      U.indicator fun _ => -((μ.real U)⁻¹ * log (c * (μ.real U)⁻¹)) := by
    ext x
    by_cases hx : x ∈ U <;> simp [uniform, hx]
  rw [entropy, h, integral_indicator hU, setIntegral_const, smul_eq_mul,
    log_mul hc.ne' (inv_pos.2 hpos).ne', log_inv, log_div hpos.ne' hc.ne']
  field_simp
  ring

/-- **Corollary 1.** The uniform distribution on `U` has zero entropy iff `μ(U) = c`. -/
theorem entropy_uniform_eq_zero_iff (hU : MeasurableSet U) (hpos : 0 < μ.real U)
    (hc : 0 < c) : entropy c (uniform μ U) μ = 0 ↔ μ.real U = c := by
  rw [entropy_uniform hU hpos hc]
  constructor
  · intro h
    rcases log_eq_zero.1 h with h | h | h
    · simp [div_eq_zero_iff, hpos.ne', hc.ne'] at h
    · exact (div_eq_one_iff_eq hc.ne').1 h
    · have : 0 < μ.real U / c := div_pos hpos hc
      linarith
  · intro h
    rw [h, div_self hc.ne', log_one]

/-- Corollary 1 for `n` DOFs: on the phase space `(ℝ²)ⁿ` the cell is `hⁿ`. -/
theorem entropy_uniform_phaseSpace {n : ℕ} {h : ℝ} {U : Set (Fin n → ℝ × ℝ)}
    (hU : MeasurableSet U) (hpos : 0 < volume.real U) (hh : 0 < h) :
    entropy (h ^ n) (uniform volume U) = log (volume.real U / h ^ n) :=
  entropy_uniform hU hpos (pow_pos hh n)

end Ensembles

/-! ### B. Gibbs' inequality against Gaussians -/

section Gibbs

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ f g J : X → ℝ}

/-- The product of a Gaussian density in the first coordinate and one in the second. -/
def gaussProd (a : ℝ) (v : ℝ≥0) (b : ℝ) (w : ℝ≥0) (y : ℝ × ℝ) : ℝ :=
  gaussianPDFReal a v y.1 * gaussianPDFReal b w y.2

variable {a b : ℝ} {v w : ℝ≥0}

lemma gaussProd_pos (hv : v ≠ 0) (hw : w ≠ 0) (y : ℝ × ℝ) : 0 < gaussProd a v b w y :=
  mul_pos (gaussianPDFReal_pos _ _ _ hv) (gaussianPDFReal_pos _ _ _ hw)

/-- A weight `J` such that every product of Gaussians in the variables `(f, g)`, multiplied by
`J`, is a subprobability density on `X`. -/
def IsGaussWeight (J f g : X → ℝ) (μ : Measure X) : Prop :=
  ∀ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 → w ≠ 0 →
    Integrable (fun x => J x * gaussProd a v b w (f x, g x)) μ ∧
      ∫ x, J x * gaussProd a v b w (f x, g x) ∂μ ≤ 1

lemma IsGaussWeight.swap (hW : IsGaussWeight J f g μ) : IsGaussWeight J g f μ := by
  intro a b v w hv hw
  simpa [gaussProd, mul_comm (gaussianPDFReal a v _)] using hW b a w v hw hv

/-- The hypotheses on an ensemble and two variables `f, g` with weight `J`. -/
structure Hyp (μ : Measure X) (ρ f g J : X → ℝ) : Prop where
  ensemble : IsEnsemble ρ μ
  measurable_fst : Measurable f
  measurable_snd : Measurable g
  integrable_fst : Integrable (fun x => f x ^ 2 * ρ x) μ
  integrable_snd : Integrable (fun x => g x ^ 2 * ρ x) μ
  pos : ∀ x, 0 < J x
  integrable_log : Integrable (fun x => ρ x * log (J x)) μ
  weight : IsGaussWeight J f g μ

lemma Hyp.swap (H : Hyp μ ρ f g J) : Hyp μ ρ g f J :=
  ⟨H.ensemble, H.measurable_snd, H.measurable_fst, H.integrable_snd, H.integrable_fst, H.pos,
    H.integrable_log, H.weight.swap⟩

/-- `-∫ ρ log G` for the Gaussian weight `G = J · g_{a,v}(f) · g_{b,w}(g)`. -/
lemma Hyp.integral_mul_log (H : Hyp μ ρ f g J) (a b : ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    Integrable (fun x => ρ x * log (J x * gaussProd a v b w (f x, g x))) μ ∧
      -∫ x, ρ x * log (J x * gaussProd a v b w (f x, g x)) ∂μ =
        log (2 * π * v) / 2 + log (2 * π * w) / 2 + (∫ x, (f x - a) ^ 2 * ρ x ∂μ) / (2 * v) +
          (∫ x, (g x - b) ^ 2 * ρ x ∂μ) / (2 * w) - ∫ x, ρ x * log (J x) ∂μ := by
  have hρ := H.ensemble
  have hfa := hρ.integrable_sub_sq_mul H.measurable_fst H.integrable_fst a
  have hgb := hρ.integrable_sub_sq_mul H.measurable_snd H.integrable_snd b
  set C := log (2 * π * v) / 2 + log (2 * π * w) / 2
  have hpt : (fun x => ρ x * log (J x * gaussProd a v b w (f x, g x))) = fun x =>
      ρ x * log (J x) - C * ρ x - (2 * v : ℝ)⁻¹ * ((f x - a) ^ 2 * ρ x) -
        (2 * w : ℝ)⁻¹ * ((g x - b) ^ 2 * ρ x) := by
    ext x
    rw [log_mul (H.pos x).ne' (gaussProd_pos hv hw _).ne', gaussProd,
      log_mul (gaussianPDFReal_pos _ _ _ hv).ne' (gaussianPDFReal_pos _ _ _ hw).ne',
      log_gaussianPDFReal hv, log_gaussianPDFReal hw]
    simp only [C]
    field_simp
    ring
  have h1 : Integrable (fun x => ρ x * log (J x) - C * ρ x) μ :=
    H.integrable_log.sub (hρ.integrable.const_mul C)
  have h2 : Integrable (fun x => ρ x * log (J x) - C * ρ x -
      (2 * v : ℝ)⁻¹ * ((f x - a) ^ 2 * ρ x)) μ := h1.sub (hfa.const_mul _)
  refine ⟨hpt ▸ h2.sub (hgb.const_mul _), ?_⟩
  rw [hpt, integral_sub h2 (hgb.const_mul _), integral_sub h1 (hfa.const_mul _),
    integral_sub H.integrable_log (hρ.integrable.const_mul C), integral_const_mul,
    integral_const_mul, integral_const_mul, hρ.integral_eq_one]
  ring

/-- Gibbs' inequality against `G = J · g_{a,v}(f) · g_{b,w}(g)`. -/
lemma Hyp.integral_negMulLog_le (H : Hyp μ ρ f g J) (a b : ℝ) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∫ x, negMulLog (ρ x) ∂μ ≤
      log (2 * π * v) / 2 + log (2 * π * w) / 2 + (∫ x, (f x - a) ^ 2 * ρ x ∂μ) / (2 * v) +
        (∫ x, (g x - b) ^ 2 * ρ x ∂μ) / (2 * w) - ∫ x, ρ x * log (J x) ∂μ := by
  obtain ⟨hi, he⟩ := H.integral_mul_log a b hv hw
  rw [← he]
  exact MeasureTheory.integral_negMulLog_le (ae_of_all _ H.ensemble.nonneg)
    H.ensemble.integral_eq_one (ae_of_all _ fun x => mul_pos (H.pos x) (gaussProd_pos hv hw _))
    (H.weight a b v w hv hw).1 (H.weight a b v w hv hw).2 H.ensemble.integrable_negMulLog hi

/-- A variable of an ensemble with finite entropy has positive variance: otherwise Gibbs'
inequality against ever narrower Gaussians would bound the entropy by `-∞`. -/
lemma Hyp.var_pos_fst (H : Hyp μ ρ f g J) : 0 < var ρ f μ := by
  refine (var_nonneg H.ensemble).lt_of_ne fun h0 => ?_
  set S := ∫ x, negMulLog (ρ x) ∂μ
  set K := log (2 * π * (1 : ℝ≥0)) / 2 + (∫ x, (g x - 0) ^ 2 * ρ x ∂μ) / (2 * (1 : ℝ≥0)) -
    ∫ x, ρ x * log (J x) ∂μ
  set t := 2 * (S - K - 1)
  have hv : (exp t / (2 * π)).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]
    positivity
  have hb := H.integral_negMulLog_le (mean ρ f μ) 0 hv one_ne_zero
  rw [← var, ← h0, Real.coe_toNNReal _ (by positivity), mul_div_cancel₀ _ (by positivity),
    log_exp] at hb
  have hS : S = ∫ x, negMulLog (ρ x) ∂μ := rfl
  simp only [t, K, zero_div, add_zero] at hb
  linarith

lemma Hyp.var_pos_snd (H : Hyp μ ρ f g J) : 0 < var ρ g μ := H.swap.var_pos_fst

/-- The Gaussian weight with the means and variances of `f, g` under `ρ`. -/
def optWeight (μ : Measure X) (ρ f g J : X → ℝ) (x : X) : ℝ :=
  J x * gaussProd (mean ρ f μ) (var ρ f μ).toNNReal (mean ρ g μ) (var ρ g μ).toNNReal (f x, g x)

lemma Hyp.var_toNNReal_ne_zero_fst (H : Hyp μ ρ f g J) : (var ρ f μ).toNNReal ≠ 0 := by
  simpa using H.var_pos_fst

lemma Hyp.var_toNNReal_ne_zero_snd (H : Hyp μ ρ f g J) : (var ρ g μ).toNNReal ≠ 0 := by
  simpa using H.var_pos_snd

lemma log_two_pi_exp_mul_sd {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    log (2 * π * exp 1 * (√s * √t)) =
      log (2 * π * s) / 2 + log (2 * π * t) / 2 + s / (2 * s) + t / (2 * t) := by
  have h2π : (2 * π : ℝ) ≠ 0 := by positivity
  rw [log_mul (mul_ne_zero h2π (exp_pos 1).ne') (by positivity), log_mul h2π (exp_pos 1).ne',
    log_exp, log_mul (sqrt_pos.2 hs).ne' (sqrt_pos.2 ht).ne', log_sqrt hs.le, log_sqrt ht.le,
    log_mul h2π hs.ne', log_mul h2π ht.ne']
  field_simp
  ring

/-- `-∫ ρ log G = log (2π e σ_f σ_g) - E[log J]` for the optimal Gaussian weight. -/
lemma Hyp.integral_mul_log_optWeight (H : Hyp μ ρ f g J) :
    Integrable (fun x => ρ x * log (optWeight μ ρ f g J x)) μ ∧
      -∫ x, ρ x * log (optWeight μ ρ f g J x) ∂μ =
        log (2 * π * exp 1 * (sd ρ f μ * sd ρ g μ)) - ∫ x, ρ x * log (J x) ∂μ := by
  obtain ⟨hi, he⟩ := H.integral_mul_log (mean ρ f μ) (mean ρ g μ) H.var_toNNReal_ne_zero_fst
    H.var_toNNReal_ne_zero_snd
  refine ⟨hi, ?_⟩
  simp only [optWeight]
  rw [he, sd, sd, log_two_pi_exp_mul_sd H.var_pos_fst H.var_pos_snd,
    Real.coe_toNNReal _ H.var_pos_fst.le, Real.coe_toNNReal _ H.var_pos_snd.le, var, var]

lemma Hyp.optWeight_pos (H : Hyp μ ρ f g J) (x : X) : 0 < optWeight μ ρ f g J x :=
  mul_pos (H.pos x) (gaussProd_pos H.var_toNNReal_ne_zero_fst H.var_toNNReal_ne_zero_snd _)

/-- `-∫ ρ log ρ ≤ log (2π e σ_f σ_g) - E[log J]`. -/
lemma Hyp.integral_negMulLog_le_log (H : Hyp μ ρ f g J) :
    ∫ x, negMulLog (ρ x) ∂μ ≤
      log (2 * π * exp 1 * (sd ρ f μ * sd ρ g μ)) - ∫ x, ρ x * log (J x) ∂μ := by
  obtain ⟨hi, he⟩ := H.integral_mul_log_optWeight
  have hW := H.weight (mean ρ f μ) (mean ρ g μ) _ _ H.var_toNNReal_ne_zero_fst
    H.var_toNNReal_ne_zero_snd
  rw [← he]
  exact MeasureTheory.integral_negMulLog_le (ae_of_all _ H.ensemble.nonneg)
    H.ensemble.integral_eq_one (ae_of_all _ H.optWeight_pos) hW.1 hW.2
    H.ensemble.integrable_negMulLog hi

lemma Hyp.sd_mul_sd_pos (H : Hyp μ ρ f g J) : 0 < sd ρ f μ * sd ρ g μ :=
  mul_pos (sqrt_pos.2 H.var_pos_fst) (sqrt_pos.2 H.var_pos_snd)

variable {h s t : ℝ}

lemma hbar_div_exp_pos (hh : 0 < h) : 0 < hbar h / exp 1 :=
  div_pos (div_pos hh (by positivity)) (exp_pos 1)

lemma hbar_div_exp_mul_exp (h t : ℝ) :
    hbar h / exp 1 * exp t = exp t * h / (2 * π * exp 1) := by
  unfold hbar
  field_simp

lemma hbar_div_exp_mul_exp_le_iff (hh : 0 < h) (hs : 0 < s) :
    hbar h / exp 1 * exp t ≤ s ↔ t ≤ log (2 * π * exp 1 * s) - log h := by
  rw [← log_div (by positivity) hh.ne', le_log_iff_exp_le (by positivity), le_div_iff₀ hh,
    hbar_div_exp_mul_exp, div_le_iff₀ (by positivity), mul_comm s]

lemma hbar_div_exp_mul_exp_eq_iff (hh : 0 < h) (hs : 0 < s) :
    s = hbar h / exp 1 * exp t ↔ t = log (2 * π * exp 1 * s) - log h := by
  rw [← log_div (by positivity) hh.ne', hbar_div_exp_mul_exp]
  constructor
  · intro H
    rw [H, show 2 * π * exp 1 * (exp t * h / (2 * π * exp 1)) / h = exp t by field_simp,
      log_exp]
  · intro H
    rw [H, exp_log (by positivity)]
    field_simp

/-- **The Gaussian bound.** `σ_f σ_g ≥ (ħ / e) e^{S_h[ρ] + E[log J]}`. -/
theorem Hyp.hbar_div_exp_mul_exp_le (H : Hyp μ ρ f g J) (hh : 0 < h) :
    hbar h / exp 1 * exp (entropy h ρ μ + ∫ x, ρ x * log (J x) ∂μ) ≤
      sd ρ f μ * sd ρ g μ := by
  rw [hbar_div_exp_mul_exp_le_iff hh H.sd_mul_sd_pos, entropy_eq H.ensemble hh]
  linarith [H.integral_negMulLog_le_log]

end Gibbs

/-! ### C. Canonical variables: Theorem 2, eq. (3) -/

section Canonical

variable {ρ : ℝ × ℝ → ℝ} {h : ℝ} {a b : ℝ} {v w : ℝ≥0}

lemma integrable_gaussProd (a b : ℝ) (v w : ℝ≥0) : Integrable (gaussProd a v b w) := by
  rw [Measure.volume_eq_prod]
  exact (integrable_gaussianPDFReal a v).mul_prod (integrable_gaussianPDFReal b w)

lemma integral_gaussProd (hv : v ≠ 0) (hw : w ≠ 0) : ∫ y, gaussProd a v b w y = 1 := by
  simp only [gaussProd]
  rw [Measure.volume_eq_prod, integral_prod_mul,
    integral_gaussianPDFReal_eq_one a hv, integral_gaussianPDFReal_eq_one b hw, one_mul]

lemma isGaussWeight_one :
    IsGaussWeight (fun _ => 1) Prod.fst Prod.snd (volume : Measure (ℝ × ℝ)) := by
  intro a b v w hv hw
  simp only [one_mul, Prod.mk.eta]
  exact ⟨integrable_gaussProd a b v w, (integral_gaussProd hv hw).le⟩

/-- The hypotheses for one DOF in canonical variables `(q, p)`: finite entropy and finite
second moments. -/
lemma hyp_canonical (hρ : IsEnsemble ρ) (hq : Integrable fun x => x.1 ^ 2 * ρ x)
    (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    Hyp volume ρ Prod.fst Prod.snd fun _ => 1 :=
  ⟨hρ, measurable_fst, measurable_snd, hq, hp, fun _ => one_pos, by simp, isGaussWeight_one⟩

/-- **Gaussians minimize the uncertainty at given entropy.** `σ_q σ_p ≥ (ħ / e) e^{S_h[ρ]}`. -/
theorem hbar_div_exp_mul_exp_entropy_le (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    hbar h / exp 1 * exp (entropy h ρ) ≤ sd ρ Prod.fst * sd ρ Prod.snd := by
  simpa using (hyp_canonical hρ hq hp).hbar_div_exp_mul_exp_le hh

lemma mean_fst_gaussProd (hρ : ρ =ᵐ[volume] gaussProd a v b w) (hv : v ≠ 0) (hw : w ≠ 0) :
    mean ρ Prod.fst = a := by
  rw [mean, integral_congr_ae (hρ.mono fun x hx => by rw [hx]), Measure.volume_eq_prod]
  simp_rw [gaussProd, ← mul_assoc]
  rw [integral_prod_mul (fun t => t * gaussianPDFReal a v t) (gaussianPDFReal b w),
    integral_mul_gaussianPDFReal hv, integral_gaussianPDFReal_eq_one b hw, mul_one]

lemma mean_snd_gaussProd (hρ : ρ =ᵐ[volume] gaussProd a v b w) (hv : v ≠ 0) (hw : w ≠ 0) :
    mean ρ Prod.snd = b := by
  rw [mean, integral_congr_ae (hρ.mono fun x hx => by rw [hx]), Measure.volume_eq_prod]
  simp_rw [gaussProd, mul_left_comm _ (gaussianPDFReal a v _)]
  rw [integral_prod_mul (gaussianPDFReal a v) (fun t => t * gaussianPDFReal b w t),
    integral_mul_gaussianPDFReal hw, integral_gaussianPDFReal_eq_one a hv, one_mul]

lemma var_fst_gaussProd (hρ : ρ =ᵐ[volume] gaussProd a v b w) (hv : v ≠ 0) (hw : w ≠ 0) :
    var ρ Prod.fst = v := by
  rw [var, mean_fst_gaussProd hρ hv hw, integral_congr_ae (hρ.mono fun x hx => by rw [hx]),
    Measure.volume_eq_prod]
  simp_rw [gaussProd, ← mul_assoc]
  rw [integral_prod_mul (fun t => (t - a) ^ 2 * gaussianPDFReal a v t) (gaussianPDFReal b w),
    integral_sub_sq_mul_gaussianPDFReal hv,
    integral_gaussianPDFReal_eq_one b hw, mul_one]

lemma var_snd_gaussProd (hρ : ρ =ᵐ[volume] gaussProd a v b w) (hv : v ≠ 0) (hw : w ≠ 0) :
    var ρ Prod.snd = w := by
  rw [var, mean_snd_gaussProd hρ hv hw, integral_congr_ae (hρ.mono fun x hx => by rw [hx]),
    Measure.volume_eq_prod]
  simp_rw [gaussProd, mul_left_comm _ (gaussianPDFReal a v _)]
  rw [integral_prod_mul (gaussianPDFReal a v) (fun t => (t - b) ^ 2 * gaussianPDFReal b w t),
    integral_sub_sq_mul_gaussianPDFReal hw,
    integral_gaussianPDFReal_eq_one a hv, one_mul]

/-- **Equality in the Gaussian bound.** `σ_q σ_p = (ħ / e) e^{S_h[ρ]}` exactly when `ρ` is a
product of Gaussians in `q` and `p`. -/
theorem sd_mul_sd_eq_iff (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    sd ρ Prod.fst * sd ρ Prod.snd = hbar h / exp 1 * exp (entropy h ρ) ↔
      ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧ ρ =ᵐ[volume] gaussProd a v b w := by
  have H := hyp_canonical hρ hq hp
  obtain ⟨hi, he⟩ := H.integral_mul_log_optWeight
  have hW := H.weight (mean ρ Prod.fst) (mean ρ Prod.snd) _ _ H.var_toNNReal_ne_zero_fst
    H.var_toNNReal_ne_zero_snd
  simp only [log_one, mul_zero, integral_zero, sub_zero] at he
  have hopt : optWeight volume ρ Prod.fst Prod.snd (fun _ => 1) =
      gaussProd (mean ρ Prod.fst) (var ρ Prod.fst).toNNReal (mean ρ Prod.snd)
        (var ρ Prod.snd).toNNReal := by
    ext x
    simp [optWeight]
  rw [hbar_div_exp_mul_exp_eq_iff hh H.sd_mul_sd_pos, entropy_eq hρ hh, sub_left_inj, ← he]
  constructor
  · intro heq
    have := ae_eq_of_integral_negMulLog_eq (ae_of_all _ hρ.nonneg) hρ.integral_eq_one
      (ae_of_all _ H.optWeight_pos) hW.1 hW.2 hρ.integrable_negMulLog hi heq
    rw [hopt] at this
    exact ⟨_, _, _, _, H.var_toNNReal_ne_zero_fst, H.var_toNNReal_ne_zero_snd, this⟩
  · rintro ⟨a, b, v, w, hv, hw, hρG⟩
    have hG : ρ =ᵐ[volume] optWeight volume ρ Prod.fst Prod.snd fun _ => 1 := by
      rw [hopt, mean_fst_gaussProd hρG hv hw, mean_snd_gaussProd hρG hv hw,
        var_fst_gaussProd hρG hv hw, var_snd_gaussProd hρG hv hw, Real.toNNReal_coe,
        Real.toNNReal_coe]
      exact hρG
    have h1 : ∫ x, negMulLog (ρ x) =
        ∫ x, negMulLog (optWeight volume ρ Prod.fst Prod.snd (fun _ => 1) x) :=
      integral_congr_ae (hG.fun_comp negMulLog)
    have h2 : ∫ x, ρ x * log (optWeight volume ρ Prod.fst Prod.snd (fun _ => 1) x) =
        ∫ x, optWeight volume ρ Prod.fst Prod.snd (fun _ => 1) x *
          log (optWeight volume ρ Prod.fst Prod.snd (fun _ => 1) x) :=
      integral_congr_ae (hG.mono fun x hx => by simp only [hx])
    rw [h1, h2, ← integral_neg]
    simp [negMulLog]

/-- Condition ZENT (lower entropic bound) for one DOF: `S_h[ρ] ≥ 0`. -/
def LowerEntropicBound (h : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop := 0 ≤ entropy h ρ

/-- Condition CUP (classical uncertainty principle) for one DOF: `σ_q σ_p ≥ ħ / e`. -/
def UncertaintyPrinciple (h : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  hbar h / exp 1 ≤ sd ρ Prod.fst * sd ρ Prod.snd

/-- **Theorem 2, eq. (3).** ZENT implies CUP. -/
theorem uncertaintyPrinciple_of_lowerEntropicBound (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x)
    (hZ : LowerEntropicBound h ρ) : UncertaintyPrinciple h ρ :=
  calc hbar h / exp 1 = hbar h / exp 1 * 1 := (mul_one _).symm
    _ ≤ hbar h / exp 1 * exp (entropy h ρ volume) :=
      mul_le_mul_of_nonneg_left (one_le_exp hZ) (hbar_div_exp_pos hh).le
    _ ≤ _ := hbar_div_exp_mul_exp_entropy_le hh hρ hq hp

/-- **Theorem 2, equality case.** Under ZENT, `σ_q σ_p = ħ / e` exactly for products of
Gaussians in `q` and `p` with `σ_q σ_p = ħ / e`. -/
theorem sd_mul_sd_eq_hbar_div_exp_iff (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x)
    (hZ : LowerEntropicBound h ρ) :
    sd ρ Prod.fst * sd ρ Prod.snd = hbar h / exp 1 ↔
      ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧ √(v : ℝ) * √(w : ℝ) = hbar h / exp 1 ∧
        ρ =ᵐ[volume] gaussProd a v b w := by
  have hb := hbar_div_exp_mul_exp_entropy_le hh hρ hq hp
  have hpos := hbar_div_exp_pos hh
  constructor
  · intro heq
    have hS : entropy h ρ = 0 := by
      refine le_antisymm ?_ hZ
      rw [heq, mul_le_iff_le_one_right hpos, exp_le_one_iff] at hb
      exact hb
    obtain ⟨a, b, v, w, hv, hw, hρG⟩ := (sd_mul_sd_eq_iff hh hρ hq hp).1 (by
      rw [hS, exp_zero, mul_one, heq])
    refine ⟨a, b, v, w, hv, hw, ?_, hρG⟩
    rw [← var_fst_gaussProd hρG hv hw, ← var_snd_gaussProd hρG hv hw]
    exact heq
  · rintro ⟨a, b, v, w, hv, hw, hvw, hρG⟩
    rw [sd, sd, var_fst_gaussProd hρG hv hw, var_snd_gaussProd hρG hv hw, hvw]

end Canonical

/-! ### D. Non-conjugate variables: Theorem 2, eq. (5) -/

section NonConjugate

variable {ρ f g : ℝ × ℝ → ℝ} {h : ℝ}

/-- Lebesgue measure on `ℝ²` is a Haar measure (seen through `volume = volume.prod volume`). -/
instance : Measure.IsAddHaarMeasure (volume : Measure (ℝ × ℝ)) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- The Poisson bracket `{f, g} = ∂_q f ∂_p g - ∂_p f ∂_q g`. -/
def poissonBracket (f g : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fderiv ℝ f x (1, 0) * fderiv ℝ g x (0, 1) - fderiv ℝ f x (0, 1) * fderiv ℝ g x (1, 0)

lemma poissonBracket_fst_snd (x : ℝ × ℝ) : poissonBracket Prod.fst Prod.snd x = 1 := by
  simp [poissonBracket, fderiv_fst, fderiv_snd]

/-- Eq. (4): the Poisson bracket is the Jacobian determinant of `(q, p) ↦ (f, g)`. -/
lemma det_prod (f' g' : ℝ × ℝ →L[ℝ] ℝ) :
    (f'.prod g').det = f' (1, 0) * g' (0, 1) - f' (0, 1) * g' (1, 0) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),
    Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]

/-- For an injective differentiable `(q, p) ↦ (f, g)`, `|{f, g}|` is a Gaussian weight. -/
lemma isGaussWeight_poissonBracket (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hinj : Function.Injective fun x => (f x, g x)) :
    IsGaussWeight (fun x => |poissonBracket f g x|) f g volume := by
  intro a b v w hv hw
  have hF : ∀ x ∈ univ, HasFDerivWithinAt (fun x => (f x, g x))
      ((fderiv ℝ f x).prod (fderiv ℝ g x)) univ x := fun x _ =>
    ((hf x).hasFDerivAt.prodMk (hg x).hasFDerivAt).hasFDerivWithinAt
  have hdet : ∀ x, ((fderiv ℝ f x).prod (fderiv ℝ g x)).det = poissonBracket f g x :=
    fun x => det_prod _ _
  have hi := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ
    hF hinj.injOn (gaussProd a v b w)).1 (integrable_gaussProd a b v w).integrableOn
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume MeasurableSet.univ hF
    hinj.injOn (gaussProd a v b w)
  simp only [hdet, smul_eq_mul, integrableOn_univ, Measure.restrict_univ] at hi he
  refine ⟨hi, ?_⟩
  rw [← he, ← integral_gaussProd hv hw]
  exact setIntegral_le_integral (integrable_gaussProd a b v w)
    (ae_of_all _ fun y => (gaussProd_pos hv hw y).le)

/-- **Theorem 2, eq. (5), for any ensemble.**
`σ_f σ_g ≥ (ħ / e) e^{S_h[ρ] + E[log |{f, g}|]}`. -/
theorem hbar_div_exp_mul_exp_entropy_add_le (hh : 0 < h) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hinj : Function.Injective fun x => (f x, g x))
    (hfg : ∀ x, poissonBracket f g x ≠ 0) (hρ : IsEnsemble ρ)
    (hf2 : Integrable fun x => f x ^ 2 * ρ x) (hg2 : Integrable fun x => g x ^ 2 * ρ x)
    (hlog : Integrable fun x => ρ x * log |poissonBracket f g x|) :
    hbar h / exp 1 * exp (entropy h ρ + ∫ x, ρ x * log |poissonBracket f g x|) ≤
      sd ρ f * sd ρ g :=
  Hyp.hbar_div_exp_mul_exp_le ⟨hρ, hf.continuous.measurable, hg.continuous.measurable, hf2, hg2,
    fun x => abs_pos.2 (hfg x), hlog, isGaussWeight_poissonBracket hf hg hinj⟩ hh

/-- **Theorem 2, eq. (5).** Under ZENT, `σ_f σ_g ≥ (ħ / e) e^{E[log |{f, g}|]}`. -/
theorem hbar_div_exp_mul_exp_le_sd_mul_sd (hh : 0 < h) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (hinj : Function.Injective fun x => (f x, g x))
    (hfg : ∀ x, poissonBracket f g x ≠ 0) (hρ : IsEnsemble ρ)
    (hf2 : Integrable fun x => f x ^ 2 * ρ x) (hg2 : Integrable fun x => g x ^ 2 * ρ x)
    (hlog : Integrable fun x => ρ x * log |poissonBracket f g x|)
    (hZ : LowerEntropicBound h ρ) :
    hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|) ≤ sd ρ f * sd ρ g := by
  refine le_trans ?_ (hbar_div_exp_mul_exp_entropy_add_le hh hf hg hinj hfg hρ hf2 hg2 hlog)
  exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (le_add_of_nonneg_left hZ))
    (hbar_div_exp_pos hh).le

end NonConjugate

/-! ### E. CUP does not imply ZENT -/

section Converse

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B U : Set X} {φ : X → ℝ} {L : ℝ}

/-- If `φ ≥ L` on `A ⊆ U` and `φ ≤ -L` on `B ⊆ U`, the uniform distribution on `U` has
`σ_φ² ≥ L² min(μ(A), μ(B)) / μ(U)`, whatever its mean. -/
lemma le_var_uniform (hA : MeasurableSet A) (hB : MeasurableSet B) (hAfin : μ A ≠ ⊤)
    (hBfin : μ B ≠ ⊤) (hAU : A ⊆ U) (hBU : B ⊆ U) (hL : 0 ≤ L) (hφA : ∀ x ∈ A, L ≤ φ x)
    (hφB : ∀ x ∈ B, φ x ≤ -L)
    (hint : Integrable (fun x => (φ x - mean (uniform μ U) φ μ) ^ 2 * uniform μ U x) μ) :
    L ^ 2 * (μ.real U)⁻¹ * min (μ.real A) (μ.real B) ≤ var (uniform μ U) φ μ := by
  set m := mean (uniform μ U) φ μ
  have hc : 0 ≤ (μ.real U)⁻¹ := inv_nonneg.2 measureReal_nonneg
  have key : ∀ C : Set X, MeasurableSet C → μ C ≠ ⊤ → C ⊆ U →
      (∀ x ∈ C, L ^ 2 ≤ (φ x - m) ^ 2) →
        L ^ 2 * (μ.real U)⁻¹ * μ.real C ≤ var (uniform μ U) φ μ := fun C hC hCfin hCU hCφ => by
    have hle : ∀ x, C.indicator (fun _ => L ^ 2 * (μ.real U)⁻¹) x ≤
        (φ x - m) ^ 2 * uniform μ U x := fun x => by
      by_cases hx : x ∈ C
      · simp only [indicator_of_mem hx, uniform, indicator_of_mem (hCU hx)]
        exact mul_le_mul_of_nonneg_right (hCφ x hx) hc
      · rw [indicator_of_notMem hx]
        exact mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ => hc) x)
    calc L ^ 2 * (μ.real U)⁻¹ * μ.real C
        = ∫ x, C.indicator (fun _ => L ^ 2 * (μ.real U)⁻¹) x ∂μ := by
          rw [integral_indicator_const _ hC, smul_eq_mul, mul_comm]
      _ ≤ var (uniform μ U) φ μ :=
          integral_mono ((integrableOn_const hCfin).integrable_indicator hC) hint hle
  by_cases hm : 0 ≤ m
  · refine le_trans ?_ (key B hB hBfin hBU fun x hx => ?_)
    · exact mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg (sq_nonneg L) hc)
    · nlinarith [hφB x hx]
  · refine le_trans ?_ (key A hA hAfin hAU fun x hx => ?_)
    · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg (sq_nonneg L) hc)
    · nlinarith [hφA x hx]

/-- The square `[a, a + ε]²`. -/
def square (a ε : ℝ) : Set (ℝ × ℝ) := Icc a (a + ε) ×ˢ Icc a (a + ε)

lemma isCompact_square (a ε : ℝ) : IsCompact (square a ε) := isCompact_Icc.prod isCompact_Icc

lemma measurableSet_square (a ε : ℝ) : MeasurableSet (square a ε) :=
  measurableSet_Icc.prod measurableSet_Icc

lemma volume_real_square (a : ℝ) {ε : ℝ} (hε : 0 ≤ ε) : volume.real (square a ε) = ε ^ 2 := by
  rw [measureReal_def, square, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc,
    add_sub_cancel_left, ENNReal.toReal_mul, ENNReal.toReal_ofReal hε, sq]

lemma integrable_mul_uniform {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKm : MeasurableSet K)
    {ψ : ℝ × ℝ → ℝ} (hψ : Continuous ψ) : Integrable fun x => ψ x * uniform volume K x := by
  have h : (fun x => ψ x * uniform volume K x) =
      K.indicator fun x => ψ x * (volume.real K)⁻¹ := by
    ext x
    by_cases hx : x ∈ K <;> simp [uniform, hx]
  rw [h]
  exact ((hψ.mul continuous_const).continuousOn.integrableOn_compact hK).integrable_indicator hKm

/-- **CUP does not imply ZENT.** The uniform distribution on the squares `[L, L + ε]²` and
`[-L - ε, -L]²` with `ε = √h / 2` and `L = √h` has entropy `log ½ < 0`, while
`σ_q σ_p ≥ h / 2 ≥ ħ / e`. -/
theorem exists_not_lowerEntropicBound {h : ℝ} (hh : 0 < h) :
    ∃ ρ : ℝ × ℝ → ℝ, IsEnsemble ρ ∧ (Integrable fun x => x.1 ^ 2 * ρ x) ∧
      (Integrable fun x => x.2 ^ 2 * ρ x) ∧ UncertaintyPrinciple h ρ ∧
        ¬ LowerEntropicBound h ρ := by
  set ε := √h / 2
  set L := √h
  have hε : 0 ≤ ε := by positivity
  have hL : 0 < L := sqrt_pos.2 hh
  have hε2 : ε ^ 2 = h / 4 := by rw [div_pow, sq_sqrt hh.le]; norm_num
  have hL2 : L ^ 2 = h := sq_sqrt hh.le
  set A := square L ε
  set B := square (-L - ε) ε
  set U := A ∪ B
  have hA := measurableSet_square L ε
  have hB := measurableSet_square (-L - ε) ε
  have hAfin : volume A ≠ ⊤ := (isCompact_square _ _).measure_lt_top.ne
  have hBfin : volume B ≠ ⊤ := (isCompact_square _ _).measure_lt_top.ne
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro x ⟨⟨hx, -⟩, -⟩ ⟨⟨-, hx'⟩, -⟩
    linarith
  have hvA : volume.real A = h / 4 := by rw [volume_real_square _ hε, hε2]
  have hvB : volume.real B = h / 4 := by rw [volume_real_square _ hε, hε2]
  have hvU : volume.real U = h / 2 := by
    rw [measureReal_union hdisj hB hAfin hBfin, hvA, hvB]
    ring
  have hU : MeasurableSet U := hA.union hB
  have hUc : IsCompact U := (isCompact_square _ _).union (isCompact_square _ _)
  have hpos : 0 < volume.real U := by rw [hvU]; positivity
  have hρ := isEnsemble_uniform hU hpos
  have hq := integrable_mul_uniform hUc hU (continuous_fst.pow 2)
  have hp := integrable_mul_uniform hUc hU (continuous_snd.pow 2)
  have hvar : ∀ φ : ℝ × ℝ → ℝ, Continuous φ → (∀ x ∈ A, L ≤ φ x) → (∀ x ∈ B, φ x ≤ -L) →
      (Integrable fun x => φ x ^ 2 * uniform volume U x) →
        h / 2 ≤ var (uniform volume U) φ := fun φ hφ hφA hφB hφ2 => by
    have := le_var_uniform hA hB hAfin hBfin subset_union_left subset_union_right hL.le hφA
      hφB (hρ.integrable_sub_sq_mul hφ.measurable hφ2 _)
    rw [hvA, hvB, min_self, hvU, hL2] at this
    convert this using 1
    field_simp
    ring
  have hvq := hvar Prod.fst continuous_fst (fun x hx => hx.1.1)
    (fun x hx => by linarith [hx.1.2]) hq
  have hvp := hvar Prod.snd continuous_snd (fun x hx => hx.2.1)
    (fun x hx => by linarith [hx.2.2]) hp
  refine ⟨uniform volume U, hρ, hq, hp, ?_, ?_⟩
  · have hsq : √(h / 2) * √(h / 2) = h / 2 := mul_self_sqrt (by positivity)
    have h1 : hbar h / exp 1 ≤ h / 2 := by
      rw [hbar, div_div]
      refine div_le_div_of_nonneg_left hh.le (by norm_num) ?_
      nlinarith [two_le_pi, add_one_le_exp (1 : ℝ)]
    refine h1.trans (hsq ▸ mul_le_mul (sqrt_le_sqrt hvq) (sqrt_le_sqrt hvp)
      (sqrt_nonneg _) (sqrt_nonneg _))
  · rw [LowerEntropicBound, entropy_uniform hU hpos hh, hvU, not_le]
    rw [show h / 2 / h = 1 / 2 by field_simp]
    exact log_neg (by norm_num) (by norm_num)

end Converse

end ClassicalUncertaintyPrinciple
