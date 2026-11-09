/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.InformationTheory.EntropyVariation
public import ForMathlib.InformationTheory.MarginalEntropy
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

The brief's own route is formalized as well. Along the variations `ρ (1 + t φ)`, `φ` bounded,
the first variation of its Lagrangian `σ_q² σ_p² + λ₁ (∫ ρ - 1) + λ₂ (S_h[ρ] - S)` is the
brief's `δL = ∫ δρ [(q - μ_q)² σ_p² + σ_q² (p - μ_p)² + λ₁ - λ₂ (log (h ρ) + 1)]`, with
`δρ = ρ φ`. For `ρ > 0` a.e. it vanishes in every direction exactly when `ρ` is the product
of Gaussians with the means and variances of `ρ`, `λ₂ = -2 σ_q² σ_p²` and
`λ₁ = λ₂ (1 + log (ħ / (σ_q σ_p)))`. So the Gaussians are the only critical points; that
they minimize comes from Gibbs' inequality. The variations `ρ φ` vanish where `ρ` does, so
`ρ > 0` must be assumed: the entropy has no derivative in directions that move mass to
`{ρ = 0}`.

For several DOFs, on the phase space `(ℝ²)ⁿ⁺¹`, ZENT is a condition on the marginal `ρᵢ` of each
DOF `i`, the integral of `ρ` over the other DOFs. The marginal is again an ensemble: finite
second moments of the other DOFs give it finite entropy, by Gibbs' inequality against a
Gaussian in the integrated variables. Its means and variances are those of `qᵢ, pᵢ` under `ρ`,
so Theorem 2 for one DOF applies to each `ρᵢ`.

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
- `ClassicalUncertaintyPrinciple.hasDerivAt_lagrangian`: the first variation `δL`.
- `ClassicalUncertaintyPrinciple.hasDerivAt_lagrangian_zero_iff`: its critical points are
  exactly the products of Gaussians.
- `ClassicalUncertaintyPrinciple.sd_mul_sd_eq_of_hasDerivAt_lagrangian`: at a critical point,
  `σ_q σ_p = (ħ / e) e^{S_h[ρ]}`.
- `ClassicalUncertaintyPrinciple.isEnsemble_marginal`: the marginal of a DOF is an ensemble.
- `ClassicalUncertaintyPrinciple.uncertaintyPrinciplePhaseSpace_of_lowerEntropicBoundPhaseSpace`,
  `ClassicalUncertaintyPrinciple.sd_mul_sd_eq_hbar_div_exp_iff_marginal`: Theorem 2 for several
  DOFs.

## iii. Table of contents

- A. Ensembles, entropy and moments
- B. Gibbs' inequality against Gaussians
- C. Canonical variables: Theorem 2, eq. (3)
- D. Non-conjugate variables: Theorem 2, eq. (5)
- E. CUP does not imply ZENT
- F. The Lagrange computation
- G. Several degrees of freedom
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

/-! ### F. The Lagrange computation -/

section Variation

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ f g φ : X → ℝ} {C c : ℝ}

lemma integrable_mul_one_add (hρ : Integrable ρ μ) (hφ : AEStronglyMeasurable φ μ)
    (hC : ∀ x, |φ x| ≤ C) (t : ℝ) : Integrable (fun x => ρ x * (1 + t * φ x)) μ :=
  hρ.mul_bdd (aestronglyMeasurable_const.add (hφ.const_mul t)) (c := 1 + |t| * C)
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      calc |1 + t * φ x| ≤ |1| + |t * φ x| := abs_add_le _ _
        _ ≤ 1 + |t| * C := by
          rw [abs_one, abs_mul]
          exact add_le_add_right (mul_le_mul_of_nonneg_left (hC x) (abs_nonneg t)) 1)

/-- The integral of `g` against the variation `ρ (1 + t φ)` is affine in `t`. -/
lemma integral_mul_one_add (hg : Integrable (fun x => g x * ρ x) μ)
    (hφ : AEStronglyMeasurable φ μ) (hC : ∀ x, |φ x| ≤ C) (t : ℝ) :
    Integrable (fun x => g x * (ρ x * φ x)) μ ∧
      Integrable (fun x => g x * (ρ x * (1 + t * φ x))) μ ∧
      ∫ x, g x * (ρ x * (1 + t * φ x)) ∂μ =
        ∫ x, g x * ρ x ∂μ + t * ∫ x, g x * (ρ x * φ x) ∂μ := by
  have h1 : Integrable (fun x => g x * (ρ x * φ x)) μ :=
    (hg.mul_bdd hφ (c := C) (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hC x))).congr
      (ae_of_all _ fun x => by simp only; ring)
  refine ⟨h1, (integrable_mul_one_add hg hφ hC t).congr
    (ae_of_all _ fun x => by simp only; ring), ?_⟩
  rw [← integral_const_mul, ← integral_add hg (h1.const_mul t)]
  congr 1
  ext x
  ring

/-- `∫ (f - m)² w = ∫ f² w - 2 m ∫ f w + m² ∫ w`. -/
lemma integral_sub_sq_mul_eq {w : X → ℝ} (hw : Integrable w μ)
    (hfw : Integrable (fun x => f x * w x) μ) (hf2w : Integrable (fun x => f x ^ 2 * w x) μ)
    (m : ℝ) :
    ∫ x, (f x - m) ^ 2 * w x ∂μ =
      ∫ x, f x ^ 2 * w x ∂μ - 2 * m * ∫ x, f x * w x ∂μ + m ^ 2 * ∫ x, w x ∂μ := by
  calc ∫ x, (f x - m) ^ 2 * w x ∂μ
      = ∫ x, f x ^ 2 * w x - 2 * m * (f x * w x) + m ^ 2 * w x ∂μ := by
        congr 1
        ext x
        ring
    _ = _ := by
        rw [integral_add, integral_sub, integral_const_mul, integral_const_mul]
        all_goals first
          | exact hf2w
          | exact hfw.const_mul _
          | exact hw.const_mul _
          | exact hf2w.sub (hfw.const_mul _)

/-- The first variation of the variance: `δσ_f² = ∫ δρ (f - E[f])²`, with `δρ = ρ φ`. The
mean moves too, but its contribution `∫ (f - E[f]) ρ` vanishes. -/
lemma hasDerivAt_var (hρ : IsEnsemble ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) (hφ : AEStronglyMeasurable φ μ)
    (hC : ∀ x, |φ x| ≤ C) :
    HasDerivAt (fun t => var (fun x => ρ x * (1 + t * φ x)) f μ)
      (∫ x, (f x - mean ρ f μ) ^ 2 * (ρ x * φ x) ∂μ) 0 := by
  have h1 : Integrable (fun x => 1 * ρ x) μ := by simpa using hρ.integrable
  have hf1 := hρ.integrable_mul hf hf2
  obtain ⟨i0, -, -⟩ := integral_mul_one_add h1 hφ hC 0
  obtain ⟨j0, -, -⟩ := integral_mul_one_add hf1 hφ hC 0
  obtain ⟨k0, -, -⟩ := integral_mul_one_add hf2 hφ hC 0
  simp only [one_mul] at i0
  have hvar : ∀ t, var (fun x => ρ x * (1 + t * φ x)) f μ =
      (∫ x, f x ^ 2 * ρ x ∂μ + t * ∫ x, f x ^ 2 * (ρ x * φ x) ∂μ) -
        2 * (mean ρ f μ + t * ∫ x, f x * (ρ x * φ x) ∂μ) ^ 2 +
        (mean ρ f μ + t * ∫ x, f x * (ρ x * φ x) ∂μ) ^ 2 * (1 + t * ∫ x, ρ x * φ x ∂μ) := by
    intro t
    obtain ⟨-, i1, i2⟩ := integral_mul_one_add h1 hφ hC t
    obtain ⟨-, j1, j2⟩ := integral_mul_one_add hf1 hφ hC t
    obtain ⟨-, k1, k2⟩ := integral_mul_one_add hf2 hφ hC t
    simp only [one_mul] at i1 i2
    simp only [var, mean]
    rw [integral_sub_sq_mul_eq i1 j1 k1, i2, j2, k2, hρ.integral_eq_one]
    ring
  have aff : ∀ a b : ℝ, HasDerivAt (fun t : ℝ => a + t * b) b 0 := fun a b => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
  rw [show (fun t => var (fun x => ρ x * (1 + t * φ x)) f μ) = _ from funext hvar]
  have hM := aff (mean ρ f μ) (∫ x, f x * (ρ x * φ x) ∂μ)
  refine (((aff _ _).sub ((hM.pow 2).const_mul 2)).add ((hM.pow 2).mul (aff 1 _))).congr_deriv ?_
  rw [integral_sub_sq_mul_eq i0 j0 k0]
  simp only [zero_mul, add_zero, mul_one, Pi.pow_apply]
  ring

/-- `-y log (c y) = -y log y - y log c`. -/
lemma neg_mul_log_mul (hc : c ≠ 0) (y : ℝ) : -(y * log (c * y)) = negMulLog y - log c * y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [log_mul hc hy, negMulLog]
  ring

lemma integrable_mul_log_mul_add_one (hc : c ≠ 0) (hρ : IsEnsemble ρ μ)
    (hφ : AEStronglyMeasurable φ μ) (hC : ∀ x, |φ x| ≤ C) :
    Integrable (fun x => ρ x * φ x * (log (c * ρ x) + 1)) μ := by
  refine ((hρ.integrable.mul_const (log c + 1)).sub hρ.integrable_negMulLog).bdd_mul hφ
    (c := C) (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hC x)) |>.congr
    (ae_of_all _ fun x => ?_)
  have := neg_mul_log_mul hc (ρ x)
  simp only [negMulLog, Pi.sub_apply] at this ⊢
  linear_combination φ x * this

/-- The first variation of the entropy: `δS_c = -∫ δρ (log (c ρ) + 1)`, with `δρ = ρ φ`. -/
lemma hasDerivAt_entropy (hc : 0 < c) (hρ : IsEnsemble ρ μ) (hφ : AEStronglyMeasurable φ μ)
    (hC : ∀ x, |φ x| ≤ C) :
    HasDerivAt (fun t => entropy c (fun x => ρ x * (1 + t * φ x)) μ)
      (∫ x, -(ρ x * φ x * (log (c * ρ x) + 1)) ∂μ) 0 := by
  have h1 : Integrable (fun x => 1 * ρ x) μ := by simpa using hρ.integrable
  obtain ⟨i0, -, -⟩ := integral_mul_one_add h1 hφ hC 0
  simp only [one_mul] at i0
  have he : ∀ t, entropy c (fun x => ρ x * (1 + t * φ x)) μ =
      ∫ x, negMulLog (ρ x * (1 + t * φ x)) ∂μ -
        log c * (∫ x, ρ x ∂μ + t * ∫ x, ρ x * φ x ∂μ) := by
    intro t
    obtain ⟨-, i1, i2⟩ := integral_mul_one_add h1 hφ hC t
    simp only [one_mul] at i1 i2
    simp only [entropy, neg_mul_log_mul hc.ne']
    rw [integral_sub (integrable_negMulLog_mul_one_add hρ.integrable hρ.integrable_negMulLog hφ
      hC t) (i1.const_mul _), integral_const_mul, i2]
  rw [show (fun t => entropy c (fun x => ρ x * (1 + t * φ x)) μ) = _ from funext he]
  have hD := (hasDerivAt_integral_negMulLog_mul_one_add hρ.nonneg hρ.integrable
    hρ.integrable_negMulLog hφ hC).sub
      (((((hasDerivAt_id (0 : ℝ)).mul_const (∫ x, ρ x * φ x ∂μ)).const_add
        (∫ x, ρ x ∂μ))).const_mul (log c))
  refine hD.congr_deriv ?_
  have hi : Integrable (fun x => -(ρ x * φ x * (log (ρ x) + 1))) μ := by
    simpa [log_one] using (integrable_mul_log_mul_add_one one_ne_zero hρ hφ hC).neg
  rw [one_mul, ← integral_const_mul, ← integral_sub hi (i0.const_mul _)]
  congr 1
  ext x
  have := neg_mul_log_mul hc.ne' (ρ x)
  simp only [negMulLog] at this
  linear_combination (-φ x) * this

end Variation

section Lagrange

variable {ρ φ : ℝ × ℝ → ℝ} {h l₁ l₂ S C : ℝ}

/-- The brief's Lagrangian `L = σ_q² σ_p² + λ₁ (∫ ρ - 1) + λ₂ (S_h[ρ] - S)`, for multipliers
`λ₁ = l₁`, `λ₂ = l₂`. -/
def lagrangian (h l₁ l₂ S : ℝ) (ρ : ℝ × ℝ → ℝ) : ℝ :=
  var ρ Prod.fst * var ρ Prod.snd + l₁ * ((∫ x, ρ x) - 1) + l₂ * (entropy h ρ - S)

/-- The bracket of the brief's first variation, `δL = ∫ δρ · eulerLagrange`:
`(q - μ_q)² σ_p² + σ_q² (p - μ_p)² + λ₁ - λ₂ (log (h ρ) + 1)`. -/
def eulerLagrange (h l₁ l₂ : ℝ) (ρ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (x.1 - mean ρ Prod.fst) ^ 2 * var ρ Prod.snd + var ρ Prod.fst * (x.2 - mean ρ Prod.snd) ^ 2 +
    l₁ - l₂ * (log (h * ρ x) + 1)

/-- **The first variation of the Lagrangian.** Along `ρ (1 + t φ)`, with `δρ = ρ φ`,
`δL = ∫ δρ [(q - μ_q)² σ_p² + σ_q² (p - μ_p)² + λ₁ - λ₂ (log (h ρ) + 1)]`. -/
theorem hasDerivAt_lagrangian (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x)
    (hφ : Measurable φ) (hC : ∀ x, |φ x| ≤ C) :
    HasDerivAt (fun t => lagrangian h l₁ l₂ S fun x => ρ x * (1 + t * φ x))
      (∫ x, ρ x * φ x * eulerLagrange h l₁ l₂ ρ x) 0 := by
  have hφ' := hφ.aestronglyMeasurable (μ := volume)
  have h1 : Integrable (fun x => 1 * ρ x) := by simpa using hρ.integrable
  obtain ⟨i0, -, -⟩ := integral_mul_one_add h1 hφ' hC 0
  simp only [one_mul] at i0
  obtain ⟨iq, -, -⟩ := integral_mul_one_add
    (hρ.integrable_sub_sq_mul measurable_fst hq (mean ρ Prod.fst)) hφ' hC 0
  obtain ⟨ip, -, -⟩ := integral_mul_one_add
    (hρ.integrable_sub_sq_mul measurable_snd hp (mean ρ Prod.snd)) hφ' hC 0
  have hN : HasDerivAt (fun t => ∫ x, ρ x * (1 + t * φ x)) (∫ x, ρ x * φ x) 0 := by
    have : (fun t => ∫ x, ρ x * (1 + t * φ x)) = fun t => (∫ x, ρ x) + t * ∫ x, ρ x * φ x :=
      funext fun t => by simpa using (integral_mul_one_add h1 hφ' hC t).2.2
    rw [this]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (∫ x, ρ x * φ x)).const_add (∫ x, ρ x)
  have hD := (((hasDerivAt_var hρ measurable_fst hq hφ' hC).mul
    (hasDerivAt_var hρ measurable_snd hp hφ' hC)).add ((hN.sub_const 1).const_mul l₁)).add
      (((hasDerivAt_entropy hh hρ hφ' hC).sub_const S).const_mul l₂)
  refine hD.congr_deriv ?_
  simp only [zero_mul, add_zero, mul_one]
  have hl := integrable_mul_log_mul_add_one hh.ne' hρ hφ' hC
  have e : ∫ x, ρ x * φ x * eulerLagrange h l₁ l₂ ρ x =
      ∫ x, (x.1 - mean ρ Prod.fst) ^ 2 * (ρ x * φ x) * var ρ Prod.snd +
        var ρ Prod.fst * ((x.2 - mean ρ Prod.snd) ^ 2 * (ρ x * φ x)) + l₁ * (ρ x * φ x) +
        l₂ * -(ρ x * φ x * (log (h * ρ x) + 1)) := by
    congr 1
    ext x
    simp only [eulerLagrange]
    ring
  rw [e, integral_add, integral_add, integral_add, integral_mul_const, integral_const_mul,
    integral_const_mul, integral_const_mul]
  all_goals first
    | exact iq.mul_const _
    | exact ip.const_mul _
    | exact i0.const_mul _
    | exact hl.neg.const_mul _
    | exact (iq.mul_const _).add (ip.const_mul _)
    | exact ((iq.mul_const _).add (ip.const_mul _)).add (i0.const_mul _)

/-- The bracket of the first variation is integrable against `ρ`. -/
lemma integrable_mul_eulerLagrange (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    Integrable fun x => ρ x * eulerLagrange h l₁ l₂ ρ x := by
  have hl := integrable_mul_log_mul_add_one hh.ne' hρ aestronglyMeasurable_const
    (C := 1) (φ := fun _ => 1) (fun _ => by simp)
  refine ((((hρ.integrable_sub_sq_mul measurable_fst hq (mean ρ Prod.fst)).mul_const
    (var ρ Prod.snd)).add ((hρ.integrable_sub_sq_mul measurable_snd hp
      (mean ρ Prod.snd)).const_mul (var ρ Prod.fst))).add (hρ.integrable.const_mul l₁)).sub
        (hl.const_mul l₂) |>.congr (ae_of_all _ fun x => ?_)
  simp only [eulerLagrange, Pi.add_apply, Pi.sub_apply, mul_one]
  ring

/-- At a product of Gaussians with `λ₂ = -2 σ_q² σ_p²`, the bracket of the first variation is
the constant `λ₁ - λ₂ (1 + log (ħ / (σ_q σ_p)))`. -/
lemma eulerLagrange_gaussProd (hh : 0 < h) {a b v w : ℝ} (hv : 0 < v) (hw : 0 < w)
    (x : ℝ × ℝ) :
    (x.1 - a) ^ 2 * w + v * (x.2 - b) ^ 2 + l₁ -
        -2 * v * w * (log (h * gaussProd a v.toNNReal b w.toNNReal x) + 1) =
      l₁ - -2 * v * w * (1 + log (hbar h / (√v * √w))) := by
  have hv' : v.toNNReal ≠ 0 := by simpa using hv
  have hw' : w.toNNReal ≠ 0 := by simpa using hw
  rw [log_mul hh.ne' (gaussProd_pos hv' hw' x).ne', gaussProd,
    log_mul (gaussianPDFReal_pos _ _ _ hv').ne' (gaussianPDFReal_pos _ _ _ hw').ne',
    log_gaussianPDFReal hv', log_gaussianPDFReal hw', Real.coe_toNNReal _ hv.le,
    Real.coe_toNNReal _ hw.le, hbar, log_div (by positivity) (by positivity),
    log_div hh.ne' (by positivity), log_mul (sqrt_pos.2 hv).ne' (sqrt_pos.2 hw).ne',
    log_sqrt hv.le, log_sqrt hw.le, log_mul (by positivity) hv.ne',
    log_mul (by positivity) hw.ne']
  field_simp
  ring

/-- `volume` on `ℝ²` is not finite. -/
lemma not_isFiniteMeasure_volume : ¬ IsFiniteMeasure (volume : Measure (ℝ × ℝ)) := by
  intro hfin
  have h := measure_lt_top (volume : Measure (ℝ × ℝ)) univ
  rw [← univ_prod_univ, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_univ,
    ENNReal.top_mul_top] at h
  exact lt_irrefl _ h

/-- **The Lagrange computation.** Let `ρ > 0` a.e. The first variation of the Lagrangian
vanishes in every bounded direction exactly when `ρ` is the product of Gaussians with the
means and variances of `ρ`, with multipliers `λ₂ = -2 σ_q² σ_p²` and
`λ₁ = λ₂ (1 + log (ħ / (σ_q σ_p)))`. -/
theorem hasDerivAt_lagrangian_zero_iff (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x)
    (hpos : ∀ᵐ x, 0 < ρ x) :
    (∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        HasDerivAt (fun t => lagrangian h l₁ l₂ S fun x => ρ x * (1 + t * φ x)) 0 0) ↔
      ρ =ᵐ[volume] gaussProd (mean ρ Prod.fst) (var ρ Prod.fst).toNNReal (mean ρ Prod.snd)
          (var ρ Prod.snd).toNNReal ∧
        l₂ = -2 * var ρ Prod.fst * var ρ Prod.snd ∧
        l₁ = l₂ * (1 + log (hbar h / (sd ρ Prod.fst * sd ρ Prod.snd))) := by
  have H := hyp_canonical hρ hq hp
  have hv := H.var_pos_fst
  have hw := H.var_pos_snd
  have hcrit : (∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
      HasDerivAt (fun t => lagrangian h l₁ l₂ S fun x => ρ x * (1 + t * φ x)) 0 0) ↔
      ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
        ∫ x, ρ x * φ x * eulerLagrange h l₁ l₂ ρ x = 0 :=
    forall_congr' fun φ => imp_congr_right fun hφ => imp_congr_right fun ⟨C, hC⟩ =>
      ⟨fun H0 => (hasDerivAt_lagrangian hh hρ hq hp hφ hC).unique H0,
        fun H0 => by
          have := hasDerivAt_lagrangian (l₁ := l₁) (l₂ := l₂) (S := S) hh hρ hq hp hφ hC
          rwa [H0] at this⟩
  rw [hcrit]
  set a := mean ρ Prod.fst
  set b := mean ρ Prod.snd
  set v := var ρ Prod.fst
  set w := var ρ Prod.snd
  constructor
  · intro H0
    -- the fundamental lemma of the calculus of variations, with indicators as directions
    have hz : ∀ᵐ x, eulerLagrange h l₁ l₂ ρ x = 0 := by
      have h0 : (fun x => ρ x * eulerLagrange h l₁ l₂ ρ x) =ᵐ[volume] 0 :=
        (integrable_mul_eulerLagrange hh hρ hq hp).ae_eq_zero_of_forall_setIntegral_eq_zero
          fun s hs _ => by
            have := H0 (s.indicator 1) (measurable_one.indicator hs)
              ⟨1, fun x => by by_cases hx : x ∈ s <;> simp [hx]⟩
            rw [← integral_indicator hs, ← this]
            congr 1
            ext x
            by_cases hx : x ∈ s <;> simp [hx]
      filter_upwards [h0, hpos] with x hx hx'
      exact (mul_eq_zero.1 hx).resolve_left hx'.ne'
    rcases lt_trichotomy l₂ 0 with hl | hl | hl
    · -- `λ₂ < 0`: `ρ` is a multiple of a product of Gaussians
      have hv'0 : (-l₂ / (2 * w)).toNNReal ≠ 0 := by
        rw [Ne, Real.toNNReal_eq_zero, not_le]; exact div_pos (by linarith) (by linarith)
      have hw'0 : (-l₂ / (2 * v)).toNNReal ≠ 0 := by
        rw [Ne, Real.toNNReal_eq_zero, not_le]; exact div_pos (by linarith) (by linarith)
      set K := exp (l₁ / l₂ - 1 - log h + log (2 * π * (-l₂ / (2 * w))) / 2 +
        log (2 * π * (-l₂ / (2 * v))) / 2)
      have hK : ρ =ᵐ[volume] fun x =>
          K * gaussProd a (-l₂ / (2 * w)).toNNReal b (-l₂ / (2 * v)).toNNReal x := by
        filter_upwards [hz, hpos] with x hx hx'
        refine log_injOn_pos hx' (mul_pos (exp_pos _) (gaussProd_pos hv'0 hw'0 x)) ?_
        change (x.1 - a) ^ 2 * w + v * (x.2 - b) ^ 2 + l₁ - l₂ * (log (h * ρ x) + 1) = 0 at hx
        rw [log_mul hh.ne' hx'.ne'] at hx
        have hl0 := hl.ne
        have hlogρ : log (ρ x) = ((x.1 - a) ^ 2 * w + v * (x.2 - b) ^ 2 + l₁) / l₂ - log h - 1 := by
          field_simp
          linarith
        rw [hlogρ, log_mul (exp_pos _).ne' (gaussProd_pos hv'0 hw'0 x).ne', log_exp, gaussProd,
          log_mul (gaussianPDFReal_pos _ _ _ hv'0).ne' (gaussianPDFReal_pos _ _ _ hw'0).ne',
          log_gaussianPDFReal hv'0, log_gaussianPDFReal hw'0,
          Real.coe_toNNReal _ (div_pos (by linarith) (by linarith)).le,
          Real.coe_toNNReal _ (div_pos (by linarith) (by linarith)).le]
        field_simp
        ring
      have hK1 : K = 1 := by
        have := hρ.integral_eq_one
        rwa [integral_congr_ae hK, integral_const_mul, integral_gaussProd hv'0 hw'0,
          mul_one] at this
      have hG : ρ =ᵐ[volume] gaussProd a (-l₂ / (2 * w)).toNNReal b (-l₂ / (2 * v)).toNNReal :=
        hK.trans (ae_of_all _ fun x => by simp [hK1])
      have hvv := var_fst_gaussProd hG hv'0 hw'0
      rw [Real.coe_toNNReal _ (div_pos (by linarith) (by linarith)).le] at hvv
      have hl₂ : l₂ = -2 * v * w := by
        field_simp at hvv
        linarith
      have hww : -l₂ / (2 * v) = w := by
        rw [hl₂]
        field_simp
      rw [← hvv, hww] at hG
      refine ⟨hG, hl₂, ?_⟩
      obtain ⟨x, hx, hxG⟩ := (hz.and hG).exists
      change (x.1 - a) ^ 2 * w + v * (x.2 - b) ^ 2 + l₁ - l₂ * (log (h * ρ x) + 1) = 0 at hx
      rw [hxG, hl₂, eulerLagrange_gaussProd hh hv hw] at hx
      rw [hl₂, show sd ρ Prod.fst volume = √v from rfl, show sd ρ Prod.snd volume = √w from rfl]
      linarith
    · -- `λ₂ = 0`: the quadratic would be constant
      have hc : Continuous fun x : ℝ × ℝ => (x.1 - a) ^ 2 * w + v * (x.2 - b) ^ 2 + l₁ := by
        fun_prop
      have he := (hc.ae_eq_iff_eq volume continuous_const).1
        (hz.mono fun x hx => by simpa [eulerLagrange, hl] using hx)
      have h1 := congrFun he (a, b)
      have h2 := congrFun he (a + 1, b)
      simp only [sub_self, add_sub_cancel_left] at h1 h2
      nlinarith
    · -- `λ₂ > 0`: `ρ` would be bounded below by a positive constant
      have hlow : ∀ᵐ x, exp (l₁ / l₂ - 1) / h ≤ ρ x := by
        filter_upwards [hz, hpos] with x hx hx'
        simp only [eulerLagrange] at hx
        have hQ : 0 ≤ (x.1 - a) ^ 2 * w + v * (x.2 - b) ^ 2 := by positivity
        have hle : l₁ / l₂ - 1 ≤ log (h * ρ x) := by
          rw [div_sub_one hl.ne', div_le_iff₀ hl]
          nlinarith
        rw [div_le_iff₀ hh, mul_comm]
        calc exp (l₁ / l₂ - 1) ≤ exp (log (h * ρ x)) := exp_le_exp.2 hle
          _ = h * ρ x := exp_log (mul_pos hh hx')
      have hint : Integrable (fun _ : ℝ × ℝ => exp (l₁ / l₂ - 1) / h) :=
        hρ.integrable.mono' aestronglyMeasurable_const (hlow.mono fun x hx => by
          rwa [Real.norm_of_nonneg (by positivity)])
      rcases integrable_const_iff.1 hint with h0 | hfin
      · exact absurd h0 (by positivity)
      · exact absurd hfin not_isFiniteMeasure_volume
  · rintro ⟨hG, hl₂, hl₁⟩ φ - -
    refine integral_eq_zero_of_ae (hG.mono fun x hx => ?_)
    change ρ x * φ x * ((x.1 - a) ^ 2 * w + v * (x.2 - b) ^ 2 + l₁ -
      l₂ * (log (h * ρ x) + 1)) = 0
    rw [hx, hl₂, eulerLagrange_gaussProd hh hv hw, hl₁, hl₂,
      show sd ρ Prod.fst volume = √v from rfl, show sd ρ Prod.snd volume = √w from rfl]
    ring

/-- **The brief's final line.** At a critical point of the Lagrangian,
`σ_q σ_p = (ħ / e) e^{S_h[ρ]}`, i.e. `S_h[ρ] = log (2π e σ_q σ_p / h)`. -/
theorem sd_mul_sd_eq_of_hasDerivAt_lagrangian (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x)
    (hpos : ∀ᵐ x, 0 < ρ x)
    (hcrit : ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∃ C, ∀ x, |φ x| ≤ C) →
      HasDerivAt (fun t => lagrangian h l₁ l₂ S fun x => ρ x * (1 + t * φ x)) 0 0) :
    sd ρ Prod.fst * sd ρ Prod.snd = hbar h / exp 1 * exp (entropy h ρ) := by
  have H := hyp_canonical hρ hq hp
  exact (sd_mul_sd_eq_iff hh hρ hq hp).2 ⟨_, _, _, _, H.var_toNNReal_ne_zero_fst,
    H.var_toNNReal_ne_zero_snd, ((hasDerivAt_lagrangian_zero_iff hh hρ hq hp hpos).1 hcrit).1⟩

end Lagrange

/-! ### G. Several degrees of freedom -/

section Reference

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ f g : X → ℝ}

lemma log_gaussProd_zero_one (y : ℝ × ℝ) :
    log (gaussProd 0 1 0 1 y) = -log (2 * π) - y.1 ^ 2 / 2 - y.2 ^ 2 / 2 := by
  rw [gaussProd, log_mul (gaussianPDFReal_pos _ _ _ one_ne_zero).ne'
    (gaussianPDFReal_pos _ _ _ one_ne_zero).ne', log_gaussianPDFReal one_ne_zero,
    log_gaussianPDFReal one_ne_zero]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  ring

/-- With finite second moments of `f, g`, `ρ log G(f, g)` is integrable for the standard
Gaussian `G`. -/
lemma IsEnsemble.integrable_mul_log_gaussProd (hρ : IsEnsemble ρ μ)
    (hf : Integrable (fun x => f x ^ 2 * ρ x) μ) (hg : Integrable (fun x => g x ^ 2 * ρ x) μ) :
    Integrable (fun x => ρ x * log (gaussProd 0 1 0 1 (f x, g x))) μ := by
  refine (((hρ.integrable.const_mul (-log (2 * π))).sub (hf.const_mul 2⁻¹)).sub
    (hg.const_mul 2⁻¹)).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.sub_apply, log_gaussProd_zero_one]
  ring

end Reference

section PhaseSpace

variable {n : ℕ} {ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ} {h : ℝ}

/-- The marginal `ρᵢ(q, p)` of the DOF `i` on the phase space `(ℝ²)ⁿ⁺¹`: the integral of `ρ`
over the other `n` DOFs. -/
def marginal (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) (i : Fin (n + 1)) (z : ℝ × ℝ) : ℝ :=
  ∫ y : Fin n → ℝ × ℝ, ρ (Fin.insertNth i z y)

lemma integrable_insertNth_iff {F : (Fin (n + 1) → ℝ × ℝ) → ℝ} (i : Fin (n + 1)) :
    Integrable (fun z : (ℝ × ℝ) × (Fin n → ℝ × ℝ) => F (Fin.insertNth i z.1 z.2))
      (volume.prod volume) ↔ Integrable F :=
  (volume_preserving_piFinSuccAbove (fun _ => ℝ × ℝ) i).symm.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)

lemma integral_insertNth (F : (Fin (n + 1) → ℝ × ℝ) → ℝ) (i : Fin (n + 1)) :
    ∫ z : (ℝ × ℝ) × (Fin n → ℝ × ℝ), F (Fin.insertNth i z.1 z.2) ∂(volume.prod volume) =
      ∫ x, F x :=
  (volume_preserving_piFinSuccAbove (fun _ => ℝ × ℝ) i).symm.integral_comp' F

/-- Moments of the marginal are moments of `ρ`. -/
lemma integral_mul_marginal {F : ℝ × ℝ → ℝ} (i : Fin (n + 1))
    (hF : Integrable fun x => F (x i) * ρ x) :
    Integrable (fun z => F z * marginal ρ i z) ∧
      ∫ z, F z * marginal ρ i z = ∫ x, F (x i) * ρ x := by
  have hw : Integrable (fun w : (ℝ × ℝ) × (Fin n → ℝ × ℝ) =>
      F w.1 * ρ (Fin.insertNth i w.1 w.2)) (volume.prod volume) := by
    simpa only [Fin.insertNth_apply_same] using
      (integrable_insertNth_iff (F := fun x => F (x i) * ρ x) i).2 hF
  refine ⟨integrable_mul_integral_prod hw, (integral_mul_integral_prod hw).trans ?_⟩
  simpa only [Fin.insertNth_apply_same] using integral_insertNth (fun x => F (x i) * ρ x) i

/-- The marginal of a DOF is an ensemble: the joint finite entropy and the finite second
moments of the other DOFs give it finite entropy. -/
theorem isEnsemble_marginal (hρ : IsEnsemble ρ)
    (hq : ∀ j, Integrable fun x => (x j).1 ^ 2 * ρ x)
    (hp : ∀ j, Integrable fun x => (x j).2 ^ 2 * ρ x) (i : Fin (n + 1)) :
    IsEnsemble (marginal ρ i) where
  nonneg z := integral_nonneg fun y => hρ.nonneg _
  integral_eq_one := by
    have := (integral_mul_marginal i (F := fun _ => 1) (by simpa using hρ.integrable)).2
    simpa [hρ.integral_eq_one] using this
  integrable_negMulLog := by
    have hG : ∀ k, Integrable fun x => ρ x * log (gaussProd 0 1 0 1 (x k)) := fun k => by
      simpa using hρ.integrable_mul_log_gaussProd (hq k) (hp k)
    have hG0 : ∀ y, 0 < gaussProd 0 1 0 1 y := gaussProd_pos one_ne_zero one_ne_zero
    refine integrable_negMulLog_integral_prod (ρ := fun w => ρ (Fin.insertNth i w.1 w.2))
      (fun z => hρ.nonneg _) ((integrable_insertNth_iff i).2 hρ.integrable)
      ((integrable_insertNth_iff (F := fun x => negMulLog (ρ x)) i).2 hρ.integrable_negMulLog)
      (γ := fun y => ∏ j, gaussProd 0 1 0 1 (y j))
      (fun y => Finset.prod_pos fun j _ => hG0 _)
      (Integrable.fintype_prod fun _ => integrable_gaussProd 0 0 1 1) ?_ ?_ hG0
      (integrable_gaussProd 0 0 1 1) ?_
    · rw [integral_fintype_prod_volume_eq_prod]
      simp [integral_gaussProd one_ne_zero one_ne_zero]
    · refine (integrable_finsetSum Finset.univ fun j _ =>
        (integrable_insertNth_iff i).2 (hG (i.succAbove j))).congr (ae_of_all _ fun z => ?_)
      simp only [Fin.insertNth_apply_succAbove]
      rw [Real.log_prod fun j _ => (hG0 _).ne', Finset.mul_sum]
    · simpa only [Fin.insertNth_apply_same] using (integrable_insertNth_iff i).2 (hG i)

variable {u : ℝ × ℝ → ℝ}

lemma mean_marginal (hρ : IsEnsemble ρ) (hu : Measurable u) (i : Fin (n + 1))
    (hu2 : Integrable fun x => u (x i) ^ 2 * ρ x) :
    mean (marginal ρ i) u = mean ρ fun x => u (x i) :=
  (integral_mul_marginal i (hρ.integrable_mul (hu.comp (measurable_pi_apply i)) hu2)).2

lemma var_marginal (hρ : IsEnsemble ρ) (hu : Measurable u) (i : Fin (n + 1))
    (hu2 : Integrable fun x => u (x i) ^ 2 * ρ x) :
    var (marginal ρ i) u = var ρ fun x => u (x i) := by
  have hm := mean_marginal hρ hu i hu2
  set a := mean ρ fun x => u (x i)
  have := (integral_mul_marginal i (F := fun z => (u z - a) ^ 2)
    (hρ.integrable_sub_sq_mul (hu.comp (measurable_pi_apply i)) hu2 a)).2
  rw [var, var, hm]
  exact this

lemma sd_marginal (hρ : IsEnsemble ρ) (hu : Measurable u) (i : Fin (n + 1))
    (hu2 : Integrable fun x => u (x i) ^ 2 * ρ x) :
    sd (marginal ρ i) u = sd ρ fun x => u (x i) := by
  rw [sd, sd, var_marginal hρ hu i hu2]

/-- Condition ZENT on the phase space `(ℝ²)ⁿ⁺¹`: the marginal of every DOF has
`S_h[ρᵢ] ≥ 0`. -/
def LowerEntropicBoundPhaseSpace (h : ℝ) (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ i, LowerEntropicBound h (marginal ρ i)

/-- Condition CUP on the phase space `(ℝ²)ⁿ⁺¹`: `σ_{qᵢ} σ_{pᵢ} ≥ ħ / e` for every DOF `i`. -/
def UncertaintyPrinciplePhaseSpace (h : ℝ) (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ i, hbar h / exp 1 ≤ sd ρ (fun x => (x i).1) * sd ρ fun x => (x i).2

/-- **Theorem 2 for `n + 1` DOFs.** ZENT implies CUP. -/
theorem uncertaintyPrinciplePhaseSpace_of_lowerEntropicBoundPhaseSpace (hh : 0 < h)
    (hρ : IsEnsemble ρ) (hq : ∀ j, Integrable fun x => (x j).1 ^ 2 * ρ x)
    (hp : ∀ j, Integrable fun x => (x j).2 ^ 2 * ρ x) (hZ : LowerEntropicBoundPhaseSpace h ρ) :
    UncertaintyPrinciplePhaseSpace h ρ := fun i => by
  have := uncertaintyPrinciple_of_lowerEntropicBound hh (isEnsemble_marginal hρ hq hp i)
    (integral_mul_marginal i (F := fun z => z.1 ^ 2) (hq i)).1
    (integral_mul_marginal i (F := fun z => z.2 ^ 2) (hp i)).1 (hZ i)
  rwa [UncertaintyPrinciple, sd_marginal hρ measurable_fst i (hq i),
    sd_marginal hρ measurable_snd i (hp i)] at this

/-- **Theorem 2 for `n + 1` DOFs, equality case.** Under ZENT for the DOF `i`,
`σ_{qᵢ} σ_{pᵢ} = ħ / e` exactly when its marginal is a product of Gaussians in `qᵢ` and `pᵢ`
with `σ_{qᵢ} σ_{pᵢ} = ħ / e`. -/
theorem sd_mul_sd_eq_hbar_div_exp_iff_marginal (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : ∀ j, Integrable fun x => (x j).1 ^ 2 * ρ x)
    (hp : ∀ j, Integrable fun x => (x j).2 ^ 2 * ρ x) (i : Fin (n + 1))
    (hZ : LowerEntropicBound h (marginal ρ i)) :
    sd ρ (fun x => (x i).1) * sd ρ (fun x => (x i).2) = hbar h / exp 1 ↔
      ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧ √(v : ℝ) * √(w : ℝ) = hbar h / exp 1 ∧
        marginal ρ i =ᵐ[volume] gaussProd a v b w := by
  rw [← sd_marginal hρ measurable_fst i (hq i), ← sd_marginal hρ measurable_snd i (hp i)]
  exact sd_mul_sd_eq_hbar_div_exp_iff hh (isEnsemble_marginal hρ hq hp i)
    (integral_mul_marginal i (F := fun z => z.1 ^ 2) (hq i)).1
    (integral_mul_marginal i (F := fun z => z.2 ^ 2) (hp i)).1 hZ

end PhaseSpace

end ClassicalUncertaintyPrinciple
