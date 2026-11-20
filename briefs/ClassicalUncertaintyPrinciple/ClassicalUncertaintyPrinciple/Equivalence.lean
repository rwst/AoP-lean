/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ClassicalUncertaintyPrinciple

/-!
# Classical uncertainty relation: the equivalence with the lower entropic bound

The revised brief *Classical uncertainty relation* states, for one degree of freedom (DOF) with
finite entropy, that the lower entropic bound ZENT (`S_h[ρ] ≥ 0`) is equivalent to the
generalized classical uncertainty relation GCUR,

  `σ_f σ_g ≥ (ħ / e) e^{E[log |{f, g}|]}` for every admissible coordinate pair `(f, g)`,

and that the canonical relation CUR (`σ_q σ_p ≥ ħ / e`) is strictly weaker. Both directions rest
on the exact identity of **Proposition 3**,

  `log (2π e σ_f σ_g / h) = S_h[ρ] + E[log |{f, g}|] + D(ρ_{fg} ‖ G_{fg})`,

where `G_{fg}` is the product of Gaussians with the means and variances of `f, g` and `D` is the
Kullback–Leibler divergence. `D ≥ 0` gives ZENT ⇒ GCUR (**Theorem 9**). Conversely, coordinates
in which `D` is arbitrarily small (**Proposition 6**) turn GCUR into `S_h[ρ] ≥ 0`
(**Theorem 12**).

The existence of such coordinates is not formalized: the brief takes it from the volume-transport
theorem of Greene and Shiohama (Proposition 5) and from an approximation by smooth positive
densities (Proposition 6, a proof sketch). Here it is the hypothesis `HasGaussianFrames`, the
conclusion of Proposition 6 for finite entropy, and Theorem 12 is proved from it.

## Main definitions

* `ClassicalUncertaintyPrinciple.matchedGauss`, `ClassicalUncertaintyPrinciple.gaussianDivergence`:
  `G_ρ` and `D(ρ ‖ G_ρ)`.
* `ClassicalUncertaintyPrinciple.IsAdmissible`: Definition 2, admissible coordinate pairs.
* `ClassicalUncertaintyPrinciple.UncertaintyRelation`,
  `ClassicalUncertaintyPrinciple.GeneralizedUncertaintyRelation`: the conditions CUR and GCUR.
* `ClassicalUncertaintyPrinciple.coordinateUncertainty`: `U_ρ(T)` of Proposition 6.
* `ClassicalUncertaintyPrinciple.HasGaussianFrames`: the conclusion of Proposition 6.
* `ClassicalUncertaintyPrinciple.correlatedGaussian`: the ensemble of Theorem 11.

## Main results

* `ClassicalUncertaintyPrinciple.IsNewVariables.log_eq_entropy_add`,
  `ClassicalUncertaintyPrinciple.IsNewVariables.sd_mul_sd_eq`: Proposition 3, eq. (4).
* `ClassicalUncertaintyPrinciple.IsNewVariables.sd_mul_sd_eq_of_entropy_densityFG_eq_zero`:
  the conclusion of Proposition 5, given the coordinates.
* `ClassicalUncertaintyPrinciple.entropy_le_coordinateUncertainty`,
  `ClassicalUncertaintyPrinciple.isGLB_coordinateUncertainty`: Proposition 6, eq. (7).
* `ClassicalUncertaintyPrinciple.exists_ensemble_not_conditions`: Theorem 8.
* `ClassicalUncertaintyPrinciple.generalizedUncertaintyRelation_of_lowerEntropicBound`,
  `ClassicalUncertaintyPrinciple.uncertaintyRelation_of_lowerEntropicBound`,
  `ClassicalUncertaintyPrinciple.sd_mul_sd_eq_hbar_div_exp_mul_exp_mul_exp`: Theorem 9, eq. (10).
* `ClassicalUncertaintyPrinciple.exists_uncertaintyRelation_not_lowerEntropicBound`: Theorem 11.
* `ClassicalUncertaintyPrinciple.lowerEntropicBound_of_generalizedUncertaintyRelation`,
  `ClassicalUncertaintyPrinciple.lowerEntropicBound_iff_generalizedUncertaintyRelation`:
  Theorem 12, from `HasGaussianFrames`.
* `ClassicalUncertaintyPrinciple.isEnsemble_mix`,
  `ClassicalUncertaintyPrinciple.entropy_mix_bounds`: the remark on convexity.
-/

open Real MeasureTheory ProbabilityTheory Set

open scoped NNReal

@[expose] public noncomputable section

namespace ClassicalUncertaintyPrinciple

/-! ### Products of Gaussians as ensembles -/

section GaussProd

variable {a b : ℝ} {v w : ℝ≥0} {h : ℝ}

lemma integrable_fst_sub_sq_mul_gaussProd (hv : v ≠ 0) (c : ℝ) :
    Integrable fun x : ℝ × ℝ => (x.1 - c) ^ 2 * gaussProd a v b w x := by
  rw [Measure.volume_eq_prod]
  exact ((integrable_sub_sq_mul_gaussianPDFReal hv c).mul_prod
    (integrable_gaussianPDFReal b w)).congr (ae_of_all _ fun x => by simp only [gaussProd]; ring)

lemma integrable_snd_sub_sq_mul_gaussProd (hw : w ≠ 0) (c : ℝ) :
    Integrable fun x : ℝ × ℝ => (x.2 - c) ^ 2 * gaussProd a v b w x := by
  rw [Measure.volume_eq_prod]
  exact ((integrable_gaussianPDFReal a v).mul_prod
    (integrable_sub_sq_mul_gaussianPDFReal hw c)).congr
      (ae_of_all _ fun x => by simp only [gaussProd]; ring)

lemma integrable_fst_mul_snd_mul_gaussProd (hv : v ≠ 0) (hw : w ≠ 0) :
    Integrable fun x : ℝ × ℝ => x.1 * x.2 * gaussProd a v b w x := by
  rw [Measure.volume_eq_prod]
  exact ((integrable_mul_gaussianPDFReal hv).mul_prod
    (integrable_mul_gaussianPDFReal hw)).congr
      (ae_of_all _ fun x => by simp only [gaussProd]; ring)

lemma integrable_fst_mul_gaussProd (hv : v ≠ 0) :
    Integrable fun x : ℝ × ℝ => x.1 * gaussProd a v b w x := by
  rw [Measure.volume_eq_prod]
  exact ((integrable_mul_gaussianPDFReal hv).mul_prod
    (integrable_gaussianPDFReal b w)).congr (ae_of_all _ fun x => by simp only [gaussProd]; ring)

lemma integrable_snd_mul_gaussProd (hw : w ≠ 0) :
    Integrable fun x : ℝ × ℝ => x.2 * gaussProd a v b w x := by
  rw [Measure.volume_eq_prod]
  exact ((integrable_gaussianPDFReal a v).mul_prod
    (integrable_mul_gaussianPDFReal hw)).congr
      (ae_of_all _ fun x => by simp only [gaussProd]; ring)

/-- A product of Gaussians is an ensemble. -/
lemma isEnsemble_gaussProd (hv : v ≠ 0) (hw : w ≠ 0) : IsEnsemble (gaussProd a v b w) where
  nonneg x := (gaussProd_pos hv hw x).le
  integral_eq_one := integral_gaussProd hv hw
  integrable_negMulLog := by
    have h1 := integrable_fst_sub_sq_mul_gaussProd (a := a) (b := b) (w := w) hv a
    have h2 := integrable_snd_sub_sq_mul_gaussProd (a := a) (b := b) (v := v) hw b
    refine (((integrable_gaussProd a b v w).const_mul
      ((log (2 * π * v) + log (2 * π * w)) / 2)).add
        ((h1.const_mul (2 * v : ℝ)⁻¹).add (h2.const_mul (2 * w : ℝ)⁻¹))).congr
          (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, negMulLog, gaussProd]
    rw [log_mul (gaussianPDFReal_pos _ _ _ hv).ne' (gaussianPDFReal_pos _ _ _ hw).ne',
      log_gaussianPDFReal hv, log_gaussianPDFReal hw]
    ring

lemma integrable_fst_sq_mul_gaussProd (hv : v ≠ 0) :
    Integrable fun x : ℝ × ℝ => x.1 ^ 2 * gaussProd a v b w x := by
  simpa using integrable_fst_sub_sq_mul_gaussProd (a := a) (b := b) (w := w) hv 0

lemma integrable_snd_sq_mul_gaussProd (hw : w ≠ 0) :
    Integrable fun x : ℝ × ℝ => x.2 ^ 2 * gaussProd a v b w x := by
  simpa using integrable_snd_sub_sq_mul_gaussProd (a := a) (b := b) (v := v) hw 0

lemma sd_mul_sd_gaussProd (hv : v ≠ 0) (hw : w ≠ 0) :
    sd (gaussProd a v b w) Prod.fst * sd (gaussProd a v b w) Prod.snd = √(v : ℝ) * √(w : ℝ) := by
  rw [sd, sd, var_fst_gaussProd (ρ := gaussProd a v b w) Filter.EventuallyEq.rfl hv hw,
    var_snd_gaussProd (ρ := gaussProd a v b w) Filter.EventuallyEq.rfl hv hw]

/-- The entropy of a product of Gaussians, `S_h = log (2π e σ_q σ_p / h)`
(Cover–Thomas, §8.4). -/
lemma entropy_gaussProd (hh : 0 < h) (hv : v ≠ 0) (hw : w ≠ 0) :
    entropy h (gaussProd a v b w) = log (2 * π * exp 1 * (√(v : ℝ) * √(w : ℝ))) - log h := by
  have hpos : 0 < √(v : ℝ) * √(w : ℝ) := by
    have : (0 : ℝ) < v := by positivity
    have : (0 : ℝ) < w := by positivity
    positivity
  have := (sd_mul_sd_eq_iff hh (isEnsemble_gaussProd (a := a) (b := b) hv hw)
    (integrable_fst_sq_mul_gaussProd hv) (integrable_snd_sq_mul_gaussProd hw)).2
      ⟨a, b, v, w, hv, hw, Filter.EventuallyEq.rfl⟩
  rw [sd_mul_sd_gaussProd hv hw] at this
  exact (hbar_div_exp_mul_exp_eq_iff hh hpos).1 this

/-- `∫ (α q + β p) (γ q + δ p) G = α γ v + β δ w` for the centred product of Gaussians. -/
lemma integral_linear_mul_linear_gaussProd (hv : v ≠ 0) (hw : w ≠ 0) (α β γ δ : ℝ) :
    Integrable (fun x : ℝ × ℝ => (α * x.1 + β * x.2) * (γ * x.1 + δ * x.2) *
      gaussProd 0 v 0 w x) ∧
    ∫ x : ℝ × ℝ, (α * x.1 + β * x.2) * (γ * x.1 + δ * x.2) * gaussProd 0 v 0 w x =
      α * γ * v + β * δ * w := by
  have i11 := integrable_fst_sq_mul_gaussProd (a := 0) (b := 0) (w := w) hv
  have i22 := integrable_snd_sq_mul_gaussProd (a := 0) (b := 0) (v := v) hw
  have i12 := integrable_fst_mul_snd_mul_gaussProd (a := 0) (b := 0) hv hw
  have e11 : ∫ x : ℝ × ℝ, x.1 ^ 2 * gaussProd 0 v 0 w x = v := by
    have := var_fst_gaussProd (ρ := gaussProd 0 v 0 w) Filter.EventuallyEq.rfl hv hw
    rw [var, mean_fst_gaussProd (ρ := gaussProd 0 v 0 w) Filter.EventuallyEq.rfl hv hw] at this
    simpa using this
  have e22 : ∫ x : ℝ × ℝ, x.2 ^ 2 * gaussProd 0 v 0 w x = w := by
    have := var_snd_gaussProd (ρ := gaussProd 0 v 0 w) Filter.EventuallyEq.rfl hv hw
    rw [var, mean_snd_gaussProd (ρ := gaussProd 0 v 0 w) Filter.EventuallyEq.rfl hv hw] at this
    simpa using this
  have e12 : ∫ x : ℝ × ℝ, x.1 * x.2 * gaussProd 0 v 0 w x = 0 := by
    rw [Measure.volume_eq_prod]
    have : (fun x : ℝ × ℝ => x.1 * x.2 * gaussProd 0 v 0 w x) =
        fun x => (x.1 * gaussianPDFReal 0 v x.1) * (x.2 * gaussianPDFReal 0 w x.2) := by
      ext x
      simp only [gaussProd]
      ring
    rw [this, integral_prod_mul (fun t => t * gaussianPDFReal 0 v t)
      (fun t => t * gaussianPDFReal 0 w t), integral_mul_gaussianPDFReal hv, zero_mul]
  have hfun : (fun x : ℝ × ℝ => (α * x.1 + β * x.2) * (γ * x.1 + δ * x.2) *
      gaussProd 0 v 0 w x) = fun x => α * γ * (x.1 ^ 2 * gaussProd 0 v 0 w x) +
        (α * δ + β * γ) * (x.1 * x.2 * gaussProd 0 v 0 w x) +
        β * δ * (x.2 ^ 2 * gaussProd 0 v 0 w x) := by
    ext x
    ring
  have hi : Integrable fun x : ℝ × ℝ => α * γ * (x.1 ^ 2 * gaussProd 0 v 0 w x) +
      (α * δ + β * γ) * (x.1 * x.2 * gaussProd 0 v 0 w x) :=
    (i11.const_mul _).add (i12.const_mul _)
  refine ⟨hfun ▸ hi.add (i22.const_mul _), ?_⟩
  rw [hfun, integral_add hi (i22.const_mul _), integral_add (i11.const_mul _) (i12.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, e11, e12, e22]
  ring

/-- `∫ (α q + β p) G = 0` for the centred product of Gaussians. -/
lemma integral_linear_mul_gaussProd (hv : v ≠ 0) (hw : w ≠ 0) (α β : ℝ) :
    Integrable (fun x : ℝ × ℝ => (α * x.1 + β * x.2) * gaussProd 0 v 0 w x) ∧
    ∫ x : ℝ × ℝ, (α * x.1 + β * x.2) * gaussProd 0 v 0 w x = 0 := by
  have i1 := integrable_fst_mul_gaussProd (a := 0) (b := 0) (w := w) hv
  have i2 := integrable_snd_mul_gaussProd (a := 0) (b := 0) (v := v) hw
  have e1 : ∫ x : ℝ × ℝ, x.1 * gaussProd 0 v 0 w x = 0 :=
    mean_fst_gaussProd (ρ := gaussProd 0 v 0 w) Filter.EventuallyEq.rfl hv hw
  have e2 : ∫ x : ℝ × ℝ, x.2 * gaussProd 0 v 0 w x = 0 :=
    mean_snd_gaussProd (ρ := gaussProd 0 v 0 w) Filter.EventuallyEq.rfl hv hw
  have hfun : (fun x : ℝ × ℝ => (α * x.1 + β * x.2) * gaussProd 0 v 0 w x) =
      fun x => α * (x.1 * gaussProd 0 v 0 w x) + β * (x.2 * gaussProd 0 v 0 w x) := by
    ext x
    ring
  refine ⟨hfun ▸ (i1.const_mul _).add (i2.const_mul _), ?_⟩
  rw [hfun, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul, e1, e2]
  ring

end GaussProd

/-! ### Proposition 3: the exact identity -/

section Identity

variable {ρ f g : ℝ × ℝ → ℝ} {h : ℝ}

/-- The product `G_ρ` of Gaussians in `q` and `p` with the means and variances of `ρ`. -/
def matchedGauss (ρ : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  gaussProd (mean ρ Prod.fst) (var ρ Prod.fst).toNNReal (mean ρ Prod.snd) (var ρ Prod.snd).toNNReal

/-- The Kullback–Leibler divergence `D(ρ ‖ G_ρ) = ∫ ρ log (ρ / G_ρ)` from the product of
Gaussians with the same means and variances. -/
def gaussianDivergence (ρ : ℝ × ℝ → ℝ) : ℝ := ∫ x, ρ x * log (ρ x / matchedGauss ρ x)

/-- `D(ρ ‖ G_ρ) = log (2π e σ_q σ_p) + ∫ ρ log ρ`: `∫ ρ log G_ρ = ∫ G_ρ log G_ρ`. -/
lemma gaussianDivergence_eq (hρ : IsEnsemble ρ) (hq : Integrable fun x => x.1 ^ 2 * ρ x)
    (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    gaussianDivergence ρ =
      log (2 * π * exp 1 * (sd ρ Prod.fst * sd ρ Prod.snd)) - ∫ x, negMulLog (ρ x) := by
  have H := hyp_canonical hρ hq hp
  obtain ⟨hi, he⟩ := H.integral_mul_log_optWeight
  have hopt : ∀ x, optWeight volume ρ Prod.fst Prod.snd (fun _ => 1) x = matchedGauss ρ x :=
    fun x => by simp [optWeight, matchedGauss]
  simp only [hopt, log_one, mul_zero, integral_zero, sub_zero] at hi he
  have hpt : (fun x => ρ x * log (ρ x / matchedGauss ρ x)) =
      fun x => -negMulLog (ρ x) - ρ x * log (matchedGauss ρ x) := by
    ext x
    rcases (hρ.nonneg x).eq_or_lt with h0 | h0
    · simp [← h0]
    · rw [log_div h0.ne' ((hopt x) ▸ H.optWeight_pos x).ne', negMulLog]
      ring
  rw [gaussianDivergence, hpt, integral_sub (f := fun x => -negMulLog (ρ x))
    hρ.integrable_negMulLog.neg hi, integral_neg]
  linarith

/-- `D(ρ ‖ G_ρ) ≥ 0`. -/
lemma gaussianDivergence_nonneg (hρ : IsEnsemble ρ) (hq : Integrable fun x => x.1 ^ 2 * ρ x)
    (hp : Integrable fun x => x.2 ^ 2 * ρ x) : 0 ≤ gaussianDivergence ρ := by
  have := (hyp_canonical hρ hq hp).integral_negMulLog_le_log
  simp only [log_one, mul_zero, integral_zero, sub_zero] at this
  rw [gaussianDivergence_eq hρ hq hp]
  linarith

/-- **Proposition 3 in canonical variables.**
`log (2π e σ_q σ_p / h) = S_h[ρ] + D(ρ ‖ G_ρ)`. -/
theorem log_eq_entropy_add_gaussianDivergence (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    log (2 * π * exp 1 * (sd ρ Prod.fst * sd ρ Prod.snd) / h) =
      entropy h ρ + gaussianDivergence ρ := by
  have := (hyp_canonical hρ hq hp).sd_mul_sd_pos
  rw [gaussianDivergence_eq hρ hq hp, entropy_eq hρ hh, log_div (by positivity) hh.ne']
  ring

lemma eq_mul_exp_of_log_eq {s t : ℝ} (hh : 0 < h) (hs : 0 < s)
    (H : log (2 * π * exp 1 * s / h) = t) : s = h / (2 * π * exp 1) * exp t := by
  rw [← H, exp_log (by positivity)]
  field_simp

lemma hbar_div_exp_eq : hbar h / exp 1 = h / (2 * π * exp 1) := by
  rw [hbar, div_div]

/-- **Theorem 9, eq. (10).** `σ_q σ_p = (ħ / e) e^{S_h[ρ]} e^{D(ρ ‖ G_ρ)}`. -/
theorem sd_mul_sd_eq_hbar_div_exp_mul_exp_mul_exp (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    sd ρ Prod.fst * sd ρ Prod.snd =
      hbar h / exp 1 * exp (entropy h ρ) * exp (gaussianDivergence ρ) := by
  rw [hbar_div_exp_eq, mul_assoc, ← exp_add]
  exact eq_mul_exp_of_log_eq hh (hyp_canonical hρ hq hp).sd_mul_sd_pos
    (log_eq_entropy_add_gaussianDivergence hh hρ hq hp)

namespace IsNewVariables

variable (H : IsNewVariables f g)
include H

lemma integrable_fst_sq_densityFG (hf2 : Integrable fun x => f x ^ 2 * ρ x) :
    Integrable fun u => u.1 ^ 2 * densityFG f g ρ u :=
  (H.integrable_mul_densityFG_iff (φ := fun u => u.1 ^ 2)).2 hf2

lemma integrable_snd_sq_densityFG (hg2 : Integrable fun x => g x ^ 2 * ρ x) :
    Integrable fun u => u.2 ^ 2 * densityFG f g ρ u :=
  (H.integrable_mul_densityFG_iff (φ := fun u => u.2 ^ 2)).2 hg2

lemma sd_mul_sd_pos (hρ : IsEnsemble ρ) (hf2 : Integrable fun x => f x ^ 2 * ρ x)
    (hg2 : Integrable fun x => g x ^ 2 * ρ x)
    (hlog : Integrable fun x => ρ x * log |poissonBracket f g x|) :
    0 < sd ρ f * sd ρ g := by
  have := (hyp_canonical (H.isEnsemble_densityFG hρ hlog) (H.integrable_fst_sq_densityFG hf2)
    (H.integrable_snd_sq_densityFG hg2)).sd_mul_sd_pos
  rwa [H.sd_densityFG_fst, H.sd_densityFG_snd] at this

/-- **Proposition 3.** `log (2π e σ_f σ_g / h) = S_h[ρ] + E[log |{f, g}|] + D(ρ_{fg} ‖ G_{fg})`. -/
theorem log_eq_entropy_add (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hf2 : Integrable fun x => f x ^ 2 * ρ x) (hg2 : Integrable fun x => g x ^ 2 * ρ x)
    (hlog : Integrable fun x => ρ x * log |poissonBracket f g x|) :
    log (2 * π * exp 1 * (sd ρ f * sd ρ g) / h) =
      entropy h ρ + (∫ x, ρ x * log |poissonBracket f g x|) +
        gaussianDivergence (densityFG f g ρ) := by
  have := log_eq_entropy_add_gaussianDivergence hh (H.isEnsemble_densityFG hρ hlog)
    (H.integrable_fst_sq_densityFG hf2) (H.integrable_snd_sq_densityFG hg2)
  rwa [H.sd_densityFG_fst, H.sd_densityFG_snd, H.entropy_densityFG hh hρ hlog] at this

/-- **Proposition 3, eq. (4).**
`σ_f σ_g = (h / 2π e) e^{S_h[ρ]} e^{E[log |{f, g}|]} e^{D(ρ_{fg} ‖ G_{fg})}`. -/
theorem sd_mul_sd_eq (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hf2 : Integrable fun x => f x ^ 2 * ρ x) (hg2 : Integrable fun x => g x ^ 2 * ρ x)
    (hlog : Integrable fun x => ρ x * log |poissonBracket f g x|) :
    sd ρ f * sd ρ g = h / (2 * π * exp 1) * exp (entropy h ρ) *
      exp (∫ x, ρ x * log |poissonBracket f g x|) * exp (gaussianDivergence (densityFG f g ρ)) := by
  rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add, ← add_assoc]
  exact eq_mul_exp_of_log_eq hh (H.sd_mul_sd_pos hρ hf2 hg2 hlog)
    (H.log_eq_entropy_add hh hρ hf2 hg2 hlog)

/-- **Proposition 5, its conclusion.** In coordinates where `ρ_{fg}` is a product of Gaussians
with zero entropy, `σ_f σ_g = h / 2π e` and `S_h[ρ] = -E[log |{f, g}|]`. -/
theorem sd_mul_sd_eq_of_entropy_densityFG_eq_zero (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hf2 : Integrable fun x => f x ^ 2 * ρ x) (hg2 : Integrable fun x => g x ^ 2 * ρ x)
    (hlog : Integrable fun x => ρ x * log |poissonBracket f g x|) {a b : ℝ} {v w : ℝ≥0}
    (hv : v ≠ 0) (hw : w ≠ 0) (hG : densityFG f g ρ =ᵐ[volume] gaussProd a v b w)
    (h0 : entropy h (densityFG f g ρ) = 0) :
    sd ρ f * sd ρ g = h / (2 * π * exp 1) ∧
      entropy h ρ = -∫ x, ρ x * log |poissonBracket f g x| := by
  have hS := H.entropy_densityFG hh hρ hlog
  have hb := (H.sd_mul_sd_eq_iff hh hρ hf2 hg2 hlog).2 ⟨a, b, v, w, hv, hw, hG⟩
  rw [← hS, h0, exp_zero, mul_one, hbar_div_exp_eq] at hb
  exact ⟨hb, by linarith⟩

end IsNewVariables

end Identity

/-! ### The conditions CUR and GCUR -/

section Conditions

variable {ρ f g : ℝ × ℝ → ℝ} {h : ℝ}

/-- **Definition 2.** An admissible coordinate pair `(f, g)` for `ρ`: `C¹`, with
`(q, p) ↦ (f, g)` injective and Jacobian `{f, g} ≠ 0` everywhere, so a `C¹` diffeomorphism onto
its (open) range, and with `E[|log |{f, g}||] < ∞`. -/
structure IsAdmissible (ρ f g : ℝ × ℝ → ℝ) : Prop where
  contDiff_fst : ContDiff ℝ 1 f
  contDiff_snd : ContDiff ℝ 1 g
  injective : Function.Injective fun x => (f x, g x)
  poissonBracket_ne_zero : ∀ x, poissonBracket f g x ≠ 0
  integrable_log : Integrable fun x => ρ x * log |poissonBracket f g x|

lemma IsAdmissible.isNewVariables (T : IsAdmissible ρ f g) : IsNewVariables f g :=
  ⟨T.contDiff_fst.differentiable one_ne_zero, T.contDiff_snd.differentiable one_ne_zero,
    T.injective, T.poissonBracket_ne_zero⟩

/-- The canonical coordinates are admissible. -/
lemma isAdmissible_fst_snd : IsAdmissible ρ Prod.fst Prod.snd where
  contDiff_fst := contDiff_fst
  contDiff_snd := contDiff_snd
  injective x y hxy := by simpa using hxy
  poissonBracket_ne_zero x := by rw [poissonBracket_fst_snd]; exact one_ne_zero
  integrable_log := by simp [poissonBracket_fst_snd]

/-- In the canonical coordinates `ρ_{qp} = ρ`. -/
lemma densityFG_fst_snd : densityFG Prod.fst Prod.snd ρ = ρ := by
  ext u
  simpa [poissonBracket_fst_snd] using
    (isAdmissible_fst_snd (ρ := ρ)).isNewVariables.densityFG_mul_abs_poissonBracket (ρ := ρ) u

/-- Condition **CUR** (classical uncertainty relation) for one DOF: `σ_q σ_p ≥ ħ / e`, with
equality exactly for independent Gaussians in `q, p` of zero entropy. -/
def UncertaintyRelation (h : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  hbar h / exp 1 ≤ sd ρ Prod.fst * sd ρ Prod.snd ∧
    (sd ρ Prod.fst * sd ρ Prod.snd = hbar h / exp 1 ↔ entropy h ρ = 0 ∧
      ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧ ρ =ᵐ[volume] gaussProd a v b w)

/-- Condition **GCUR** (generalized classical uncertainty relation) for one DOF: for every
admissible coordinate pair `(f, g)` with finite variances,
`σ_f σ_g ≥ (ħ / e) e^{E[log |{f, g}|]}`, with equality exactly when `S_h[ρ] = 0` and `ρ_{fg}` is
a product of Gaussians. -/
def GeneralizedUncertaintyRelation (h : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∀ f g : ℝ × ℝ → ℝ, IsAdmissible ρ f g → (Integrable fun x => f x ^ 2 * ρ x) →
    (Integrable fun x => g x ^ 2 * ρ x) →
    hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|) ≤ sd ρ f * sd ρ g ∧
      (sd ρ f * sd ρ g = hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|) ↔
        entropy h ρ = 0 ∧ ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧
          densityFG f g ρ =ᵐ[volume] gaussProd a v b w)

/-- Since `{q, p} = 1`, GCUR reduces to CUR in the canonical coordinates. -/
theorem GeneralizedUncertaintyRelation.uncertaintyRelation
    (hG : GeneralizedUncertaintyRelation h ρ) (hq : Integrable fun x => x.1 ^ 2 * ρ x)
    (hp : Integrable fun x => x.2 ^ 2 * ρ x) : UncertaintyRelation h ρ := by
  have := hG Prod.fst Prod.snd isAdmissible_fst_snd hq hp
  simp only [poissonBracket_fst_snd, abs_one, log_one, mul_zero, integral_zero, exp_zero, mul_one,
    densityFG_fst_snd] at this
  exact this

end Conditions

/-! ### Theorem 9: ZENT implies GCUR and CUR -/

section Theorem9

variable {ρ : ℝ × ℝ → ℝ} {h : ℝ}

/-- **Theorem 9.** Over finite entropy, ZENT implies GCUR, with its equality case. -/
theorem generalizedUncertaintyRelation_of_lowerEntropicBound (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hZ : LowerEntropicBound h ρ) : GeneralizedUncertaintyRelation h ρ :=
  fun _ _ T hf2 hg2 =>
    ⟨T.isNewVariables.hbar_div_exp_mul_exp_le_sd_mul_sd hh hρ hf2 hg2 T.integrable_log hZ,
      T.isNewVariables.sd_mul_sd_eq_hbar_div_exp_mul_exp_iff hh hρ hf2 hg2 T.integrable_log hZ⟩

/-- **Theorem 9.** Over finite entropy and finite variances, ZENT implies CUR, with its equality
case. -/
theorem uncertaintyRelation_of_lowerEntropicBound (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x)
    (hZ : LowerEntropicBound h ρ) : UncertaintyRelation h ρ :=
  (generalizedUncertaintyRelation_of_lowerEntropicBound hh hρ hZ).uncertaintyRelation hq hp

end Theorem9

/-! ### Theorem 8: finite entropy guarantees none of the conditions -/

section Theorem8

variable {h : ℝ}

lemma hbar_div_exp_pos' (hh : 0 < h) : 0 < h / (4 * π * exp 1) := by positivity

/-- **Theorem 8.** Over finite entropy, none of ZENT, CUR and GCUR is guaranteed: the product of
centred Gaussians with `σ_q = σ_p = √(h / 4π e)` has entropy `-log 2` and
`σ_q σ_p = ħ / 2e < ħ / e`. -/
theorem exists_ensemble_not_conditions (hh : 0 < h) :
    ∃ ρ : ℝ × ℝ → ℝ, IsEnsemble ρ ∧ (Integrable fun x => x.1 ^ 2 * ρ x) ∧
      (Integrable fun x => x.2 ^ 2 * ρ x) ∧ entropy h ρ = -log 2 ∧
      ¬ LowerEntropicBound h ρ ∧ ¬ UncertaintyRelation h ρ ∧
      ¬ GeneralizedUncertaintyRelation h ρ := by
  set κ := h / (4 * π * exp 1)
  have hκ : 0 < κ := hbar_div_exp_pos' hh
  have hv : κ.toNNReal ≠ 0 := by simpa using hκ
  have hsd : √(κ.toNNReal : ℝ) * √(κ.toNNReal : ℝ) = κ := by
    rw [Real.coe_toNNReal _ hκ.le, mul_self_sqrt hκ.le]
  set ρ := gaussProd 0 κ.toNNReal 0 κ.toNNReal
  have hρ : IsEnsemble ρ := isEnsemble_gaussProd hv hv
  have hq := integrable_fst_sq_mul_gaussProd (a := 0) (b := 0) (w := κ.toNNReal) hv
  have hp := integrable_snd_sq_mul_gaussProd (a := 0) (b := 0) (v := κ.toNNReal) hv
  have hS : entropy h ρ = -log 2 := by
    rw [entropy_gaussProd hh hv hv, hsd, ← log_div (by positivity) hh.ne', ← log_inv]
    congr 1
    simp only [κ]
    field_simp
    ring
  have hlt : sd ρ Prod.fst * sd ρ Prod.snd < hbar h / exp 1 := by
    rw [sd_mul_sd_gaussProd hv hv, hsd, hbar_div_exp_eq]
    simp only [κ]
    exact div_lt_div_of_pos_left hh (by positivity) (by nlinarith [exp_pos 1, pi_pos])
  have hnot : ¬ UncertaintyRelation h ρ := fun hU => (not_le.2 hlt) hU.1
  refine ⟨ρ, hρ, hq, hp, hS, ?_, hnot, fun hG => hnot (hG.uncertaintyRelation hq hp)⟩
  rw [LowerEntropicBound, hS, not_le, neg_neg_iff_pos]
  exact log_pos one_lt_two

end Theorem8

/-! ### Theorem 11: CUR does not imply ZENT -/

section Theorem11

variable {h s k : ℝ}

/-- The second coordinate `p + k q` of the shear `(q, p) ↦ (q, p + k q)`. -/
def shearSnd (k : ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ ℝ ℝ + k • ContinuousLinearMap.fst ℝ ℝ ℝ

@[simp] lemma shearSnd_apply (k : ℝ) (x : ℝ × ℝ) : shearSnd k x = x.2 + k * x.1 := by
  simp [shearSnd]

lemma poissonBracket_shear (k : ℝ) (x : ℝ × ℝ) : poissonBracket Prod.fst (shearSnd k) x = 1 := by
  simp [poissonBracket, fderiv_fst, ContinuousLinearMap.fderiv]

/-- The shear coordinates `(q, p + k q)` are admissible for every ensemble. -/
lemma isAdmissible_shear {ρ : ℝ × ℝ → ℝ} (k : ℝ) : IsAdmissible ρ Prod.fst (shearSnd k) where
  contDiff_fst := contDiff_fst
  contDiff_snd := (shearSnd k).contDiff
  injective x y hxy := by
    simp only [Prod.mk.injEq, shearSnd_apply] at hxy
    exact Prod.ext hxy.1 (by rw [hxy.1] at hxy; linarith [hxy.2])
  poissonBracket_ne_zero x := by rw [poissonBracket_shear]; exact one_ne_zero
  integrable_log := by simp [poissonBracket_shear]

/-- The momentum width `c = h / (4π e s)` of Theorem 11. -/
def corrWidth (h s : ℝ) : ℝ := h / (4 * π * exp 1 * s)

/-- The shear `k = 2√2 c / s` of Theorem 11. -/
def corrShear (h s : ℝ) : ℝ := 2 * √2 * corrWidth h s / s

/-- The independent Gaussians `X, Y` of Theorem 11, scaled: the density of `(s X, c Y)`. -/
def corrBase (h s : ℝ) : ℝ × ℝ → ℝ :=
  gaussProd 0 (s ^ 2).toNNReal 0 (corrWidth h s ^ 2).toNNReal

/-- **The ensemble of Theorem 11**, the density of `q = s X`, `p = c (2√2 X + Y)`:
`ρ_{qp} = (2π s c)⁻¹ e^{-((q / s)² + (p / c - 2√2 q / s)²) / 2}`. -/
def correlatedGaussian (h s : ℝ) (x : ℝ × ℝ) : ℝ :=
  corrBase h s (x.1, x.2 - corrShear h s * x.1)

lemma corrWidth_pos (hh : 0 < h) (hs : 0 < s) : 0 < corrWidth h s := by unfold corrWidth; positivity

lemma corrBase_v_ne_zero (hs : 0 < s) : (s ^ 2).toNNReal ≠ 0 := by simpa using hs.ne'

lemma corrBase_w_ne_zero (hh : 0 < h) (hs : 0 < s) : (corrWidth h s ^ 2).toNNReal ≠ 0 := by
  simpa using (corrWidth_pos hh hs).ne'

/-- `ρ_{qp}` is the density of the base Gaussian in the shear coordinates `(q, p + k q)`. -/
lemma correlatedGaussian_eq :
    correlatedGaussian h s = densityFG Prod.fst (shearSnd (corrShear h s)) (corrBase h s) := by
  ext u
  have := (isAdmissible_shear (ρ := corrBase h s) (corrShear h s)).isNewVariables
    |>.densityFG_mul_abs_poissonBracket (ρ := corrBase h s) (u.1, u.2 - corrShear h s * u.1)
  simp only [poissonBracket_shear, abs_one, mul_one, shearSnd_apply, sub_add_cancel] at this
  rw [correlatedGaussian, ← this]

lemma isEnsemble_correlatedGaussian (hh : 0 < h) (hs : 0 < s) :
    IsEnsemble (correlatedGaussian h s) := by
  rw [correlatedGaussian_eq]
  exact (isAdmissible_shear (ρ := corrBase h s) _).isNewVariables.isEnsemble_densityFG
    (isEnsemble_gaussProd (corrBase_v_ne_zero hs) (corrBase_w_ne_zero hh hs))
    (by simp [poissonBracket_shear])

/-- Integrals against `ρ_{qp}` of a quadratic form in `(q, p)`, as integrals against the base. -/
lemma integral_linear_sq_correlatedGaussian (hh : 0 < h) (hs : 0 < s) (α β : ℝ) :
    Integrable (fun u : ℝ × ℝ => (α * u.1 + β * u.2) ^ 2 * correlatedGaussian h s u) ∧
    ∫ u : ℝ × ℝ, (α * u.1 + β * u.2) ^ 2 * correlatedGaussian h s u =
      (α + β * corrShear h s) ^ 2 * s ^ 2 + β ^ 2 * corrWidth h s ^ 2 := by
  have H := (isAdmissible_shear (ρ := corrBase h s) (corrShear h s)).isNewVariables
  obtain ⟨hi, he⟩ := integral_linear_mul_linear_gaussProd (corrBase_v_ne_zero hs)
    (corrBase_w_ne_zero hh hs) (α + β * corrShear h s) β (α + β * corrShear h s) β
  have hfun : (fun x : ℝ × ℝ => (α * x.1 + β * shearSnd (corrShear h s) x) ^ 2 * corrBase h s x) =
      fun x => ((α + β * corrShear h s) * x.1 + β * x.2) *
        ((α + β * corrShear h s) * x.1 + β * x.2) * corrBase h s x := by
    ext x
    simp only [shearSnd_apply]
    ring
  rw [correlatedGaussian_eq]
  refine ⟨(H.integrable_mul_densityFG_iff (φ := fun u => (α * u.1 + β * u.2) ^ 2)).2
    (hfun ▸ hi), ?_⟩
  rw [H.integral_mul_densityFG (φ := fun u => (α * u.1 + β * u.2) ^ 2)]
  simp only at hfun ⊢
  rw [hfun]
  unfold corrBase
  rw [he, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  ring

/-- The mean of a linear form in `(q, p)` under `ρ_{qp}` is zero. -/
lemma mean_linear_correlatedGaussian (hh : 0 < h) (hs : 0 < s) (α β : ℝ) :
    mean (correlatedGaussian h s) (fun u => α * u.1 + β * u.2) = 0 := by
  have H := (isAdmissible_shear (ρ := corrBase h s) (corrShear h s)).isNewVariables
  rw [mean, correlatedGaussian_eq,
    H.integral_mul_densityFG (φ := fun u => α * u.1 + β * u.2)]
  have hfun : (fun x : ℝ × ℝ => (α * x.1 + β * shearSnd (corrShear h s) x) * corrBase h s x) =
      fun x => ((α + β * corrShear h s) * x.1 + β * x.2) * corrBase h s x := by
    ext x
    simp only [shearSnd_apply]
    ring
  simp only at hfun ⊢
  rw [hfun]
  exact (integral_linear_mul_gaussProd (corrBase_v_ne_zero hs)
    (corrBase_w_ne_zero hh hs) _ _).2

lemma sd_linear_correlatedGaussian (hh : 0 < h) (hs : 0 < s) (α β : ℝ) :
    sd (correlatedGaussian h s) (fun u => α * u.1 + β * u.2) =
      √((α + β * corrShear h s) ^ 2 * s ^ 2 + β ^ 2 * corrWidth h s ^ 2) := by
  rw [sd, var, mean_linear_correlatedGaussian hh hs]
  simp only [sub_zero]
  rw [(integral_linear_sq_correlatedGaussian hh hs α β).2]

lemma corrShear_sq_mul (hs : 0 < s) : corrShear h s ^ 2 * s ^ 2 = 8 * corrWidth h s ^ 2 := by
  unfold corrShear
  rw [div_pow, mul_pow, mul_pow, sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  ring

lemma s_mul_corrWidth (hs : 0 < s) : s * corrWidth h s = h / (4 * π * exp 1) := by
  unfold corrWidth
  field_simp

lemma fst_eq_linear : (Prod.fst : ℝ × ℝ → ℝ) = fun u => 1 * u.1 + 0 * u.2 := by
  ext u; ring

lemma snd_eq_linear : (Prod.snd : ℝ × ℝ → ℝ) = fun u => 0 * u.1 + 1 * u.2 := by
  ext u; ring

lemma shearSnd_eq_linear : (⇑(shearSnd k) : ℝ × ℝ → ℝ) = fun u => k * u.1 + 1 * u.2 := by
  ext u; simp only [shearSnd_apply]; ring

/-- `σ_q = s`. -/
lemma sd_fst_correlatedGaussian (hh : 0 < h) (hs : 0 < s) :
    sd (correlatedGaussian h s) Prod.fst = s := by
  rw [fst_eq_linear, sd_linear_correlatedGaussian hh hs]
  simp only [zero_mul, add_zero, one_pow, one_mul, zero_pow two_ne_zero]
  exact sqrt_sq hs.le

/-- `σ_p = 3 c`. -/
lemma sd_snd_correlatedGaussian (hh : 0 < h) (hs : 0 < s) :
    sd (correlatedGaussian h s) Prod.snd = 3 * corrWidth h s := by
  rw [snd_eq_linear, sd_linear_correlatedGaussian hh hs]
  have hc := corrWidth_pos hh hs
  simp only [one_mul, zero_add, one_pow]
  rw [corrShear_sq_mul hs, show 8 * corrWidth h s ^ 2 + corrWidth h s ^ 2 =
    (3 * corrWidth h s) ^ 2 by ring]
  exact sqrt_sq (by positivity)

/-- `σ_g = c` for `g = p - k q`. -/
lemma sd_shear_correlatedGaussian (hh : 0 < h) (hs : 0 < s) :
    sd (correlatedGaussian h s) (shearSnd (-corrShear h s)) = corrWidth h s := by
  rw [shearSnd_eq_linear, sd_linear_correlatedGaussian hh hs]
  simp only [one_mul, neg_add_cancel, zero_pow two_ne_zero, zero_mul, zero_add, one_pow]
  exact sqrt_sq (corrWidth_pos hh hs).le

/-- `S_h[ρ] = -log 2`. -/
lemma entropy_correlatedGaussian (hh : 0 < h) (hs : 0 < s) :
    entropy h (correlatedGaussian h s) = -log 2 := by
  have H := (isAdmissible_shear (ρ := corrBase h s) (corrShear h s)).isNewVariables
  have hv := corrBase_v_ne_zero hs
  have hw := corrBase_w_ne_zero hh hs
  rw [correlatedGaussian_eq, H.entropy_densityFG (ρ := corrBase h s) hh
    (show IsEnsemble (corrBase h s) volume from isEnsemble_gaussProd (a := 0) (b := 0) hv hw)
    (by simp [poissonBracket_shear])]
  simp only [poissonBracket_shear, abs_one, log_one, mul_zero, integral_zero, add_zero]
  unfold corrBase
  rw [entropy_gaussProd hh hv hw, Real.coe_toNNReal _ (by positivity),
    Real.coe_toNNReal _ (by positivity), sqrt_sq hs.le, sqrt_sq (corrWidth_pos hh hs).le,
    s_mul_corrWidth hs, ← log_div (by positivity) hh.ne', ← log_inv]
  congr 1
  field_simp
  ring

/-- **Theorem 11.** Over finite entropy, CUR does not guarantee ZENT: the correlated Gaussian
`q = s X`, `p = c (2√2 X + Y)` with `c = h / 4π e s` satisfies CUR strictly
(`σ_q σ_p = 3h / 4π e`), has entropy `-log 2`, and violates GCUR in the coordinates
`(q, p - 2√2 (c / s) q)`. -/
theorem exists_uncertaintyRelation_not_lowerEntropicBound (hh : 0 < h) (hs : 0 < s) :
    IsEnsemble (correlatedGaussian h s) ∧
      (Integrable fun x => x.1 ^ 2 * correlatedGaussian h s x) ∧
      (Integrable fun x => x.2 ^ 2 * correlatedGaussian h s x) ∧
      sd (correlatedGaussian h s) Prod.fst * sd (correlatedGaussian h s) Prod.snd =
        3 * h / (4 * π * exp 1) ∧
      UncertaintyRelation h (correlatedGaussian h s) ∧
      entropy h (correlatedGaussian h s) = -log 2 ∧
      ¬ LowerEntropicBound h (correlatedGaussian h s) ∧
      ¬ GeneralizedUncertaintyRelation h (correlatedGaussian h s) := by
  have hc := corrWidth_pos hh hs
  have hq : Integrable fun x : ℝ × ℝ => x.1 ^ 2 * correlatedGaussian h s x := by
    simpa using (integral_linear_sq_correlatedGaussian hh hs 1 0).1
  have hp : Integrable fun x : ℝ × ℝ => x.2 ^ 2 * correlatedGaussian h s x := by
    simpa using (integral_linear_sq_correlatedGaussian hh hs 0 1).1
  have hprod : sd (correlatedGaussian h s) Prod.fst * sd (correlatedGaussian h s) Prod.snd =
      3 * h / (4 * π * exp 1) := by
    rw [sd_fst_correlatedGaussian hh hs, sd_snd_correlatedGaussian hh hs,
      show s * (3 * corrWidth h s) = 3 * (s * corrWidth h s) by ring, s_mul_corrWidth hs]
    ring
  have hS := entropy_correlatedGaussian hh hs
  have hlog2 : 0 < log 2 := log_pos one_lt_two
  have hħ : hbar h / exp 1 < 3 * h / (4 * π * exp 1) := by
    rw [hbar_div_exp_eq, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [exp_pos 1, pi_pos, mul_pos (mul_pos hh pi_pos) (exp_pos 1)]
  refine ⟨isEnsemble_correlatedGaussian hh hs, hq, hp, hprod, ⟨?_, ?_⟩, hS, ?_, ?_⟩
  · rw [hprod]
    exact hħ.le
  · rw [hprod, hS]
    exact iff_of_false hħ.ne' fun h0 => by linarith [h0.1]
  · rw [LowerEntropicBound, hS]
    linarith
  · intro hG
    have hg2 : Integrable fun x : ℝ × ℝ =>
        shearSnd (-corrShear h s) x ^ 2 * correlatedGaussian h s x := by
      have := (integral_linear_sq_correlatedGaussian hh hs (-corrShear h s) 1).1
      simpa only [shearSnd_apply, one_mul, add_comm] using this
    have := (hG Prod.fst (shearSnd (-corrShear h s)) (isAdmissible_shear _) hq hg2).1
    simp only [poissonBracket_shear, abs_one, log_one, mul_zero, integral_zero, exp_zero,
      mul_one] at this
    rw [sd_fst_correlatedGaussian hh hs, sd_shear_correlatedGaussian hh hs,
      s_mul_corrWidth hs, hbar_div_exp_eq] at this
    have : h / (2 * π * exp 1) ≤ h / (4 * π * exp 1) := this
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at this
    nlinarith [exp_pos 1, pi_pos, mul_pos (mul_pos hh pi_pos) (exp_pos 1)]

end Theorem11

/-! ### Proposition 6 and Theorem 12: GCUR implies ZENT -/

section Theorem12

variable {ρ f g : ℝ × ℝ → ℝ} {h : ℝ}

/-- `U_ρ(T) = log (2π e σ_f σ_g / h) - E[log |{f, g}|]` for the coordinates `T = (f, g)`. -/
def coordinateUncertainty (h : ℝ) (ρ f g : ℝ × ℝ → ℝ) : ℝ :=
  log (2 * π * exp 1 * (sd ρ f * sd ρ g) / h) - ∫ x, ρ x * log |poissonBracket f g x|

/-- `U_ρ(T) = S_h[ρ] + D(ρ_{fg} ‖ G_{fg}) ≥ S_h[ρ]` for finite variances. -/
theorem entropy_le_coordinateUncertainty (hh : 0 < h) (hρ : IsEnsemble ρ) (T : IsAdmissible ρ f g)
    (hf2 : Integrable fun x => f x ^ 2 * ρ x) (hg2 : Integrable fun x => g x ^ 2 * ρ x) :
    coordinateUncertainty h ρ f g = entropy h ρ + gaussianDivergence (densityFG f g ρ) ∧
      entropy h ρ ≤ coordinateUncertainty h ρ f g := by
  have H := T.isNewVariables
  have he := H.log_eq_entropy_add hh hρ hf2 hg2 T.integrable_log
  have hD := gaussianDivergence_nonneg (H.isEnsemble_densityFG hρ T.integrable_log)
    (H.integrable_fst_sq_densityFG hf2) (H.integrable_snd_sq_densityFG hg2)
  refine ⟨by rw [coordinateUncertainty, he]; ring, ?_⟩
  rw [coordinateUncertainty, he]
  linarith

/-- The inequality of GCUR says `U_ρ(T) ≥ 0`. -/
lemma hbar_div_exp_mul_exp_le_iff_coordinateUncertainty_nonneg (hh : 0 < h) (hρ : IsEnsemble ρ)
    (T : IsAdmissible ρ f g) (hf2 : Integrable fun x => f x ^ 2 * ρ x)
    (hg2 : Integrable fun x => g x ^ 2 * ρ x) :
    hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|) ≤ sd ρ f * sd ρ g ↔
      0 ≤ coordinateUncertainty h ρ f g := by
  have hpos := T.isNewVariables.sd_mul_sd_pos hρ hf2 hg2 T.integrable_log
  rw [hbar_div_exp_mul_exp_le_iff hh hpos, coordinateUncertainty, log_div (by positivity) hh.ne']
  constructor <;> intro <;> linarith

/-- The conclusion of **Proposition 6** for finite entropy: admissible coordinates with finite
variances in which `D(ρ_{fg} ‖ G_{fg})` is arbitrarily small. The brief obtains them by
approximating `ρ` with smooth positive densities and transporting these to a fixed product of
Gaussians; this is not formalized. -/
def HasGaussianFrames (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ f g : ℝ × ℝ → ℝ, IsAdmissible ρ f g ∧ (Integrable fun x => f x ^ 2 * ρ x) ∧
    (Integrable fun x => g x ^ 2 * ρ x) ∧ gaussianDivergence (densityFG f g ρ) < ε

/-- `D(ρ ‖ G_ρ) = 0` when `ρ` is a.e. a product of Gaussians. -/
lemma gaussianDivergence_eq_zero {a b : ℝ} {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0)
    (hG : ρ =ᵐ[volume] gaussProd a v b w) : gaussianDivergence ρ = 0 := by
  have hm : matchedGauss ρ = gaussProd a v b w := by
    rw [matchedGauss, mean_fst_gaussProd hG hv hw, mean_snd_gaussProd hG hv hw,
      var_fst_gaussProd hG hv hw, var_snd_gaussProd hG hv hw, Real.toNNReal_coe,
      Real.toNNReal_coe]
  rw [gaussianDivergence, hm]
  refine integral_eq_zero_of_ae (hG.mono fun x hx => ?_)
  change ρ x * log (ρ x / gaussProd a v b w x) = 0
  rw [hx, div_self (gaussProd_pos hv hw x).ne', log_one, mul_zero]

/-- **Proposition 5 gives Gaussian frames.** Coordinates in which `ρ_{fg}` is a product of
Gaussians, as Greene–Shiohama provide for a positive smooth `ρ`, make the divergence vanish. -/
theorem hasGaussianFrames_of_densityFG_eq (T : IsAdmissible ρ f g)
    (hf2 : Integrable fun x => f x ^ 2 * ρ x) (hg2 : Integrable fun x => g x ^ 2 * ρ x)
    {a b : ℝ} {v w : ℝ≥0} (hv : v ≠ 0) (hw : w ≠ 0)
    (hG : densityFG f g ρ =ᵐ[volume] gaussProd a v b w) : HasGaussianFrames ρ :=
  fun _ hε => ⟨f, g, T, hf2, hg2, (gaussianDivergence_eq_zero hv hw hG).symm ▸ hε⟩

/-- **Proposition 6, eq. (7)**, for finite entropy and from `HasGaussianFrames`:
`inf_T U_ρ(T) = S_h[ρ]` over admissible coordinates with finite variances. -/
theorem isGLB_coordinateUncertainty (hh : 0 < h) (hρ : IsEnsemble ρ) (hF : HasGaussianFrames ρ) :
    IsGLB {u | ∃ f g : ℝ × ℝ → ℝ, IsAdmissible ρ f g ∧ (Integrable fun x => f x ^ 2 * ρ x) ∧
      (Integrable fun x => g x ^ 2 * ρ x) ∧ u = coordinateUncertainty h ρ f g} (entropy h ρ) := by
  refine ⟨?_, fun b hb => le_of_forall_pos_lt_add fun ε hε => ?_⟩
  · rintro _ ⟨f, g, T, hf2, hg2, rfl⟩
    exact (entropy_le_coordinateUncertainty hh hρ T hf2 hg2).2
  · obtain ⟨f, g, T, hf2, hg2, hD⟩ := hF ε hε
    have hU := (entropy_le_coordinateUncertainty hh hρ T hf2 hg2).1
    have := hb ⟨f, g, T, hf2, hg2, rfl⟩
    linarith

/-- **Theorem 12**, from the conclusion of Proposition 6. Over finite entropy, GCUR implies
ZENT. -/
theorem lowerEntropicBound_of_generalizedUncertaintyRelation (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hF : HasGaussianFrames ρ) (hG : GeneralizedUncertaintyRelation h ρ) :
    LowerEntropicBound h ρ := by
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨f, g, T, hf2, hg2, hD⟩ := hF ε hε
  have h1 := (hbar_div_exp_mul_exp_le_iff_coordinateUncertainty_nonneg hh hρ T hf2 hg2).1
    (hG f g T hf2 hg2).1
  have hU := (entropy_le_coordinateUncertainty hh hρ T hf2 hg2).1
  linarith

/-- **Theorem 12**, from the conclusion of Proposition 6. Over finite entropy, GCUR and ZENT
are equivalent. -/
theorem lowerEntropicBound_iff_generalizedUncertaintyRelation (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hF : HasGaussianFrames ρ) :
    LowerEntropicBound h ρ ↔ GeneralizedUncertaintyRelation h ρ :=
  ⟨generalizedUncertaintyRelation_of_lowerEntropicBound hh hρ,
    lowerEntropicBound_of_generalizedUncertaintyRelation hh hρ hF⟩

end Theorem12

/-! ### Convexity of the finite-entropy domain -/

section Convexity

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ σ : X → ℝ} {c t : ℝ}

lemma negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  have key : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a * log a ≤ a * log (a + b) := fun {a b} ha hb => by
    rcases ha.eq_or_lt with rfl | ha
    · simp
    · exact mul_le_mul_of_nonneg_left (log_le_log ha (by linarith)) ha.le
  have h1 := key hx hy
  have h2 := key hy hx
  rw [add_comm y x] at h2
  simp only [negMulLog]
  nlinarith

/-- Pointwise bounds on `-m log m` for the mixture `m = t a + (1 - t) b`. -/
lemma negMulLog_mix_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * negMulLog a + (1 - t) * negMulLog b ≤ negMulLog (t * a + (1 - t) * b) ∧
      negMulLog (t * a + (1 - t) * b) ≤ t * negMulLog a + (1 - t) * negMulLog b +
        (a * negMulLog t + b * negMulLog (1 - t)) := by
  refine ⟨?_, ?_⟩
  · simpa [smul_eq_mul] using
      Real.concaveOn_negMulLog.2 (mem_Ici.2 ha) (mem_Ici.2 hb) ht0 (by linarith) (by ring)
  · refine (negMulLog_add_le (mul_nonneg ht0 ha) (mul_nonneg (by linarith) hb)).trans_eq ?_
    rw [negMulLog_mul, negMulLog_mul]
    ring

lemma integrable_negMulLog_mix (hρ : IsEnsemble ρ μ) (hσ : IsEnsemble σ μ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : Integrable (fun x => negMulLog (t * ρ x + (1 - t) * σ x)) μ := by
  have hm : AEStronglyMeasurable (fun x => t * ρ x + (1 - t) * σ x) μ :=
    ((hρ.integrable.const_mul t).add (hσ.integrable.const_mul (1 - t))).1
  refine integrable_of_le_of_le (Real.continuous_negMulLog.comp_aestronglyMeasurable hm)
    (ae_of_all _ fun x => (negMulLog_mix_bounds (hρ.nonneg x) (hσ.nonneg x) ht0 ht1).1)
    (ae_of_all _ fun x => (negMulLog_mix_bounds (hρ.nonneg x) (hσ.nonneg x) ht0 ht1).2)
    ((hρ.integrable_negMulLog.const_mul t).add (hσ.integrable_negMulLog.const_mul (1 - t)))
    (((hρ.integrable_negMulLog.const_mul t).add (hσ.integrable_negMulLog.const_mul (1 - t))).add
      ((hρ.integrable.mul_const (negMulLog t)).add (hσ.integrable.mul_const (negMulLog (1 - t)))))

/-- **Convexity.** A mixture of two ensembles of finite entropy is one. -/
theorem isEnsemble_mix (hρ : IsEnsemble ρ μ) (hσ : IsEnsemble σ μ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsEnsemble (fun x => t * ρ x + (1 - t) * σ x) μ where
  nonneg x := add_nonneg (mul_nonneg ht0 (hρ.nonneg x)) (mul_nonneg (by linarith) (hσ.nonneg x))
  integral_eq_one := by
    rw [integral_add (hρ.integrable.const_mul t) (hσ.integrable.const_mul (1 - t)),
      integral_const_mul, integral_const_mul, hρ.integral_eq_one, hσ.integral_eq_one]
    ring
  integrable_negMulLog := integrable_negMulLog_mix hρ hσ ht0 ht1

/-- **Convexity, the entropy of a mixture.** With `ρ_t = t ρ + (1 - t) σ`,
`0 ≤ S[ρ_t] - t S[ρ] - (1 - t) S[σ] ≤ -t log t - (1 - t) log (1 - t)`. -/
theorem entropy_mix_bounds (hc : 0 < c) (hρ : IsEnsemble ρ μ) (hσ : IsEnsemble σ μ) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    0 ≤ entropy c (fun x => t * ρ x + (1 - t) * σ x) μ - (t * entropy c ρ μ +
        (1 - t) * entropy c σ μ) ∧
      entropy c (fun x => t * ρ x + (1 - t) * σ x) μ - (t * entropy c ρ μ +
        (1 - t) * entropy c σ μ) ≤ negMulLog t + negMulLog (1 - t) := by
  have hm := integrable_negMulLog_mix hρ hσ ht0 ht1
  have i1 : Integrable (fun x => t * negMulLog (ρ x) + (1 - t) * negMulLog (σ x)) μ :=
    (hρ.integrable_negMulLog.const_mul t).add (hσ.integrable_negMulLog.const_mul (1 - t))
  have i2 : Integrable (fun x => ρ x * negMulLog t + σ x * negMulLog (1 - t)) μ :=
    (hρ.integrable.mul_const (negMulLog t)).add (hσ.integrable.mul_const (negMulLog (1 - t)))
  have i12 : Integrable (fun x => (t * negMulLog (ρ x) + (1 - t) * negMulLog (σ x)) +
      (ρ x * negMulLog t + σ x * negMulLog (1 - t))) μ := i1.add i2
  have lo := integral_mono i1 hm fun x =>
    (negMulLog_mix_bounds (hρ.nonneg x) (hσ.nonneg x) ht0 ht1).1
  have hi := integral_mono hm i12 fun x =>
    (negMulLog_mix_bounds (hρ.nonneg x) (hσ.nonneg x) ht0 ht1).2
  rw [integral_add (hρ.integrable_negMulLog.const_mul t) (hσ.integrable_negMulLog.const_mul _),
    integral_const_mul, integral_const_mul] at lo
  rw [integral_add i1 i2, integral_add (hρ.integrable_negMulLog.const_mul t)
    (hσ.integrable_negMulLog.const_mul _), integral_const_mul, integral_const_mul,
    integral_add (hρ.integrable.mul_const _) (hσ.integrable.mul_const _), integral_mul_const,
    integral_mul_const, hρ.integral_eq_one, hσ.integral_eq_one] at hi
  rw [entropy_eq (isEnsemble_mix hρ hσ ht0 ht1) hc, entropy_eq hρ hc, entropy_eq hσ hc]
  constructor <;> nlinarith

end Convexity

end ClassicalUncertaintyPrinciple
