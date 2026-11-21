/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ClassicalUncertaintyPrinciple.Equivalence
public import Mathlib.Probability.Distributions.Cauchy

import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Classical uncertainty relation: the extended variance

The brief *Classical uncertainty relation* allows infinite variances through the extended variance

  `σ_f² = inf_a E[(f - a)²] ∈ [0, ∞]`,

defined even when `f` has no mean, and states CUR and GCUR with it. The conditions
`UncertaintyRelation` and `GeneralizedUncertaintyRelation` of
`ClassicalUncertaintyPrinciple.Equivalence` use Bochner variances and so finite second moments.
This file states the conditions with the extended variance and shows that nothing is lost.

The extended variance is finite exactly when `f` has a finite second moment, and then it is the
variance, attained at the mean, since `E[(f - a)²] = σ_f² + (E[f] - a)²`. It is never zero for a
coordinate of an admissible pair: `ρ_{fg}` is a density on the plane, and a line has no area. So
an infinite variance makes `σ_f σ_g = ∞`: the inequality holds, and the equality, which needs
`ρ_{fg}` to be a product of Gaussians and so finite variances, fails on both sides. Hence the
extended GCUR is GCUR, and the extended CUR is CUR when the canonical variances are finite and
holds automatically otherwise. Theorems 9 and 12 follow in the brief's form, Theorem 9 for CUR
without any moment hypothesis.

The remark *Entropy and variance* of the brief, that finite entropy does not require finite
canonical variances, has the product of two standard Cauchy densities as an example.

## Main definitions

* `ClassicalUncertaintyPrinciple.extendedVar`, `ClassicalUncertaintyPrinciple.extendedSd`: the
  extended variance and standard deviation.
* `ClassicalUncertaintyPrinciple.ExtendedUncertaintyRelation`,
  `ClassicalUncertaintyPrinciple.ExtendedGeneralizedUncertaintyRelation`: CUR and GCUR as the
  brief states them.

## Main results

* `ClassicalUncertaintyPrinciple.extendedVar_eq_ofReal_var`,
  `ClassicalUncertaintyPrinciple.extendedVar_ne_top_iff`: the extended variance is the variance
  when finite, and finite exactly for a finite second moment.
* `ClassicalUncertaintyPrinciple.IsAdmissible.extendedVar_fst_ne_zero`,
  `ClassicalUncertaintyPrinciple.IsAdmissible.extendedVar_snd_ne_zero`: admissible coordinates
  are not almost surely constant.
* `ClassicalUncertaintyPrinciple.extendedGeneralizedUncertaintyRelation_iff`: the extended GCUR
  is GCUR.
* `ClassicalUncertaintyPrinciple.extendedUncertaintyRelation_iff`,
  `ClassicalUncertaintyPrinciple.extendedUncertaintyRelation_of_not_integrable`: the extended CUR
  is CUR for finite canonical variances, and automatic otherwise.
* `ClassicalUncertaintyPrinciple.extendedGeneralizedUncertaintyRelation_of_lowerEntropicBound`,
  `ClassicalUncertaintyPrinciple.extendedUncertaintyRelation_of_lowerEntropicBound`: Theorem 9.
* `ClassicalUncertaintyPrinciple.lowerEntropicBound_iff_extendedGeneralizedUncertaintyRelation`:
  Theorem 12.
* `ClassicalUncertaintyPrinciple.exists_isEnsemble_extendedVar_eq_top`: the remark *Entropy and
  variance*.
-/

open Real MeasureTheory ProbabilityTheory Set

open scoped NNReal ENNReal

@[expose] public noncomputable section

namespace ClassicalUncertaintyPrinciple

/-! ### The extended variance -/

section ExtendedVariance

variable {X : Type*} [MeasurableSpace X]

/-- The extended variance `σ_f² = inf_a E[(f - a)²] ∈ [0, ∞]`, defined even when `f` has no
mean. -/
def extendedVar (ρ f : X → ℝ) (μ : Measure X := by volume_tac) : ℝ≥0∞ :=
  ⨅ a : ℝ, ∫⁻ x, ENNReal.ofReal ((f x - a) ^ 2 * ρ x) ∂μ

/-- The extended standard deviation `σ_f ∈ [0, ∞]`. -/
def extendedSd (ρ f : X → ℝ) (μ : Measure X := by volume_tac) : ℝ≥0∞ :=
  extendedVar ρ f μ ^ (1 / 2 : ℝ)

variable {μ : Measure X} {ρ f : X → ℝ}

/-- A probability density, of finite or infinite entropy. -/
structure IsDensity (ρ : X → ℝ) (μ : Measure X := by volume_tac) : Prop where
  nonneg : ∀ x, 0 ≤ ρ x
  integral_eq_one : ∫ x, ρ x ∂μ = 1

lemma IsEnsemble.isDensity (hρ : IsEnsemble ρ μ) : IsDensity ρ μ :=
  ⟨hρ.nonneg, hρ.integral_eq_one⟩

namespace IsDensity

variable (hρ : IsDensity ρ μ)
include hρ

lemma integrable : Integrable ρ μ :=
  Integrable.of_integral_ne_zero (by rw [hρ.integral_eq_one]; norm_num)

lemma integrable_mul (hf : Measurable f) (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) :
    Integrable (fun x => f x * ρ x) μ := by
  refine (hf2.add hρ.integrable).mono' (hf.aestronglyMeasurable.mul hρ.integrable.1)
    (ae_of_all _ fun x => ?_)
  have hx : ‖f x‖ ≤ f x ^ 2 + 1 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (f x), abs_nonneg (f x)]
  rw [norm_mul, Real.norm_of_nonneg (hρ.nonneg x), Pi.add_apply, ← add_one_mul]
  exact mul_le_mul_of_nonneg_right hx (hρ.nonneg x)

lemma var_nonneg : 0 ≤ var ρ f μ :=
  integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hρ.nonneg x)

end IsDensity

lemma integrable_sub_sq_mul (hρ : IsDensity ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) (a : ℝ) :
    Integrable (fun x => (f x - a) ^ 2 * ρ x) μ :=
  ((hf2.sub ((hρ.integrable_mul hf hf2).const_mul (2 * a))).add
    (hρ.integrable.const_mul (a ^ 2))).congr (ae_of_all _ fun x => by
      simp only [Pi.add_apply, Pi.sub_apply]
      ring)

/-- `E[(f - a)²] = σ_f² + (E[f] - a)²`. -/
lemma integral_sub_sq_mul (hρ : IsDensity ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) (a : ℝ) :
    ∫ x, (f x - a) ^ 2 * ρ x ∂μ = var ρ f μ + (mean ρ f μ - a) ^ 2 := by
  have h1 := hρ.integrable_mul hf hf2
  have key : ∀ c, ∫ x, (f x - c) ^ 2 * ρ x ∂μ =
      ∫ x, f x ^ 2 * ρ x ∂μ - 2 * c * mean ρ f μ + c ^ 2 := fun c => by
    have e : (fun x => (f x - c) ^ 2 * ρ x) =
        fun x => (f x ^ 2 * ρ x - 2 * c * (f x * ρ x)) + c ^ 2 * ρ x :=
      funext fun x => by ring
    rw [e, integral_add (f := fun x => f x ^ 2 * ρ x - 2 * c * (f x * ρ x))
      (hf2.sub (h1.const_mul _)) (hρ.integrable.const_mul _),
      integral_sub (f := fun x => f x ^ 2 * ρ x) hf2 (h1.const_mul _), integral_const_mul,
      integral_const_mul,
      hρ.integral_eq_one, mean]
    ring
  rw [var, key, key]
  ring

lemma lintegral_sub_sq_mul (hρ : IsDensity ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) (a : ℝ) :
    ∫⁻ x, ENNReal.ofReal ((f x - a) ^ 2 * ρ x) ∂μ =
      ENNReal.ofReal (var ρ f μ + (mean ρ f μ - a) ^ 2) := by
  rw [← integral_sub_sq_mul hρ hf hf2 a, ofReal_integral_eq_lintegral_ofReal
    (integrable_sub_sq_mul hρ hf hf2 a) (ae_of_all _ fun x => mul_nonneg (sq_nonneg _)
      (hρ.nonneg x))]

/-- For a finite second moment the extended variance is the variance, attained at the mean. -/
theorem extendedVar_eq_ofReal_var (hρ : IsDensity ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) :
    extendedVar ρ f μ = ENNReal.ofReal (var ρ f μ) := by
  refine le_antisymm ((iInf_le _ (mean ρ f μ)).trans_eq ?_) (le_iInf fun a => ?_)
  · rw [lintegral_sub_sq_mul hρ hf hf2, sub_self]
    simp
  · rw [lintegral_sub_sq_mul hρ hf hf2]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (sq_nonneg _))

/-- The extended variance is finite exactly for a finite second moment. -/
theorem extendedVar_ne_top_iff (hρ : IsDensity ρ μ) (hf : Measurable f) :
    extendedVar ρ f μ ≠ ⊤ ↔ Integrable (fun x => f x ^ 2 * ρ x) μ := by
  refine ⟨fun h => ?_, fun hf2 => by
    rw [extendedVar_eq_ofReal_var hρ hf hf2]; exact ENNReal.ofReal_ne_top⟩
  obtain ⟨a, ha⟩ := iInf_lt_iff.1 (lt_top_iff_ne_top.2 h)
  have hi : Integrable (fun x => (f x - a) ^ 2 * ρ x) μ :=
    ⟨((hf.sub_const a).pow_const 2).aestronglyMeasurable.mul hρ.integrable.1,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (sq_nonneg _)
        (hρ.nonneg x))).2 ha⟩
  refine ((hi.const_mul 2).add (hρ.integrable.const_mul (2 * a ^ 2))).mono'
    ((hf.pow_const 2).aestronglyMeasurable.mul hρ.integrable.1) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρ.nonneg x))]
  have hle : f x ^ 2 ≤ 2 * (f x - a) ^ 2 + 2 * a ^ 2 := by nlinarith [sq_nonneg (f x - 2 * a)]
  have := mul_le_mul_of_nonneg_right hle (hρ.nonneg x)
  simp only [Pi.add_apply]
  linarith

theorem extendedVar_eq_top_iff (hρ : IsDensity ρ μ) (hf : Measurable f) :
    extendedVar ρ f μ = ⊤ ↔ ¬Integrable (fun x => f x ^ 2 * ρ x) μ := by
  rw [← extendedVar_ne_top_iff hρ hf, not_not]

lemma sd_nonneg : 0 ≤ sd ρ f μ := sqrt_nonneg _

lemma extendedSd_eq_ofReal_sd (hρ : IsDensity ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) :
    extendedSd ρ f μ = ENNReal.ofReal (sd ρ f μ) := by
  rw [extendedSd, extendedVar_eq_ofReal_var hρ hf hf2, sd, Real.sqrt_eq_rpow,
    ENNReal.ofReal_rpow_of_nonneg (hρ.var_nonneg) (by norm_num)]

lemma extendedSd_eq_top_iff : extendedSd ρ f μ = ⊤ ↔ extendedVar ρ f μ = ⊤ := by
  simp [extendedSd, ENNReal.rpow_eq_top_iff]

lemma extendedSd_eq_zero_iff : extendedSd ρ f μ = 0 ↔ extendedVar ρ f μ = 0 := by
  simp [extendedSd, ENNReal.rpow_eq_zero_iff]

/-- A variable that takes each value on a null set has a positive variance. -/
lemma var_pos (hρ : IsDensity ρ μ) (hf : Measurable f)
    (hf2 : Integrable (fun x => f x ^ 2 * ρ x) μ) (hnull : ∀ c, μ (f ⁻¹' {c}) = 0) :
    0 < var ρ f μ := by
  refine (hρ.var_nonneg).lt_of_ne fun h0 => ?_
  set m := mean ρ f μ
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (sq_nonneg _) (hρ.nonneg x))
    (integrable_sub_sq_mul hρ hf hf2 m)).1 h0.symm
  have hne : ∀ᵐ x ∂μ, f x ≠ m := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    exact hnull m
  have hρ0 : ρ =ᵐ[μ] 0 := (hz.and hne).mono fun x ⟨h1, h2⟩ => by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)) h2
    · exact h
  have := hρ.integral_eq_one
  rw [integral_congr_ae hρ0] at this
  simp at this

end ExtendedVariance

/-! ### Admissible coordinates are not almost surely constant -/

section Admissible

variable {ρ f g : ℝ × ℝ → ℝ} {h : ℝ}

lemma volume_fst_preimage (c : ℝ) : volume (Prod.fst ⁻¹' {c} : Set (ℝ × ℝ)) = 0 := by
  have : (Prod.fst ⁻¹' {c} : Set (ℝ × ℝ)) = {c} ×ˢ univ := by ext; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

lemma volume_snd_preimage (c : ℝ) : volume (Prod.snd ⁻¹' {c} : Set (ℝ × ℝ)) = 0 := by
  have : (Prod.snd ⁻¹' {c} : Set (ℝ × ℝ)) = univ ×ˢ {c} := by ext; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

namespace IsNewVariables

variable (H : IsNewVariables f g)
include H

/-- `ρ_{fg}` is a density. -/
lemma isDensity_densityFG (hρ : IsDensity ρ) : IsDensity (densityFG f g ρ) where
  nonneg u := by
    by_cases hu : u ∈ range fun x => (f x, g x)
    · obtain ⟨x, rfl⟩ := hu
      rw [densityFG, pushDensity_apply H.injective]
      exact div_nonneg (hρ.nonneg x) (abs_nonneg _)
    · rw [densityFG, pushDensity_of_notMem_range hu]
  integral_eq_one := by
    simpa [hρ.integral_eq_one] using H.integral_mul_densityFG (ρ := ρ) (φ := fun _ => 1)

lemma var_densityFG_fst : var (densityFG f g ρ) Prod.fst = var ρ f := by
  rw [var, var, H.mean_densityFG_fst]
  exact H.integral_mul_densityFG (φ := fun u => (u.1 - mean ρ f) ^ 2)

lemma var_densityFG_snd : var (densityFG f g ρ) Prod.snd = var ρ g := by
  rw [var, var, H.mean_densityFG_snd]
  exact H.integral_mul_densityFG (φ := fun u => (u.2 - mean ρ g) ^ 2)

end IsNewVariables

namespace IsAdmissible

variable (T : IsAdmissible ρ f g)
include T

lemma measurable_left : Measurable f := T.contDiff_fst.continuous.measurable

lemma measurable_right : Measurable g := T.contDiff_snd.continuous.measurable

/-- The first coordinate of an admissible pair has a nonzero extended variance. -/
theorem extendedVar_fst_ne_zero (hρ : IsDensity ρ) : extendedVar ρ f ≠ 0 := by
  by_cases hf2 : Integrable fun x => f x ^ 2 * ρ x
  · rw [extendedVar_eq_ofReal_var hρ T.measurable_left hf2, Ne, ENNReal.ofReal_eq_zero, not_le,
      ← T.isNewVariables.var_densityFG_fst]
    exact var_pos (T.isNewVariables.isDensity_densityFG hρ) measurable_fst
      (T.isNewVariables.integrable_fst_sq_densityFG hf2) volume_fst_preimage
  · rw [(extendedVar_eq_top_iff hρ T.measurable_left).2 hf2]
    exact ENNReal.top_ne_zero

/-- The second coordinate of an admissible pair has a nonzero extended variance. -/
theorem extendedVar_snd_ne_zero (hρ : IsDensity ρ) : extendedVar ρ g ≠ 0 := by
  by_cases hg2 : Integrable fun x => g x ^ 2 * ρ x
  · rw [extendedVar_eq_ofReal_var hρ T.measurable_right hg2, Ne, ENNReal.ofReal_eq_zero, not_le,
      ← T.isNewVariables.var_densityFG_snd]
    exact var_pos (T.isNewVariables.isDensity_densityFG hρ) measurable_snd
      (T.isNewVariables.integrable_snd_sq_densityFG hg2) volume_snd_preimage
  · rw [(extendedVar_eq_top_iff hρ T.measurable_right).2 hg2]
    exact ENNReal.top_ne_zero

/-- An infinite variance in an admissible pair makes `σ_f σ_g = ∞`. -/
theorem extendedSd_mul_eq_top (hρ : IsDensity ρ)
    (h2 : ¬((Integrable fun x => f x ^ 2 * ρ x) ∧ Integrable fun x => g x ^ 2 * ρ x)) :
    extendedSd ρ f * extendedSd ρ g = ⊤ := by
  rw [ENNReal.mul_eq_top]
  rcases not_and_or.1 h2 with hf | hg
  · exact Or.inr ⟨extendedSd_eq_top_iff.2 ((extendedVar_eq_top_iff hρ T.measurable_left).2 hf),
      fun h0 => T.extendedVar_snd_ne_zero hρ (extendedSd_eq_zero_iff.1 h0)⟩
  · exact Or.inl ⟨fun h0 => T.extendedVar_fst_ne_zero hρ (extendedSd_eq_zero_iff.1 h0),
      extendedSd_eq_top_iff.2 ((extendedVar_eq_top_iff hρ T.measurable_right).2 hg)⟩

/-- If `ρ_{fg}` is a product of Gaussians, both variances are finite. -/
lemma integrable_sq_of_densityFG_ae_eq
    (hP : ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧ densityFG f g ρ =ᵐ[volume] gaussProd a v b w) :
    (Integrable fun x => f x ^ 2 * ρ x) ∧ Integrable fun x => g x ^ 2 * ρ x := by
  obtain ⟨a, b, v, w, hv, hw, hG⟩ := hP
  exact ⟨T.isNewVariables.integrable_fst_sq_of_densityFG_ae_eq hv hG,
    T.isNewVariables.integrable_snd_sq_of_densityFG_ae_eq hw hG⟩

end IsAdmissible

end Admissible

/-! ### The extended conditions -/

section Conditions

variable {ρ : ℝ × ℝ → ℝ} {h : ℝ}

/-- Condition **CUR** as the brief states it, with extended standard deviations:
`σ_q σ_p ≥ ħ / e`, with equality exactly for independent Gaussians in `q, p` of zero entropy. -/
def ExtendedUncertaintyRelation (h : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ENNReal.ofReal (hbar h / exp 1) ≤ extendedSd ρ Prod.fst * extendedSd ρ Prod.snd ∧
    (extendedSd ρ Prod.fst * extendedSd ρ Prod.snd = ENNReal.ofReal (hbar h / exp 1) ↔
      entropy h ρ = 0 ∧
        ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧ ρ =ᵐ[volume] gaussProd a v b w)

/-- Condition **GCUR** as the brief states it, with extended standard deviations: for every
admissible coordinate pair `(f, g)`, `σ_f σ_g ≥ (ħ / e) e^{E[log |{f, g}|]}`, with equality
exactly when `S_h[ρ] = 0` and `ρ_{fg}` is a product of Gaussians. -/
def ExtendedGeneralizedUncertaintyRelation (h : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
  ∀ f g : ℝ × ℝ → ℝ, IsAdmissible ρ f g →
    ENNReal.ofReal (hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|)) ≤
        extendedSd ρ f * extendedSd ρ g ∧
      (extendedSd ρ f * extendedSd ρ g =
          ENNReal.ofReal (hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|)) ↔
        entropy h ρ = 0 ∧ ∃ (a b : ℝ) (v w : ℝ≥0), v ≠ 0 ∧ w ≠ 0 ∧
          densityFG f g ρ =ᵐ[volume] gaussProd a v b w)

lemma ofReal_le_mul_and_iff {B s t : ℝ} (hB : 0 ≤ B) (hs : 0 ≤ s) (ht : 0 ≤ t) {P : Prop} :
    (ENNReal.ofReal B ≤ ENNReal.ofReal s * ENNReal.ofReal t ∧
        (ENNReal.ofReal s * ENNReal.ofReal t = ENNReal.ofReal B ↔ P)) ↔
      B ≤ s * t ∧ (s * t = B ↔ P) := by
  rw [← ENNReal.ofReal_mul hs, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hs ht),
    ENNReal.ofReal_eq_ofReal_iff (mul_nonneg hs ht) hB]

lemma ofReal_le_and_iff_of_eq_top {B : ℝ} {S : ℝ≥0∞} (hS : S = ⊤) {P : Prop} (hP : ¬P) :
    ENNReal.ofReal B ≤ S ∧ (S = ENNReal.ofReal B ↔ P) := by
  rw [hS]
  exact ⟨le_top, iff_of_false ENNReal.top_ne_ofReal hP⟩

lemma hbar_div_exp_mul_exp_nonneg (hh : 0 < h) (t : ℝ) : 0 ≤ hbar h / exp 1 * exp t := by
  have := hbar_pos hh
  positivity

/-- The extended GCUR is GCUR: an infinite variance satisfies the inequality and fails both
sides of the equality condition. -/
theorem extendedGeneralizedUncertaintyRelation_iff (hh : 0 < h) (hρ : IsEnsemble ρ) :
    ExtendedGeneralizedUncertaintyRelation h ρ ↔ GeneralizedUncertaintyRelation h ρ := by
  constructor
  · intro hE f g T hf2 hg2
    have := hE f g T
    rwa [extendedSd_eq_ofReal_sd hρ.isDensity T.measurable_left hf2,
      extendedSd_eq_ofReal_sd hρ.isDensity T.measurable_right hg2,
      ofReal_le_mul_and_iff (hbar_div_exp_mul_exp_nonneg hh _) sd_nonneg
        sd_nonneg] at this
  · intro hG f g T
    by_cases h2 : (Integrable fun x => f x ^ 2 * ρ x) ∧ Integrable fun x => g x ^ 2 * ρ x
    · rw [extendedSd_eq_ofReal_sd hρ.isDensity T.measurable_left h2.1,
        extendedSd_eq_ofReal_sd hρ.isDensity T.measurable_right h2.2,
        ofReal_le_mul_and_iff (hbar_div_exp_mul_exp_nonneg hh _) sd_nonneg
          sd_nonneg]
      exact hG f g T h2.1 h2.2
    · exact ofReal_le_and_iff_of_eq_top (T.extendedSd_mul_eq_top hρ.isDensity h2) fun hP =>
        h2 (T.integrable_sq_of_densityFG_ae_eq hP.2)

/-- Since `{q, p} = 1`, the extended GCUR reduces to the extended CUR in the canonical
coordinates. -/
theorem ExtendedGeneralizedUncertaintyRelation.extendedUncertaintyRelation
    (hE : ExtendedGeneralizedUncertaintyRelation h ρ) : ExtendedUncertaintyRelation h ρ := by
  have := hE Prod.fst Prod.snd isAdmissible_fst_snd
  simp only [poissonBracket_fst_snd, abs_one, log_one, mul_zero, integral_zero, exp_zero, mul_one,
    densityFG_fst_snd] at this
  exact this

/-- For finite canonical variances the extended CUR is CUR. -/
theorem extendedUncertaintyRelation_iff (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hq : Integrable fun x => x.1 ^ 2 * ρ x) (hp : Integrable fun x => x.2 ^ 2 * ρ x) :
    ExtendedUncertaintyRelation h ρ ↔ UncertaintyRelation h ρ := by
  rw [ExtendedUncertaintyRelation, UncertaintyRelation,
    extendedSd_eq_ofReal_sd hρ.isDensity measurable_fst hq,
    extendedSd_eq_ofReal_sd hρ.isDensity measurable_snd hp,
    ofReal_le_mul_and_iff (by simpa using hbar_div_exp_mul_exp_nonneg hh 0) sd_nonneg
      sd_nonneg]

/-- An infinite canonical variance makes the extended CUR automatic. -/
theorem extendedUncertaintyRelation_of_not_integrable (hρ : IsDensity ρ)
    (h2 : ¬((Integrable fun x => x.1 ^ 2 * ρ x) ∧ Integrable fun x => x.2 ^ 2 * ρ x)) :
    ExtendedUncertaintyRelation h ρ := by
  have T : IsAdmissible ρ Prod.fst Prod.snd := isAdmissible_fst_snd
  refine ofReal_le_and_iff_of_eq_top (T.extendedSd_mul_eq_top hρ h2) fun hP => h2 ?_
  exact T.integrable_sq_of_densityFG_ae_eq (by rw [densityFG_fst_snd]; exact hP.2)

/-- **Theorem 9**, as the brief states it. Over finite entropy, ZENT implies the extended GCUR,
with its equality case. -/
theorem extendedGeneralizedUncertaintyRelation_of_lowerEntropicBound (hh : 0 < h)
    (hρ : IsEnsemble ρ) (hZ : LowerEntropicBound h ρ) :
    ExtendedGeneralizedUncertaintyRelation h ρ :=
  (extendedGeneralizedUncertaintyRelation_iff hh hρ).2
    (generalizedUncertaintyRelation_of_lowerEntropicBound hh hρ hZ)

/-- **Theorem 9**, as the brief states it. Over finite entropy, ZENT implies the extended CUR,
with its equality case; no variance needs to be finite. -/
theorem extendedUncertaintyRelation_of_lowerEntropicBound (hh : 0 < h) (hρ : IsEnsemble ρ)
    (hZ : LowerEntropicBound h ρ) : ExtendedUncertaintyRelation h ρ :=
  ExtendedGeneralizedUncertaintyRelation.extendedUncertaintyRelation
    (extendedGeneralizedUncertaintyRelation_of_lowerEntropicBound hh hρ hZ)

/-- **Theorem 12**, as the brief states it. Over finite entropy, the extended GCUR and ZENT are
equivalent. -/
theorem lowerEntropicBound_iff_extendedGeneralizedUncertaintyRelation (hh : 0 < h)
    (hρ : IsEnsemble ρ) :
    LowerEntropicBound h ρ ↔ ExtendedGeneralizedUncertaintyRelation h ρ := by
  rw [extendedGeneralizedUncertaintyRelation_iff hh hρ]
  exact lowerEntropicBound_iff_generalizedUncertaintyRelation hh hρ

end Conditions

/-! ### Entropy and variance: a product of Cauchy densities -/

section Cauchy

/-- The standard Cauchy density is an ensemble: `-c log c = c log π + log (1 + t²) / π (1 + t²)`,
and `log (1 + t²) ≤ 4 (1 + t²)^{1/4}`. -/
lemma isEnsemble_cauchy : IsEnsemble (cauchyPDFReal 0 1) where
  nonneg x := (cauchyPDF_pos 0 one_ne_zero x).le
  integral_eq_one := integral_cauchyPDFReal_eq_one 0 one_ne_zero
  integrable_negMulLog := by
    have hc : Continuous fun t : ℝ => 1 + t ^ 2 := by fun_prop
    have hJ : Integrable fun t : ℝ => ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) :=
      integrable_rpow_neg_one_add_norm_sq (by norm_num)
    have hL : Integrable fun t : ℝ => log (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by
      refine (hJ.const_mul 4).mono'
        ((hc.log fun t => by positivity).mul (hc.inv₀ fun t => by positivity)).aestronglyMeasurable
        (ae_of_all _ fun t => ?_)
      have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
      have hl : 0 ≤ log (1 + t ^ 2) := log_nonneg (by nlinarith [sq_nonneg t])
      rw [Real.norm_of_nonneg (mul_nonneg hl (inv_nonneg.2 h1.le)), Real.norm_eq_abs, sq_abs,
        show -(3 / 2 : ℝ) / 2 = 1 / 4 - 1 by norm_num, rpow_sub_one h1.ne', div_eq_mul_inv]
      have := mul_le_mul_of_nonneg_right
        (Real.log_le_rpow_div h1.le (by norm_num : (0 : ℝ) < 1 / 4)) (inv_nonneg.2 h1.le)
      calc log (1 + t ^ 2) * (1 + t ^ 2)⁻¹
          ≤ (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 / 4) * (1 + t ^ 2)⁻¹ := this
        _ = 4 * ((1 + t ^ 2) ^ (1 / 4 : ℝ) * (1 + t ^ 2)⁻¹) := by ring
    refine (((integrable_cauchyPDFReal 0 (γ := 1)).const_mul (log π)).add
      (hL.const_mul π⁻¹)).congr (ae_of_all _ fun t => ?_)
    have h1 : (0 : ℝ) < t ^ 2 + 1 := by positivity
    simp only [Pi.add_apply, negMulLog, cauchyPDFReal_def, NNReal.coe_one, mul_one, sub_zero,
      one_pow]
    rw [log_mul (inv_ne_zero pi_ne_zero) (inv_ne_zero h1.ne'), log_inv, log_inv, add_comm 1 (t ^ 2)]
    ring

/-- The standard Cauchy density has no finite second moment. -/
lemma not_integrable_sq_mul_cauchy : ¬Integrable fun t : ℝ => t ^ 2 * cauchyPDFReal 0 1 t := by
  intro hi
  have hconst : Integrable (fun _ : ℝ => π⁻¹) :=
    (hi.add (integrable_cauchyPDFReal 0 (γ := 1))).congr (ae_of_all _ fun t => by
      have h1 : (0 : ℝ) < t ^ 2 + 1 := by positivity
      simp only [Pi.add_apply, cauchyPDFReal_def, NNReal.coe_one, mul_one, sub_zero, one_pow]
      field_simp)
  rcases integrable_const_iff.1 hconst with h0 | hfin
  · exact inv_ne_zero pi_ne_zero h0
  · exact measure_ne_top (volume : Measure ℝ) univ Real.volume_univ

/-- **Entropy and variance.** Finite entropy does not require finite canonical variances: the
product of two standard Cauchy densities is an ensemble with `σ_q = σ_p = ∞`. -/
theorem exists_isEnsemble_extendedVar_eq_top :
    ∃ ρ : ℝ × ℝ → ℝ, IsEnsemble ρ ∧ extendedVar ρ Prod.fst = ⊤ ∧ extendedVar ρ Prod.snd = ⊤ := by
  have hc := isEnsemble_cauchy
  have hρ := isEnsemble_pairDensity hc hc
  refine ⟨pairDensity (cauchyPDFReal 0 1) (cauchyPDFReal 0 1), hρ,
    (extendedVar_eq_top_iff hρ.isDensity measurable_fst).2 fun hi => ?_,
    (extendedVar_eq_top_iff hρ.isDensity measurable_snd).2 fun hi => ?_⟩
  · rw [Measure.volume_eq_prod] at hi
    refine not_integrable_sq_mul_cauchy (hi.integral_prod_left.congr (ae_of_all _ fun t => ?_))
    simp only [pairDensity, ← mul_assoc, integral_const_mul, hc.integral_eq_one, mul_one]
  · rw [Measure.volume_eq_prod] at hi
    refine not_integrable_sq_mul_cauchy (hi.integral_prod_right.congr (ae_of_all _ fun t => ?_))
    simp only [pairDensity]
    simp_rw [show ∀ s, t ^ 2 * (cauchyPDFReal 0 1 s * cauchyPDFReal 0 1 t) =
      t ^ 2 * cauchyPDFReal 0 1 t * cauchyPDFReal 0 1 s from fun s => by ring]
    rw [integral_const_mul, hc.integral_eq_one, mul_one]

end Cauchy

end ClassicalUncertaintyPrinciple
