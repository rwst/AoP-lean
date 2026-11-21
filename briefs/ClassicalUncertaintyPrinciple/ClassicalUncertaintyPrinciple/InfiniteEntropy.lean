/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ClassicalUncertaintyPrinciple.ExtendedVariance

import Mathlib.MeasureTheory.Function.Floor

/-!
# Classical uncertainty relation: infinite and undefined entropy

The brief *Classical uncertainty relation* extends Proposition 6 to densities of well-defined
infinite entropy, and remarks (*Infinite and undefined entropy*) that for `S[ρ] = +∞`, and for
undefined `S[ρ]`, every admissible frame has an infinite variance, so that GCUR holds and cannot
guarantee that the entropy exists.

Entropies are real numbers in this formalization, so an infinite entropy is described by the two
halves of the entropy integral. Both cases of the remark are the case
`∫ (-ρ log ρ)⁺ = ∞`: the entropy is `+∞` when the other half `∫ (ρ log ρ)⁺` is finite, and
undefined when it is infinite too.

Finite variances of an admissible pair `(f, g)` rule this out. With `J = |{f, g}|` and `G` the
standard Gaussian, Gibbs' inequality `-p log p ≤ -p log q + q - p` against `q = J · G(f, g)` gives

  `-ρ log ρ ≤ ρ |log J| + ρ (log 2π + f² / 2 + g² / 2) + J · G(f, g)`,

where the first term is integrable by admissibility, the second by the finite variances, and the
last integrates to `∫_{range (f, g)} G ≤ 1` by the change of variables.

Densities of each kind are built from boxes `[n, n + 1) × [0, aₙ)` of masses `2⁻⁽ⁿ⁺¹⁾` and
heights `exp (±2ⁿ⁺¹)`, each of which contributes `∓1` to the entropy; so the entropy is `+∞` or
`-∞`. An equal mixture of the two, placed in `x.2 ≥ 0` and `x.2 < 0`, has undefined entropy,
as the remark on convexity says of every mixture of disjoint support: mixing in the second
density changes each half of the entropy integral only by an integrable term. By the result
above, the mixture satisfies GCUR.

## Main definitions

* `ClassicalUncertaintyPrinciple.entropyPos`, `ClassicalUncertaintyPrinciple.entropyNeg`: the
  halves `∫ (-ρ log ρ)⁺` and `∫ (ρ log ρ)⁺` of the entropy integral.
* `ClassicalUncertaintyPrinciple.boxExample`: densities of entropy `+∞` and `-∞`;
  `ClassicalUncertaintyPrinciple.undefinedEntropyExample`: one of undefined entropy.

## Main results

* `ClassicalUncertaintyPrinciple.IsAdmissible.entropyPos_lt_top`: finite variances in an
  admissible frame make `∫ (-ρ log ρ)⁺` finite.
* `ClassicalUncertaintyPrinciple.IsAdmissible.extendedSd_mul_eq_top_of_entropyPos_eq_top`:
  for `∫ (-ρ log ρ)⁺ = ∞`, `σ_f σ_g = ∞` in every admissible frame.
* `ClassicalUncertaintyPrinciple.extendedGeneralizedUncertaintyRelation_of_entropyPos_eq_top`,
  `ClassicalUncertaintyPrinciple.extendedUncertaintyRelation_of_entropyPos_eq_top`: the
  remark *Infinite and undefined entropy*: then GCUR and CUR hold, although `ρ` is not an
  ensemble (`ClassicalUncertaintyPrinciple.not_isEnsemble_of_entropyPos_eq_top`).
* `ClassicalUncertaintyPrinciple.entropy_mix_undefined`: the remark on convexity, that a mixture
  of densities with disjoint supports and entropies `+∞` and `-∞` has undefined entropy.
* `ClassicalUncertaintyPrinciple.exists_isDensity_entropy`: densities of entropy `+∞`, `-∞` and
  undefined;
  `ClassicalUncertaintyPrinciple.exists_entropy_undefined_extendedGeneralizedUncertaintyRelation`:
  one of undefined entropy satisfies GCUR.
-/

open Real MeasureTheory Set

open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace ClassicalUncertaintyPrinciple

/-- The positive half `∫ (-ρ log ρ)⁺ ∈ [0, ∞]` of the entropy integral. The entropy is `+∞` when
it is infinite and `∫ (ρ log ρ)⁺` is finite, and undefined when both are infinite. -/
def entropyPos {X : Type*} [MeasurableSpace X] (ρ : X → ℝ) (μ : Measure X := by volume_tac) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (negMulLog (ρ x)) ∂μ

/-- The negative half `∫ (ρ log ρ)⁺ ∈ [0, ∞]` of the entropy integral. The entropy is `-∞` when
it is infinite and `∫ (-ρ log ρ)⁺` is finite. -/
def entropyNeg {X : Type*} [MeasurableSpace X] (ρ : X → ℝ) (μ : Measure X := by volume_tac) :
    ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (ρ x * log (ρ x)) ∂μ

variable {ρ f g : ℝ × ℝ → ℝ} {h : ℝ}

/-- Gibbs' inequality, pointwise: `-p log p ≤ -p log q + q - p` for `p ≥ 0` and `q > 0`. -/
lemma negMulLog_le {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) : negMulLog p ≤ -(p * log q) + q - p := by
  rcases hp.eq_or_lt with rfl | hp
  · simp only [negMulLog_zero, zero_mul, neg_zero, zero_add, sub_zero]
    exact hq.le
  · have h1 := mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (div_pos hq hp)) hp.le
    rw [log_div hq.ne' hp.ne', mul_sub_one, mul_div_cancel₀ _ hp.ne'] at h1
    rw [negMulLog]
    linarith [mul_sub p (log q) (log p)]

namespace IsAdmissible

variable (T : IsAdmissible ρ f g)
include T

/-- **Finite variances bound the entropy from above.** In an admissible frame with finite
variances, the positive half `∫ (-ρ log ρ)⁺` of the entropy integral is finite: Gibbs' inequality
against `|{f, g}| · G(f, g)`, with `G` the standard Gaussian. -/
theorem entropyPos_lt_top (hρ : IsDensity ρ) (hf2 : Integrable fun x => f x ^ 2 * ρ x)
    (hg2 : Integrable fun x => g x ^ 2 * ρ x) :
    entropyPos ρ < ⊤ := by
  have H := T.isNewVariables
  set γ := gaussProd 0 1 0 1 with hγdef
  set J : ℝ × ℝ → ℝ := fun x => |poissonBracket f g x| with hJdef
  have hJ : ∀ x, 0 < J x := fun x => abs_pos.2 (H.poissonBracket_ne_zero x)
  have hγ : ∀ u, 0 < γ u := gaussProd_pos one_ne_zero one_ne_zero
  have hl2 : 0 ≤ log (2 * π) := log_nonneg (by linarith [Real.two_le_pi])
  -- the integrable part of the bound
  set B : ℝ × ℝ → ℝ := fun x =>
    ρ x * |log (J x)| + (log (2 * π) * ρ x + f x ^ 2 * ρ x / 2 + g x ^ 2 * ρ x / 2) with hBdef
  have hB0 : ∀ x, 0 ≤ B x := fun x => by
    have := hρ.nonneg x
    simp only [hBdef]
    positivity
  have hlogJ : Integrable fun x => ρ x * |log (J x)| :=
    T.integrable_log.norm.congr (ae_of_all _ fun x => by
      simp only [hJdef]
      rw [norm_mul, Real.norm_of_nonneg (hρ.nonneg x), Real.norm_eq_abs])
  have hB : Integrable B :=
    hlogJ.add (((hρ.integrable.const_mul _).add (hf2.div_const 2)).add (hg2.div_const 2))
  -- the pointwise bound
  have hle : ∀ x, ENNReal.ofReal (negMulLog (ρ x)) ≤
      ENNReal.ofReal (B x) + ENNReal.ofReal (J x * γ (f x, g x)) := fun x => by
    rw [← ENNReal.ofReal_add (hB0 x) (mul_pos (hJ x) (hγ _)).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := negMulLog_le (hρ.nonneg x) (mul_pos (hJ x) (hγ (f x, g x)))
    rw [log_mul (hJ x).ne' (hγ _).ne', hγdef, log_gaussProd_zero_one] at h1
    have h2 : -(ρ x * log (J x)) ≤ ρ x * |log (J x)| := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) (hρ.nonneg x)
    have h3 := hρ.nonneg x
    simp only [hBdef]
    linarith
  -- the change of variables: `∫ J · G(f, g) = ∫_{range (f, g)} G ≤ 1`
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume MeasurableSet.univ
    (fun x _ => (H.hasFDerivAt x).hasFDerivWithinAt) H.injective.injOn
    (fun u => ENNReal.ofReal (γ u))
  rw [image_univ, Measure.restrict_univ] at hcv
  have hJγ : ∫⁻ x, ENNReal.ofReal (J x * γ (f x, g x)) < ⊤ := by
    calc ∫⁻ x, ENNReal.ofReal (J x * γ (f x, g x))
        = ∫⁻ x, ENNReal.ofReal |((fderiv ℝ f x).prod (fderiv ℝ g x)).det| *
            ENNReal.ofReal (γ (f x, g x)) :=
          lintegral_congr fun x => by rw [ENNReal.ofReal_mul (abs_nonneg _), abs_det_prod_fderiv]
      _ = ∫⁻ u in range fun x => (f x, g x), ENNReal.ofReal (γ u) := hcv.symm
      _ ≤ ∫⁻ u, ENNReal.ofReal (γ u) := setLIntegral_le_lintegral _ _
      _ < ⊤ := (integrable_gaussProd 0 0 1 1).lintegral_lt_top
  calc entropyPos ρ volume
      ≤ ∫⁻ x, (ENNReal.ofReal (B x) + ENNReal.ofReal (J x * γ (f x, g x))) := lintegral_mono hle
    _ = (∫⁻ x, ENNReal.ofReal (B x)) + ∫⁻ x, ENNReal.ofReal (J x * γ (f x, g x)) :=
        lintegral_add_left' hB.aemeasurable.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hB.lintegral_lt_top, hJγ⟩

/-- For `∫ (-ρ log ρ)⁺ = ∞`, no admissible frame has finite variances. -/
theorem not_integrable_sq_of_entropyPos_eq_top (hρ : IsDensity ρ)
    (hS : entropyPos ρ = ⊤) :
    ¬((Integrable fun x => f x ^ 2 * ρ x) ∧ Integrable fun x => g x ^ 2 * ρ x) :=
  fun h2 => (T.entropyPos_lt_top hρ h2.1 h2.2).ne hS

/-- For `∫ (-ρ log ρ)⁺ = ∞`, that is for `S[ρ] = +∞` or undefined, `σ_f σ_g = ∞` in every
admissible frame. -/
theorem extendedSd_mul_eq_top_of_entropyPos_eq_top (hρ : IsDensity ρ)
    (hS : entropyPos ρ = ⊤) :
    extendedSd ρ f * extendedSd ρ g = ⊤ :=
  T.extendedSd_mul_eq_top hρ (T.not_integrable_sq_of_entropyPos_eq_top hρ hS)

end IsAdmissible

/-- A density with `∫ (-ρ log ρ)⁺ = ∞` is not an ensemble: its entropy is not finite. -/
theorem not_isEnsemble_of_entropyPos_eq_top
    (hS : entropyPos ρ = ⊤) : ¬IsEnsemble ρ :=
  fun hρ => hρ.integrable_negMulLog.lintegral_lt_top.ne hS

/-- **The remark *Infinite and undefined entropy*.** For `S[ρ] = +∞`, and for undefined `S[ρ]`,
that is for `∫ (-ρ log ρ)⁺ = ∞`, every admissible frame has an infinite variance, so the
extended GCUR holds; it cannot guarantee that the entropy exists. -/
theorem extendedGeneralizedUncertaintyRelation_of_entropyPos_eq_top (hρ : IsDensity ρ)
    (hS : entropyPos ρ = ⊤) :
    ExtendedGeneralizedUncertaintyRelation h ρ := fun _ _ T =>
  ofReal_le_and_iff_of_eq_top (T.extendedSd_mul_eq_top_of_entropyPos_eq_top hρ hS)
    fun hP => T.not_integrable_sq_of_entropyPos_eq_top hρ hS
      (T.integrable_sq_of_densityFG_ae_eq hP.2)

/-- For `∫ (-ρ log ρ)⁺ = ∞` the extended CUR holds. -/
theorem extendedUncertaintyRelation_of_entropyPos_eq_top (hρ : IsDensity ρ)
    (hS : entropyPos ρ = ⊤) : ExtendedUncertaintyRelation h ρ :=
  ExtendedGeneralizedUncertaintyRelation.extendedUncertaintyRelation
    (extendedGeneralizedUncertaintyRelation_of_entropyPos_eq_top hρ hS)

/-! ### The remark on convexity: mixtures of disjoint support -/

section Mixture

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {ρ σ : X → ℝ} {t : ℝ}

/-- A mixture of densities is a density. -/
lemma IsDensity.mix (hρ : IsDensity ρ μ) (hσ : IsDensity σ μ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsDensity (fun x => t * ρ x + (1 - t) * σ x) μ where
  nonneg x := add_nonneg (mul_nonneg ht0 (hρ.nonneg x)) (mul_nonneg (by linarith) (hσ.nonneg x))
  integral_eq_one := by
    rw [integral_add (hρ.integrable.const_mul _) (hσ.integrable.const_mul _), integral_const_mul,
      integral_const_mul, hρ.integral_eq_one, hσ.integral_eq_one]
    ring

/-- Mixing in a density of disjoint support keeps `∫ (-ρ log ρ)⁺ = ∞`:
`-tρ log (tρ) = t (-ρ log ρ) - tρ log t ≥ t (-ρ log ρ)`. -/
theorem entropyPos_mix_eq_top (hd : ∀ x, ρ x = 0 ∨ σ x = 0) (ht0 : 0 < t) (ht1 : t < 1)
    (hρ : IsDensity ρ μ) (hS : entropyPos ρ μ = ⊤) :
    entropyPos (fun x => t * ρ x + (1 - t) * σ x) μ = ⊤ := by
  refine eq_top_iff.2 ?_
  calc ⊤ = ENNReal.ofReal t * entropyPos ρ μ := by
        rw [hS, ENNReal.mul_top (by simpa using ht0)]
    _ ≤ ∫⁻ x, ENNReal.ofReal t * ENNReal.ofReal (negMulLog (ρ x)) ∂μ :=
        lintegral_const_mul_le _ _
    _ ≤ _ := lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul ht0.le]
  rcases hd x with h0 | h0
  · simp [h0]
  · refine ENNReal.ofReal_le_ofReal ?_
    simp only [h0, mul_zero, add_zero]
    rw [negMulLog_mul]
    nlinarith [negMulLog_nonneg ht0.le ht1.le, hρ.nonneg x]

/-- Mixing in a density of disjoint support keeps `∫ (ρ log ρ)⁺ = ∞`:
`tσ log (tσ) = t σ log σ + tσ log t`, where the last term is integrable. -/
theorem entropyNeg_mix_eq_top (hd : ∀ x, ρ x = 0 ∨ σ x = 0) (ht0 : 0 < t) (ht1 : t < 1)
    (hσ : IsDensity σ μ) (hS : entropyNeg σ μ = ⊤) :
    entropyNeg (fun x => t * ρ x + (1 - t) * σ x) μ = ⊤ := by
  set m := 1 - t with hm
  have hm0 : 0 < m := by linarith
  have hm1 : m ≤ 1 := by linarith
  set R : X → ℝ := fun x => negMulLog m * σ x with hR
  have hRi : Integrable R μ := hσ.integrable.const_mul _
  have hle : ∀ x, ENNReal.ofReal m * ENNReal.ofReal (σ x * log (σ x)) ≤
      ENNReal.ofReal ((t * ρ x + m * σ x) * log (t * ρ x + m * σ x)) + ENNReal.ofReal (R x) := by
    intro x
    rw [← ENNReal.ofReal_mul hm0.le]
    rcases hd x with h0 | h0
    · simp only [h0, mul_zero, zero_add]
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_add_le
      have := negMulLog_mul m (σ x)
      simp only [negMulLog, hR] at this ⊢
      nlinarith [this]
    · simp [h0]
  have h1 : ⊤ ≤ entropyNeg (fun x => t * ρ x + m * σ x) μ + ∫⁻ x, ENNReal.ofReal (R x) ∂μ := by
    calc ⊤ = ENNReal.ofReal m * entropyNeg σ μ := by
          rw [hS, ENNReal.mul_top (by simpa using hm0)]
      _ ≤ ∫⁻ x, ENNReal.ofReal m * ENNReal.ofReal (σ x * log (σ x)) ∂μ :=
          lintegral_const_mul_le _ _
      _ ≤ ∫⁻ x, (ENNReal.ofReal ((t * ρ x + m * σ x) * log (t * ρ x + m * σ x)) +
            ENNReal.ofReal (R x)) ∂μ := lintegral_mono hle
      _ = _ := lintegral_add_right' _ hRi.aemeasurable.ennreal_ofReal
  by_contra hne
  exact (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hne, hRi.lintegral_lt_top⟩).ne (top_le_iff.1 h1)

/-- **The remark on convexity.** A mixture of densities with disjoint supports and entropies
`+∞` and `-∞` has undefined entropy: both halves of its entropy integral are infinite. -/
theorem entropy_mix_undefined (hd : ∀ x, ρ x = 0 ∨ σ x = 0) (ht0 : 0 < t) (ht1 : t < 1)
    (hρ : IsDensity ρ μ) (hσ : IsDensity σ μ) (hP : entropyPos ρ μ = ⊤)
    (hN : entropyNeg σ μ = ⊤) :
    entropyPos (fun x => t * ρ x + (1 - t) * σ x) μ = ⊤ ∧
      entropyNeg (fun x => t * ρ x + (1 - t) * σ x) μ = ⊤ :=
  ⟨entropyPos_mix_eq_top hd ht0 ht1 hρ hP, entropyNeg_mix_eq_top hd ht0 ht1 hσ hN⟩

end Mixture

/-! ### Densities of infinite and undefined entropy -/

section Boxes

/-- The box `[n, n + 1) × [b, b + a)`. -/
def box (b a : ℝ) (n : ℕ) : Set (ℝ × ℝ) := Ico (n : ℝ) (n + 1) ×ˢ Ico b (b + a)

/-- The density `c n` on the box `[n, n + 1) × [b n, b n + a n)`, for every `n`, and `0` off
the boxes. -/
def boxDensity (b a c : ℕ → ℝ) (x : ℝ × ℝ) : ℝ :=
  if 0 ≤ x.1 ∧ x.2 ∈ Ico (b ⌊x.1⌋₊) (b ⌊x.1⌋₊ + a ⌊x.1⌋₊) then c ⌊x.1⌋₊ else 0

variable {b a c : ℕ → ℝ}

lemma measurableSet_box (b a : ℝ) (n : ℕ) : MeasurableSet (box b a n) :=
  measurableSet_Ico.prod measurableSet_Ico

lemma volume_box (b : ℝ) {a : ℝ} (n : ℕ) : volume (box b a n) = ENNReal.ofReal a := by
  rw [box, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico]
  simp

lemma mem_box_iff {n : ℕ} {x : ℝ × ℝ} :
    x ∈ box (b n) (a n) n ↔ ⌊x.1⌋₊ = n ∧ 0 ≤ x.1 ∧ x.2 ∈ Ico (b n) (b n + a n) := by
  simp only [box, mem_prod, mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h0 : 0 ≤ x.1 := le_trans (Nat.cast_nonneg n) h1
    exact ⟨(Nat.floor_eq_iff h0).2 ⟨h1, h2⟩, h0, h3⟩
  · rintro ⟨h1, h0, h3⟩
    exact ⟨(Nat.floor_eq_iff h0).1 h1, h3⟩

lemma measurable_boxDensity : Measurable (boxDensity b a c) := by
  have hf : Measurable fun x : ℝ × ℝ => ⌊x.1⌋₊ := Measurable.nat_floor measurable_fst
  have hb : Measurable fun x : ℝ × ℝ => b ⌊x.1⌋₊ := measurable_from_nat.comp hf
  have ha : Measurable fun x : ℝ × ℝ => a ⌊x.1⌋₊ := measurable_from_nat.comp hf
  have hc : Measurable fun x : ℝ × ℝ => c ⌊x.1⌋₊ := measurable_from_nat.comp hf
  exact Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le hb measurable_snd).inter (measurableSet_lt measurable_snd (hb.add ha))))
    hc measurable_const

lemma boxDensity_nonneg (hc : ∀ n, 0 ≤ c n) (x : ℝ × ℝ) : 0 ≤ boxDensity b a c x := by
  unfold boxDensity
  split_ifs
  exacts [hc _, le_rfl]

/-- A function of `boxDensity` vanishing at `0` is a sum over the disjoint boxes. -/
lemma comp_boxDensity {φ : ℝ → ℝ≥0∞} (hφ : φ 0 = 0) (x : ℝ × ℝ) :
    φ (boxDensity b a c x) = ∑' n, (box (b n) (a n) n).indicator (fun _ => φ (c n)) x := by
  by_cases hx : 0 ≤ x.1 ∧ x.2 ∈ Ico (b ⌊x.1⌋₊) (b ⌊x.1⌋₊ + a ⌊x.1⌋₊)
  · rw [boxDensity, ite_eq_left hx, tsum_eq_single ⌊x.1⌋₊]
    · rw [indicator_of_mem (mem_box_iff.2 ⟨rfl, hx⟩)]
    · intro m hm
      exact indicator_of_notMem (fun h => hm (mem_box_iff.1 h).1.symm) _
  · rw [boxDensity, ite_eq_right hx, hφ]
    refine ((tsum_congr fun m => indicator_of_notMem (fun h => ?_) _).trans tsum_zero).symm
    obtain ⟨h1, h2, h3⟩ := mem_box_iff.1 h
    subst h1
    exact hx ⟨h2, h3⟩

/-- `∫ φ(ρ) = ∑ₙ aₙ φ(cₙ)` for a function `φ` vanishing at `0`. -/
theorem lintegral_boxDensity {φ : ℝ → ℝ≥0∞} (hφ : φ 0 = 0) :
    ∫⁻ x, φ (boxDensity b a c x) = ∑' n, ENNReal.ofReal (a n) * φ (c n) := by
  simp_rw [comp_boxDensity hφ]
  rw [lintegral_tsum fun n => aemeasurable_const.indicator (measurableSet_box _ _ n)]
  congr 1
  ext n
  rw [lintegral_indicator_const (measurableSet_box _ _ n), volume_box, mul_comm]

lemma isDensity_boxDensity (ha : ∀ n, 0 ≤ a n) (hc : ∀ n, 0 ≤ c n)
    (h1 : ∑' n, ENNReal.ofReal (a n * c n) = 1) : IsDensity (boxDensity b a c) where
  nonneg := boxDensity_nonneg hc
  integral_eq_one := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (boxDensity_nonneg hc))
      measurable_boxDensity.aestronglyMeasurable,
      lintegral_boxDensity (φ := ENNReal.ofReal) ENNReal.ofReal_zero]
    simp_rw [← ENNReal.ofReal_mul (ha _)]
    rw [h1, ENNReal.toReal_one]

/-- The heights `cₙ = exp (s 2ⁿ⁺¹)`. -/
def boxHeight (s : ℝ) (n : ℕ) : ℝ := exp (s * 2 ^ (n + 1))

/-- The widths `aₙ = 2⁻⁽ⁿ⁺¹⁾ / cₙ`, so that the box `n` has mass `2⁻⁽ⁿ⁺¹⁾`. -/
def boxWidth (s : ℝ) (n : ℕ) : ℝ := (1 / 2) ^ (n + 1) / boxHeight s n

/-- Boxes of masses `2⁻⁽ⁿ⁺¹⁾` and heights `exp (s 2ⁿ⁺¹)`, each contributing `-s` to the entropy;
in `x.2 ≥ 0` for `t = 0`, and in `x.2 < 0` for `t = -1`. -/
def boxExample (s t : ℝ) : ℝ × ℝ → ℝ :=
  boxDensity (fun n => t * boxWidth s n) (boxWidth s) (boxHeight s)

lemma boxWidth_pos (s : ℝ) (n : ℕ) : 0 < boxWidth s n := by
  unfold boxWidth boxHeight
  positivity

lemma boxWidth_mul_boxHeight (s : ℝ) (n : ℕ) :
    boxWidth s n * boxHeight s n = (1 / 2) ^ (n + 1) :=
  div_mul_cancel₀ _ (exp_pos _).ne'

lemma half_pow_mul_two_pow (n : ℕ) : ((1 : ℝ) / 2) ^ (n + 1) * 2 ^ (n + 1) = 1 := by
  rw [← mul_pow]
  norm_num

lemma boxWidth_mul_negMulLog (s : ℝ) (n : ℕ) :
    boxWidth s n * negMulLog (boxHeight s n) = -s := by
  have hw := boxWidth_mul_boxHeight s n
  rw [boxHeight] at hw ⊢
  rw [negMulLog, log_exp]
  linear_combination (-(s * 2 ^ (n + 1))) * hw - s * half_pow_mul_two_pow n

lemma boxWidth_mul_mul_log (s : ℝ) (n : ℕ) :
    boxWidth s n * (boxHeight s n * log (boxHeight s n)) = s := by
  have hw := boxWidth_mul_boxHeight s n
  rw [boxHeight] at hw ⊢
  rw [log_exp]
  linear_combination (s * 2 ^ (n + 1)) * hw + s * half_pow_mul_two_pow n

lemma isDensity_boxExample (s t : ℝ) : IsDensity (boxExample s t) := by
  refine isDensity_boxDensity (fun n => (boxWidth_pos s n).le) (fun n => (exp_pos _).le) ?_
  simp_rw [boxWidth_mul_boxHeight]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    ((summable_geometric_two.mul_left (1 / 2)).congr fun n => by rw [pow_succ']),
    ← ENNReal.ofReal_one]
  congr 1
  simp_rw [pow_succ']
  rw [tsum_mul_left, tsum_geometric_two]
  norm_num

lemma entropyPos_boxExample (s t : ℝ) :
    entropyPos (boxExample s t) = ∑' _ : ℕ, ENNReal.ofReal (-s) := by
  rw [entropyPos]
  refine (lintegral_boxDensity (φ := fun y => ENNReal.ofReal (negMulLog y)) (by simp)).trans ?_
  congr 1
  ext n
  rw [← ENNReal.ofReal_mul (boxWidth_pos s n).le, boxWidth_mul_negMulLog]

lemma entropyNeg_boxExample (s t : ℝ) :
    entropyNeg (boxExample s t) = ∑' _ : ℕ, ENNReal.ofReal s := by
  rw [entropyNeg]
  refine (lintegral_boxDensity (φ := fun y => ENNReal.ofReal (y * log y)) (by simp)).trans ?_
  congr 1
  ext n
  rw [← ENNReal.ofReal_mul (boxWidth_pos s n).le, boxWidth_mul_mul_log]

lemma tsum_ofReal_one : ∑' _ : ℕ, ENNReal.ofReal 1 = ⊤ :=
  ENNReal.tsum_const_eq_top_of_ne_zero (by simp)

lemma tsum_ofReal_neg_one : ∑' _ : ℕ, ENNReal.ofReal (-1) = 0 := by
  rw [ENNReal.ofReal_of_nonpos (by norm_num), tsum_zero]

/-- A density of entropy `+∞`: `∫ (-ρ log ρ)⁺ = ∞` and `∫ (ρ log ρ)⁺ = 0`. -/
theorem entropyPos_boxExample_neg_one (t : ℝ) :
    entropyPos (boxExample (-1) t) = ⊤ ∧ entropyNeg (boxExample (-1) t) = 0 := by
  rw [entropyPos_boxExample, entropyNeg_boxExample, neg_neg]
  exact ⟨tsum_ofReal_one, tsum_ofReal_neg_one⟩

/-- A density of entropy `-∞`: `∫ (-ρ log ρ)⁺ = 0` and `∫ (ρ log ρ)⁺ = ∞`. -/
theorem entropyNeg_boxExample_one (t : ℝ) :
    entropyPos (boxExample 1 t) = 0 ∧ entropyNeg (boxExample 1 t) = ⊤ := by
  rw [entropyPos_boxExample, entropyNeg_boxExample]
  exact ⟨tsum_ofReal_neg_one, tsum_ofReal_one⟩

/-- The boxes of `boxExample (-1) 0` lie in `x.2 ≥ 0`, those of `boxExample 1 (-1)` in
`x.2 < 0`. -/
lemma boxExample_disjoint (x : ℝ × ℝ) :
    boxExample (-1) 0 x = 0 ∨ boxExample 1 (-1) x = 0 := by
  by_cases h : x.2 < 0
  · left
    rw [boxExample, boxDensity, ite_eq_right_iff]
    rintro ⟨-, h1, -⟩
    simp only [zero_mul] at h1
    exfalso
    linarith
  · right
    rw [boxExample, boxDensity, ite_eq_right_iff]
    rintro ⟨-, -, h2⟩
    exfalso
    linarith

/-- The undefined-entropy density: an equal mixture of `boxExample (-1) 0` and
`boxExample 1 (-1)`. -/
def undefinedEntropyExample : ℝ × ℝ → ℝ :=
  fun x => 1 / 2 * boxExample (-1) 0 x + (1 - 1 / 2) * boxExample 1 (-1) x

/-- **Densities of entropy `+∞`, `-∞` and undefined.** -/
theorem exists_isDensity_entropy :
    (∃ ρ : ℝ × ℝ → ℝ, IsDensity ρ ∧ entropyPos ρ = ⊤ ∧ entropyNeg ρ = 0) ∧
    (∃ ρ : ℝ × ℝ → ℝ, IsDensity ρ ∧ entropyPos ρ = 0 ∧ entropyNeg ρ = ⊤) ∧
    (∃ ρ : ℝ × ℝ → ℝ, IsDensity ρ ∧ entropyPos ρ = ⊤ ∧ entropyNeg ρ = ⊤) :=
  ⟨⟨_, isDensity_boxExample (-1) 0, entropyPos_boxExample_neg_one 0⟩,
    ⟨_, isDensity_boxExample 1 (-1), entropyNeg_boxExample_one (-1)⟩,
    ⟨undefinedEntropyExample, (isDensity_boxExample (-1) 0).mix (isDensity_boxExample 1 (-1))
      (by norm_num) (by norm_num),
      entropy_mix_undefined boxExample_disjoint (by norm_num) (by norm_num)
        (isDensity_boxExample (-1) 0) (isDensity_boxExample 1 (-1))
        (entropyPos_boxExample_neg_one 0).1 (entropyNeg_boxExample_one (-1)).2⟩⟩

/-- **The remark *Infinite and undefined entropy*, an instance.** A density of undefined entropy
satisfies the extended GCUR, and so CUR, for every `h`. -/
theorem exists_entropy_undefined_extendedGeneralizedUncertaintyRelation :
    ∃ ρ : ℝ × ℝ → ℝ, IsDensity ρ ∧ entropyPos ρ = ⊤ ∧ entropyNeg ρ = ⊤ ∧
      ∀ h, ExtendedGeneralizedUncertaintyRelation h ρ := by
  obtain ⟨ρ, hρ, hP, hN⟩ := exists_isDensity_entropy.2.2
  exact ⟨ρ, hρ, hP, hN, fun _ => extendedGeneralizedUncertaintyRelation_of_entropyPos_eq_top hρ hP⟩

end Boxes

end ClassicalUncertaintyPrinciple
