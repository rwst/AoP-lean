/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ClassicalUncertaintyPrinciple.ExtendedVariance

import ForMathlib.InformationTheory.SmoothApproximation
import Mathlib.MeasureTheory.Function.Floor

/-!
# Classical uncertainty relation: infinite and undefined entropy

The brief *Classical uncertainty relation* extends Proposition 6 to densities of well-defined
infinite entropy, and remarks (*Infinite and undefined entropy*) that for `S[ρ] = +∞`, and for
undefined `S[ρ]`, every admissible frame has an infinite variance, so that GCUR holds and cannot
guarantee that the entropy exists, while for `S[ρ] = -∞` GCUR fails in some bounded admissible
coordinates.

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

For `S[ρ] = -∞`, that is `∫ (ρ log ρ)⁺ = ∞` with `∫ (-ρ log ρ)⁺` finite, the brief's proof
sketch transports smooth densities `η` with `E[ln η]` finite and large to a uniform density on a
bounded rectangle. Here `η` smooths `min ρ j` shell by shell, as for finite entropy but with the
exceptional sets weighed by `ρ` (`MeasureTheory.exists_contDiff_integral_mul_log_min_sub_lt`),
so `E[ln η] > E[ln (min ρ j)] - 1`, which tends to `∞` with `j` by monotone convergence. The polar
transport of `η` to the standard Gaussian, followed by the distribution function `Φ` in each
coordinate, gives coordinates with values in `[-1, 1]` and Jacobian `η`, so
`U_ρ(T) ≤ |ln (2π e / h)| - E[ln η]`. A negative `U_ρ(T)` violates GCUR.

## Main definitions

* `ClassicalUncertaintyPrinciple.entropyPos`, `ClassicalUncertaintyPrinciple.entropyNeg`: the
  halves `∫ (-ρ log ρ)⁺` and `∫ (ρ log ρ)⁺` of the entropy integral.
* `ClassicalUncertaintyPrinciple.gaussPrim`: the standard Gaussian distribution function, less
  `1 / 2`.
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
* `ClassicalUncertaintyPrinciple.exists_isAdmissible_coordinateUncertainty_lt`,
  `ClassicalUncertaintyPrinciple.not_bddBelow_coordinateUncertainty`: Proposition 6 for
  `S[ρ] = -∞`, `inf_T U_ρ(T) = -∞`, over bounded admissible coordinates;
  `ClassicalUncertaintyPrinciple.exists_bounded_coordinates`: the coordinates, with a given
  Jacobian.
* `ClassicalUncertaintyPrinciple.not_extendedGeneralizedUncertaintyRelation_of_entropyNeg_eq_top`,
  `ClassicalUncertaintyPrinciple.not_generalizedUncertaintyRelation_of_entropyNeg_eq_top`: the
  remark *Infinite and undefined entropy*: for `S[ρ] = -∞`, GCUR fails;
  `ClassicalUncertaintyPrinciple.exists_not_extendedGeneralizedUncertaintyRelation`: an instance.
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


/-! ### Entropy `-∞`: GCUR fails -/

section NegInfinite

open ProbabilityTheory

open scoped Interval

/-- For `j ≥ 1` and `∫ (-ρ log ρ)⁺ < ∞`, the truncation `ρ log (min ρ j)` is integrable: it lies
between `-(-ρ log ρ)⁺` and `ρ log j`. -/
lemma integrable_mul_log_min (hρ : IsDensity ρ) (hP : entropyPos ρ ≠ ⊤) {j : ℝ} (hj : 1 ≤ j) :
    Integrable fun x => ρ x * log (min (ρ x) j) := by
  have hρa := hρ.integrable.aemeasurable
  have hPi : Integrable fun x => (ENNReal.ofReal (negMulLog (ρ x))).toReal :=
    integrable_toReal_of_lintegral_ne_top
      ((Real.continuous_negMulLog.measurable.comp_aemeasurable hρa).ennreal_ofReal) hP
  refine (hPi.add (hρ.integrable.mul_const (log j))).mono'
    ((measurable_id.mul (measurable_id.min measurable_const).log).comp_aemeasurable
      hρa).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h0 := hρ.nonneg x
  have hlj : 0 ≤ ρ x * log j := mul_nonneg h0 (log_nonneg hj)
  have hm : negMulLog (ρ x) ≤ max (negMulLog (ρ x)) 0 := le_max_left _ _
  have hm0 : 0 ≤ max (negMulLog (ρ x)) 0 := le_max_right _ _
  simp only [Pi.add_apply]
  rw [ENNReal.toReal_ofReal', Real.norm_eq_abs, abs_le]
  rcases le_total (ρ x) j with hx | hx
  · rw [min_eq_left hx]
    have h1 : ρ x * log (ρ x) ≤ ρ x * log j := by
      rcases h0.eq_or_lt with h0' | h0'
      · rw [← h0', zero_mul, zero_mul]
      · exact mul_le_mul_of_nonneg_left (log_le_log h0' hx) h0
    have hneg : negMulLog (ρ x) = -(ρ x * log (ρ x)) := by rw [negMulLog]; ring
    constructor <;> linarith
  · rw [min_eq_right hx]
    constructor <;> linarith

/-- **Entropy `-∞` makes the truncated expectations of `log ρ` unbounded.** For
`∫ (-ρ log ρ)⁺ < ∞` and `∫ (ρ log ρ)⁺ = ∞`, `∫ ρ log (min ρ j) → ∞` as `j → ∞`, by monotone
convergence. -/
lemma exists_lt_integral_mul_log_min (hρ : IsDensity ρ) (hP : entropyPos ρ ≠ ⊤)
    (hN : entropyNeg ρ = ⊤) (A : ℝ) :
    ∃ j : ℕ, A < ∫ x, ρ x * log (min (ρ x) (j + 1)) := by
  set v : ℕ → ℝ × ℝ → ℝ := fun j x => ρ x * log (min (ρ x) (j + 1)) with hv
  have hj1 : ∀ j : ℕ, (1 : ℝ) ≤ j + 1 := fun j => by linarith [j.cast_nonneg (α := ℝ)]
  have hvi : ∀ j, Integrable (v j) := fun j => integrable_mul_log_min hρ hP (hj1 j)
  have hle : ∀ j x, v j x ≤ ρ x * log (ρ x) := fun j x => by
    rcases (hρ.nonneg x).eq_or_lt with h0 | h0
    · simp [hv, ← h0]
    · exact mul_le_mul_of_nonneg_left
        (log_le_log (lt_min h0 (by linarith [hj1 j])) (min_le_left _ _)) h0.le
  have hmono : ∀ x, Monotone fun j => ENNReal.ofReal (v j x) := fun x i j hij => by
    refine ENNReal.ofReal_le_ofReal ?_
    rcases (hρ.nonneg x).eq_or_lt with h0 | h0
    · simp [hv, ← h0]
    · have hij' : (i : ℝ) + 1 ≤ j + 1 := by
        have : (i : ℝ) ≤ j := by exact_mod_cast hij
        linarith
      exact mul_le_mul_of_nonneg_left (log_le_log (lt_min h0 (by linarith [hj1 i]))
        (min_le_min_left _ hij')) h0.le
  have hsup : ∀ x, ⨆ j, ENNReal.ofReal (v j x) = ENNReal.ofReal (ρ x * log (ρ x)) := fun x => by
    refine le_antisymm (iSup_le fun j => ENNReal.ofReal_le_ofReal (hle j x)) ?_
    obtain ⟨j, hj⟩ := exists_nat_ge (ρ x)
    refine le_iSup_of_le j (le_of_eq ?_)
    simp only [hv]
    rw [min_eq_left (by linarith)]
  have hlim : ⨆ j, ∫⁻ x, ENNReal.ofReal (v j x) = ⊤ := by
    rw [← lintegral_iSup' (fun j => (hvi j).aemeasurable.ennreal_ofReal) (ae_of_all _ hmono)]
    simp_rw [hsup]
    exact hN
  set E := (entropyPos ρ).toReal with hE
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  obtain ⟨j, hj⟩ := lt_iSup_iff.1 (hlim ▸ ENNReal.ofReal_lt_top :
    ENNReal.ofReal (max A 0 + E) < ⨆ j, ∫⁻ x, ENNReal.ofReal (v j x))
  refine ⟨j, ?_⟩
  have h1 : max A 0 + E < (∫⁻ x, ENNReal.ofReal (v j x)).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (hvi j).lintegral_lt_top.ne).1 hj
  have h2 : (∫⁻ x, ENNReal.ofReal (-v j x)).toReal ≤ E := by
    refine ENNReal.toReal_mono hP (lintegral_mono fun x => ?_)
    rw [ENNReal.ofReal_le_ofReal_iff']
    rcases le_total (ρ x) (j + 1) with hx | hx
    · left
      simp only [hv, min_eq_left hx, negMulLog]
      exact le_of_eq (by ring)
    · right
      simp only [hv, min_eq_right hx]
      have := mul_nonneg (hρ.nonneg x) (log_nonneg (hj1 j))
      linarith
  have h4 : A ≤ max A 0 := le_max_left _ _
  change A < ∫ x, v j x
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hvi j)]
  linarith

lemma gaussProd_zero_one_le_one (y : ℝ × ℝ) : gaussProd 0 1 0 1 y ≤ 1 := by
  by_contra hy
  have h1 := Real.log_pos (not_le.1 hy)
  rw [log_gaussProd_zero_one] at h1
  have := log_nonneg (by linarith [Real.two_le_pi] : (1 : ℝ) ≤ 2 * π)
  nlinarith [sq_nonneg y.1, sq_nonneg y.2]

/-- The standard Gaussian distribution function, less `1 / 2`: `Φ u = ∫₀ᵘ φ`. -/
def gaussPrim (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, gaussianPDFReal 0 1 t

lemma continuous_gaussianPDFReal_zero_one : Continuous (gaussianPDFReal 0 1) := by
  unfold gaussianPDFReal
  fun_prop

lemma hasDerivAt_gaussPrim (u : ℝ) : HasDerivAt gaussPrim (gaussianPDFReal 0 1 u) u :=
  (continuous_gaussianPDFReal_zero_one.integral_hasStrictDerivAt 0 u).hasDerivAt

lemma deriv_gaussPrim : deriv gaussPrim = gaussianPDFReal 0 1 :=
  funext fun u => (hasDerivAt_gaussPrim u).deriv

lemma contDiff_gaussPrim : ContDiff ℝ 1 gaussPrim := by
  rw [contDiff_one_iff_deriv, deriv_gaussPrim]
  exact ⟨fun u => (hasDerivAt_gaussPrim u).differentiableAt, continuous_gaussianPDFReal_zero_one⟩

lemma strictMono_gaussPrim : StrictMono gaussPrim :=
  strictMono_of_deriv_pos fun u => by
    rw [deriv_gaussPrim]
    exact gaussianPDFReal_pos _ _ _ one_ne_zero

lemma abs_gaussPrim_le (u : ℝ) : |gaussPrim u| ≤ 1 := by
  rw [gaussPrim, ← Real.norm_eq_abs, intervalIntegral.norm_integral_eq_norm_integral_uIoc,
    Real.norm_of_nonneg (setIntegral_nonneg measurableSet_uIoc fun t _ =>
      gaussianPDFReal_nonneg _ _ _)]
  calc ∫ t in Ι 0 u, gaussianPDFReal 0 1 t ≤ ∫ t, gaussianPDFReal 0 1 t :=
        setIntegral_le_integral (integrable_gaussianPDFReal 0 1)
          (ae_of_all _ fun t => gaussianPDFReal_nonneg _ _ _)
    _ = 1 := integral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- **Bounded coordinates with a given Jacobian.** A positive `C¹` probability density `η` on
the plane is the Jacobian `|{f, g}|` of `C¹` coordinates `f = Φ ∘ T₁`, `g = Φ ∘ T₂` with values
in `[-1, 1]`: `T` transports `η` to the standard Gaussian
(`PolarTransport.exists_transport_gaussian`), and the distribution function `Φ` in each
coordinate takes the Gaussian to the uniform density on a square. -/
lemma exists_bounded_coordinates {η : ℝ × ℝ → ℝ} (hηc : ContDiff ℝ 1 η) (hηpos : ∀ x, 0 < η x)
    (hη1 : ∫ x, η x = 1) :
    ∃ f g : ℝ × ℝ → ℝ, ContDiff ℝ 1 f ∧ ContDiff ℝ 1 g ∧
      Function.Injective (fun x => (f x, g x)) ∧ (∀ x, |poissonBracket f g x| = η x) ∧
      (∀ x, |f x| ≤ 1) ∧ ∀ x, |g x| ≤ 1 := by
  obtain ⟨T, hT1, hTb, hTη⟩ :=
    PolarTransport.exists_transport_gaussian hηc le_rfl hηpos hη1 (v := 1) one_ne_zero
  have hTd : Differentiable ℝ T := hT1.differentiable one_ne_zero
  have h1 : ∀ x, HasFDerivAt (fun x => (T x).1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ T x)) x := fun x =>
    hasFDerivAt_fst.comp x (hTd x).hasFDerivAt
  have h2 : ∀ x, HasFDerivAt (fun x => (T x).2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ T x)) x := fun x =>
    hasFDerivAt_snd.comp x (hTd x).hasFDerivAt
  have hd1 : ∀ x, HasFDerivAt (fun x => gaussPrim (T x).1)
      (gaussianPDFReal 0 1 (T x).1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ T x)) x :=
    fun x => (hasDerivAt_gaussPrim _).comp_hasFDerivAt x (h1 x)
  have hd2 : ∀ x, HasFDerivAt (fun x => gaussPrim (T x).2)
      (gaussianPDFReal 0 1 (T x).2 • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (fderiv ℝ T x)) x :=
    fun x => (hasDerivAt_gaussPrim _).comp_hasFDerivAt x (h2 x)
  have hpb : ∀ x, poissonBracket (fun x => gaussPrim (T x).1) (fun x => gaussPrim (T x).2) x =
      gaussianPDFReal 0 1 (T x).1 * gaussianPDFReal 0 1 (T x).2 * (fderiv ℝ T x).det :=
    fun x => by
      rw [← poissonBracket_eq_det hTd, poissonBracket, poissonBracket, (hd1 x).fderiv,
        (hd2 x).fderiv, (h1 x).fderiv, (h2 x).fderiv]
      simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
        smul_eq_mul]
      ring
  refine ⟨fun x => gaussPrim (T x).1, fun x => gaussPrim (T x).2,
    contDiff_gaussPrim.comp (contDiff_fst.comp hT1),
    contDiff_gaussPrim.comp (contDiff_snd.comp hT1), fun x y hxy => hTb.1 ?_, fun x => ?_,
    fun x => abs_gaussPrim_le _, fun x => abs_gaussPrim_le _⟩
  · simp only [Prod.mk.injEq] at hxy
    exact Prod.ext (strictMono_gaussPrim.injective hxy.1) (strictMono_gaussPrim.injective hxy.2)
  · rw [hpb, abs_mul, abs_of_pos (mul_pos (gaussianPDFReal_pos _ _ _ one_ne_zero)
      (gaussianPDFReal_pos _ _ _ one_ne_zero))]
    exact (hTη x).symm

lemma integrable_sq_mul_of_abs_le_one (hρ : IsDensity ρ) (hf : Measurable f)
    (hf1 : ∀ x, |f x| ≤ 1) : Integrable fun x => f x ^ 2 * ρ x :=
  hρ.integrable.mono' ((hf.pow_const 2).aestronglyMeasurable.mul hρ.integrable.1)
    (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρ.nonneg x))]
      exact mul_le_of_le_one_left (hρ.nonneg x) ((sq_le_one_iff_abs_le_one _).2 (hf1 x)))

lemma sd_le_one_of_abs_le_one (hρ : IsDensity ρ) (hf : Measurable f) (hf1 : ∀ x, |f x| ≤ 1) :
    sd ρ f ≤ 1 := by
  have hf2 := integrable_sq_mul_of_abs_le_one hρ hf hf1
  have h := integral_sub_sq_mul hρ hf hf2 0
  simp only [sub_zero] at h
  have h2 : ∫ x, f x ^ 2 * ρ x ≤ ∫ x, ρ x := integral_mono hf2 hρ.integrable fun x =>
    mul_le_of_le_one_left (hρ.nonneg x) ((sq_le_one_iff_abs_le_one _).2 (hf1 x))
  rw [hρ.integral_eq_one] at h2
  have hv : var ρ f ≤ 1 := by nlinarith [sq_nonneg (mean ρ f)]
  exact (Real.sqrt_le_sqrt hv).trans_eq Real.sqrt_one

lemma log_le_abs_log {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : log x ≤ |log y| := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [log_zero]
    exact abs_nonneg _
  · exact (log_le_log hx hxy).trans (le_abs_self _)

/-- **Proposition 6 for entropy `-∞`.** For `∫ (ρ log ρ)⁺ = ∞` and `∫ (-ρ log ρ)⁺ < ∞`, that is
for `S[ρ] = -∞`, `U_ρ(T)` takes arbitrarily negative values on admissible coordinates with
values in `[-1, 1]`. Following the brief: smooth positive densities `η` with `E[ln η] → ∞`
(`MeasureTheory.exists_contDiff_integral_mul_log_min_sub_lt`) are the Jacobians of bounded
coordinates (`exists_bounded_coordinates`), so that
`U_ρ(T) ≤ |ln (2π e / h)| - E[ln η]`. -/
theorem exists_isAdmissible_coordinateUncertainty_lt (hh : 0 < h) (hρ : IsDensity ρ)
    (hP : entropyPos ρ ≠ ⊤) (hN : entropyNeg ρ = ⊤) (M : ℝ) :
    ∃ f g : ℝ × ℝ → ℝ, IsAdmissible ρ f g ∧ (∀ x, |f x| ≤ 1) ∧ (∀ x, |g x| ≤ 1) ∧
      coordinateUncertainty h ρ f g < M := by
  set c := |log (2 * π * exp 1 / h)| with hc
  obtain ⟨j, hj⟩ := exists_lt_integral_mul_log_min hρ hP hN (c - M + 1)
  have hj1 : (1 : ℝ) ≤ j + 1 := by linarith [j.cast_nonneg (α := ℝ)]
  have hv : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  obtain ⟨η, hηc, hηpos, -, hη1, hηl, hηlt⟩ := exists_contDiff_integral_mul_log_min_sub_lt
    (μ := volume) (n := 1) (C := 1) hρ.nonneg hρ.integrable hρ.integral_eq_one
    (by linarith : (0 : ℝ) < j + 1) (integrable_mul_log_min hρ hP hj1)
    (contDiff_gaussProd 0 0 1 1) (gaussProd_pos hv hv) gaussProd_zero_one_le_one
    (integrable_gaussProd 0 0 1 1) (integral_gaussProd hv hv) one_pos
  obtain ⟨f, g, hf, hg, hinj, hJ, hf1, hg1⟩ := exists_bounded_coordinates hηc hηpos hη1
  have T : IsAdmissible ρ f g :=
    ⟨hf, hg, hinj, fun x h0 => (hηpos x).ne' (by rw [← hJ x, h0, abs_zero]),
      hηl.congr (ae_of_all _ fun x => by simp only [hJ])⟩
  refine ⟨f, g, T, hf1, hg1, ?_⟩
  have hsf := sd_le_one_of_abs_le_one hρ T.measurable_left hf1
  have hsg := sd_le_one_of_abs_le_one hρ T.measurable_right hg1
  have hss : sd ρ f * sd ρ g ≤ 1 :=
    (mul_le_mul hsf hsg sd_nonneg zero_le_one).trans_eq (one_mul 1)
  have hss0 : 0 ≤ sd ρ f * sd ρ g := mul_nonneg sd_nonneg sd_nonneg
  have hlog : log (2 * π * exp 1 * (sd ρ f * sd ρ g) / h) ≤ c := by
    refine log_le_abs_log (by positivity) ?_
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (by positivity) hss) hh.le
  have hI : ∫ x, ρ x * log |poissonBracket f g x| = ∫ x, ρ x * log (η x) := by
    simp only [hJ]
  rw [coordinateUncertainty, hI]
  linarith

/-- **Proposition 6, eq. (7), for entropy `-∞`**: `inf_T U_ρ(T) = -∞ = S_h[ρ]` over admissible
coordinates with finite variances. -/
theorem not_bddBelow_coordinateUncertainty (hh : 0 < h) (hρ : IsDensity ρ)
    (hP : entropyPos ρ ≠ ⊤) (hN : entropyNeg ρ = ⊤) :
    ¬BddBelow {u | ∃ f g : ℝ × ℝ → ℝ, IsAdmissible ρ f g ∧
      (Integrable fun x => f x ^ 2 * ρ x) ∧ (Integrable fun x => g x ^ 2 * ρ x) ∧
      u = coordinateUncertainty h ρ f g} := by
  rintro ⟨b, hb⟩
  obtain ⟨f, g, T, hf1, hg1, hU⟩ := exists_isAdmissible_coordinateUncertainty_lt hh hρ hP hN b
  exact hU.not_ge (hb ⟨f, g, T, integrable_sq_mul_of_abs_le_one hρ T.measurable_left hf1,
    integrable_sq_mul_of_abs_le_one hρ T.measurable_right hg1, rfl⟩)

/-- A negative `U_ρ(T)` violates the inequality of GCUR: `σ_f σ_g < (ħ / e) e^{E[log |{f, g}|]}`. -/
lemma sd_mul_sd_lt_of_coordinateUncertainty_neg (hh : 0 < h)
    (hU : coordinateUncertainty h ρ f g < 0) :
    sd ρ f * sd ρ g < hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|) := by
  have hB : 0 < hbar h / exp 1 * exp (∫ x, ρ x * log |poissonBracket f g x|) := by
    have := hbar_pos hh
    positivity
  rcases (mul_nonneg (sd_nonneg (ρ := ρ) (f := f)) (sd_nonneg (ρ := ρ) (f := g))).eq_or_lt
    with h0 | h0
  · rw [← h0]
    exact hB
  · rw [coordinateUncertainty, sub_neg, log_lt_iff_lt_exp (by positivity), div_lt_iff₀ hh]
      at hU
    rw [hbar_div_exp_eq, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    linarith

/-- **GCUR fails for entropy `-∞`.** For `∫ (ρ log ρ)⁺ = ∞` and `∫ (-ρ log ρ)⁺ < ∞`, bounded
admissible coordinates violate the inequality of the extended GCUR. -/
theorem not_extendedGeneralizedUncertaintyRelation_of_entropyNeg_eq_top (hh : 0 < h)
    (hρ : IsDensity ρ) (hP : entropyPos ρ ≠ ⊤) (hN : entropyNeg ρ = ⊤) :
    ¬ExtendedGeneralizedUncertaintyRelation h ρ := by
  intro hE
  obtain ⟨f, g, T, hf1, hg1, hU⟩ := exists_isAdmissible_coordinateUncertainty_lt hh hρ hP hN 0
  have h1 := (hE f g T).1
  rw [extendedSd_eq_ofReal_sd hρ T.measurable_left
      (integrable_sq_mul_of_abs_le_one hρ T.measurable_left hf1),
    extendedSd_eq_ofReal_sd hρ T.measurable_right
      (integrable_sq_mul_of_abs_le_one hρ T.measurable_right hg1),
    ← ENNReal.ofReal_mul sd_nonneg,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg sd_nonneg sd_nonneg)] at h1
  exact h1.not_gt (sd_mul_sd_lt_of_coordinateUncertainty_neg hh hU)

/-- **GCUR fails for entropy `-∞`**, with finite variances. -/
theorem not_generalizedUncertaintyRelation_of_entropyNeg_eq_top (hh : 0 < h)
    (hρ : IsDensity ρ) (hP : entropyPos ρ ≠ ⊤) (hN : entropyNeg ρ = ⊤) :
    ¬GeneralizedUncertaintyRelation h ρ := by
  intro hG
  obtain ⟨f, g, T, hf1, hg1, hU⟩ := exists_isAdmissible_coordinateUncertainty_lt hh hρ hP hN 0
  exact ((hG f g T (integrable_sq_mul_of_abs_le_one hρ T.measurable_left hf1)
    (integrable_sq_mul_of_abs_le_one hρ T.measurable_right hg1)).1).not_gt
    (sd_mul_sd_lt_of_coordinateUncertainty_neg hh hU)

/-- **Entropy `-∞`, an instance.** A density of entropy `-∞` violates the extended GCUR for
every `h > 0`. -/
theorem exists_not_extendedGeneralizedUncertaintyRelation :
    ∃ ρ : ℝ × ℝ → ℝ, IsDensity ρ ∧ entropyPos ρ = 0 ∧ entropyNeg ρ = ⊤ ∧
      ∀ h, 0 < h → ¬ExtendedGeneralizedUncertaintyRelation h ρ := by
  obtain ⟨ρ, hρ, hP, hN⟩ := exists_isDensity_entropy.2.1
  exact ⟨ρ, hρ, hP, hN, fun _ hh => not_extendedGeneralizedUncertaintyRelation_of_entropyNeg_eq_top
    hh hρ (by rw [hP]; exact ENNReal.zero_ne_top) hN⟩

end NegInfinite

end ClassicalUncertaintyPrinciple
