/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.InformationTheory.MarginalEntropy

/-!
# Entropy of products and subadditivity

For probability densities `f` on `X` and `g` on `Y` with finite entropy, the product
`f(x) g(y)` has finite entropy `-∫ f log f - ∫ g log g`. Conversely, for a probability density
`ρ` on `X × Y` whose marginals `ρ_X(x) = ∫ ρ(x, y) dy` and `ρ_Y(y) = ∫ ρ(x, y) dx` have finite
entropy, the entropy is subadditive,

  `-∫ ρ log ρ ≤ -∫ ρ_X log ρ_X - ∫ ρ_Y log ρ_Y`.

This is Gibbs' inequality against `ρ_X ⊗ ρ_Y`, which may vanish, but only where `ρ` vanishes
almost everywhere.

## Main results

* `MeasureTheory.integral_negMulLog_mul_prod`: the entropy of a product is the sum;
* `MeasureTheory.ae_pos_integral_prod_fst`: `ρ > 0` implies `ρ_X > 0` almost everywhere;
* `MeasureTheory.integral_negMulLog_le_add`: subadditivity.
-/

open Real

public section

namespace MeasureTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [SFinite μ] [SFinite ν]

section Product

variable {f : X → ℝ} {g : Y → ℝ}

lemma negMulLog_mul_eq (a b : ℝ) : negMulLog (a * b) = negMulLog a * b + a * negMulLog b := by
  rw [negMulLog_mul]
  ring

omit [SFinite μ] [SFinite ν] in
theorem integrable_negMulLog_mul_prod (hf : Integrable f μ) (hg : Integrable g ν)
    (hff : Integrable (fun x => negMulLog (f x)) μ)
    (hgg : Integrable (fun y => negMulLog (g y)) ν) :
    Integrable (fun z : X × Y => negMulLog (f z.1 * g z.2)) (μ.prod ν) := by
  simp_rw [negMulLog_mul_eq]
  exact (hff.mul_prod hg).add (hf.mul_prod hgg)

/-- **The entropy of a product** of probability densities is the sum of the entropies. -/
theorem integral_negMulLog_mul_prod (hf : Integrable f μ) (hg : Integrable g ν)
    (hff : Integrable (fun x => negMulLog (f x)) μ) (hgg : Integrable (fun y => negMulLog (g y)) ν)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ y, g y ∂ν = 1) :
    ∫ z, negMulLog (f z.1 * g z.2) ∂(μ.prod ν) =
      ∫ x, negMulLog (f x) ∂μ + ∫ y, negMulLog (g y) ∂ν := by
  simp_rw [negMulLog_mul_eq]
  rw [integral_add (hff.mul_prod hg) (hf.mul_prod hgg),
    integral_prod_mul (fun x => negMulLog (f x)) g, integral_prod_mul f fun y => negMulLog (g y),
    hf1, hg1, mul_one, one_mul]

end Product

variable {ρ : X × Y → ℝ}

theorem integrable_mul_integral_prod_snd {g : Y → ℝ}
    (hg : Integrable (fun z => g z.2 * ρ z) (μ.prod ν)) :
    Integrable (fun y => g y * ∫ x, ρ (x, y) ∂μ) ν := by
  simpa only [← integral_const_mul] using hg.integral_prod_right

/-- Moments of the marginal `∫ ρ(x, y) dμ(x)` are moments of `ρ`. -/
theorem integral_mul_integral_prod_snd {g : Y → ℝ}
    (hg : Integrable (fun z => g z.2 * ρ z) (μ.prod ν)) :
    ∫ y, g y * ∫ x, ρ (x, y) ∂μ ∂ν = ∫ z, g z.2 * ρ z ∂(μ.prod ν) := by
  rw [integral_prod_symm _ hg]
  simp_rw [integral_const_mul]

/-- Where `ρ ≥ 0` is positive, its marginal `ρ_X` is positive, almost everywhere. -/
theorem ae_pos_integral_prod_fst (hρ0 : ∀ z, 0 ≤ ρ z) (hρ : Integrable ρ (μ.prod ν)) :
    ∀ᵐ z ∂(μ.prod ν), 0 < ρ z → 0 < ∫ y, ρ (z.1, y) ∂ν := by
  set ρ' := hρ.aestronglyMeasurable.mk ρ
  have hm : StronglyMeasurable ρ' := hρ.aestronglyMeasurable.stronglyMeasurable_mk
  have he : ρ =ᵐ[μ.prod ν] ρ' := hρ.aestronglyMeasurable.ae_eq_mk
  have hρ' : Integrable ρ' (μ.prod ν) := hρ.congr he
  have hF : ∀ᵐ x ∂μ, ∫ y, ρ (x, y) ∂ν = ∫ y, ρ' (x, y) ∂ν := by
    filter_upwards [Measure.ae_ae_of_ae_prod he] with x hx using integral_congr_ae hx
  have hs : MeasurableSet {z : X × Y | 0 < ρ' z → 0 < ∫ y, ρ' (z.1, y) ∂ν} :=
    measurableSet_setOfPred.2 ((measurableSet_lt measurable_const hm.measurable).mem.imp
      (measurableSet_lt measurable_const
        (hm.integral_prod_right'.measurable.comp measurable_fst)).mem)
  have hP : ∀ᵐ z ∂(μ.prod ν), 0 < ρ' z → 0 < ∫ y, ρ' (z.1, y) ∂ν := by
    rw [Measure.ae_prod_iff_ae_ae hs]
    filter_upwards [hρ'.prod_right_ae,
      Measure.ae_ae_of_ae_prod (he.mono fun z hz => hz ▸ hρ0 z)] with x hi hn
    by_cases hpos : 0 < ∫ y, ρ' (x, y) ∂ν
    · exact ae_of_all _ fun _ _ => hpos
    have h0 : ∫ y, ρ' (x, y) ∂ν = 0 := le_antisymm (not_lt.1 hpos) (integral_nonneg_of_ae hn)
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hn hi).1 h0] with y hy hlt
    exact absurd hy hlt.ne'
  filter_upwards [he, Measure.quasiMeasurePreserving_fst.ae hF, hP] with z h1 h2 h3 hz
  rw [h2]
  exact h3 (h1 ▸ hz)

/-- Where `ρ ≥ 0` is positive, its marginal `ρ_Y` is positive, almost everywhere. -/
theorem ae_pos_integral_prod_snd (hρ0 : ∀ z, 0 ≤ ρ z) (hρ : Integrable ρ (μ.prod ν)) :
    ∀ᵐ z ∂(μ.prod ν), 0 < ρ z → 0 < ∫ x, ρ (x, z.2) ∂μ := by
  have h := ae_pos_integral_prod_fst (μ := ν) (ν := μ) (ρ := ρ ∘ Prod.swap) (fun _ => hρ0 _)
    hρ.swap
  simpa using Measure.measurePreserving_swap.quasiMeasurePreserving.ae h

/-- `ρ(x, y) log ρ_X(x)` is integrable if the marginal `ρ_X` has finite entropy. -/
theorem integrable_mul_log_integral_prod_fst (hρ0 : ∀ z, 0 ≤ ρ z) (hρ : Integrable ρ (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (∫ y, ρ (x, y) ∂ν)) μ) :
    Integrable (fun z => ρ z * log (∫ y, ρ (z.1, y) ∂ν)) (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : X × Y => log (∫ y, ρ (z.1, y) ∂ν)) (μ.prod ν) :=
    (measurable_log.comp_aemeasurable
      hρ.integral_prod_left.aemeasurable).aestronglyMeasurable.comp_fst
  refine (integrable_prod_iff (f := fun z => ρ z * log (∫ y, ρ (z.1, y) ∂ν))
    (hρ.aestronglyMeasurable.mul hm)).2 ⟨?_, ?_⟩
  · filter_upwards [hρ.prod_right_ae] with x hx using hx.mul_const _
  · refine hX.norm.congr (ae_of_all _ fun x => ?_)
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ0 _)]
    rw [integral_mul_const, negMulLog, abs_mul, abs_neg,
      abs_of_nonneg (integral_nonneg fun y => hρ0 _)]

/-- `ρ(x, y) log ρ_Y(y)` is integrable if the marginal `ρ_Y` has finite entropy. -/
theorem integrable_mul_log_integral_prod_snd (hρ0 : ∀ z, 0 ≤ ρ z) (hρ : Integrable ρ (μ.prod ν))
    (hY : Integrable (fun y => negMulLog (∫ x, ρ (x, y) ∂μ)) ν) :
    Integrable (fun z => ρ z * log (∫ x, ρ (x, z.2) ∂μ)) (μ.prod ν) := by
  have h := integrable_mul_log_integral_prod_fst (μ := ν) (ν := μ) (ρ := ρ ∘ Prod.swap)
    (fun _ => hρ0 _) hρ.swap hY
  simpa [Function.comp_def] using h.swap

/-- **Subadditivity of the entropy.** For a probability density `ρ ≥ 0` on `X × Y` with finite
entropy whose marginals have finite entropy, `-∫ ρ log ρ ≤ -∫ ρ_X log ρ_X - ∫ ρ_Y log ρ_Y`. -/
theorem integral_negMulLog_le_add (hρ0 : ∀ z, 0 ≤ ρ z) (hρ : Integrable ρ (μ.prod ν))
    (hρ1 : ∫ z, ρ z ∂(μ.prod ν) = 1) (hρρ : Integrable (fun z => negMulLog (ρ z)) (μ.prod ν))
    (hX : Integrable (fun x => negMulLog (∫ y, ρ (x, y) ∂ν)) μ)
    (hY : Integrable (fun y => negMulLog (∫ x, ρ (x, y) ∂μ)) ν) :
    ∫ z, negMulLog (ρ z) ∂(μ.prod ν) ≤
      ∫ x, negMulLog (∫ y, ρ (x, y) ∂ν) ∂μ + ∫ y, negMulLog (∫ x, ρ (x, y) ∂μ) ∂ν := by
  set ρX := fun x => ∫ y, ρ (x, y) ∂ν
  set ρY := fun y => ∫ x, ρ (x, y) ∂μ
  have hpos : ∀ᵐ z ∂(μ.prod ν), 0 < ρ z → 0 < ρX z.1 ∧ 0 < ρY z.2 := by
    filter_upwards [ae_pos_integral_prod_fst hρ0 hρ, ae_pos_integral_prod_snd hρ0 hρ]
      with z h1 h2 hz using ⟨h1 hz, h2 hz⟩
  have h1X := integrable_mul_log_integral_prod_fst hρ0 hρ hX
  have h1Y := integrable_mul_log_integral_prod_snd hρ0 hρ hY
  have hsplit : (fun z => ρ z * log (ρX z.1 * ρY z.2)) =ᵐ[μ.prod ν]
      fun z => ρ z * log (ρX z.1) + ρ z * log (ρY z.2) := by
    filter_upwards [hpos] with z hz
    rcases (hρ0 z).eq_or_lt with h | h
    · simp [← h]
    · obtain ⟨ha, hb⟩ := hz h
      rw [log_mul ha.ne' hb.ne', mul_add]
  have hmX : ∫ z, ρ z * log (ρX z.1) ∂(μ.prod ν) = -∫ x, negMulLog (ρX x) ∂μ := by
    have hc : Integrable (fun z => log (ρX z.1) * ρ z) (μ.prod ν) :=
      h1X.congr (ae_of_all _ fun z => mul_comm _ _)
    rw [integral_congr_ae (ae_of_all _ fun z => mul_comm _ _),
      ← integral_mul_integral_prod (g := fun x => log (ρX x)) (ρ := ρ) hc, ← integral_neg]
    simp [negMulLog, mul_comm, ρX]
  have hmY : ∫ z, ρ z * log (ρY z.2) ∂(μ.prod ν) = -∫ y, negMulLog (ρY y) ∂ν := by
    have hc : Integrable (fun z => log (ρY z.2) * ρ z) (μ.prod ν) :=
      h1Y.congr (ae_of_all _ fun z => mul_comm _ _)
    rw [integral_congr_ae (ae_of_all _ fun z => mul_comm _ _),
      ← integral_mul_integral_prod_snd (g := fun y => log (ρY y)) (ρ := ρ) hc, ← integral_neg]
    simp [negMulLog, mul_comm, ρY]
  have hG1 : ∫ z, ρX z.1 * ρY z.2 ∂(μ.prod ν) ≤ 1 := by
    rw [integral_prod_mul, ← integral_prod _ hρ, ← integral_prod_symm _ hρ, hρ1, one_mul]
  have h := integral_negMulLog_le_of_imp_pos (ae_of_all _ hρ0) hρ1
    (ae_of_all _ fun z => mul_nonneg (integral_nonneg fun y => hρ0 _)
      (integral_nonneg fun x => hρ0 _))
    (hpos.mono fun z hz h => mul_pos (hz h).1 (hz h).2)
    (hρ.integral_prod_left.mul_prod hρ.integral_prod_right) hG1 hρρ
    ((h1X.add h1Y).congr hsplit.symm)
  rw [integral_congr_ae hsplit, integral_add h1X h1Y, hmX, hmY] at h
  linarith

end MeasureTheory
