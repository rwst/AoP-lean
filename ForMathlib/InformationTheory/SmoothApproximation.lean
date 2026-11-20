/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.Floor

/-!
# Approximation of a density in relative entropy by smooth positive densities

Let `ρ ≥ 0` be a probability density with `ρ log ρ` integrable on a finite-dimensional real space
with an additive Haar measure, and `γ` a positive `Cⁿ` probability density. For every `ε > 0` there
is a positive `Cⁿ` probability density `η` with
  `∫ ρ log (ρ / η) < ε`,
the relative entropy `D(ρ ‖ η)`, and then `ρ log η` is integrable.

A finite entropy gives no moment of `ρ`, so no fixed reference density controls `D(ρ ‖ η)`, and
a single smoothing scale does not do either. The density `η` is built shell by shell: with
`A_k = {k ≤ ‖x‖ < k + 1}`,
  `η = (1 - t) ∑ₖ (1_{A_k} ρ) ⋆ φ_{N k} + t γ`,
where `φ_m` is a normalized bump of radius `1 / (m + 1)`. The sum is locally finite, so `η` is
`Cⁿ`, and it has mass `1`. By Lebesgue's differentiation theorem the scale `N k` can be chosen so
that `(1_{A_k} ρ) ⋆ φ_{N k} ≥ (1 - t) ρ` on `A_k` outside a set where `ρ log (ρ / t γ)`, which is
integrable on the bounded shell, has integral below `t / 2 ^ (k + 1)`.

## Main results

* `MeasureTheory.exists_contDiff_integral_mul_log_div_lt`: the approximation;
* `MeasureTheory.integrable_mul_log_of_integrable_mul_log_div`: `ρ log η` is then integrable.
-/

open Real Set Filter Topology Metric

open scoped ENNReal Convolution

public noncomputable section

namespace MeasureTheory

/-- With `ρ log ρ` and `ρ log (ρ / η)` integrable, so is `ρ log η`. -/
theorem integrable_mul_log_of_integrable_mul_log_div {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {ρ η : α → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hη : ∀ x, 0 < η x) (hρl : Integrable (fun x => ρ x * log (ρ x)) μ)
    (hd : Integrable (fun x => ρ x * log (ρ x / η x)) μ) :
    Integrable (fun x => ρ x * log (η x)) μ := by
  refine (hρl.sub hd).congr (ae_of_all _ fun x => ?_)
  rcases (hρ0 x).eq_or_lt with h0 | h0
  · simp [← h0]
  · simp only [Pi.sub_apply]
    rw [log_div h0.ne' (hη x).ne']
    ring

namespace DensityApprox

section Shell

variable {E : Type*} [NormedAddCommGroup E]

/-- The shell `k ≤ ‖x‖ < k + 1`. -/
def shell (k : ℕ) : Set E := {x | ⌊‖x‖⌋₊ = k}

lemma mem_shell {k : ℕ} {x : E} : x ∈ shell k ↔ (k : ℝ) ≤ ‖x‖ ∧ ‖x‖ < k + 1 :=
  Nat.floor_eq_iff (norm_nonneg x)

lemma mem_shell_floor (x : E) : x ∈ shell ⌊‖x‖⌋₊ := by simp [shell]

lemma measurableSet_shell [MeasurableSpace E] [BorelSpace E] (k : ℕ) :
    MeasurableSet (shell k : Set E) :=
  measurable_norm.nat_floor (measurableSet_singleton k)

lemma pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint (shell : ℕ → Set E)) :=
  fun _ _ hij => Set.disjoint_left.2 fun _ hi hj => hij (hi.symm.trans hj)

lemma iUnion_shell : ⋃ k, (shell k : Set E) = univ :=
  eq_univ_of_forall fun x => mem_iUnion.2 ⟨_, mem_shell_floor x⟩

end Shell

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {ρ : E → ℝ}

/-- A bump function of outer radius `1 / (m + 1)` and inner radius half of it. -/
def bump (m : ℕ) : ContDiffBump (0 : E) where
  rIn := 1 / (2 * (m + 1))
  rOut := 1 / (m + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

variable (μ) in
/-- The part of `ρ` on the shell `k`, smoothed at scale `1 / (m + 1)`. -/
def piece (ρ : E → ℝ) (k m : ℕ) : E → ℝ :=
  (bump m).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] (shell k).indicator ρ

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma piece_nonneg (hρ0 : ∀ x, 0 ≤ ρ x) (k m : ℕ) (x : E) : 0 ≤ piece μ ρ k m x := by
  rw [piece, convolution_def]
  refine integral_nonneg fun y => ?_
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact mul_nonneg ((bump m).nonneg_normed y) (indicator_nonneg (fun z _ => hρ0 z) _)

lemma contDiff_piece (hρ : Integrable ρ μ) (k m : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (piece μ ρ k m) :=
  (bump m).hasCompactSupport_normed.contDiff_convolution_left _ (bump m).contDiff_normed
    (hρ.indicator (measurableSet_shell k)).locallyIntegrable

lemma piece_ne_zero {k m : ℕ} {x : E} (hx : piece μ ρ k m x ≠ 0) :
    (k : ℝ) < ‖x‖ + 1 ∧ ‖x‖ < k + 2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset _ (Function.mem_support.2 hx)
  rw [(bump m).support_normed_eq, mem_ball_zero_iff] at ha
  have hb' := mem_shell.1 (support_indicator_subset hb)
  have ha1 : ‖a‖ < 1 := ha.trans_le <| by
    change 1 / ((m : ℝ) + 1) ≤ 1
    rw [div_le_one (by positivity)]
    linarith [m.cast_nonneg (α := ℝ)]
  have h1 := norm_add_le a b
  have h2 := norm_sub_le (a + b) a
  rw [add_sub_cancel_left] at h2
  constructor <;> linarith

lemma integrable_piece (hρ : Integrable ρ μ) (k m : ℕ) : Integrable (piece μ ρ k m) μ :=
  (bump m).integrable_normed.integrable_convolution _ (hρ.indicator (measurableSet_shell k))

lemma integral_piece (hρ : Integrable ρ μ) (k m : ℕ) :
    ∫ x, piece μ ρ k m x ∂μ = ∫ x in shell k, ρ x ∂μ := by
  rw [piece, integral_convolution _ (bump m).integrable_normed
    (hρ.indicator (measurableSet_shell k)), (bump m).integral_normed,
    integral_indicator (measurableSet_shell k)]
  simp

lemma tendsto_piece (hρ : Integrable ρ μ) (k : ℕ) :
    ∀ᵐ x ∂μ, Tendsto (fun m => piece μ ρ k m x) atTop (𝓝 ((shell k).indicator ρ x)) :=
  ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := bump) (K := 2)
    tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall fun m => le_of_eq <| by
      change 1 / ((m : ℝ) + 1) = 2 * (1 / (2 * (m + 1)))
      field_simp)
    (hρ.indicator (measurableSet_shell k)).locallyIntegrable

lemma piece_eq_zero {R : ℝ} {k m : ℕ} {x : E} (hx : ‖x‖ < R) (hk : ⌈R⌉₊ + 1 ≤ k) :
    piece μ ρ k m x = 0 := by
  by_contra h
  have h1 := (piece_ne_zero h).1
  have h2 : ((⌈R⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
  push_cast at h2
  linarith [Nat.le_ceil R]

variable (μ) in
/-- The smoothed shells, summed. -/
def smoothSum (ρ : E → ℝ) (N : ℕ → ℕ) (x : E) : ℝ := ∑' k, piece μ ρ k (N k) x

lemma smoothSum_eq (N : ℕ → ℕ) {R : ℝ} {x : E} (hx : ‖x‖ < R) :
    smoothSum μ ρ N x = ∑ k ∈ Finset.range (⌈R⌉₊ + 1), piece μ ρ k (N k) x :=
  tsum_eq_sum fun _ hk => piece_eq_zero hx (not_lt.1 fun h => hk (Finset.mem_range.2 h))

lemma contDiff_smoothSum (hρ : Integrable ρ μ) (N : ℕ → ℕ) {n : ℕ∞} :
    ContDiff ℝ n (smoothSum μ ρ N) := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  have hs : ContDiff ℝ n fun y => ∑ k ∈ Finset.range (⌈‖x‖ + 1⌉₊ + 1), piece μ ρ k (N k) y :=
    ContDiff.sum fun k _ => contDiff_piece hρ k (N k)
  refine hs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [ball_mem_nhds x one_pos] with y hy
  refine smoothSum_eq N ?_
  rw [mem_ball, dist_eq_norm] at hy
  linarith [norm_sub_norm_le y x]

omit [BorelSpace E] [μ.IsAddHaarMeasure] in
lemma smoothSum_nonneg (hρ0 : ∀ x, 0 ≤ ρ x) (N : ℕ → ℕ) (x : E) : 0 ≤ smoothSum μ ρ N x :=
  tsum_nonneg fun k => piece_nonneg hρ0 k (N k) x

lemma piece_le_smoothSum (hρ0 : ∀ x, 0 ≤ ρ x) (N : ℕ → ℕ) (k : ℕ) (x : E) :
    piece μ ρ k (N k) x ≤ smoothSum μ ρ N x := by
  rw [smoothSum_eq N (lt_add_one ‖x‖)]
  by_cases h : piece μ ρ k (N k) x = 0
  · rw [h]
    exact Finset.sum_nonneg fun j _ => piece_nonneg hρ0 j (N j) x
  · refine Finset.single_le_sum (f := fun j => piece μ ρ j (N j) x)
      (fun j _ => piece_nonneg hρ0 j (N j) x) (Finset.mem_range.2 ?_)
    have h1 := (piece_ne_zero h).1
    have h2 : (k : ℝ) < ⌈‖x‖ + 1⌉₊ + 1 := by linarith [Nat.le_ceil (‖x‖ + 1)]
    exact_mod_cast h2

lemma tsum_lintegral_piece (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ μ) (N : ℕ → ℕ) :
    ∑' k, ∫⁻ x, ‖piece μ ρ k (N k) x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (ρ x) ∂μ := by
  have h : ∀ k, ∫⁻ x, ‖piece μ ρ k (N k) x‖ₑ ∂μ = ∫⁻ x in shell k, ENNReal.ofReal (ρ x) ∂μ := by
    intro k
    simp_rw [Real.enorm_of_nonneg (piece_nonneg hρ0 k (N k) _)]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_piece hρ k (N k))
      (ae_of_all _ (piece_nonneg hρ0 k (N k))), integral_piece hρ,
      ofReal_integral_eq_lintegral_ofReal hρ.integrableOn (ae_of_all _ hρ0)]
  simp_rw [h]
  rw [← lintegral_iUnion measurableSet_shell pairwise_disjoint_shell, iUnion_shell,
    Measure.restrict_univ]

lemma integral_smoothSum (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ μ) (N : ℕ → ℕ) :
    ∫ x, smoothSum μ ρ N x ∂μ = ∫ x, ρ x ∂μ := by
  unfold smoothSum
  rw [integral_tsum (fun k => (contDiff_piece hρ k (N k) (n := 0)).continuous.aestronglyMeasurable)
    (by rw [tsum_lintegral_piece hρ0 hρ]; exact hρ.lintegral_lt_top.ne)]
  simp_rw [integral_piece hρ]
  rw [(hasSum_integral_iUnion measurableSet_shell pairwise_disjoint_shell
    (by rw [iUnion_shell]; exact hρ.integrableOn)).tsum_eq, iUnion_shell, Measure.restrict_univ]

end DensityApprox

open DensityApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {ρ : E → ℝ}

/-- **Approximation in relative entropy**, for a measurable `ρ`. -/
theorem exists_contDiff_integral_mul_log_div_lt_of_measurable {γ : E → ℝ} {n : ℕ∞}
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ μ) (hρ1 : ∫ x, ρ x ∂μ = 1)
    (hρl : Integrable (fun x => ρ x * log (ρ x)) μ) (hγ : ContDiff ℝ n γ) (hγ0 : ∀ x, 0 < γ x)
    (hγi : Integrable γ μ) (hγ1 : ∫ x, γ x ∂μ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : E → ℝ, ContDiff ℝ n η ∧ (∀ x, 0 < η x) ∧ Integrable η μ ∧ ∫ x, η x ∂μ = 1 ∧
      Integrable (fun x => ρ x * log (ρ x / η x)) μ ∧ ∫ x, ρ x * log (ρ x / η x) ∂μ < ε := by
  set t : ℝ := min (1 / 2) (ε / 10) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht2 : t ≤ 1 / 2 := min_le_left _ _
  have htε : t ≤ ε / 10 := min_le_right _ _
  -- `γ` is bounded below on balls
  have hc : ∀ k : ℕ, ∃ c > 0, ∀ x ∈ closedBall (0 : E) (k + 1), c ≤ γ x := fun k => by
    obtain ⟨x₀, -, hx₀⟩ := (isCompact_closedBall (0 : E) (k + 1)).exists_isMinOn
      (nonempty_closedBall.2 (by positivity)) hγ.continuous.continuousOn
    exact ⟨γ x₀, hγ0 x₀, fun x hx => hx₀ hx⟩
  choose c hc0 hc using hc
  -- the bound for `ρ log (ρ / t γ)` on the shell `k`
  set F : ℕ → E → ℝ := fun k x => |ρ x * log (ρ x)| + ρ x * |log (t * c k)| with hF
  have hFm : ∀ k, Measurable (F k) := fun k => by fun_prop
  have hFi : ∀ k, Integrable (F k) μ := fun k => hρl.abs.add (hρ.mul_const _)
  have hF0 : ∀ k x, 0 ≤ F k x := fun k x =>
    add_nonneg (abs_nonneg _) (mul_nonneg (hρ0 x) (abs_nonneg _))
  -- where the smoothed shell falls short of `(1 - t) ρ`
  set bad : ℕ → ℕ → Set E := fun k m => shell k ∩ {x | piece μ ρ k m x < (1 - t) * ρ x}
    with hbad_def
  have hbad : ∀ k m, MeasurableSet (bad k m) := fun k m =>
    (measurableSet_shell k).inter (measurableSet_lt
      (contDiff_piece hρ k m (n := 0)).continuous.measurable (hρm.const_mul _))
  -- the smoothing scales
  have hN : ∀ k, ∃ m, ∫⁻ x in bad k m, ENNReal.ofReal (F k x) ∂μ <
      ENNReal.ofReal (t / 2 / 2 ^ k) := by
    intro k
    have hlim : Tendsto (fun m => ∫⁻ x in bad k m, ENNReal.ofReal (F k x) ∂μ) atTop (𝓝 0) := by
      simp_rw [← lintegral_indicator (hbad k _)]
      have h := tendsto_lintegral_of_dominated_convergence (μ := μ)
        (F := fun m => (bad k m).indicator fun x => ENNReal.ofReal (F k x))
        (f := fun _ => 0) (fun x => ENNReal.ofReal (F k x))
        (fun m => (ENNReal.measurable_ofReal.comp (hFm k)).indicator (hbad k m))
        (fun m => ae_of_all _ fun x => indicator_le_self _ _ x)
        ((hFi k).lintegral_lt_top.ne) ?_
      · rwa [lintegral_zero] at h
      filter_upwards [tendsto_piece hρ k] with x hx
      refine tendsto_const_nhds.congr' ?_
      by_cases hs : x ∈ shell k
      · rcases (hρ0 x).eq_or_lt with h0 | h0
        · refine Eventually.of_forall fun m =>
            (indicator_of_notMem (fun (hb : x ∈ bad k m) => ?_) _).symm
          have : piece μ ρ k m x < (1 - t) * ρ x := hb.2
          rw [← h0, mul_zero] at this
          exact (piece_nonneg hρ0 k m x).not_gt this
        · rw [indicator_of_mem hs] at hx
          have hlt : (1 - t) * ρ x < ρ x := by nlinarith
          filter_upwards [hx.eventually (lt_mem_nhds hlt)] with m hm
          exact (indicator_of_notMem (fun (hb : x ∈ bad k m) => hb.2.not_gt hm) _).symm
      · exact Eventually.of_forall fun m =>
          (indicator_of_notMem (fun (hb : x ∈ bad k m) => hs hb.1) _).symm
    exact (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity)))).exists
  choose N hN using hN
  -- the approximant
  set κ := smoothSum μ ρ N with hκ
  have hκ0 : ∀ x, 0 ≤ κ x := smoothSum_nonneg hρ0 N
  have hκ1 : ∫ x, κ x ∂μ = 1 := (integral_smoothSum hρ0 hρ N).trans hρ1
  have hκi : Integrable κ μ := Integrable.of_integral_ne_zero (by rw [hκ1]; exact one_ne_zero)
  set η : E → ℝ := fun x => (1 - t) * κ x + t * γ x with hη
  have hηc : ContDiff ℝ n η :=
    (contDiff_const.mul (contDiff_smoothSum hρ N)).add (contDiff_const.mul hγ)
  have hηpos : ∀ x, 0 < η x := fun x => by
    have := hκ0 x
    have := hγ0 x
    simp only [hη]
    nlinarith
  have hηi : Integrable η μ := (hκi.const_mul _).add (hγi.const_mul _)
  have hη1 : ∫ x, η x ∂μ = 1 := by
    simp only [hη]
    rw [integral_add (hκi.const_mul _) (hγi.const_mul _), integral_const_mul, integral_const_mul,
      hκ1, hγ1]
    ring
  -- the bad set and its contribution
  set B := ⋃ k, bad k (N k) with hB
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun k => hbad k (N k)
  set Fx : E → ℝ := fun x => F ⌊‖x‖⌋₊ x with hFx
  have hFxm : Measurable Fx := by
    have hcm : Measurable fun x : E => |log (t * c ⌊‖x‖⌋₊)| :=
      (measurable_from_nat (f := fun k => |log (t * c k)|)).comp measurable_norm.nat_floor
    simp only [hFx, hF]
    fun_prop
  have hFx0 : ∀ x, 0 ≤ B.indicator Fx x := fun x => indicator_nonneg (fun y _ => hF0 _ y) x
  have hlin : ∫⁻ x in B, ENNReal.ofReal (Fx x) ∂μ ≤ ENNReal.ofReal t := by
    rw [hB, lintegral_iUnion (fun k => hbad k (N k))
      (fun i j hij => (pairwise_disjoint_shell hij).mono inter_subset_left inter_subset_left)]
    calc ∑' k, ∫⁻ x in bad k (N k), ENNReal.ofReal (Fx x) ∂μ
        = ∑' k, ∫⁻ x in bad k (N k), ENNReal.ofReal (F k x) ∂μ := by
          congr 1
          ext k
          refine setLIntegral_congr_fun (hbad k (N k)) fun x hx => ?_
          simp only [hFx]
          rw [show ⌊‖x‖⌋₊ = k from hx.1]
      _ ≤ ∑' k, ENNReal.ofReal (t / 2 / 2 ^ k) := tsum_le_tsum fun k => (hN k).le
      _ = ENNReal.ofReal t := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) (summable_geometric_two' t),
            tsum_geometric_two']
  have hind : ∀ x, ENNReal.ofReal (B.indicator Fx x) =
      B.indicator (fun x => ENNReal.ofReal (Fx x)) x := fun x => by
    by_cases hx : x ∈ B <;> simp [hx]
  have hGb : Integrable (B.indicator Fx) μ := by
    refine ⟨(hFxm.indicator hBm).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hFx0)]
    simp_rw [hind]
    rw [lintegral_indicator hBm]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  have hGb_int : ∫ x, B.indicator Fx x ∂μ ≤ t := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hFx0) hGb.aestronglyMeasurable]
    simp_rw [hind]
    rw [lintegral_indicator hBm]
    exact ENNReal.toReal_le_of_le_ofReal ht0.le hlin
  -- pointwise bounds
  have hup : ∀ x, ρ x * log (ρ x / η x) ≤ ρ x * (8 * t) + B.indicator Fx x := by
    intro x
    have hxk : x ∈ shell ⌊‖x‖⌋₊ := mem_shell_floor x
    rcases (hρ0 x).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, zero_mul, zero_add]
      exact hFx0 x
    by_cases hb : x ∈ bad ⌊‖x‖⌋₊ (N ⌊‖x‖⌋₊)
    · rw [indicator_of_mem (show x ∈ B from mem_iUnion.2 ⟨_, hb⟩)]
      set k := ⌊‖x‖⌋₊
      have hxb : x ∈ closedBall (0 : E) (k + 1) := by
        rw [mem_closedBall_zero_iff]
        exact (mem_shell.1 hxk).2.le
      have hck := hc k x hxb
      have hη' : t * c k ≤ η x := by
        have := hκ0 x
        have := hc0 k
        simp only [hη]
        nlinarith
      have htc : 0 < t * c k := mul_pos ht0 (hc0 k)
      have h1 : log (ρ x / η x) ≤ log (ρ x) - log (t * c k) := by
        rw [← log_div h0.ne' htc.ne']
        exact log_le_log (div_pos h0 (hηpos x)) (div_le_div_of_nonneg_left h0.le htc hη')
      have h2 : ρ x * log (ρ x / η x) ≤ ρ x * log (ρ x) - ρ x * log (t * c k) := by
        nlinarith
      have h3 : ρ x * log (ρ x) ≤ |ρ x * log (ρ x)| := le_abs_self _
      have h4 : -(ρ x * log (t * c k)) ≤ ρ x * |log (t * c k)| := by
        rw [← mul_neg]
        exact mul_le_mul_of_nonneg_left (neg_le_abs _) h0.le
      have h5 : 0 ≤ ρ x * (8 * t) := by positivity
      simp only [hFx, hF]
      linarith
    · have hpk : (1 - t) * ρ x ≤ piece μ ρ ⌊‖x‖⌋₊ (N ⌊‖x‖⌋₊) x :=
        not_lt.1 fun h => hb ⟨hxk, h⟩
      have hκx := piece_le_smoothSum (μ := μ) hρ0 N ⌊‖x‖⌋₊ x
      have h1t : 0 < 1 - t := by linarith
      have hη' : (1 - t) ^ 2 * ρ x ≤ η x := by
        have := hγ0 x
        simp only [hη]
        nlinarith
      have hq : ρ x / η x ≤ 1 + 8 * t := by
        rw [div_le_iff₀ (hηpos x)]
        have hpoly : 1 ≤ (1 + 8 * t) * (1 - t) ^ 2 := by
          nlinarith [sq_nonneg (t - 1 / 2)]
        nlinarith
      have hl : log (ρ x / η x) ≤ 8 * t := by
        linarith [log_le_sub_one_of_pos (div_pos h0 (hηpos x))]
      have := mul_le_mul_of_nonneg_left hl h0.le
      linarith [hFx0 x]
  have hlow : ∀ x, ρ x - η x ≤ ρ x * log (ρ x / η x) := by
    intro x
    rcases (hρ0 x).eq_or_lt with h0 | h0
    · rw [← h0]
      simpa using (hηpos x).le
    · have h1 := one_sub_inv_le_log_of_pos (div_pos h0 (hηpos x))
      rw [inv_div] at h1
      have h2 : ρ x * (1 - η x / ρ x) = ρ x - η x := by field_simp
      nlinarith
  -- conclusion
  have hfm : Measurable fun x => ρ x * log (ρ x / η x) :=
    hρm.mul (hρm.div hηc.continuous.measurable).log
  have hup_i : Integrable (fun x => ρ x * (8 * t) + B.indicator Fx x) μ :=
    (hρ.mul_const _).add hGb
  have hfi : Integrable (fun x => ρ x * log (ρ x / η x)) μ :=
    integrable_of_le_of_le hfm.aestronglyMeasurable (ae_of_all _ hlow) (ae_of_all _ hup)
      (hρ.sub hηi) hup_i
  refine ⟨η, hηc, hηpos, hηi, hη1, hfi, ?_⟩
  calc ∫ x, ρ x * log (ρ x / η x) ∂μ ≤ ∫ x, (ρ x * (8 * t) + B.indicator Fx x) ∂μ :=
        integral_mono hfi hup_i hup
    _ = 8 * t + ∫ x, B.indicator Fx x ∂μ := by
        rw [integral_add (hρ.mul_const _) hGb, integral_mul_const, hρ1, one_mul]
    _ < ε := by linarith

/-- **Approximation in relative entropy.** A probability density `ρ` with `ρ log ρ` integrable
is the limit, in relative entropy, of positive `Cⁿ` probability densities: for `ε > 0` there is
one, `η`, with `∫ ρ log (ρ / η) < ε`. Any positive `Cⁿ` probability density `γ` serves as a
reference for the construction. -/
theorem exists_contDiff_integral_mul_log_div_lt {γ : E → ℝ} {n : ℕ∞} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ : Integrable ρ μ) (hρ1 : ∫ x, ρ x ∂μ = 1) (hρl : Integrable (fun x => ρ x * log (ρ x)) μ)
    (hγ : ContDiff ℝ n γ) (hγ0 : ∀ x, 0 < γ x) (hγi : Integrable γ μ) (hγ1 : ∫ x, γ x ∂μ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : E → ℝ, ContDiff ℝ n η ∧ (∀ x, 0 < η x) ∧ Integrable η μ ∧ ∫ x, η x ∂μ = 1 ∧
      Integrable (fun x => ρ x * log (ρ x / η x)) μ ∧ ∫ x, ρ x * log (ρ x / η x) ∂μ < ε := by
  -- a measurable, nonnegative version of `ρ`
  set ρ' : E → ℝ := fun x => max (hρ.aestronglyMeasurable.mk ρ x) 0 with hρ'
  have hρ'm : Measurable ρ' := hρ.aestronglyMeasurable.stronglyMeasurable_mk.measurable.max
    measurable_const
  have hae : ρ' =ᵐ[μ] ρ := by
    filter_upwards [hρ.aestronglyMeasurable.ae_eq_mk] with x hx
    simp only [hρ', ← hx, max_eq_left (hρ0 x)]
  have hρ'i : Integrable ρ' μ := hρ.congr hae.symm
  have hρ'1 : ∫ x, ρ' x ∂μ = 1 := (integral_congr_ae hae).trans hρ1
  have hρ'l : Integrable (fun x => ρ' x * log (ρ' x)) μ :=
    hρl.congr (hae.mono fun x hx => by simp only [hx])
  obtain ⟨η, hηc, hηpos, hηi, hη1, hfi, hf⟩ :=
    exists_contDiff_integral_mul_log_div_lt_of_measurable hρ'm (fun x => le_max_right _ _) hρ'i
      hρ'1 hρ'l hγ hγ0 hγi hγ1 hε
  have hae' : (fun x => ρ' x * log (ρ' x / η x)) =ᵐ[μ] fun x => ρ x * log (ρ x / η x) :=
    hae.mono fun x hx => by simp only [hx]
  exact ⟨η, hηc, hηpos, hηi, hη1, hfi.congr hae', (integral_congr_ae hae').symm.trans_lt hf⟩

end MeasureTheory
