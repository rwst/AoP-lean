/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Physlib.Mathematics.ForMathlib.OneParameterSubgroups.Unitary
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.StoneUnitaryGroup

/-!
# Spectral cutoffs of a unitary group

## i. Overview

Let `μS` be a projection-valued measure on `ℝ`, so that `V t = ∫ e^{itx} dμS(x)` is a strongly
continuous unitary group (`WOTSpectralMeasure.expIntegral`); by Stone's theorem every strongly
continuous unitary group has this form. Its generator `∫ x dμS(x)` is unbounded in general.

Cutting the spectrum off at `M ≥ 0`, with `c_M (x) = max (-M) (min x M)`, gives the groups
`W_M t = ∫ e^{it c_M(x)} dμS(x)`. Since `|e^{iθ} - e^{iθ'}| ≤ |θ - θ'|` and `|c_M| ≤ M`, the bounded
spectral integral gives `‖W_M t - W_M s‖ ≤ M |t - s|`. So `W_M` is a norm-continuous unitary group,
with bounded generator of norm at most `M`. As `M → ∞`, `c_M (x) = x` eventually for each `x`, and
dominated convergence in `‖(W_M t - V t) x‖² = ∫ |e^{it c_M} - e^{itx}|² dμ_x` gives
`W_M t → V t` strongly. This is the bounded convergence theorem for the spectral calculus.

The spectral projector `P_m = μS [-m, m]` cuts off the other way: on its range, `W_M = W_m` for
`M ≥ m`, and `P_m → 1` strongly as `m → ∞`.

## ii. Key results

- `QuantumMechanics.cutoffGroup`: the group `W_M t = exp (it c_M(H))`.
- `QuantumMechanics.norm_cutoffGroup_generator_le`: its generator has norm at most `M`.
- `QuantumMechanics.tendsto_cutoffGroup_apply`: `W_M t → V t` strongly as `M → ∞`.
- `QuantumMechanics.spectralCutoffProj`: the spectral projector `P_m` of `[-m, m]`.
- `QuantumMechanics.cutoffGroup_mul_spectralCutoffProj`: `W_M t P_m = W_m t P_m` for `M ≥ m`.
- `QuantumMechanics.tendsto_spectralCutoffProj_apply`: `P_m → 1` strongly.

## iii. References

- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer (2012),
  Prop 4.12 (bounded convergence) and Thm 4.16.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology
open Filter Set MeasureTheory ProbabilisticTheory.QuantumMechanics
  ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (μS : WOTSpectralMeasure ℝ E)

/-! ## A. The cutoff function -/

/-- The cutoff `c_M (x) = max (-M) (min x M)`. -/
def spectralCutoff (M x : ℝ) : ℝ := max (-M) (min x M)

lemma continuous_spectralCutoff (M : ℝ) : Continuous (spectralCutoff M) :=
  continuous_const.max (continuous_id.min continuous_const)

lemma abs_spectralCutoff_le (M x : ℝ) : |spectralCutoff M x| ≤ |M| := by
  rw [abs_le]
  refine ⟨(neg_le_neg (le_abs_self M)).trans (le_max_left _ _), ?_⟩
  exact (max_le_max le_rfl (min_le_right _ _)).trans (by rw [max_comm, ← abs_eq_max_neg])

lemma spectralCutoff_eq {M x : ℝ} (h : |x| ≤ M) : spectralCutoff M x = x := by
  rw [abs_le] at h
  rw [spectralCutoff, min_eq_left h.2, max_eq_right h.1]

/-- The multiplier `x ↦ e^{it c_M(x)}`. -/
def cutoffExp (M t : ℝ) : ℝ → ℂ := fun x => expFunction t (spectralCutoff M x)

lemma measurable_cutoffExp (M t : ℝ) : Measurable (cutoffExp M t) :=
  (expFunction_measurable t).comp (continuous_spectralCutoff M).measurable

lemma norm_cutoffExp (M t x : ℝ) : ‖cutoffExp M t x‖ = 1 := expFunction_modulus t _

lemma bounded_cutoffExp (M t : ℝ) : ∃ C, ∀ x, ‖cutoffExp M t x‖ ≤ C :=
  ⟨1, fun x => (norm_cutoffExp M t x).le⟩

/-- `|e^{itc} - e^{isc}| ≤ |M| |t - s|` for `c = c_M (x)`. -/
lemma norm_cutoffExp_sub_le (M t s x : ℝ) :
    ‖cutoffExp M t x - cutoffExp M s x‖ ≤ |M| * |t - s| := by
  set c := spectralCutoff M x
  have h : cutoffExp M t x - cutoffExp M s x =
      expFunction s c * (Complex.exp (Complex.I * ((t - s) * c : ℝ)) - 1) := by
    simp only [cutoffExp, expFunction, c, mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, expFunction_modulus, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (abs_spectralCutoff_le M x) (abs_nonneg _)

/-! ## B. The cutoff group -/

/-- `∫ e^{it c_M(x)} dμS(x)`. -/
def cutoffIntegral (M t : ℝ) : E →WOT[ℂ] E :=
  boundedIntegral μS (cutoffExp M t) (measurable_cutoffExp M t) (bounded_cutoffExp M t)

lemma cutoffIntegral_add (M t s : ℝ) :
    cutoffIntegral μS M (t + s) = cutoffIntegral μS M t * cutoffIntegral μS M s := by
  rw [cutoffIntegral, cutoffIntegral, cutoffIntegral, ← boundedIntegral_mul]
  exact boundedIntegral_congr μS _ _ _ _ fun x => congrFun (expFunction_add t s) _

lemma cutoffIntegral_zero (M : ℝ) : cutoffIntegral μS M 0 = 1 := by
  rw [cutoffIntegral]
  calc _ = boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
        ⟨‖(1 : ℂ)‖, fun _ => le_rfl⟩ :=
        boundedIntegral_congr μS _ _ _ _ fun x => by simp [cutoffExp, expFunction]
    _ = 1 := by rw [boundedIntegral_const, one_smul]

lemma star_cutoffIntegral (M t : ℝ) : star (cutoffIntegral μS M t) = cutoffIntegral μS M (-t) := by
  rw [cutoffIntegral, ← boundedIntegral_star]
  exact boundedIntegral_congr μS _ _ _ _ fun x => (congrFun (expFunction_neg_eq_star t) _).symm

lemma cutoffIntegral_mem_unitary (M t : ℝ) : cutoffIntegral μS M t ∈ unitary (E →WOT[ℂ] E) := by
  rw [Unitary.mem_iff, star_cutoffIntegral, ← cutoffIntegral_add, ← cutoffIntegral_add,
    neg_add_cancel, add_neg_cancel, cutoffIntegral_zero]
  exact ⟨rfl, rfl⟩

/-- `‖W_M t - W_M s‖ ≤ |M| |t - s|`. -/
lemma norm_cutoffIntegral_sub_le (M t s : ℝ) :
    ‖(cutoffIntegral μS M t).toCLM - (cutoffIntegral μS M s).toCLM‖ ≤ |M| * |t - s| := by
  have h := boundedIntegral_sub μS (measurable_cutoffExp M t) (measurable_cutoffExp M s)
    (bounded_cutoffExp M t) (bounded_cutoffExp M s)
  rw [← ContinuousLinearMapWOT.toCLM_sub, cutoffIntegral, cutoffIntegral, ← h]
  exact boundedIntegral_norm_le_of_bound μS _ (by positivity) fun x =>
    norm_cutoffExp_sub_le M t s x

/-- **The cutoff group** `W_M t = exp (it c_M(H))`, a norm-continuous unitary group. -/
def cutoffGroup (M : ℝ) : UnitaryOneParameterGroup E where
  toAddChar :=
    { toFun := fun t => (cutoffIntegral μS M t).toCLM
      map_zero_eq_one' := by rw [cutoffIntegral_zero]; rfl
      map_add_eq_mul' := fun t s => by rw [cutoffIntegral_add]; rfl }
  mem_unitary t := by
    have h := Unitary.mem_iff.mp (cutoffIntegral_mem_unitary μS M t)
    rw [Unitary.mem_iff]
    exact ⟨congrArg ContinuousLinearMapWOT.toCLM h.1, congrArg ContinuousLinearMapWOT.toCLM h.2⟩
  continuous := by
    refine LipschitzWith.continuous (K := ‖M‖₊) (LipschitzWith.of_dist_le_mul fun t s => ?_)
    rw [dist_eq_norm, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
    exact norm_cutoffIntegral_sub_le μS M t s

lemma cutoffGroup_apply (M t : ℝ) : cutoffGroup μS M t = (cutoffIntegral μS M t).toCLM := rfl

/-- The generator of the cutoff group has norm at most `M`. -/
theorem norm_cutoffGroup_generator_le {M : ℝ} (hM : 0 ≤ M) :
    ‖(cutoffGroup μS M).generator‖ ≤ M := by
  have hlip : LipschitzWith ‖M‖₊ (cutoffGroup μS M : ℝ → E →L[ℂ] E) :=
    LipschitzWith.of_dist_le_mul fun t s => by
      rw [dist_eq_norm, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
      exact norm_cutoffIntegral_sub_le μS M t s
  rw [UnitaryOneParameterGroup.generator, norm_smul, Complex.norm_I, one_mul]
  refine (norm_deriv_le_of_lipschitz hlip).trans_eq ?_
  rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hM]

/-! ## C. Strong convergence -/

/-- **Bounded convergence**: `W_M t → V t` strongly as `M → ∞`. -/
theorem tendsto_cutoffGroup_apply (t : ℝ) (x : E) :
    Tendsto (fun M => cutoffGroup μS M t x) atTop (𝓝 ((expIntegral μS t).toCLM x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set μ := μS.diagonalMeasure x
  set F : ℝ → ℝ → ℝ := fun M z => ‖cutoffExp M t z - expFunction t z‖ ^ 2
  have hsq : ∀ M, ‖cutoffGroup μS M t x - (expIntegral μS t).toCLM x‖ ^ 2 = ∫ z, F M z ∂μ := by
    intro M
    have h := boundedIntegral_sub μS (measurable_cutoffExp M t) (expFunction_measurable t)
      (bounded_cutoffExp M t) (expFunction_bounded t)
    rw [cutoffGroup_apply, ← sub_apply, ← ContinuousLinearMapWOT.toCLM_sub,
      cutoffIntegral, expIntegral, ← h, ContinuousLinearMapWOT.toCLM_apply,
      boundedIntegral_norm_sq_eq_integral]
    rfl
  have hint : Tendsto (fun M => ∫ z, F M z ∂μ) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun M =>
        (((measurable_cutoffExp M t).sub (expFunction_measurable t)).norm.pow_const 2
          ).aestronglyMeasurable
    · refine Eventually.of_forall fun M => Eventually.of_forall fun z => ?_
      have h : ‖cutoffExp M t z - expFunction t z‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_cutoffExp, expFunction_modulus]
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (cutoffExp M t z - expFunction t z)]
    · refine Eventually.of_forall fun z => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |z|] with M hM
      simp [F, cutoffExp, spectralCutoff_eq hM]
  rw [integral_zero] at hint
  have h := (Real.continuous_sqrt.tendsto 0).comp hint
  rw [Real.sqrt_zero] at h
  refine h.congr fun M => ?_
  simp only [Function.comp_apply, ← hsq, Real.sqrt_sq (norm_nonneg _)]

/-! ## D. Spectral projectors -/

/-- The indicator of `[-m, m]`. -/
def cutoffIndicator (m : ℝ) : ℝ → ℂ := (Icc (-m) m).indicator fun _ => (1 : ℂ)

lemma measurable_cutoffIndicator (m : ℝ) : Measurable (cutoffIndicator m) :=
  measurable_const.indicator measurableSet_Icc

lemma bounded_cutoffIndicator (m : ℝ) : ∃ C, ∀ x, ‖cutoffIndicator m x‖ ≤ C :=
  ⟨1, fun x => by by_cases hx : x ∈ Icc (-m) m <;> simp [cutoffIndicator, hx]⟩

/-- The spectral projector `P_m = μS [-m, m]`. -/
def spectralCutoffProj (m : ℝ) : E →L[ℂ] E := (μS (Icc (-m) m)).toCLM

lemma spectralCutoffProj_eq (m : ℝ) : spectralCutoffProj μS m =
    (boundedIntegral μS (cutoffIndicator m) (measurable_cutoffIndicator m)
      (bounded_cutoffIndicator m)).toCLM := by
  rw [spectralCutoffProj]
  exact congrArg _ (boundedIntegral_indicator μS measurableSet_Icc).symm

lemma isStarProjection_spectralCutoffProj (m : ℝ) :
    IsStarProjection (spectralCutoffProj μS m) := by
  have h := μS.isStarProjection (Icc (-m) m)
  exact ⟨congrArg ContinuousLinearMapWOT.toCLM h.isIdempotentElem.eq,
    congrArg ContinuousLinearMapWOT.toCLM h.isSelfAdjoint.star_eq⟩

/-- On the range of `P_m`, the cutoff groups agree beyond `m`: `W_M t P_m = W_m t P_m`. -/
theorem cutoffGroup_mul_spectralCutoffProj {m M : ℝ} (hm : m ≤ M) (t : ℝ) :
    cutoffGroup μS M t * spectralCutoffProj μS m =
      cutoffGroup μS m t * spectralCutoffProj μS m := by
  rw [spectralCutoffProj_eq, cutoffGroup_apply, cutoffGroup_apply, cutoffIntegral, cutoffIntegral,
    ← ContinuousLinearMapWOT.toCLM_mul, ← ContinuousLinearMapWOT.toCLM_mul, ← boundedIntegral_mul,
    ← boundedIntegral_mul]
  refine congrArg _ (boundedIntegral_congr μS _ _ _ _ fun x => ?_)
  by_cases hx : x ∈ Icc (-m) m
  · have hxm : |x| ≤ m := abs_le.mpr hx
    simp [cutoffIndicator, hx, cutoffExp, spectralCutoff_eq hxm, spectralCutoff_eq (hxm.trans hm)]
  · simp [cutoffIndicator, hx]

/-- `P_m → 1` strongly as `m → ∞`. -/
theorem tendsto_spectralCutoffProj_apply (x : E) :
    Tendsto (fun m => spectralCutoffProj μS m x) atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set μ := μS.diagonalMeasure x
  set F : ℝ → ℝ → ℝ := fun m z => ‖cutoffIndicator m z - 1‖ ^ 2
  have h1 : (1 : E →WOT[ℂ] E) = boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
      ⟨‖(1 : ℂ)‖, fun _ => le_rfl⟩ := by rw [boundedIntegral_const, one_smul]
  have hsq : ∀ m, ‖spectralCutoffProj μS m x - x‖ ^ 2 = ∫ z, F m z ∂μ := by
    intro m
    have h := boundedIntegral_sub μS (measurable_cutoffIndicator m) measurable_const
      (bounded_cutoffIndicator m) ⟨‖(1 : ℂ)‖, fun _ => le_rfl⟩
    have hx : x = (1 : E →WOT[ℂ] E).toCLM x := rfl
    rw [spectralCutoffProj_eq]
    nth_rw 2 [hx]
    rw [h1, ← sub_apply, ← ContinuousLinearMapWOT.toCLM_sub, ← h,
      ContinuousLinearMapWOT.toCLM_apply, boundedIntegral_norm_sq_eq_integral]
    rfl
  have hint : Tendsto (fun m => ∫ z, F m z ∂μ) atTop (𝓝 (∫ _ : ℝ, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
      (integrable_const _) ?_
    · exact Eventually.of_forall fun m =>
        (((measurable_cutoffIndicator m).sub measurable_const).norm.pow_const 2
          ).aestronglyMeasurable
    · refine Eventually.of_forall fun m => Eventually.of_forall fun z => ?_
      by_cases hz : z ∈ Icc (-m) m <;> simp [F, cutoffIndicator, hz]
    · refine Eventually.of_forall fun z => tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop |z|] with m hm
      simp [F, cutoffIndicator, abs_le.mp hm]
  rw [integral_zero] at hint
  have h := (Real.continuous_sqrt.tendsto 0).comp hint
  rw [Real.sqrt_zero] at h
  refine h.congr fun m => ?_
  simp only [Function.comp_apply, ← hsq, Real.sqrt_sq (norm_nonneg _)]

end QuantumMechanics
