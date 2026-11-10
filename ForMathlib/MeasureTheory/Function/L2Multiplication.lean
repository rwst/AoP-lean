/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.l2DiagonalEvolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Multiplication operators on `L²` and their unitary evolution

For a measurable `a : α → ℝ`, the multiplication operator `f ↦ a f` on `L²(μ)` is defined on its
maximal domain `{f | a f ∈ L²}`. The operators `U t f = e^{-i a t} f` are the unitary group
`e^{-i t A}` it generates. Each `U t` is defined on the whole space, but the orbit `t ↦ U t f`
solves the Schrödinger equation `d/dt (U t f) = -i A (U t f)` exactly when `f` lies in the
domain of `A`: outside the domain the orbit is differentiable nowhere. This is the `L²(μ)`
version of `lp.diagonalEvolution`.

## Main definitions

* `MeasureTheory.L2.mulDomain a`: the maximal domain;
* `MeasureTheory.L2.mulOp a`: the multiplication operator, as a partially defined linear map;
* `MeasureTheory.L2.mulEvolution ha t`: the unitary `U t`, as a linear isometry equivalence.

## Main results

* `MeasureTheory.L2.mulEvolution_mem_mulDomain_iff`: `U t` preserves the domain of `A`;
* `MeasureTheory.L2.hasDerivAt_mulEvolution`: on the domain, `t ↦ U t f` has derivative
  `-i A (U t f)`;
* `MeasureTheory.L2.not_differentiableAt_mulEvolution`: off the domain, it is not
  differentiable;
* `MeasureTheory.L2.differentiableAt_mulEvolution_iff`: the two together.
-/

open Complex Filter Topology
open lp (phase norm_phase phase_add phase_neg_mul_phase hasDerivAt_phase norm_phase_sub_one_le)

@[expose] public noncomputable section

namespace MeasureTheory.L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} (a : α → ℝ)

lemma norm_sq_eq_integral (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [@norm_sq_eq_re_inner ℂ, inner_def, ← integral_re (integrable_inner f f)]
  congr 1 with x
  exact inner_self_eq_norm_sq _

/-- The maximal domain `{f | a f ∈ L²}` of the multiplication operator by `a`. -/
def mulDomain : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (fun x => (a x : ℂ) * f x) 2 μ}
  add_mem' {f g} hf hg := by
    change MemLp (fun x => (a x : ℂ) * (f + g : Lp ℂ 2 μ) x) 2 μ
    refine (MemLp.add hf hg).ae_eq ?_
    filter_upwards [Lp.coeFn_add f g] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, mul_add]
  zero_mem' := by
    change MemLp (fun x => (a x : ℂ) * (0 : Lp ℂ 2 μ) x) 2 μ
    refine (Lp.memLp (0 : Lp ℂ 2 μ)).ae_eq ?_
    filter_upwards [Lp.coeFn_zero ℂ 2 μ] with x hx
    rw [hx, Pi.zero_apply, mul_zero]
  smul_mem' c f hf := by
    change MemLp (fun x => (a x : ℂ) * (c • f : Lp ℂ 2 μ) x) 2 μ
    refine (MemLp.const_smul hf c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    rw [hx, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

lemma mem_mulDomain {f : Lp ℂ 2 μ} :
    f ∈ mulDomain a ↔ MemLp (fun x => (a x : ℂ) * f x) 2 μ :=
  Iff.rfl

/-- The multiplication operator `f ↦ a f` on its maximal domain. -/
def mulOp : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := mulDomain a
  toFun :=
    { toFun f := MemLp.toLp (fun x => (a x : ℂ) * (f : Lp ℂ 2 μ) x) f.2
      map_add' f g := by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (mem_mulDomain a |>.1 (f + g).2),
          MemLp.coeFn_toLp (mem_mulDomain a |>.1 f.2), MemLp.coeFn_toLp (mem_mulDomain a |>.1 g.2),
          Lp.coeFn_add (MemLp.toLp _ (mem_mulDomain a |>.1 f.2))
            (MemLp.toLp _ (mem_mulDomain a |>.1 g.2)),
          Lp.coeFn_add (f : Lp ℂ 2 μ) g] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, Submodule.coe_add, h5, Pi.add_apply, mul_add]
      map_smul' c f := by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (mem_mulDomain a |>.1 (c • f).2),
          MemLp.coeFn_toLp (mem_mulDomain a |>.1 f.2),
          Lp.coeFn_smul c (MemLp.toLp _ (mem_mulDomain a |>.1 f.2)), Lp.coeFn_smul c (f : Lp ℂ 2 μ)]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, Submodule.coe_smul, h4, Pi.smul_apply,
          smul_eq_mul, smul_eq_mul, mul_left_comm] }

lemma domain_mulOp : (mulOp a : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ).domain = mulDomain a :=
  rfl

lemma coeFn_mulOp (f : (mulOp a : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ).domain) :
    mulOp a f =ᵐ[μ] fun x => (a x : ℂ) * (f : Lp ℂ 2 μ) x :=
  MemLp.coeFn_toLp ((mem_mulDomain a).1 f.2)

variable {a} (ha : Measurable a)
include ha

lemma memLp_phase_mul (t : ℝ) {f : α → ℂ} (hf : MemLp f 2 μ) :
    MemLp (fun x => phase (a x) t * f x) 2 μ := by
  have hc : Continuous fun r => phase r t := by
    unfold phase
    fun_prop
  refine hf.congr_norm ((hc.measurable.comp ha).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [norm_mul, norm_phase, one_mul]

/-- Multiplication by `e^{-i a t}`, as a map of `L²`. -/
def mulPhase (t : ℝ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ := (memLp_phase_mul ha t (Lp.memLp f)).toLp

lemma coeFn_mulPhase (t : ℝ) (f : Lp ℂ 2 μ) :
    mulPhase ha t f =ᵐ[μ] fun x => phase (a x) t * f x :=
  MemLp.coeFn_toLp _

/-- The unitary evolution `U t f = e^{-i a t} f` generated by the multiplication operator by
`a`. -/
def mulEvolution (t : ℝ) : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun := mulPhase ha t
  invFun := mulPhase ha (-t)
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_mulPhase ha t (f + g), coeFn_mulPhase ha t f, coeFn_mulPhase ha t g,
      Lp.coeFn_add (mulPhase ha t f) (mulPhase ha t g), Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, mul_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_mulPhase ha t (c • f), coeFn_mulPhase ha t f,
      Lp.coeFn_smul c (mulPhase ha t f), Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, mul_left_comm]
  left_inv f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_mulPhase ha (-t) (mulPhase ha t f), coeFn_mulPhase ha t f]
      with x h1 h2
    rw [h1, h2, ← mul_assoc, phase_neg_mul_phase, one_mul]
  right_inv f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_mulPhase ha t (mulPhase ha (-t) f), coeFn_mulPhase ha (-t) f]
      with x h1 h2
    have := phase_neg_mul_phase (a x) (-t)
    rw [neg_neg] at this
    rw [h1, h2, ← mul_assoc, this, one_mul]
  norm_map' f := by
    change ‖mulPhase ha t f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable f)]
    filter_upwards [coeFn_mulPhase ha t f] with x hx
    rw [hx, norm_mul, norm_phase, one_mul]

lemma coeFn_mulEvolution (t : ℝ) (f : Lp ℂ 2 μ) :
    mulEvolution ha t f =ᵐ[μ] fun x => phase (a x) t * f x :=
  coeFn_mulPhase ha t f

/-- `U t` preserves the domain of the multiplication operator. -/
theorem mulEvolution_mem_mulDomain_iff (t : ℝ) {f : Lp ℂ 2 μ} :
    mulEvolution ha t f ∈ mulDomain a ↔ f ∈ mulDomain a := by
  have hm (g : Lp ℂ 2 μ) : AEStronglyMeasurable (fun x => (a x : ℂ) * g x) μ :=
    (Complex.continuous_ofReal.measurable.comp ha).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable g)
  have hn : ∀ᵐ x ∂μ, ‖(a x : ℂ) * mulEvolution ha t f x‖ = ‖(a x : ℂ) * f x‖ := by
    filter_upwards [coeFn_mulEvolution ha t f] with x hx
    rw [hx, norm_mul, norm_mul, norm_mul, norm_phase, one_mul]
  exact ⟨fun h => MemLp.congr_norm h (hm f) hn,
    fun h => MemLp.congr_norm h (hm _) (hn.mono fun _ hx => hx.symm)⟩

/-- On the domain of `A = mulOp a`, the orbit `t ↦ U t f` solves the Schrödinger equation
`d/dt (U t f) = -i A (U t f)`. -/
theorem hasDerivAt_mulEvolution {f : Lp ℂ 2 μ} (hf : f ∈ mulDomain a) (t : ℝ) :
    HasDerivAt (fun s => mulEvolution ha s f)
      (-(I • mulOp a ⟨mulEvolution ha t f, (mulEvolution_mem_mulDomain_iff ha t).2 hf⟩)) t := by
  have hm := (mulEvolution_mem_mulDomain_iff ha t).2 hf
  set v : Lp ℂ 2 μ := -(I • mulOp a ⟨mulEvolution ha t f, hm⟩)
  have hv : v =ᵐ[μ] fun x => -(I * (a x * phase (a x) t)) * f x := by
    filter_upwards [Lp.coeFn_neg (I • mulOp a ⟨mulEvolution ha t f, hm⟩),
      Lp.coeFn_smul I (mulOp a ⟨mulEvolution ha t f, hm⟩), coeFn_mulOp a ⟨mulEvolution ha t f, hm⟩,
      coeFn_mulEvolution ha t f] with x h1 h2 h3 h4
    rw [h1, Pi.neg_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]
    ring
  set G : ℝ → α → ℂ := fun h x =>
    h⁻¹ • (phase (a x) (t + h) * f x - phase (a x) t * f x) - -(I * (a x * phase (a x) t)) * f x
  set w : ℝ → Lp ℂ 2 μ := fun h => h⁻¹ • (mulEvolution ha (t + h) f - mulEvolution ha t f) - v
  have hw (h : ℝ) : w h =ᵐ[μ] G h := by
    filter_upwards [Lp.coeFn_sub (h⁻¹ • (mulEvolution ha (t + h) f - mulEvolution ha t f)) v,
      Lp.coeFn_smul h⁻¹ (mulEvolution ha (t + h) f - mulEvolution ha t f),
      Lp.coeFn_sub (mulEvolution ha (t + h) f) (mulEvolution ha t f),
      coeFn_mulEvolution ha (t + h) f, coeFn_mulEvolution ha t f, hv] with x h1 h2 h3 h4 h5 h6
    simp only [w, G]
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, Pi.sub_apply, h4, h5, h6]
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  change Tendsto (fun h => ‖w h‖) _ _
  have hsum : Integrable (fun x => 4 * ‖(a x : ℂ) * f x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).const_mul 4
  have hsq : Tendsto (fun h => ‖w h‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simp only [norm_sq_eq_integral]
    have key : Tendsto (fun h => ∫ x, ‖G h x‖ ^ 2 ∂μ) (𝓝[≠] 0) (𝓝 (∫ _, (0 : ℝ) ∂μ)) := by
      refine tendsto_integral_filter_of_dominated_convergence _
        (Eventually.of_forall fun h => ((Lp.aestronglyMeasurable (w h)).congr (hw h)).norm.pow 2)
        ?_ hsum (ae_of_all _ fun x => ?_)
      · filter_upwards [self_mem_nhdsWithin] with h (hh : h ≠ 0)
        refine ae_of_all _ fun x => ?_
        simp only [G]
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), phase_add]
        have he : h⁻¹ • (phase (a x) t * phase (a x) h * f x - phase (a x) t * f x) -
            -(I * (a x * phase (a x) t)) * f x =
            phase (a x) t * f x * (h⁻¹ • (phase (a x) h - 1) + I * a x) := by
          simp only [real_smul]
          ring
        have hb : ‖h⁻¹ • (phase (a x) h - 1)‖ ≤ |a x| := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
          calc |h|⁻¹ * ‖phase (a x) h - 1‖ ≤ |h|⁻¹ * (|a x| * |h|) :=
                mul_le_mul_of_nonneg_left (norm_phase_sub_one_le _ _) (by positivity)
            _ = |a x| := by field_simp [abs_ne_zero.2 hh]
        have hn : ‖h⁻¹ • (phase (a x) h - 1) + I * a x‖ ≤ 2 * |a x| := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]
          linarith
        rw [he, norm_mul, norm_mul, norm_phase, one_mul, norm_mul, norm_real, Real.norm_eq_abs]
        calc (‖f x‖ * ‖h⁻¹ • (phase (a x) h - 1) + I * a x‖) ^ 2 ≤ (‖f x‖ * (2 * |a x|)) ^ 2 :=
              pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hn (norm_nonneg _)) 2
          _ = 4 * (|a x| * ‖f x‖) ^ 2 := by ring
      · -- Each value converges, since `s ↦ e^{-i a x s} f x` is differentiable.
        have hd := hasDerivAt_iff_tendsto_slope_zero.1
          ((hasDerivAt_phase (a x) t).mul_const (f x))
        exact ((tendsto_sub_nhds_zero_iff.2 hd).norm.pow 2).trans (le_of_eq (by simp))
    rw [integral_zero] at key
    refine key.congr' ?_
    filter_upwards with h
    exact integral_congr_ae ((hw h).mono fun x hx => by simp only [hx])
  have := hsq.sqrt
  rw [Real.sqrt_zero] at this
  exact this.congr fun h => Real.sqrt_sq (norm_nonneg _)

/-- Off the domain of `A = mulOp a`, the orbit `t ↦ U t f` is differentiable nowhere: along a
sequence of slopes converging a.e., a derivative `y` would equal `-i a (U t f)` a.e., and
`y ∈ L²` would put `f` in the domain. -/
theorem not_differentiableAt_mulEvolution {f : Lp ℂ 2 μ} (hf : f ∉ mulDomain a) (t : ℝ) :
    ¬ DifferentiableAt ℝ (fun s => mulEvolution ha s f) t := by
  intro hd
  apply hf
  set y := deriv (fun s => mulEvolution ha s f) t
  set hs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs0 : Tendsto hs atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ),
      Eventually.of_forall fun n => (one_div_pos.2 (Nat.cast_add_one_pos n)).ne'⟩
  set S : ℕ → Lp ℂ 2 μ := fun n =>
    (hs n)⁻¹ • (mulEvolution ha (t + hs n) f - mulEvolution ha t f)
  have hS : Tendsto S atTop (𝓝 y) :=
    (hasDerivAt_iff_tendsto_slope_zero.1 hd.hasDerivAt).comp hs0
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hS).exists_seq_tendsto_ae
  have hSe : ∀ᵐ x ∂μ, ∀ n, S n x =
      (hs n)⁻¹ • (phase (a x) (t + hs n) * f x - phase (a x) t * f x) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_smul (hs n)⁻¹ (mulEvolution ha (t + hs n) f - mulEvolution ha t f),
      Lp.coeFn_sub (mulEvolution ha (t + hs n) f) (mulEvolution ha t f),
      coeFn_mulEvolution ha (t + hs n) f, coeFn_mulEvolution ha t f] with x h1 h2 h3 h4
    simp only [S]
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4]
  have hy : ∀ᵐ x ∂μ, y x = -(I * (a x * phase (a x) t)) * f x := by
    filter_upwards [hae, hSe] with x h1 h2
    have hd := (hasDerivAt_iff_tendsto_slope_zero.1
      ((hasDerivAt_phase (a x) t).mul_const (f x))).comp (hs0.comp hns.tendsto_atTop)
    refine tendsto_nhds_unique h1 (hd.congr fun i => ?_)
    simp only [Function.comp_apply, h2]
  rw [mem_mulDomain]
  refine MemLp.congr_norm (Lp.memLp y) ((Complex.continuous_ofReal.measurable.comp
    ha).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) ?_
  filter_upwards [hy] with x hx
  rw [hx, norm_mul, norm_neg, norm_mul, norm_I, one_mul, norm_mul, norm_phase, mul_one,
    norm_mul]

/-- The Schrödinger equation for `A = mulOp a` holds along the orbit of `f` exactly when `f`
lies in the domain of `A`. -/
theorem differentiableAt_mulEvolution_iff {f : Lp ℂ 2 μ} (t : ℝ) :
    DifferentiableAt ℝ (fun s => mulEvolution ha s f) t ↔ f ∈ mulDomain a :=
  ⟨fun hd => by_contra fun hf => not_differentiableAt_mulEvolution ha hf t hd,
    fun hf => (hasDerivAt_mulEvolution ha hf t).differentiableAt⟩

end MeasureTheory.L2
