/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Infinite-dimensionality of `L²`

If a measure space contains infinitely many pairwise disjoint measurable sets of positive
finite measure, then `L²` is infinite-dimensional: the indicator functions of these sets are
nonzero and pairwise orthogonal.

## Main results

* `MeasureTheory.L2.not_finiteDimensional_of_disjoint`
* `MeasureTheory.L2.not_finiteDimensional_euclidean`: `L²(ℝⁿ⁺¹)` is infinite-dimensional.
-/

open Set
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace MeasureTheory.L2

/-- `L²(X, μ)` is infinite-dimensional if `X` has infinitely many pairwise disjoint sets of
positive finite measure. -/
theorem not_finiteDimensional_of_disjoint {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (A : ℕ → Set X) (hA : ∀ k, MeasurableSet (A k)) (hfin : ∀ k, μ (A k) ≠ ⊤)
    (hpos : ∀ k, μ (A k) ≠ 0) (hd : Pairwise (Function.onFun Disjoint A)) :
    ¬ FiniteDimensional ℂ (Lp ℂ 2 μ) := by
  intro hfd
  let f : ℕ → Lp ℂ 2 μ := fun k => indicatorConstLp 2 (hA k) (hfin k) (1 : ℂ)
  have hne : ∀ k, f k ≠ 0 := by
    intro k h
    have := congrArg norm h
    rw [norm_zero, norm_indicatorConstLp (by norm_num) (by norm_num)] at this
    simp only [norm_one, one_mul] at this
    have hr : 0 < μ.real (A k) := ENNReal.toReal_pos (hpos k) (hfin k)
    have : 0 < μ.real (A k) ^ (1 / (2 : ENNReal).toReal) := by positivity
    linarith
  have horth : Pairwise fun j k => ⟪f j, f k⟫_ℂ = 0 := by
    intro j k hjk
    rw [L2.inner_indicatorConstLp_one (hA j) (hfin j)]
    have hae : ∀ᵐ x ∂μ.restrict (A j), (f k : X → ℂ) x = 0 := by
      have h1 := ae_restrict_of_ae (s := A j) (indicatorConstLp_coeFn (p := 2) (hs := hA k)
        (hμs := hfin k) (c := (1 : ℂ)))
      filter_upwards [h1, ae_restrict_mem (hA j)] with x hx hxj
      rw [hx, indicator_of_notMem (fun hxk => (hd hjk).ne_of_mem hxj hxk rfl)]
    rw [integral_congr_ae hae, integral_zero]
  have hli := linearIndependent_of_ne_zero_of_inner_eq_zero hne horth
  have := hli.finite_of_isNoetherian
  exact not_finite ℕ

/-- `L²(ℝⁿ⁺¹)` is infinite-dimensional: take the balls of radius `1/2` around `k e₀`. -/
theorem not_finiteDimensional_euclidean (n : ℕ) :
    ¬ FiniteDimensional ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))) := by
  let e₀ : EuclideanSpace ℝ (Fin (n + 1)) := EuclideanSpace.single 0 1
  refine not_finiteDimensional_of_disjoint (fun k => Metric.ball ((k : ℝ) • e₀) (1 / 2))
    (fun _ => Metric.isOpen_ball.measurableSet) (fun _ => measure_ball_lt_top.ne)
    (fun _ => (Metric.measure_ball_pos _ _ (by norm_num)).ne') ?_
  intro j k hjk
  refine Metric.ball_disjoint_ball ?_
  have he : ‖e₀‖ = 1 := by simp [e₀]
  rw [dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hjk with h | h
  · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith
  · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith

instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- `L²(ℝⁿ)` is separable. -/
instance separableSpace_euclidean (n : ℕ) :
    TopologicalSpace.SeparableSpace (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :=
  inferInstance

end MeasureTheory.L2
