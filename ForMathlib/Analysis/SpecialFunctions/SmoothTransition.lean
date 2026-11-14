/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth diffeomorphisms of `ℝ` that grow as fast as prescribed

For every sequence `c : ℕ → ℝ` there is a smooth diffeomorphism `e` of `ℝ` with
`|e x| ≥ c k` whenever `|x| ≥ k + 1`. It is `x + ∑ₖ cₖ (σ(x - k) - σ(-x - k))` for the smooth
transition function `σ` and `cₖ ≥ 0`: each term is a smooth monotone step that vanishes on
`[-k, k]`, so the sum is locally finite.

## Main results

* `Real.staircase`: the function above;
* `Real.exists_contDiff_homeomorph_le_abs`: the diffeomorphism.
-/

open Set Filter Topology
open scoped ContDiff

@[expose] public noncomputable section

namespace Real

/-- The odd smooth step `c (σ(x - k) - σ(-x - k))`: zero on `[-k, k]`, equal to `c` for
`x ≥ k + 1` and to `-c` for `x ≤ -(k + 1)`. -/
def stairStep (c : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  c * (smoothTransition (x - k) - smoothTransition (-x - k))

variable {c : ℝ} {k : ℕ} {x : ℝ}

lemma stairStep_eq_zero (hx : |x| ≤ k) : stairStep c k x = 0 := by
  have h1 : x - k ≤ 0 := by linarith [le_abs_self x]
  have h2 : -x - k ≤ 0 := by linarith [neg_abs_le x]
  simp [stairStep, smoothTransition.zero_of_nonpos h1, smoothTransition.zero_of_nonpos h2]

lemma contDiff_stairStep {n : ℕ∞} : ContDiff ℝ n (stairStep c k) := by
  unfold stairStep
  have h1 : ContDiff ℝ n fun x : ℝ => smoothTransition (x - k) :=
    smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have h2 : ContDiff ℝ n fun x : ℝ => smoothTransition (-x - k) :=
    smoothTransition.contDiff.comp (contDiff_id.neg.sub contDiff_const)
  exact contDiff_const.mul (h1.sub h2)

lemma monotone_stairStep (hc : 0 ≤ c) : Monotone (stairStep c k) := by
  intro x y hxy
  unfold stairStep
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h1 := smoothTransition.monotone (show x - k ≤ y - k by linarith)
  have h2 := smoothTransition.monotone (show -y - k ≤ -x - k by linarith)
  linarith

lemma stairStep_nonneg (hc : 0 ≤ c) (hx : 0 ≤ x) : 0 ≤ stairStep c k x := by
  simpa [stairStep_eq_zero (show |(0 : ℝ)| ≤ k by simp)] using monotone_stairStep (k := k) hc hx

lemma stairStep_nonpos (hc : 0 ≤ c) (hx : x ≤ 0) : stairStep c k x ≤ 0 := by
  simpa [stairStep_eq_zero (show |(0 : ℝ)| ≤ k by simp)] using monotone_stairStep (k := k) hc hx

lemma stairStep_of_le (hx : (k : ℝ) + 1 ≤ x) : stairStep c k x = c := by
  have h1 : 1 ≤ x - k := by linarith
  have h2 : -x - k ≤ 0 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  simp [stairStep, smoothTransition.one_of_one_le h1, smoothTransition.zero_of_nonpos h2]

lemma stairStep_of_le_neg (hx : x ≤ -((k : ℝ) + 1)) : stairStep c k x = -c := by
  have h1 : x - k ≤ 0 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h2 : 1 ≤ -x - k := by linarith
  simp [stairStep, smoothTransition.one_of_one_le h2, smoothTransition.zero_of_nonpos h1]

/-- The staircase `x + ∑ₖ cₖ (σ(x - k) - σ(-x - k))`. -/
def staircase (c : ℕ → ℝ) (x : ℝ) : ℝ := x + ∑' k, stairStep (c k) k x

variable {c : ℕ → ℝ}

/-- On `[-N, N]` the staircase is a finite sum. -/
lemma tsum_stairStep_eq_sum {N : ℕ} (hx : |x| ≤ N) :
    ∑' k, stairStep (c k) k x = ∑ k ∈ Finset.range N, stairStep (c k) k x :=
  tsum_eq_sum fun k hk => stairStep_eq_zero
    (hx.trans (by exact_mod_cast not_lt.1 (Finset.mem_range.not.1 hk)))

lemma contDiff_staircase {n : ℕ∞} : ContDiff ℝ n (staircase c) := by
  refine contDiff_iff_contDiffAt.2 fun x₀ => ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (|x₀| + 1)
  have hfin : ContDiff ℝ n fun x => x + ∑ k ∈ Finset.range N, stairStep (c k) k x :=
    contDiff_id.add (ContDiff.sum fun k _ => contDiff_stairStep)
  refine hfin.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
  have : |x| ≤ N := by
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have := abs_sub_abs_le_abs_sub x x₀
    linarith [abs_nonneg x₀]
  rw [staircase, tsum_stairStep_eq_sum this]

lemma monotone_tsum_stairStep (hc : ∀ k, 0 ≤ c k) :
    Monotone fun x => ∑' k, stairStep (c k) k x := by
  intro x y hxy
  obtain ⟨N, hN⟩ := exists_nat_ge (max |x| |y|)
  have hx : |x| ≤ N := by linarith [le_max_left |x| |y|]
  have hy : |y| ≤ N := by linarith [le_max_right |x| |y|]
  simp only
  rw [tsum_stairStep_eq_sum hx, tsum_stairStep_eq_sum hy]
  exact Finset.sum_le_sum fun k _ => monotone_stairStep (hc k) hxy

lemma strictMono_staircase (hc : ∀ k, 0 ≤ c k) : StrictMono (staircase c) :=
  fun _ _ hxy => add_lt_add_of_lt_of_le hxy (monotone_tsum_stairStep hc hxy.le)

lemma tsum_stairStep_nonneg (hc : ∀ k, 0 ≤ c k) (hx : 0 ≤ x) :
    0 ≤ ∑' k, stairStep (c k) k x :=
  tsum_nonneg fun k => stairStep_nonneg (hc k) hx

lemma tsum_stairStep_nonpos (hc : ∀ k, 0 ≤ c k) (hx : x ≤ 0) :
    ∑' k, stairStep (c k) k x ≤ 0 :=
  tsum_nonpos fun k => stairStep_nonpos (hc k) hx

lemma le_staircase (hc : ∀ k, 0 ≤ c k) (hx : (k : ℝ) + 1 ≤ x) : c k ≤ staircase c x := by
  obtain ⟨N, hN⟩ := exists_nat_ge (x + k + 1)
  have hx0 : 0 ≤ x := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hxN : |x| ≤ N := by rw [abs_of_nonneg hx0]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hkN : k ∈ Finset.range N := by
    rw [Finset.mem_range]
    have : (k : ℝ) < N := by linarith
    exact_mod_cast this
  rw [staircase, tsum_stairStep_eq_sum hxN]
  have := Finset.single_le_sum (f := fun j => stairStep (c j) j x)
    (fun j _ => stairStep_nonneg (hc j) hx0) hkN
  rw [stairStep_of_le hx] at this
  linarith

lemma staircase_le_neg (hc : ∀ k, 0 ≤ c k) (hx : x ≤ -((k : ℝ) + 1)) : staircase c x ≤ -c k := by
  obtain ⟨N, hN⟩ := exists_nat_ge (-x + k + 1)
  have hx0 : x ≤ 0 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hxN : |x| ≤ N := by rw [abs_of_nonpos hx0]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hkN : k ∈ Finset.range N := by
    rw [Finset.mem_range]
    have : (k : ℝ) < N := by linarith
    exact_mod_cast this
  rw [staircase, tsum_stairStep_eq_sum hxN]
  have := Finset.single_le_sum (f := fun j => -stairStep (c j) j x)
    (fun j _ => neg_nonneg.2 (stairStep_nonpos (hc j) hx0)) hkN
  rw [Finset.sum_neg_distrib, stairStep_of_le_neg hx] at this
  linarith

lemma surjective_staircase (hc : ∀ k, 0 ≤ c k) : Function.Surjective (staircase c) := by
  refine (contDiff_staircase (c := c) (n := 0)).continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact le_add_of_nonneg_right (tsum_stairStep_nonneg hc hx)
  · refine tendsto_atBot_mono' atBot ?_ tendsto_id
    filter_upwards [eventually_le_atBot 0] with x hx
    exact add_le_of_nonpos_right (tsum_stairStep_nonpos hc hx)

/-- **Smooth diffeomorphisms of `ℝ` grow as fast as prescribed.** For every `c : ℕ → ℝ` there
is a smooth diffeomorphism `e` of `ℝ`, with smooth inverse, such that `c k ≤ |e x|` whenever
`k + 1 ≤ |x|`. -/
theorem exists_contDiff_homeomorph_le_abs (c : ℕ → ℝ) :
    ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
      ∀ (k : ℕ) (x : ℝ), (k : ℝ) + 1 ≤ |x| → c k ≤ |e x| := by
  set c' : ℕ → ℝ := fun k => max (c k) 0
  have hc : ∀ k, 0 ≤ c' k := fun k => le_max_right _ _
  let o := (strictMono_staircase hc).orderIsoOfSurjective _ (surjective_staircase hc)
  let e : ℝ ≃ₜ ℝ := o.toHomeomorph
  have he : (e : ℝ → ℝ) = staircase c' := rfl
  have hS : Differentiable ℝ fun x => ∑' k, stairStep (c' k) k x := by
    have : Differentiable ℝ (staircase c') := contDiff_staircase (n := 1).differentiable one_ne_zero
    have h2 : (fun x => ∑' k, stairStep (c' k) k x) = fun x => staircase c' x - x := by
      ext x; simp [staircase]
    rw [h2]
    exact this.sub differentiable_id
  have hderiv (x : ℝ) : HasDerivAt e (1 + deriv (fun x => ∑' k, stairStep (c' k) k x) x) x := by
    rw [he]
    exact (hasDerivAt_id x).add (hS x).hasDerivAt
  have hpos (x : ℝ) : 1 + deriv (fun x => ∑' k, stairStep (c' k) k x) x ≠ 0 :=
    (lt_of_lt_of_le one_pos (le_add_of_nonneg_right
      (monotone_tsum_stairStep hc).deriv_nonneg)).ne'
  refine ⟨e, he ▸ contDiff_staircase, e.contDiff_symm_deriv hpos hderiv (he ▸ contDiff_staircase),
    fun k x hx => ?_⟩
  rw [he]
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx
    exact (le_max_left _ _).trans ((le_staircase hc hx).trans (le_abs_self _))
  · rw [abs_of_neg hx0] at hx
    exact (le_max_left _ _).trans ((le_neg.1 (staircase_le_neg hc (by linarith))).trans
      (neg_le_abs _))

end Real
