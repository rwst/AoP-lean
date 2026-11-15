/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Gluing translated bumps into a Schwartz function

Let `ρ ∈ 𝓢(E, F)` vanish outside the closed ball of radius `r < 1/2` about `0`, let `y : ℕ → E`
be a sequence of points at mutual distance at least `1`, and let `c : ℕ → ℝ` decay rapidly along
`y`: `|c j| (1 + ‖y j‖)^m` is bounded for every `m`. Then `∑ j, c j • ρ (· - y j)` is a Schwartz
function, equal to `c j • ρ (· - y j)` on the ball of radius `1/2` about `y j`. At every point at
most one term of the sum is non-zero, so no convergence argument is needed.

This is the test function used to show that a bound fails along a sequence running to infinity,
e.g. that a smooth multiplier of `𝓢` has temperate growth.

## Main results

* `SchwartzMap.exists_eqOn_ball_smul`: the glued Schwartz function;
* `SchwartzMap.exists_abs_inv_pow_mul_le`: coefficients that decay rapidly along any sequence;
* `SchwartzMap.exists_strictMono_pairwise_one_le`: a sequence whose norms tend to infinity has a
  subsequence of points at mutual distance at least `1`.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology ContDiff

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ρ : 𝓢(E, F)} {r : ℝ} {y : ℕ → E} {c : ℕ → ℝ}

private lemma smul_comp_sub_eq_zero (hsupp : tsupport ρ ⊆ closedBall 0 r) {x : E} {j : ℕ}
    (h : r < ‖x - y j‖) : c j • ρ (x - y j) = 0 := by
  have h0 : ρ (x - y j) = 0 := image_eq_zero_of_notMem_tsupport fun hm => by
    have := hsupp hm
    rw [mem_closedBall_zero_iff] at this
    linarith
  rw [h0, smul_zero]

/-- Near every point, at most one term of the glued sum is non-zero. -/
private lemma exists_eventually_forall_ne (hr : r < 1 / 2) (hsupp : tsupport ρ ⊆ closedBall 0 r)
    (hy : Pairwise fun i j => 1 ≤ ‖y i - y j‖) (x : E) :
    ∃ j, ∀ᶠ z in 𝓝 x, ∀ i ≠ j, c i • ρ (z - y i) = 0 := by
  by_cases h : ∃ j, x ∈ ball (y j) (1 / 2)
  · obtain ⟨j, hj⟩ := h
    refine ⟨j, mem_of_superset (isOpen_ball.mem_nhds hj) fun z hz i hi =>
      smul_comp_sub_eq_zero hsupp ?_⟩
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := hy hi
    have h2 : ‖y i - y j‖ ≤ ‖z - y j‖ + ‖z - y i‖ := by
      calc ‖y i - y j‖ = ‖(z - y j) - (z - y i)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith
  · push Not at h
    refine ⟨0, mem_of_superset (ball_mem_nhds x (by linarith : 0 < 1 / 2 - r)) fun z hz i _ =>
      smul_comp_sub_eq_zero hsupp ?_⟩
    rw [mem_ball, dist_eq_norm] at hz
    have h1 := h i
    rw [mem_ball, dist_eq_norm, not_lt] at h1
    have h2 : ‖x - y i‖ ≤ ‖z - y i‖ + ‖z - x‖ := by
      calc ‖x - y i‖ = ‖(z - y i) - (z - x)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith

private lemma contDiff_smul_comp_sub (j : ℕ) : ContDiff ℝ ∞ fun x => c j • ρ (x - y j) :=
  ((ρ.smooth ⊤).comp (ContDiff.sub contDiff_id contDiff_const)).const_smul (c j)

private lemma iteratedFDeriv_smul_comp_sub (n j : ℕ) (x : E) :
    iteratedFDeriv ℝ n (fun x => c j • ρ (x - y j)) x = c j • iteratedFDeriv ℝ n ρ (x - y j) := by
  have h : ContDiff ℝ n fun x => ρ (x - y j) :=
    (ρ.smooth n).comp (ContDiff.sub contDiff_id contDiff_const)
  rw [iteratedFDeriv_const_smul_apply' h.contDiffAt, iteratedFDeriv_comp_sub]

/-- The decay estimate for a single term, uniform in `j`. -/
private lemma norm_pow_mul_iteratedFDeriv_le (hr : r < 1 / 2)
    (hsupp : tsupport ρ ⊆ closedBall 0 r) {k : ℕ} {C : ℝ}
    (hC : ∀ j, |c j| * (1 + ‖y j‖) ^ k ≤ C) {n : ℕ} {S : ℝ}
    (hS : ∀ z, ‖iteratedFDeriv ℝ n ρ z‖ ≤ S) (j : ℕ) (x : E) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => c j • ρ (x - y j)) x‖ ≤ C * S := by
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have hC0 : 0 ≤ C := (by positivity : 0 ≤ |c j| * (1 + ‖y j‖) ^ k).trans (hC j)
  rw [iteratedFDeriv_smul_comp_sub, norm_smul, Real.norm_eq_abs]
  by_cases hx : ‖x - y j‖ ≤ r
  · have hxy : ‖x‖ ≤ 1 + ‖y j‖ := by
      have := norm_le_norm_add_norm_sub' x (y j)
      rw [norm_sub_rev] at this
      linarith [norm_sub_rev x (y j)]
    calc ‖x‖ ^ k * (|c j| * ‖iteratedFDeriv ℝ n ρ (x - y j)‖)
        ≤ (1 + ‖y j‖) ^ k * (|c j| * S) := by
          gcongr
          · exact hS _
      _ = (|c j| * (1 + ‖y j‖) ^ k) * S := by ring
      _ ≤ C * S := by gcongr; exact hC j
  · have : iteratedFDeriv ℝ n ρ (x - y j) = 0 := by
      by_contra hne
      have hm := hsupp (support_iteratedFDeriv_subset n hne)
      rw [mem_closedBall_zero_iff] at hm
      exact hx hm
    rw [this, norm_zero, mul_zero, mul_zero]
    positivity

/-- **Gluing translated bumps.** Let `ρ ∈ 𝓢(E, F)` vanish outside the closed ball of radius
`r < 1/2`, let the points `y j` be at mutual distance at least `1`, and let `c` decay rapidly along
`y`. Then some Schwartz function equals `c j • ρ (· - y j)` on the ball of radius `1/2` about
`y j`, for every `j`. -/
theorem exists_eqOn_ball_smul (hr : r < 1 / 2) (hsupp : tsupport ρ ⊆ closedBall 0 r)
    (hy : Pairwise fun i j => 1 ≤ ‖y i - y j‖)
    (hc : ∀ m : ℕ, ∃ C, ∀ j, |c j| * (1 + ‖y j‖) ^ m ≤ C) :
    ∃ f : 𝓢(E, F), ∀ j, EqOn f (fun x => c j • ρ (x - y j)) (ball (y j) (1 / 2)) := by
  set g : E → F := fun x => ∑' j, c j • ρ (x - y j)
  have hloc : ∀ x, ∃ j, g =ᶠ[𝓝 x] fun x => c j • ρ (x - y j) := fun x => by
    obtain ⟨j, hj⟩ := exists_eventually_forall_ne (c := c) hr hsupp hy x
    exact ⟨j, hj.mono fun z hz => tsum_eq_single j hz⟩
  have hsmooth : ContDiff ℝ ∞ g := contDiff_iff_contDiffAt.2 fun x => by
    obtain ⟨j, hj⟩ := hloc x
    exact (contDiff_smul_comp_sub j).contDiffAt.congr_of_eventuallyEq hj
  refine ⟨⟨g, hsmooth, fun k n => ?_⟩, fun j x hx => ?_⟩
  · obtain ⟨C, hC⟩ := hc k
    obtain ⟨S, -, hS⟩ := ρ.decay 0 n
    simp only [pow_zero, one_mul] at hS
    refine ⟨C * S, fun x => ?_⟩
    obtain ⟨j, hj⟩ := hloc x
    rw [(hj.iteratedFDeriv ℝ n).eq_of_nhds]
    exact norm_pow_mul_iteratedFDeriv_le hr hsupp hC hS j x
  · change ∑' i, c i • ρ (x - y i) = _
    refine tsum_eq_single j fun i hi => smul_comp_sub_eq_zero hsupp ?_
    rw [mem_ball, dist_eq_norm] at hx
    have h1 := hy hi
    have h2 : ‖y i - y j‖ ≤ ‖x - y j‖ + ‖x - y i‖ := by
      calc ‖y i - y j‖ = ‖(x - y j) - (x - y i)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith

omit [NormedSpace ℝ E] in
/-- The coefficients `(1 + ‖y j‖)^{-j}` decay rapidly along `y`, as `exists_eqOn_ball_smul`
requires. -/
theorem exists_abs_inv_pow_mul_le (y : ℕ → E) (m : ℕ) :
    ∃ C, ∀ j, |((1 + ‖y j‖) ^ j)⁻¹| * (1 + ‖y j‖) ^ m ≤ C := by
  refine ⟨1 + ∑ i ∈ Finset.range m, (1 + ‖y i‖) ^ m, fun j => ?_⟩
  have h1 : 1 ≤ 1 + ‖y j‖ := le_add_of_nonneg_right (norm_nonneg _)
  have hpos : 0 < (1 + ‖y j‖) ^ j := by positivity
  rw [abs_of_pos (inv_pos.2 hpos)]
  have hsum : 0 ≤ ∑ i ∈ Finset.range m, (1 + ‖y i‖) ^ m := by positivity
  rcases le_or_gt m j with hmj | hjm
  · calc ((1 + ‖y j‖) ^ j)⁻¹ * (1 + ‖y j‖) ^ m ≤ ((1 + ‖y j‖) ^ j)⁻¹ * (1 + ‖y j‖) ^ j :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hmj) (by positivity)
      _ = 1 := inv_mul_cancel₀ hpos.ne'
      _ ≤ _ := by linarith
  · calc ((1 + ‖y j‖) ^ j)⁻¹ * (1 + ‖y j‖) ^ m ≤ 1 * (1 + ‖y j‖) ^ m := by
          gcongr; exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
      _ ≤ ∑ i ∈ Finset.range m, (1 + ‖y i‖) ^ m := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun i => (1 + ‖y i‖) ^ m) (fun _ _ => by positivity)
            (Finset.mem_range.2 hjm)
      _ ≤ _ := by linarith

omit [NormedSpace ℝ E] in
/-- A sequence whose norms tend to infinity has a subsequence of points at mutual distance at
least `1`. -/
theorem exists_strictMono_pairwise_one_le {x : ℕ → E}
    (hx : Tendsto (fun j => ‖x j‖) atTop atTop) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ Pairwise fun i j => 1 ≤ ‖x (σ i) - x (σ j)‖ := by
  have : ∀ m, ∃ k, m < k ∧ ‖x m‖ + 1 ≤ ‖x k‖ := fun m =>
    ((eventually_gt_atTop m).and (hx.eventually_ge_atTop (‖x m‖ + 1))).exists
  choose next hnext using this
  set σ : ℕ → ℕ := fun j => next^[j] 0
  have hsucc : ∀ j, σ (j + 1) = next (σ j) := fun j => Function.iterate_succ_apply' _ _ _
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ fun j => by
    rw [hsucc]; exact (hnext _).1
  have hnorm : ∀ i j, i < j → ‖x (σ i)‖ + 1 ≤ ‖x (σ j)‖ := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => rw [hsucc]; exact (hnext _).2
    | succ j _ ih =>
      rw [hsucc]
      linarith [(hnext (σ j)).2]
  have hle : ∀ i j, i < j → 1 ≤ ‖x (σ i) - x (σ j)‖ := fun i j hij => by
    have := norm_sub_norm_le (x (σ j)) (x (σ i))
    rw [norm_sub_rev] at this
    linarith [hnorm i j hij]
  refine ⟨σ, hσ, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact hle i j h
  · rw [norm_sub_rev]; exact hle j i h

end SchwartzMap
