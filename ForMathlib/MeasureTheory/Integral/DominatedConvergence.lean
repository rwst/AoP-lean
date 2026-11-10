/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence with convergent dominating functions

The generalized dominated convergence theorem: if `Fₙ → f` a.e. and `|Fₙ| ≤ Hₙ`, where the
dominating functions themselves converge, `Hₙ → h` a.e. and in `L¹`, then `∫ Fₙ → ∫ f`.
Mathlib's `MeasureTheory.tendsto_integral_of_dominated_convergence` is the case `Hₙ = h`.

## Main statements

* `MeasureTheory.tendsto_integral_of_dominated_of_tendsto_L1`: the generalized dominated
  convergence theorem for real-valued functions.
-/

public section

open Filter Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The generalized dominated convergence theorem: if `Fₙ → f` a.e. and `|Fₙ| ≤ Hₙ` a.e., where
`Hₙ → h` a.e. and `∫ |Hₙ - h| → 0`, then `∫ Fₙ → ∫ f`. The proof clamps `Fₙ` to `[-|h|, |h|]`:
the clamped functions converge by dominated convergence, and the rest is at most `|Hₙ - h|`. -/
theorem tendsto_integral_of_dominated_of_tendsto_L1 {F H : ℕ → α → ℝ} {f h : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hH : ∀ n, Integrable (H n) μ)
    (hh : Integrable h μ) (h_bound : ∀ n, ∀ᵐ x ∂μ, |F n x| ≤ H n x)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (hH_lim : ∀ᵐ x ∂μ, Tendsto (fun n => H n x) atTop (𝓝 (h x)))
    (hH_L1 : Tendsto (fun n => ∫ x, |H n x - h x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  set C : ℕ → α → ℝ := fun n x => max (min (F n x) |h x|) (-|h x|) with hC_def
  have hCm : ∀ n, AEStronglyMeasurable (C n) μ := fun n =>
    ((hF n).inf hh.1.norm).sup hh.1.norm.neg
  have hC_le : ∀ n x, |C n x| ≤ |h x| := fun n x => abs_le.2
    ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith [abs_nonneg (h x)])⟩
  have hCi : ∀ n, Integrable (C n) μ := fun n =>
    hh.abs.mono' (hCm n) (ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hC_le n x))
  have hFi : ∀ n, Integrable (F n) μ := fun n =>
    (hH n).mono' (hF n) ((h_bound n).mono fun x hx => (Real.norm_eq_abs _).trans_le hx)
  -- The limit `f` is dominated by `h`, so clamping does not change it.
  have hf_le : ∀ᵐ x ∂μ, |f x| ≤ h x := by
    filter_upwards [h_lim, hH_lim, ae_all_iff.2 h_bound] with x hx hHx hbx
    exact le_of_tendsto_of_tendsto' hx.abs hHx hbx
  have h1 : Tendsto (fun n => ∫ x, C n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |h x|) hCm hh.abs
      (fun n => ae_of_all _ fun x => (Real.norm_eq_abs _).trans_le (hC_le n x)) ?_
    filter_upwards [h_lim, hf_le] with x hx hfx
    have hfx' : max (min (f x) |h x|) (-|h x|) = f x := by
      have := le_abs_self (h x)
      have := abs_le.1 (hfx.trans this)
      rw [min_eq_left this.2, max_eq_left this.1]
    rw [← hfx']
    exact (hx.min tendsto_const_nhds).max tendsto_const_nhds
  have h2 : Tendsto (fun n => ∫ x, (F n x - C n x) ∂μ) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (Eventually.of_forall fun n => ?_) hH_L1
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae ((hFi n).sub (hCi n)).norm
      ((hH n).sub hh).abs ?_)
    filter_upwards [h_bound n] with x hx
    have := abs_le.1 hx
    have := le_abs_self (h x)
    have := neg_abs_le (h x)
    have := le_abs_self (H n x - h x)
    rw [Real.norm_eq_abs, abs_le]
    simp only [hC_def]
    constructor
    · rcases le_total (F n x) |h x| with h3 | h3
      · rw [min_eq_left h3]
        rcases le_total (F n x) (-|h x|) with h4 | h4
        · rw [max_eq_right h4]; linarith
        · rw [max_eq_left h4]; linarith [abs_nonneg (H n x - h x)]
      · rw [min_eq_right h3, max_eq_left (by linarith [abs_nonneg (h x)])]
        linarith [abs_nonneg (H n x - h x)]
    · rcases le_total (F n x) |h x| with h3 | h3
      · rw [min_eq_left h3]
        rcases le_total (F n x) (-|h x|) with h4 | h4
        · rw [max_eq_right h4]; linarith [abs_nonneg (H n x - h x)]
        · rw [max_eq_left h4]; linarith [abs_nonneg (H n x - h x)]
      · rw [min_eq_right h3, max_eq_left (by linarith [abs_nonneg (h x)])]
        linarith
  have := h1.add h2
  rw [add_zero] at this
  refine this.congr fun n => ?_
  refine (integral_add (hCi n) ((hFi n).sub (hCi n))).symm.trans ?_
  exact integral_congr_ae (ae_of_all _ fun x => by simp)

end MeasureTheory
