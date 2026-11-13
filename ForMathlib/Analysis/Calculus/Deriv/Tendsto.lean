/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Convergent functions with convergent derivatives

If `f : ℝ → F` converges at `+∞` and its derivative converges to `c`, then `c = 0`
(`eq_zero_of_tendsto_of_hasDerivAt`). By the mean value inequality, `f (t + 1) - f t` is close to
`c` for large `t`, and it tends to `0` because `f` converges.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `f` converges at `+∞` and `f'` converges to `c`, then `c = 0`. -/
theorem eq_zero_of_tendsto_of_hasDerivAt {f g : ℝ → F} {a c : F}
    (hf : ∀ᶠ t in atTop, HasDerivAt f (g t) t) (hfa : Tendsto f atTop (𝓝 a))
    (hgc : Tendsto g atTop (𝓝 c)) : c = 0 := by
  have h0 : Tendsto (fun t => f (t + 1) - f t) atTop (𝓝 0) := by
    simpa using (hfa.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).sub hfa
  have hc : Tendsto (fun t => f (t + 1) - f t) atTop (𝓝 c) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hf
    obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp
      ((Metric.tendsto_nhds.mp hgc) (ε / 2) (half_pos hε))
    filter_upwards [eventually_ge_atTop (max T₁ T₂)] with t ht
    have hd : ∀ s ∈ Icc t (t + 1),
        HasDerivWithinAt (fun s => f s - s • c) (g s - c) (Icc t (t + 1)) s := fun s hs => by
      have := (hT₁ s ((le_max_left _ _).trans (ht.trans hs.1))).sub
        ((hasDerivAt_id' s).smul_const c)
      rw [one_smul] at this
      exact this.hasDerivWithinAt
    have hb : ∀ s ∈ Ico t (t + 1), ‖g s - c‖ ≤ ε / 2 := fun s hs =>
      (dist_eq_norm (g s) c ▸ hT₂ s ((le_max_right _ _).trans (ht.trans hs.1))).le
    have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb (t + 1)
      ⟨by linarith, le_rfl⟩
    rw [dist_eq_norm]
    calc ‖f (t + 1) - f t - c‖ = ‖f (t + 1) - (t + 1) • c - (f t - t • c)‖ := by
          congr 1
          rw [add_smul, one_smul]
          abel
      _ ≤ ε / 2 * (t + 1 - t) := h
      _ < ε := by linarith
  exact tendsto_nhds_unique hc h0
