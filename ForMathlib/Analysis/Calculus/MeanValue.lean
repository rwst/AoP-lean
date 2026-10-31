/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Functions with vanishing derivative on a half-line

A function that is continuous from the right at `a` and has derivative zero at every point of
`(a, ∞)` is constant on `[a, ∞)`. This is the form of uniqueness needed for evolution equations
that are only assumed to hold for positive times.

## Main results

* `eq_of_hasDerivAt_eq_zero_of_continuousWithinAt`
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function continuous from the right at `a`, with derivative zero on `(a, ∞)`, is constant on
`[a, ∞)`. -/
theorem eq_of_hasDerivAt_eq_zero_of_continuousWithinAt {f : ℝ → E} {a : ℝ}
    (hc : ContinuousWithinAt f (Ici a) a) (hd : ∀ t, a < t → HasDerivAt f 0 t) {t : ℝ}
    (ht : a ≤ t) : f t = f a := by
  rcases ht.eq_or_lt with rfl | ht
  · rfl
  have hconst : ∀ s ∈ Ioc a t, f t = f s := fun s hs =>
    constant_of_has_deriv_right_zero
      (fun x hx => (hd x (hs.1.trans_le hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (hs.1.trans_le hx.1)).hasDerivWithinAt) t ⟨hs.2, le_rfl⟩
  have h1 : Tendsto f (𝓝[>] a) (𝓝 (f a)) := (hc.mono Ioi_subset_Ici_self).tendsto
  have h2 : Tendsto f (𝓝[>] a) (𝓝 (f t)) :=
    tendsto_const_nhds.congr' (eventuallyEq_of_mem (Ioo_mem_nhdsGT ht) fun s hs =>
      hconst s ⟨hs.1, hs.2.le⟩)
  exact tendsto_nhds_unique h2 h1
