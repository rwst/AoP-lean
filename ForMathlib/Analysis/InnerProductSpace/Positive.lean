/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The null vectors of a positive operator

If `T` is positive and `re ⟪T x, x⟫ = 0`, then `T x = 0`. This is Cauchy–Schwarz for the positive
semidefinite form `(x, y) ↦ ⟪T x, y⟫`, proved directly: the quadratic
`s ↦ re ⟪T (x + s T x), x + s T x⟫ = 2 s ‖T x‖² + s² re ⟪T (T x), T x⟫` is nonnegative and vanishes
at `s = 0`, so its linear coefficient `‖T x‖²` is zero.

## Main results

* `LinearMap.IsPositive.apply_eq_zero_of_re_inner_eq_zero`
-/

@[expose] public section

open RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-- A positive operator kills every vector on which its quadratic form vanishes. -/
theorem IsPositive.apply_eq_zero_of_re_inner_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsPositive) {x : E}
    (hx : re ⟪T x, x⟫ = 0) : T x = 0 := by
  set a := re ⟪T (T x), T x⟫
  have ha : 0 ≤ a := hT.re_inner_nonneg_left _
  have h : ∀ s : ℝ, 0 ≤ 2 * s * ‖T x‖ ^ 2 + s ^ 2 * a := fun s => by
    have h := hT.re_inner_nonneg_left (x + (s : 𝕜) • T x)
    have hs : ⟪T (T x), x⟫ = ⟪T x, T x⟫ := hT.isSymmetric (T x) x
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, conj_ofReal, hs, hx, re_ofReal_mul, inner_self_eq_norm_sq] at h
    nlinarith
  have h' := h (-‖T x‖ ^ 2 / (a + 1))
  rw [div_pow, neg_sq] at h'
  have hN : ‖T x‖ ^ 2 * ‖T x‖ ^ 2 * (a + 2) ≤ 0 := by
    have := mul_nonneg (le_of_lt (by positivity : (0 : ℝ) < (a + 1) ^ 2)) h'
    field_simp at this
    nlinarith
  have hN0 : ‖T x‖ ^ 2 * ‖T x‖ ^ 2 ≤ 0 := by nlinarith [mul_nonneg (sq_nonneg ‖T x‖) ha]
  simpa using le_antisymm hN0 (by positivity)

end LinearMap
