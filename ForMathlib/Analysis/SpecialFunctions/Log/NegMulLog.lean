/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Subadditivity of `x ↦ -x log x`

## Main statements

* `Real.negMulLog_add_le`: `negMulLog (x + y) ≤ negMulLog x + negMulLog y` for `x, y ≥ 0`.
-/

public section

namespace Real

lemma negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  rcases hy.eq_or_lt with rfl | hy'
  · simp
  have h1 : log x ≤ log (x + y) := log_le_log hx' (by linarith)
  have h2 : log y ≤ log (x + y) := log_le_log hy' (by linarith)
  simp only [negMulLog]
  nlinarith [mul_le_mul_of_nonneg_left h1 hx, mul_le_mul_of_nonneg_left h2 hy]

end Real
