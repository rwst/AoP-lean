/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Weighted sums of coordinates on `lp` are lower semicontinuous

For weights `w i ≥ 0`, the map `f ↦ ∑ wᵢ ‖fᵢ‖^q` from `lp E p` to `[0, ∞]` is lower
semicontinuous, being a sum of nonnegative continuous functions. For `p = q = 2` this is the
quadratic form of a positive diagonal operator, extended by `∞` off its form domain.

## Main results

* `lp.lowerSemicontinuous_tsum_mul_enorm_pow`
-/

@[expose] public section

open scoped ENNReal NNReal

namespace lp

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- `f ↦ ∑ wᵢ ‖fᵢ‖ₑ^q` is lower semicontinuous on `lp E p`. -/
theorem lowerSemicontinuous_tsum_mul_enorm_pow (w : ι → ℝ≥0) (q : ℕ) :
    LowerSemicontinuous fun f : lp E p => ∑' i, (w i : ℝ≥0∞) * ‖f i‖ₑ ^ q :=
  lowerSemicontinuous_tsum fun i =>
    ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
      ((ENNReal.continuous_pow q).comp
        (continuous_enorm.comp (lipschitzWith_one_eval p i).continuous))).lowerSemicontinuous

end lp
