/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# `Matrix.toEuclideanLin` is multiplicative

## Main results

* `Matrix.toEuclideanLin_mul`: `toEuclideanLin (A * B) = toEuclideanLin A * toEuclideanLin B`.
-/

@[expose] public section

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

theorem toEuclideanLin_mul (A B : Matrix n n 𝕜) :
    toEuclideanLin (A * B) = toEuclideanLin A * toEuclideanLin B := by
  rw [← coe_toEuclideanCLM_eq_toEuclideanLin, map_mul]
  rfl

end Matrix
