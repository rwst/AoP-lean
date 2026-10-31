/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Spans of finite sets as double orthogonal complements

The span of a finite set is finite-dimensional, hence complete, so it is its own double
orthogonal complement, in any inner product space.

## Main results

* `Submodule.mem_span_of_forall_inner_eq_zero`: a vector orthogonal to every vector that is
  orthogonal to a finite set lies in the span of that set.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A vector orthogonal to every vector that is orthogonal to a finite set lies in the span of
that set. -/
theorem mem_span_of_forall_inner_eq_zero {s : Set E} (hs : s.Finite) {v : E}
    (h : ∀ x, (∀ w ∈ s, ⟪w, x⟫_𝕜 = 0) → ⟪v, x⟫_𝕜 = 0) : v ∈ span 𝕜 s := by
  have := FiniteDimensional.span_of_finite 𝕜 hs
  rw [← (span 𝕜 s).orthogonal_orthogonal, mem_orthogonal']
  exact fun u hu => h u fun w hw => inner_right_of_mem_orthogonal (subset_span hw) hu

end Submodule
