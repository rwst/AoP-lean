/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The norm of a positive operator is at most its trace

In an eigenbasis `T x = ∑ᵢ λᵢ ⟪eᵢ, x⟫ eᵢ` with `0 ≤ λᵢ ≤ ∑ⱼ λⱼ = re tr T`, so
`‖T x‖² = ∑ᵢ λᵢ² ‖⟪eᵢ, x⟫‖² ≤ (re tr T)² ‖x‖²`.

## Main results

* `LinearMap.IsPositive.norm_apply_le_re_trace_mul`
* `ContinuousLinearMap.norm_le_re_trace`
-/

@[expose] public section

open RCLike
open scoped ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-- A positive operator stretches no vector by more than its trace. -/
theorem IsPositive.norm_apply_le_re_trace_mul {T : E →ₗ[𝕜] E} (hT : T.IsPositive) (x : E) :
    ‖T x‖ ≤ re (T.trace 𝕜 E) * ‖x‖ := by
  set b := hT.isSymmetric.eigenvectorBasis rfl
  set μ := hT.isSymmetric.eigenvalues rfl
  have hμ : ∀ i, 0 ≤ μ i := hT.nonneg_eigenvalues rfl
  have htr : re (T.trace 𝕜 E) = ∑ i, μ i := hT.isSymmetric.re_trace_eq_sum_eigenvalues rfl
  have hle : ∀ i, μ i ≤ re (T.trace 𝕜 E) := fun i => htr ▸
    Finset.single_le_sum (fun j _ => hμ j) (Finset.mem_univ i)
  have hinner : ∀ i, ‖⟪b i, T x⟫‖ = μ i * ‖⟪b i, x⟫‖ := fun i => by
    rw [← hT.isSymmetric, hT.isSymmetric.apply_eigenvectorBasis, inner_smul_left, norm_mul,
      conj_ofReal, norm_ofReal, abs_of_nonneg (hμ i)]
  have h0 : 0 ≤ re (T.trace 𝕜 E) := htr ▸ Finset.sum_nonneg fun i _ => hμ i
  refine le_of_sq_le_sq ?_ (by positivity)
  rw [← b.sum_sq_norm_inner_right (T x), mul_pow, ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [hinner, mul_pow]
  gcongr
  · exact hμ i
  · exact hle i

end LinearMap

namespace ContinuousLinearMap

/-- The operator norm of a positive operator is at most its trace. -/
theorem norm_le_re_trace {T : E →L[𝕜] E} (hT : (T : E →ₗ[𝕜] E).IsPositive) :
    ‖T‖ ≤ re (LinearMap.trace 𝕜 E T) :=
  T.opNorm_le_bound (RCLike.nonneg_iff.mp hT.trace_nonneg).1 hT.norm_apply_le_re_trace_mul

end ContinuousLinearMap
