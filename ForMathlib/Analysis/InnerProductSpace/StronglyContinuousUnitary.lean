/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Strongly continuous families of unitaries

If `t ↦ U t x` is continuous for every `x` and every `U t` is unitary, then so is
`t ↦ (U t)† x`: `‖U t† x - U s† x‖ = ‖x - U t (U s† x)‖`, which tends to `‖x - U s (U s† x)‖ = 0`.

## Main results

* `ContinuousLinearMap.continuous_star_apply_of_mem_unitary`
-/

open Filter Topology

public section

namespace ContinuousLinearMap

variable {𝕜 E X : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [TopologicalSpace X]

/-- The adjoints of a strongly continuous family of unitaries are strongly continuous. -/
theorem continuous_star_apply_of_mem_unitary {U : X → E →L[𝕜] E}
    (hU : ∀ t, U t ∈ unitary (E →L[𝕜] E)) (hc : ∀ x, Continuous (U · x)) (x : E) :
    Continuous fun t => star (U t) x := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h : Tendsto (fun t => ‖x - U t (star (U t₀) x)‖) (𝓝 t₀) (𝓝 ‖x - U t₀ (star (U t₀) x)‖) :=
    (continuous_const.sub (hc _)).norm.tendsto t₀
  have h₀ : x - U t₀ (star (U t₀) x) = 0 := by
    change x - (U t₀ * star (U t₀)) x = 0
    rw [(Unitary.mem_iff.mp (hU t₀)).2]
    exact sub_self x
  rw [h₀, norm_zero] at h
  refine h.congr fun t => ?_
  rw [← norm_map_of_mem_unitary (hU t) (star (U t) x - star (U t₀) x), map_sub]
  congr 2
  change x = (U t * star (U t)) x
  rw [(Unitary.mem_iff.mp (hU t)).2]
  rfl

end ContinuousLinearMap
