/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Isometries of finite-dimensional inner product spaces are unitary

## Main results

* `ContinuousLinearMap.mem_unitary_iff_star_mul_self`: in finite dimension, a continuous linear
  endomorphism `U` is unitary as soon as `U† U = 1`.
-/

@[expose] public section

namespace ContinuousLinearMap

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H] [FiniteDimensional 𝕜 H]

theorem mem_unitary_iff_star_mul_self {U : H →L[𝕜] H} :
    U ∈ unitary (H →L[𝕜] H) ↔ star U * U = 1 := by
  refine ⟨fun h => (Unitary.mem_iff.mp h).1, fun h => Unitary.mem_iff.mpr ⟨h, ?_⟩⟩
  have h' : ((star U : H →L[𝕜] H) : H →ₗ[𝕜] H) * U = 1 := by
    rw [← toLinearMap_mul, h]; rfl
  apply coe_injective
  rw [toLinearMap_mul]
  exact mul_eq_one_comm.mp h'

alias ⟨_, mem_unitary_of_star_mul_self⟩ := mem_unitary_iff_star_mul_self

end ContinuousLinearMap
