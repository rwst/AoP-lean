/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Symmetric extensions and closed operators

Results on partially defined operators used to identify an operator sum `S + T` with a given
self-adjoint operator.

## Main results

* `IsSelfAdjoint.isFormalAdjoint`: a self-adjoint operator is symmetric;
* `LinearPMap.IsFormalAdjoint.add`: the sum of two symmetric operators, on the intersection of
  their domains, is symmetric;
* `LinearPMap.eq_of_le_of_isFormalAdjoint`: a self-adjoint operator has no proper symmetric
  extension;
* `LinearPMap.IsClosed.exists_mem_domain_of_hasSum`: if `∑ xᵢ = y` and `∑ T xᵢ = z` for a closed
  operator `T`, then `y ∈ D(T)` and `T y = z`.
-/

open scoped InnerProductSpace

@[expose] public section

namespace LinearPMap

section InnerProduct

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A self-adjoint operator is symmetric. -/
theorem _root_.IsSelfAdjoint.isFormalAdjoint [CompleteSpace E] {A : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) : A.IsFormalAdjoint A := by
  have h := adjoint_isFormalAdjoint hA.dense_domain
  rwa [isSelfAdjoint_def.mp hA] at h

/-- The sum of two symmetric operators, on the intersection of their domains, is symmetric. -/
theorem IsFormalAdjoint.add {S T : E →ₗ.[𝕜] E} (hS : S.IsFormalAdjoint S)
    (hT : T.IsFormalAdjoint T) : (S + T).IsFormalAdjoint (S + T) := fun x y => by
  rw [add_apply, add_apply, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) (hS ⟨x, x.2.1⟩ ⟨y, y.2.1⟩) (hT ⟨x, x.2.2⟩ ⟨y, y.2.2⟩)

/-- A self-adjoint operator has no proper symmetric extension: if `A ≤ S` with `A` self-adjoint
and `S` symmetric, then `A = S`. -/
theorem eq_of_le_of_isFormalAdjoint [CompleteSpace E] {A S : E →ₗ.[𝕜] E}
    (hA : IsSelfAdjoint A) (hle : A ≤ S) (hS : S.IsFormalAdjoint S) : A = S := by
  -- `D(S) ⊆ D(A†) = D(A)`, tested against `A ≤ S`.
  refine eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun x hx => ?_)
  rw [← isSelfAdjoint_def.mp hA]
  refine mem_adjoint_domain_of_exists _ ⟨S ⟨x, hx⟩, fun y => ?_⟩
  rw [hle.2 (y := ⟨y, hle.1 y.2⟩) rfl]
  exact hS ⟨x, hx⟩ ⟨y, hle.1 y.2⟩

end InnerProduct

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A closed operator commutes with summation: if `∑ xᵢ = y` and `∑ T xᵢ = z`, then `y ∈ D(T)`
and `T y = z`. -/
theorem IsClosed.exists_mem_domain_of_hasSum {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) {ι : Type*}
    {x : ι → T.domain} {y : E} {z : F} (hx : HasSum (fun i => (x i : E)) y)
    (hz : HasSum (fun i => T (x i)) z) : ∃ hy : y ∈ T.domain, T ⟨y, hy⟩ = z := by
  have hmem : (y, z) ∈ T.graph := by
    refine IsClosed.mem_of_tendsto hT (hx.prodMk hz) (Filter.Eventually.of_forall fun s => ?_)
    exact Submodule.sum_mem _ fun i _ => T.mem_graph (x i)
  obtain ⟨w, h1, h2⟩ := (mem_graph_iff T).mp hmem
  subst h1
  exact ⟨w.2, h2⟩

end LinearPMap
