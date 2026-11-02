/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Multilinear maps on an orthonormal basis

A continuous multilinear map on copies of a finite-dimensional real inner product space is
controlled by its values on tuples of vectors of an orthonormal basis.

## Main results

* `ContinuousMultilinearMap.norm_le_sum_orthonormalBasis`: `‖f‖ ≤ ∑ᵣ ‖f (b ∘ r)‖`, the sum
  running over all tuples `r` of basis indices.
-/

@[expose] public section

namespace ContinuousMultilinearMap

variable {ι V G : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A continuous multilinear map is bounded by the sum of its values on tuples of vectors of an
orthonormal basis. -/
theorem norm_le_sum_orthonormalBasis {m : ℕ} (b : OrthonormalBasis ι ℝ V)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin m => V) G) :
    ‖f‖ ≤ ∑ r : Fin m → ι, ‖f (fun j => b (r j))‖ := by
  refine f.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun j => ∑ i, inner ℝ (b i) (v j) • b i := funext fun j => (b.sum_repr' (v j)).symm
  rw [hv, f.map_sum]
  simp only [map_smul_univ]
  calc ‖∑ r : Fin m → ι, (∏ j, inner ℝ (b (r j)) (v j)) • f (fun j => b (r j))‖
      ≤ ∑ r : Fin m → ι, ‖(∏ j, inner ℝ (b (r j)) (v j)) • f (fun j => b (r j))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r : Fin m → ι, (∏ j, ‖v j‖) * ‖f (fun j => b (r j))‖ := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [norm_smul, norm_prod]
        gcongr with j
        simpa [b.orthonormal.1 (r j)] using norm_inner_le_norm (𝕜 := ℝ) (b (r j)) (v j)
    _ = (∑ r : Fin m → ι, ‖f (fun j => b (r j))‖) * ∏ j, ‖∑ i, inner ℝ (b i) (v j) • b i‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_comm]
        congr 1
        exact Finset.prod_congr rfl fun j _ => by rw [b.sum_repr' (v j)]

end ContinuousMultilinearMap
