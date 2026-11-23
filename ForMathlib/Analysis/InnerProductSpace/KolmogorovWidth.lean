/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Normed.Module.KolmogorovWidth
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Kolmogorov widths of weighted unit balls

Let `b` be a Hilbert basis of `E` indexed by `ℕ`, and `w` a monotone sequence of positive
weights. The weighted unit ball `b.weightedBall w` is the set of `x` with
`∑ i, (w i * ‖⟪b i, x⟫‖) ^ 2 ≤ 1`, the unit ball of `ℓ²(w)` in the coordinates of `b`. Its
`k`-th Kolmogorov width relative to the unit ball of `E` is `(w k)⁻¹`.

The lower bound is the dimension count behind all such results: a subspace spanned by `k`
vectors misses a unit vector of any `k + 1`-dimensional subspace, in the sense that some unit
vector there is orthogonal to it.

## Main definitions

* `HilbertBasis.weightedBall b w`: the unit ball of `ℓ²(w)` in the coordinates of `b`.

## Main statements

* `ofReal_le_kolmogorovWidth_of_orthonormal`: if `A` contains `r • y` for every `y` of norm at
  most one in the span of `k + 1` orthonormal vectors, its `k`-th width relative to the unit ball
  is at least `r`.
* `HilbertBasis.kolmogorovWidth_weightedBall`: the `k`-th width of `b.weightedBall w` relative to
  the unit ball is `(w k)⁻¹`.

## References

* A. Pinkus, *n-Widths in Approximation Theory*, Springer, 1985, Chapter IV.
-/

@[expose] public section

open Set Submodule Metric
open scoped Pointwise ENNReal NNReal InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Some unit vector in the span of `k + 1` orthonormal vectors is orthogonal to `k` given
vectors. -/
theorem Orthonormal.exists_norm_eq_one_inner_eq_zero {k : ℕ} {u : Fin (k + 1) → E}
    (hu : Orthonormal 𝕜 u) (v : Fin k → E) :
    ∃ y ∈ span 𝕜 (range u), ‖y‖ = 1 ∧ ∀ i, ⟪v i, y⟫ = 0 := by
  let f : (Fin (k + 1) → 𝕜) →ₗ[𝕜] Fin k → 𝕜 :=
    (LinearMap.pi fun i => innerₛₗ 𝕜 (v i)) ∘ₗ Fintype.linearCombination 𝕜 u
  have hf : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).mp hf
  set y₀ := ∑ j, a j • u j with hy₀
  have hy₀0 : y₀ ≠ 0 := fun h0 =>
    ha0 (funext (Fintype.linearIndependent_iff.mp hu.linearIndependent a h0))
  have hv : ∀ i, ⟪v i, y₀⟫ = 0 := fun i => by
    simpa [hy₀, inner_sum, inner_smul_right, f, Fintype.linearCombination_apply] using
      congr_fun (LinearMap.mem_ker.mp ha) i
  refine ⟨(‖y₀‖⁻¹ : 𝕜) • y₀, smul_mem _ _ (sum_mem fun j _ => smul_mem _ _
    (subset_span (mem_range_self j))), ?_, fun i => by simp [inner_smul_right, hv]⟩
  rw [norm_smul, norm_inv, RCLike.norm_ofReal, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy₀0)]

/-- **Lower bound for widths.** If `A` contains `r • y` for every `y` with `‖y‖ ≤ 1` in the
span of `k + 1` orthonormal vectors, then the `k`-th width of `A` relative to the unit ball is
at least `r`. -/
theorem ofReal_le_kolmogorovWidth_of_orthonormal {k : ℕ} {u : Fin (k + 1) → E}
    (hu : Orthonormal 𝕜 u) {r : ℝ} {A : Set E}
    (hA : ∀ y ∈ span 𝕜 (range u), ‖y‖ ≤ 1 → (r : 𝕜) • y ∈ A) :
    ENNReal.ofReal r ≤ kolmogorovWidth 𝕜 A (closedBall 0 1) k := by
  refine le_kolmogorovWidth fun c v h => ?_
  obtain ⟨y, hyu, hy1, hyv⟩ := hu.exists_norm_eq_one_inner_eq_zero v
  obtain ⟨_, ⟨z, hz, rfl⟩, l, hl, hzl⟩ := h (hA y hyu hy1.le)
  have hyl : ⟪y, l⟫ = 0 := by
    have : span 𝕜 (range v) ≤ LinearMap.ker (innerₛₗ 𝕜 y) :=
      span_le.mpr <| by rintro _ ⟨i, rfl⟩; simpa [inner_eq_zero_symm] using hyv i
    exact this hl
  have key : (r : 𝕜) = c * ⟪y, z⟫ := by
    have := congr_arg (fun x => ⟪y, x⟫) hzl
    simp only [inner_add_right, inner_smul_right, hyl, add_zero,
      inner_self_eq_norm_sq_to_K, hy1] at this
    simpa using this.symm
  have hz1 : ‖z‖ ≤ 1 := by simpa using hz
  have : r ≤ ‖c‖ := by
    calc r ≤ ‖(r : 𝕜)‖ := by simpa using le_abs_self r
      _ = ‖c‖ * ‖⟪y, z⟫‖ := by rw [key, norm_mul]
      _ ≤ ‖c‖ * (‖y‖ * ‖z‖) := by gcongr; exact norm_inner_le_norm y z
      _ ≤ ‖c‖ := by rw [hy1, one_mul]; exact mul_le_of_le_one_right (norm_nonneg c) hz1
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
  exact ENNReal.ofReal_le_ofReal this

namespace HilbertBasis

/-- The unit ball of `ℓ²(w)` in the coordinates of the Hilbert basis `b`. -/
def weightedBall (b : HilbertBasis ℕ 𝕜 E) (w : ℕ → ℝ) : Set E :=
  {x | ∀ s : Finset ℕ, ∑ i ∈ s, (w i * ‖⟪b i, x⟫‖) ^ 2 ≤ 1}

variable (b : HilbertBasis ℕ 𝕜 E) {w : ℕ → ℝ}

/-- **Upper bound.** The first `k` basis vectors approximate the weighted unit ball within
`(w k)⁻¹`. -/
theorem kolmogorovWidth_weightedBall_le (hw : Monotone w) (hw0 : 0 < w 0) (k : ℕ) :
    kolmogorovWidth 𝕜 (b.weightedBall w) (closedBall 0 1) k ≤ ENNReal.ofReal (w k)⁻¹ := by
  have hwk : 0 < w k := hw0.trans_le (hw (Nat.zero_le k))
  refine (kolmogorovWidth_le (c := ((w k)⁻¹ : 𝕜)) (fun i : Fin k => b i) ?_).trans_eq ?_
  · intro x hx
    set l := ∑ i : Fin k, ⟪b i, x⟫ • b i
    have hcoef : ∀ i, ⟪b i, x - l⟫ = if i < k then 0 else ⟪b i, x⟫ := fun i => by
      have hl : ⟪b i, l⟫ = if i < k then ⟪b i, x⟫ else 0 := by
        simp only [l, inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
          mul_ite, mul_one, mul_zero]
        rw [Fin.sum_univ_eq_sum_range (fun j => if i = j then ⟪b j, x⟫ else 0) k,
          Finset.sum_ite_eq]
        simp
      rw [inner_sub_right, hl]
      split_ifs <;> simp
    have hnorm : (w k * ‖x - l‖) ^ 2 ≤ 1 := by
      have hs := (b.hasSum_norm_inner_sq (x - l)).mul_left (w k ^ 2)
      rw [mul_pow, ← hs.tsum_eq]
      refine Real.tsum_le_of_sum_le (fun i => by positivity) fun s => (le_trans ?_ (hx s))
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hcoef i, ← mul_pow]
      split_ifs with hi
      · simp; positivity
      · exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hw (not_lt.mp hi)) (norm_nonneg _)) 2
    refine ⟨((w k)⁻¹ : 𝕜) • ((w k : 𝕜) • (x - l)), ⟨(w k : 𝕜) • (x - l), ?_, rfl⟩, l,
      sum_mem fun i _ => smul_mem _ _ (subset_span (mem_range_self i)), ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal, abs_of_pos hwk]
      nlinarith [norm_nonneg (x - l)]
    · rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast hwk.ne'), one_smul]
      exact sub_add_cancel x l
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm]
    simp [abs_of_pos hwk]

/-- **Lower bound.** The weighted unit ball contains `(w k)⁻¹ • y` for every `y` of norm at most
one in the span of the first `k + 1` basis vectors. -/
theorem ofReal_le_kolmogorovWidth_weightedBall (hw : Monotone w) (hw0 : 0 < w 0) (k : ℕ) :
    ENNReal.ofReal (w k)⁻¹ ≤ kolmogorovWidth 𝕜 (b.weightedBall w) (closedBall 0 1) k := by
  have hwk : 0 < w k := hw0.trans_le (hw (Nat.zero_le k))
  refine ofReal_le_kolmogorovWidth_of_orthonormal (u := fun i : Fin (k + 1) => b i)
    (b.orthonormal.comp _ Fin.val_injective) fun y hy hy1 s => ?_
  have hzero : ∀ i, k < i → ⟪b i, y⟫ = 0 := fun i hi => by
    have : span 𝕜 (range fun j : Fin (k + 1) => b j) ≤ LinearMap.ker (innerₛₗ 𝕜 (b i)) :=
      span_le.mpr <| by
        rintro _ ⟨j, rfl⟩
        exact b.orthonormal.inner_eq_zero (by omega)
    exact this hy
  calc ∑ i ∈ s, (w i * ‖⟪b i, (((w k)⁻¹ : ℝ) : 𝕜) • y⟫‖) ^ 2
      ≤ ∑ i ∈ s, ‖⟪b i, y⟫‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [inner_smul_right, norm_mul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hwk)]
        rcases le_or_gt i k with hi | hi
        · have : w i * (w k)⁻¹ ≤ 1 := by
            rw [mul_inv_le_iff₀ hwk, one_mul]; exact hw hi
          have hwi : 0 ≤ w i := hw0.le.trans (hw (Nat.zero_le i))
          rw [← mul_assoc]
          exact pow_le_pow_left₀ (by positivity)
            (mul_le_of_le_one_left (norm_nonneg _) this) 2
        · simp [hzero i hi]
    _ ≤ ‖y‖ ^ 2 := b.orthonormal.sum_inner_products_le y
    _ ≤ 1 := by nlinarith [norm_nonneg y]

/-- **Kolmogorov widths of a weighted unit ball.** For monotone positive weights `w`, the
`k`-th width of the unit ball of `ℓ²(w)` relative to the unit ball of `E` is `(w k)⁻¹`. -/
theorem kolmogorovWidth_weightedBall (hw : Monotone w) (hw0 : 0 < w 0) (k : ℕ) :
    kolmogorovWidth 𝕜 (b.weightedBall w) (closedBall 0 1) k = ENNReal.ofReal (w k)⁻¹ :=
  (b.kolmogorovWidth_weightedBall_le hw hw0 k).antisymm
    (b.ofReal_le_kolmogorovWidth_weightedBall hw hw0 k)

end HilbertBasis

end
