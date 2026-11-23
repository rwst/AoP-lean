/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.GroupTheory.GroupAction.Pointwise

/-!
# Kolmogorov widths

Let `A` and `B` be sets in a vector space `E` over a normed field `𝕜`. The `k`-th Kolmogorov
width of `A` relative to `B` is the infimum of `‖c‖` over all `c : 𝕜` for which
`A ⊆ c • B + L` with `L` spanned by `k` vectors. When `B` is the unit ball of a norm, it is the
least uniform error with which a `k`-dimensional subspace approximates `A`.

The definition is purely algebraic, so widths are compared across linear maps without any
topology. This is the form used for the isomorphic classification of power series spaces
(Kolmogorov, Pełczyński, Mityagin).

## Main definitions

* `kolmogorovWidth 𝕜 A B k`: the `k`-th Kolmogorov width of `A` relative to `B`, in `ℝ≥0∞`.

## Main statements

* `kolmogorovWidth_le`: an inclusion `A ⊆ c • B + span 𝕜 (range v)` bounds the width by `‖c‖`.
* `kolmogorovWidth_mono_left`, `kolmogorovWidth_anti_right`, `kolmogorovWidth_anti_index`:
  monotonicity in `A`, `B` and `k`.
* `kolmogorovWidth_image_le`: linear maps do not increase widths.
* `kolmogorovWidth_le_mul_of_subset`: if `f '' A ⊆ c₁ • B` and `B' ⊆ c₂ • f '' A'`, then the
  width of `B'` relative to `B` is at most `‖c₁‖ * ‖c₂‖` times that of `A'` relative to `A`. This
  is how continuity of a linear map and of its inverse compares widths in two spaces.

## References

* A. Pinkus, *n-Widths in Approximation Theory*, Springer, 1985.
* R. Meise, D. Vogt, *Introduction to Functional Analysis*, Oxford University Press, 1997.
-/

@[expose] public section

open Set Submodule
open scoped Pointwise ENNReal NNReal

variable (𝕜 : Type*) {E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F]

/-- The `k`-th Kolmogorov width of `A` relative to `B`: the infimum of `‖c‖` over all `c` with
`A ⊆ c • B + L` for a subspace `L` spanned by `k` vectors. -/
noncomputable def kolmogorovWidth (A B : Set E) (k : ℕ) : ℝ≥0∞ :=
  ⨅ (c : 𝕜) (v : Fin k → E) (_ : A ⊆ c • B + (span 𝕜 (range v) : Set E)), (‖c‖₊ : ℝ≥0∞)

variable {𝕜}

theorem kolmogorovWidth_le {A B : Set E} {k : ℕ} {c : 𝕜} (v : Fin k → E)
    (h : A ⊆ c • B + (span 𝕜 (range v) : Set E)) :
    kolmogorovWidth 𝕜 A B k ≤ ‖c‖₊ :=
  iInf₂_le_of_le c v (iInf_le_of_le h le_rfl)

/-- A lower bound for the width: `r` is below `‖c‖` for every admissible `c`. -/
theorem le_kolmogorovWidth {A B : Set E} {k : ℕ} {r : ℝ≥0∞}
    (h : ∀ (c : 𝕜) (v : Fin k → E), A ⊆ c • B + (span 𝕜 (range v) : Set E) → r ≤ ‖c‖₊) :
    r ≤ kolmogorovWidth 𝕜 A B k :=
  le_iInf₂ fun c v => le_iInf (h c v)

theorem kolmogorovWidth_mono_left {A A' B : Set E} (hA : A ⊆ A') (k : ℕ) :
    kolmogorovWidth 𝕜 A B k ≤ kolmogorovWidth 𝕜 A' B k :=
  le_kolmogorovWidth fun _ v h => kolmogorovWidth_le v (hA.trans h)

theorem kolmogorovWidth_anti_right {A B B' : Set E} (hB : B ⊆ B') (k : ℕ) :
    kolmogorovWidth 𝕜 A B' k ≤ kolmogorovWidth 𝕜 A B k :=
  le_kolmogorovWidth fun _ v h =>
    kolmogorovWidth_le v (h.trans (add_subset_add_right (smul_set_mono hB)))

/-- More vectors give a smaller width. -/
theorem kolmogorovWidth_anti_index (A B : Set E) {k l : ℕ} (hkl : k ≤ l) :
    kolmogorovWidth 𝕜 A B l ≤ kolmogorovWidth 𝕜 A B k := by
  refine le_kolmogorovWidth fun c v h => kolmogorovWidth_le
    (fun i : Fin l => if hi : (i : ℕ) < k then v ⟨i, hi⟩ else 0) (h.trans ?_)
  refine add_subset_add_left (SetLike.coe_subset_coe.mpr (span_mono ?_))
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, i.2.trans_le hkl⟩, by simp⟩

/-- Linear maps do not increase widths. -/
theorem kolmogorovWidth_image_le (f : E →ₗ[𝕜] F) (A B : Set E) (k : ℕ) :
    kolmogorovWidth 𝕜 (f '' A) (f '' B) k ≤ kolmogorovWidth 𝕜 A B k := by
  refine le_kolmogorovWidth fun c v h => kolmogorovWidth_le (f ∘ v) ?_
  calc f '' A ⊆ f '' (c • B + (span 𝕜 (range v) : Set E)) := image_mono h
    _ = c • f '' B + (span 𝕜 (range (f ∘ v)) : Set F) := by
      rw [image_add, image_smul_set, range_comp, ← map_coe, map_span]

/-- **Transfer of widths.** If `f '' A ⊆ c₁ • B` and `B' ⊆ c₂ • f '' A'`, then the width of `B'`
relative to `B` is at most `‖c₁‖ * ‖c₂‖` times the width of `A'` relative to `A`. -/
theorem kolmogorovWidth_le_mul_of_subset (f : E →ₗ[𝕜] F) {A A' : Set E} {B B' : Set F}
    {c₁ c₂ : 𝕜} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h₁ : f '' A ⊆ c₁ • B) (h₂ : B' ⊆ c₂ • f '' A')
    (k : ℕ) :
    kolmogorovWidth 𝕜 B' B k ≤ ‖c₁‖₊ * ‖c₂‖₊ * kolmogorovWidth 𝕜 A' A k := by
  have hM : ((‖c₁‖₊ : ℝ≥0∞) * ‖c₂‖₊) ≠ 0 := by simp [hc₁, hc₂]
  have hM' : ((‖c₁‖₊ : ℝ≥0∞) * ‖c₂‖₊) ≠ ⊤ := ENNReal.mul_ne_top (by simp) (by simp)
  rw [← ENNReal.inv_mul_le_iff hM hM']
  refine le_kolmogorovWidth fun c v h => ?_
  rw [ENNReal.inv_mul_le_iff hM hM']
  refine (kolmogorovWidth_le (c := c₂ * c * c₁) (f ∘ v) ?_).trans_eq
    (by simp only [nnNorm_mul, ENNReal.coe_mul]; ring)
  rintro _ hy
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := h₂ hy
  obtain ⟨_, ⟨a, ha, rfl⟩, l, hl, rfl⟩ := h hx
  obtain ⟨b, hb, hab⟩ := h₁ ⟨a, ha, rfl⟩
  refine ⟨(c₂ * c * c₁) • b, ⟨b, hb, rfl⟩, c₂ • f l, ?_, ?_⟩
  · rw [range_comp, ← map_span]
    exact smul_mem _ _ ⟨l, hl, rfl⟩
  · simp only [map_add, map_smul, ← hab, smul_add, smul_smul, mul_assoc]

end
