/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Convex.Basic

/-!
# Maps that preserve convex combinations of two points

A map `f` that preserves the convex combinations `a • x + b • y` of two points of a convex set `s`
preserves all finite convex combinations of points of `s`. The scalars only need to form an
ordered semifield, so this applies to `ℝ≥0`-combinations of measures.

## Main results

* `Convex.sum_mem_of_semifield`: a convex set contains the finite convex combinations of its
  points, over an ordered semifield;
* `Convex.map_sum_of_map_add`: a map preserving convex combinations of two points preserves
  finite convex combinations.
-/

@[expose] public section

variable {𝕜 E F ι : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F] {s : Set E}

/-- The joint induction behind `Convex.sum_mem_of_semifield` and `Convex.map_sum_of_map_add`. -/
private theorem Convex.sum_mem_and_map_sum (hs : Convex 𝕜 s) {f : E → F}
    (hf : ∀ x ∈ s, ∀ y ∈ s, ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = a • f x + b • f y)
    (t : Finset ι) {w : ι → 𝕜} {z : ι → E} (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s ∧ f (∑ i ∈ t, w i • z i) = ∑ i ∈ t, w i • f (z i) := by
  classical
  induction t using Finset.induction_on generalizing w with
  | empty => simp at h₁
  | insert j t hj ih =>
    rw [Finset.sum_insert hj] at h₁
    simp only [Finset.mem_insert, forall_eq_or_imp] at h₀ hz
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    set c := ∑ i ∈ t, w i
    have hc0 : 0 ≤ c := Finset.sum_nonneg h₀.2
    rcases hc0.eq_or_lt with hc | hc
    · have hw : ∀ i ∈ t, w i = 0 := (Finset.sum_eq_zero_iff_of_nonneg h₀.2).1 hc.symm
      have hwj : w j = 1 := by rw [← hc, add_zero] at h₁; exact h₁
      have hE : ∑ i ∈ t, w i • z i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hw i hi, zero_smul]
      have hF : ∑ i ∈ t, w i • f (z i) = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hw i hi, zero_smul]
      rw [hE, hF, hwj, one_smul, one_smul, add_zero, add_zero]
      exact ⟨hz.1, rfl⟩
    · have h₀' : ∀ i ∈ t, 0 ≤ w i / c := fun i hi => div_nonneg (h₀.2 i hi) hc.le
      have h₁' : ∑ i ∈ t, w i / c = 1 := by
        simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul, mul_inv_cancel₀ hc.ne']
      obtain ⟨hy, hfy⟩ := ih h₀' h₁' hz.2
      have hsum : ∀ g : ι → F, ∑ i ∈ t, w i • g i = c • ∑ i ∈ t, (w i / c) • g i := fun g => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_div_cancel₀ _ hc.ne']
      have hsumE : ∑ i ∈ t, w i • z i = c • ∑ i ∈ t, (w i / c) • z i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_div_cancel₀ _ hc.ne']
      rw [hsumE, hsum, ← hfy]
      exact ⟨hs hz.1 hy h₀.1 hc.le h₁, hf _ hz.1 _ hy _ _ h₀.1 hc.le h₁⟩

/-- A convex set contains the finite convex combinations of its points. Unlike `Convex.sum_mem`,
the scalars only need to form an ordered semifield, such as `ℝ≥0`. -/
theorem Convex.sum_mem_of_semifield (hs : Convex 𝕜 s) {t : Finset ι} {w : ι → 𝕜} {z : ι → E}
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s :=
  (hs.sum_mem_and_map_sum (f := fun x => x) (fun _ _ _ _ _ _ _ _ _ => rfl) t h₀ h₁ hz).1

/-- A map that preserves the convex combinations of two points of a convex set preserves the
finite convex combinations of its points. -/
theorem Convex.map_sum_of_map_add (hs : Convex 𝕜 s) {f : E → F}
    (hf : ∀ x ∈ s, ∀ y ∈ s, ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = a • f x + b • f y)
    {t : Finset ι} {w : ι → 𝕜} {z : ι → E} (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) :
    f (∑ i ∈ t, w i • z i) = ∑ i ∈ t, w i • f (z i) :=
  (hs.sum_mem_and_map_sum hf t h₀ h₁ hz).2
