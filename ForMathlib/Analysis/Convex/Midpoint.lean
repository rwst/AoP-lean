/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Bounded maps that preserve midpoints

A solution of Jensen's functional equation `f ((s + u) / 2) = (f s + f u) / 2` on `[0, 1]` with
values in a normed space is affine as soon as it is bounded; no continuity is needed. Subtracting
the affine interpolation leaves a solution `g` with `g 0 = g 1 = 0`, for which
`g t = g (2 t) / 2` on `[0, 1/2]` and `g t = g (2 t - 1) / 2` on `[1/2, 1]`, so a bound `B` on
`‖g‖` improves to `B / 2`, hence to `0`.

Along each segment of a convex set this gives: a bounded map that preserves midpoints preserves
all convex combinations of two points.

## Main results

* `eq_sub_smul_add_smul_of_map_midpoint`: a bounded solution of Jensen's equation on `[0, 1]` is
  affine;
* `Convex.map_add_of_map_midpoint`: on a convex set, a bounded map preserving midpoints preserves
  convex combinations of two points.
-/

@[expose] public section

open Filter Set Topology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A bounded solution of Jensen's functional equation on `[0, 1]` is affine. -/
theorem eq_sub_smul_add_smul_of_map_midpoint {f : ℝ → F} {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ B)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1, f ((s + u) / 2) = (2⁻¹ : ℝ) • (f s + f u))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : f t = (1 - t) • f 0 + t • f 1 := by
  set g : ℝ → F := fun t => f t - ((1 - t) • f 0 + t • f 1) with hg
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : g 1 = 0 := by simp [g]
  have hgm : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      g ((s + u) / 2) = (2⁻¹ : ℝ) • (g s + g u) := by
    intro s hs u hu
    simp only [g, hf s hs u hu]
    module
  have hgB : ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ ≤ 2 * B := by
    intro t ht
    calc ‖g t‖ ≤ ‖f t‖ + (‖(1 - t) • f 0‖ + ‖t • f 1‖) :=
          (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ B + ((1 - t) * B + t * B) := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 ht.2),
            Real.norm_of_nonneg ht.1]
          have := hB t ht
          have := hB 0 ⟨le_rfl, zero_le_one⟩
          have := hB 1 ⟨zero_le_one, le_rfl⟩
          gcongr <;> linarith [ht.1, ht.2]
      _ = 2 * B := by ring
  have key : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) 1, ‖g t‖ ≤ 2 * B * (2⁻¹ : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simpa using hgB
    | succ n ih =>
      intro t ht
      rcases le_total t 2⁻¹ with h | h
      · have h2 : 2 * t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith⟩
        have e := hgm 0 ⟨le_rfl, zero_le_one⟩ (2 * t) h2
        rw [hg0, zero_add, zero_add, mul_div_cancel_left₀ _ two_ne_zero] at e
        rw [e, norm_smul, Real.norm_of_nonneg (by norm_num), pow_succ]
        linarith [ih _ h2]
      · have h2 : 2 * t - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [ht.2]⟩
        have e := hgm _ h2 1 ⟨zero_le_one, le_rfl⟩
        rw [hg1, add_zero, sub_add_cancel, mul_div_cancel_left₀ _ two_ne_zero] at e
        rw [e, norm_smul, Real.norm_of_nonneg (by norm_num), pow_succ]
        linarith [ih _ h2]
  have hlim : Tendsto (fun n : ℕ => 2 * B * (2⁻¹ : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul (2 * B)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp (ge_of_tendsto' hlim fun n => key n t ht))

/-- On a convex set, a bounded map that preserves midpoints preserves convex combinations of two
points. -/
theorem Convex.map_add_of_map_midpoint {s : Set E} (hs : Convex ℝ s) {f : E → F} {B : ℝ}
    (hB : ∀ x ∈ s, ‖f x‖ ≤ B)
    (hf : ∀ x ∈ s, ∀ y ∈ s,
      f ((2⁻¹ : ℝ) • x + (2⁻¹ : ℝ) • y) = (2⁻¹ : ℝ) • f x + (2⁻¹ : ℝ) • f y)
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) = a • f x + b • f y := by
  obtain rfl : b = 1 - a := by linarith
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • y + t • x ∈ s := fun t ht =>
    hs hy hx (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  have h := eq_sub_smul_add_smul_of_map_midpoint (f := fun t => f ((1 - t) • y + t • x))
    (fun t ht => hB _ (hm t ht)) (fun t ht u hu => by
      rw [smul_add, ← hf _ (hm t ht) _ (hm u hu)]
      congr 1
      module) (t := a) ⟨ha, by linarith⟩
  simp only [sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add] at h
  rw [add_comm (a • x), h, add_comm]
