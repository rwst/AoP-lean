/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Functions that are affine along the chords of a ball

Let `f` be a real function on a real normed space that is affine along every chord of the unit
sphere: `f (t x + (1 - t) y) = t f x + (1 - t) f y` for unit vectors `x`, `y` and `t ∈ [0, 1]`.
Then `f` is affine on the closed unit ball, `f v = f 0 + L v` for a linear map `L`.

Along the diameter through `±x`, `f (s x) = f 0 + s (f x - f 0)`, so `L v = |v| (f (v / |v|) - f 0)`
is homogeneous. It is additive because `(|u| x + |v| y) / (|u| + |v|)`, with `x`, `y` the
directions of `u`, `v`, lies on the chord from `x` to `y`.

In an inner product space, if moreover `f ≤ 1` on the sphere, `f a = 1` and `f (-a) = 0` for a
unit vector `a`, then `f v = (1 + ⟪a, v⟫) / 2`: the maximum of an affine function on the ball lies
in the direction of its gradient, which is therefore along `a`. For a unit `e ⊥ a` and
`x = ((1 - t²) a + 2 t e) / (1 + t²)` on the sphere, `f x ≤ 1` reads `2 t L e ≤ t²`, which for
`t = L e` forces `L e = 0`.

## Main results

* `exists_linearMap_eq_of_chord`: a function affine along the chords of the unit sphere is affine
  on the closed unit ball.
* `eq_of_chord_of_le_one`: such a function with `f ≤ 1` on the sphere, `f a = 1` and
  `f (-a) = 0` is `(1 + ⟪a, ·⟫) / 2`.
-/

@[expose] public noncomputable section

open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ}

section Chord

variable (hf : ∀ x y : V, ‖x‖ = 1 → ‖y‖ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
  f (t • x + (1 - t) • y) = t * f x + (1 - t) * f y)
include hf

lemma apply_neg_of_chord {x : V} (hx : ‖x‖ = 1) : f (-x) = 2 * f 0 - f x := by
  have h := hf x (-x) hx (by rwa [norm_neg]) 2⁻¹ (by norm_num) (by norm_num)
  rw [show (2⁻¹ : ℝ) • x + (1 - 2⁻¹ : ℝ) • -x = 0 by module] at h
  linarith

/-- Along the diameter through `±x`, `f (s x) = f 0 + s (f x - f 0)`. -/
lemma apply_smul_of_chord {x : V} (hx : ‖x‖ = 1) {s : ℝ} (hs : |s| ≤ 1) :
    f (s • x) = f 0 + s * (f x - f 0) := by
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  have h := hf x (-x) hx (by rwa [norm_neg]) ((1 + s) / 2) (by linarith) (by linarith)
  rw [show ((1 + s) / 2) • x + (1 - (1 + s) / 2) • -x = s • x by module,
    apply_neg_of_chord hf hx] at h
  rw [h]
  ring

omit hf in
/-- The linear part `‖v‖ (f (v / ‖v‖) - f 0)` of `f`. -/
private def linearPart (f : V → ℝ) (v : V) : ℝ := ‖v‖ * (f (‖v‖⁻¹ • v) - f 0)

omit hf in
private lemma eq_norm_smul {v : V} (hv : v ≠ 0) :
    ‖‖v‖⁻¹ • v‖ = 1 ∧ v = ‖v‖ • ‖v‖⁻¹ • v := by
  have h0 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  refine ⟨?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
  · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

private lemma linearPart_smul_unit {x : V} (hx : ‖x‖ = 1) (c : ℝ) :
    linearPart f (c • x) = c * (f x - f 0) := by
  simp only [linearPart, norm_smul, hx, mul_one, Real.norm_eq_abs, smul_smul]
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · rw [abs_of_neg hc, show (-c)⁻¹ * c = -1 by rw [inv_neg, neg_mul, inv_mul_cancel₀ hc.ne],
      neg_one_smul, apply_neg_of_chord hf hx]
    ring
  · simp
  · rw [abs_of_pos hc, inv_mul_cancel₀ hc.ne', one_smul]

private lemma linearPart_smul (c : ℝ) (v : V) : linearPart f (c • v) = c * linearPart f v := by
  by_cases hv : v = 0
  · simp [linearPart, hv]
  obtain ⟨hx, hvx⟩ := eq_norm_smul hv
  conv_lhs => rw [hvx, smul_smul]
  conv_rhs => rw [hvx]
  rw [linearPart_smul_unit hf hx, linearPart_smul_unit hf hx]
  ring

private lemma apply_eq_linearPart {v : V} (hv : ‖v‖ ≤ 1) : f v = f 0 + linearPart f v := by
  by_cases hv0 : v = 0
  · simp [linearPart, hv0]
  obtain ⟨hx, hvx⟩ := eq_norm_smul hv0
  conv_lhs => rw [hvx]
  rw [apply_smul_of_chord hf hx (by rwa [abs_norm]), linearPart]

private lemma linearPart_smul_add_smul {x y : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    linearPart f (α • x + β • y) = α * (f x - f 0) + β * (f y - f 0) := by
  set t := α / (α + β)
  have ht0 : 0 ≤ t := by positivity
  have e1 : (α + β) * t = α := by simp only [t]; field_simp
  have e2 : (α + β) * (1 - t) = β := by rw [mul_sub, e1]; ring
  have ht1 : t ≤ 1 := by nlinarith
  have hw : ‖t • x + (1 - t) • y‖ ≤ 1 := by
    calc ‖t • x + (1 - t) • y‖ ≤ ‖t • x‖ + ‖(1 - t) • y‖ := norm_add_le _ _
      _ = 1 := by
        rw [norm_smul, norm_smul, hx, hy, Real.norm_of_nonneg ht0,
          Real.norm_of_nonneg (by linarith)]
        ring
  have huv : α • x + β • y = (α + β) • (t • x + (1 - t) • y) := by
    rw [smul_add, smul_smul, smul_smul, e1, e2]
  rw [huv, linearPart_smul hf, ← sub_eq_of_eq_add' (apply_eq_linearPart hf hw),
    hf x y hx hy t ht0 ht1]
  linear_combination (f x - f 0) * e1 + (f y - f 0) * e2

private lemma linearPart_add (u v : V) :
    linearPart f (u + v) = linearPart f u + linearPart f v := by
  by_cases hu : u = 0
  · simp [linearPart, hu]
  by_cases hv : v = 0
  · simp [linearPart, hv]
  obtain ⟨hx, hux⟩ := eq_norm_smul hu
  obtain ⟨hy, hvy⟩ := eq_norm_smul hv
  rw [hux, hvy, linearPart_smul_add_smul hf hx hy (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv),
    linearPart_smul_unit hf hx, linearPart_smul_unit hf hy]

/-- **A function affine along the chords of the unit sphere is affine on the closed unit ball.** -/
theorem exists_linearMap_eq_of_chord : ∃ L : V →ₗ[ℝ] ℝ, ∀ v : V, ‖v‖ ≤ 1 → f v = f 0 + L v :=
  ⟨{ toFun := linearPart f
     map_add' := linearPart_add hf
     map_smul' := linearPart_smul hf },
    fun _ hv => apply_eq_linearPart hf hv⟩

end Chord

/-- **An affine function on the ball with maximum `1` at `a` and value `0` at `-a`.** If `f` is
affine along the chords of the unit sphere, `f ≤ 1` on the sphere, `f a = 1` and `f (-a) = 0` for
a unit vector `a`, then `f v = (1 + ⟪a, v⟫) / 2` on the closed unit ball. -/
theorem eq_of_chord_of_le_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {f : V → ℝ} (hf : ∀ x y : V, ‖x‖ = 1 → ‖y‖ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • x + (1 - t) • y) = t * f x + (1 - t) * f y)
    (h1 : ∀ x : V, ‖x‖ = 1 → f x ≤ 1) {a : V} (ha : ‖a‖ = 1) (hfa : f a = 1) (hfna : f (-a) = 0)
    {v : V} (hv : ‖v‖ ≤ 1) : f v = (1 + ⟪a, v⟫) / 2 := by
  obtain ⟨L, hL⟩ := exists_linearMap_eq_of_chord hf
  have hf0 : f 0 = 2⁻¹ := by
    have := apply_neg_of_chord hf ha
    linarith
  have hLa : L a = 2⁻¹ := by
    have := hL a ha.le
    linarith
  -- `L` vanishes on unit vectors orthogonal to `a`.
  have hLe : ∀ e : V, ‖e‖ = 1 → ⟪a, e⟫ = 0 → L e = 0 := by
    intro e he hae
    set ℓ := L e
    have hD : 0 < 1 + ℓ ^ 2 := by positivity
    set x := ((1 - ℓ ^ 2) / (1 + ℓ ^ 2)) • a + (2 * ℓ / (1 + ℓ ^ 2)) • e
    have hx : ‖x‖ = 1 := by
      have h2 : ‖x‖ ^ 2 = 1 := by
        rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, hae, norm_smul,
          norm_smul, ha, he, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs,
          sq_abs]
        field_simp
        ring
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2
    have hfx := h1 x hx
    rw [hL x hx.le, hf0, map_add, map_smul, map_smul, hLa, smul_eq_mul, smul_eq_mul] at hfx
    have key : 2 * ℓ ^ 2 ≤ ℓ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hfx hD.le
      field_simp at this
      nlinarith
    nlinarith [sq_nonneg ℓ]
  -- `L v = ⟪a, v⟫ L a`, splitting off the part of `v` orthogonal to `a`.
  have hw : L (v - ⟪a, v⟫ • a) = 0 := by
    set w := v - ⟪a, v⟫ • a
    have haw : ⟪a, w⟫ = 0 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ha]
      ring
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    have h0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    have he : ‖‖w‖⁻¹ • w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]
    have hae : ⟪a, ‖w‖⁻¹ • w⟫ = 0 := by rw [real_inner_smul_right, haw, mul_zero]
    have := hLe _ he hae
    rw [map_smul, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left (inv_ne_zero h0)
  have hLv : L v = ⟪a, v⟫ * 2⁻¹ := by
    calc L v = L (⟪a, v⟫ • a + (v - ⟪a, v⟫ • a)) := by rw [add_sub_cancel]
      _ = ⟪a, v⟫ * 2⁻¹ := by rw [map_add, hw, map_smul, hLa, smul_eq_mul, add_zero]
  rw [hL v hv, hf0, hLv]
  ring
