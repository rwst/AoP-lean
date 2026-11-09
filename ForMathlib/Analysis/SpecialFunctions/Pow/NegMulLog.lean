/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Power bounds for `x ↦ -x log x`

Since `log y ≤ y - 1`, applied to `y = x^{-1/4}`, `-x log x ≤ 4 x^{3/4}`; together with
`-x log x ≤ 1 - x` this gives `-x log x ≤ 8 (x (1 - x))^{3/4}` on `[0, 1]`. Summed over a
probability vector `p`, whose terms satisfy `pᵢ (1 - pᵢ) ≤ ∑ⱼ pⱼ (1 - pⱼ) = 1 - ∑ⱼ pⱼ²`, the
Shannon entropy is at most `8 n (1 - ∑ⱼ pⱼ²)^{3/4}`: it is small when the collision probability
`∑ⱼ pⱼ²` is close to one.

## Main statements

* `Real.negMulLog_le_four_mul_rpow`: `-x log x ≤ 4 x^{3/4}` for `x ≥ 0`.
* `Real.negMulLog_le_eight_mul_rpow`: `-x log x ≤ 8 (x (1 - x))^{3/4}` on `[0, 1]`.
* `Real.sum_negMulLog_le`: `∑ᵢ -pᵢ log pᵢ ≤ 8 n (1 - ∑ᵢ pᵢ²)^{3/4}` for a probability vector.
-/

public section

namespace Real

/-- `-x log x ≤ 4 x^{3/4}` for `x ≥ 0`. -/
lemma negMulLog_le_four_mul_rpow {x : ℝ} (hx : 0 ≤ x) : negMulLog x ≤ 4 * x ^ (3 / 4 : ℝ) := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp [zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0)]
  have h := log_le_sub_one_of_pos (rpow_pos_of_pos hx' (-1 / 4 : ℝ))
  rw [log_rpow hx'] at h
  have hx34 : x ^ (3 / 4 : ℝ) = x * x ^ (-1 / 4 : ℝ) := by
    rw [show (3 / 4 : ℝ) = 1 + -1 / 4 by norm_num, rpow_add hx', rpow_one]
  rw [hx34, negMulLog]
  nlinarith [mul_le_mul_of_nonneg_left h hx, rpow_pos_of_pos hx' (-1 / 4 : ℝ)]

/-- `-x log x ≤ 8 (x (1 - x))^{3/4}` for `0 ≤ x ≤ 1`. -/
lemma negMulLog_le_eight_mul_rpow {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    negMulLog x ≤ 8 * (x * (1 - x)) ^ (3 / 4 : ℝ) := by
  have hle : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → y ≤ y ^ (3 / 4 : ℝ) := fun y hy0 hy1 => by
    simpa using rpow_le_rpow_of_exponent_ge' hy0 hy1 (by norm_num) (by norm_num : (3 / 4 : ℝ) ≤ 1)
  rcases le_total x (1 / 2) with hx | hx
  · -- `x (1 - x) ≥ x / 2`, and `(1/2)^{3/4} ≥ 1/2`.
    have hm : x * (1 / 2) ≤ x * (1 - x) := mul_le_mul_of_nonneg_left (by linarith) h0
    have h2 : (x * (1 / 2)) ^ (3 / 4 : ℝ) ≤ (x * (1 - x)) ^ (3 / 4 : ℝ) :=
      rpow_le_rpow (by positivity) hm (by norm_num)
    rw [mul_rpow h0 (by norm_num)] at h2
    have h3 := hle (1 / 2) (by norm_num) (by norm_num)
    have h4 := negMulLog_le_four_mul_rpow h0
    have h5 : 0 ≤ x ^ (3 / 4 : ℝ) := rpow_nonneg h0 _
    nlinarith [mul_le_mul_of_nonneg_left h3 h5]
  · -- `x (1 - x) ≥ (1 - x) / 2`, and `y^{3/4} ≥ y` on `[0, 1]`.
    have hm : (1 / 2) * (1 - x) ≤ x * (1 - x) := mul_le_mul_of_nonneg_right hx (by linarith)
    have h2 : ((1 / 2) * (1 - x)) ^ (3 / 4 : ℝ) ≤ (x * (1 - x)) ^ (3 / 4 : ℝ) :=
      rpow_le_rpow (by nlinarith) hm (by norm_num)
    have h3 := hle ((1 / 2) * (1 - x)) (by nlinarith) (by nlinarith)
    have h4 := negMulLog_le_one_sub_self h0
    nlinarith

/-- **The Shannon entropy is bounded by the collision probability**: for a probability vector
`p` on a finite set `s`, `∑ᵢ -pᵢ log pᵢ ≤ 8 |s| (1 - ∑ᵢ pᵢ²)^{3/4}`. -/
theorem sum_negMulLog_le {ι : Type*} (s : Finset ι) {p : ι → ℝ} (hp0 : ∀ i ∈ s, 0 ≤ p i)
    (hp1 : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, negMulLog (p i) ≤ 8 * s.card * (1 - ∑ i ∈ s, p i ^ 2) ^ (3 / 4 : ℝ) := by
  have hle1 : ∀ i ∈ s, p i ≤ 1 := fun i hi => hp1 ▸ Finset.single_le_sum hp0 hi
  have hq : ∀ i ∈ s, 0 ≤ p i * (1 - p i) := fun i hi =>
    mul_nonneg (hp0 i hi) (by linarith [hle1 i hi])
  have hsum : ∑ i ∈ s, p i * (1 - p i) = 1 - ∑ i ∈ s, p i ^ 2 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp1, sq]
  calc ∑ i ∈ s, negMulLog (p i) ≤ ∑ i ∈ s, 8 * (p i * (1 - p i)) ^ (3 / 4 : ℝ) :=
        Finset.sum_le_sum fun i hi => negMulLog_le_eight_mul_rpow (hp0 i hi) (hle1 i hi)
    _ ≤ ∑ i ∈ s, 8 * (1 - ∑ i ∈ s, p i ^ 2) ^ (3 / 4 : ℝ) := Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_left (rpow_le_rpow (hq i hi)
          (hsum ▸ Finset.single_le_sum hq hi) (by norm_num)) (by norm_num)
    _ = 8 * s.card * (1 - ∑ i ∈ s, p i ^ 2) ^ (3 / 4 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Real
