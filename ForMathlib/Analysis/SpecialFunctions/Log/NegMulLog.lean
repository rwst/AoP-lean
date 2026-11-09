/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Subadditivity of `x ↦ -x log x`, and weights of infinite Shannon entropy

## Main statements

* `Real.negMulLog_add_le`: `negMulLog (x + y) ≤ negMulLog x + negMulLog y` for `x, y ≥ 0`.
* `Real.exists_hasSum_one_tsum_negMulLog_eq_top`: there are countably many weights `wᵢ ≥ 0`
  with `∑ᵢ wᵢ = 1` and Shannon entropy `∑ᵢ -wᵢ log wᵢ = ∞`. Block `k` has `2 ^ 2 ^ (k + 1)`
  equal weights of total `2⁻¹ ^ (k + 1)`, and contributes at least `log 2` to the entropy.
-/

public section

open scoped ENNReal

namespace Real

lemma negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  rcases hy.eq_or_lt with rfl | hy'
  · simp
  have h1 : log x ≤ log (x + y) := log_le_log hx' (by linarith)
  have h2 : log y ≤ log (x + y) := log_le_log hy' (by linarith)
  simp only [negMulLog]
  nlinarith [mul_le_mul_of_nonneg_left h1 hx, mul_le_mul_of_nonneg_left h2 hy]

theorem exists_hasSum_one_tsum_negMulLog_eq_top :
    ∃ (ι : Type) (_ : Countable ι) (w : ι → ℝ), (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧
      ∑' i, ENNReal.ofReal (negMulLog (w i)) = ∞ := by
  set N : ℕ → ℕ := fun k => 2 ^ 2 ^ (k + 1)
  set a : ℕ → ℝ := fun k => 1 / 2 / 2 ^ k
  have ha0 : ∀ k, 0 < a k := fun k => by positivity
  have hN0 : ∀ k, (0 : ℝ) < N k := fun k => by positivity
  set w : (Σ k, Fin (N k)) → ℝ := fun i => a i.1 / N i.1
  have hw0 : ∀ i, 0 ≤ w i := fun i => (div_pos (ha0 _) (hN0 _)).le
  have hfib : ∀ k, HasSum (fun j : Fin (N k) => w ⟨k, j⟩) (a k) := fun k => by
    convert hasSum_fintype (fun j : Fin (N k) => w ⟨k, j⟩) using 1
    simp only [w, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [(hN0 k).ne']
  have hw : HasSum w 1 := by
    refine (hasSum_geometric_two' 1).sigma_of_hasSum hfib ?_
    refine (summable_sigma_of_nonneg hw0).mpr ⟨fun k => (hfib k).summable, ?_⟩
    simp only [fun k => (hfib k).tsum_eq]
    exact (hasSum_geometric_two' 1).summable
  refine ⟨_, inferInstance, w, hw0, hw, ?_⟩
  have hblock : ∀ k, ENNReal.ofReal (log 2) ≤
      ∑' j : Fin (N k), ENNReal.ofReal (negMulLog (w ⟨k, j⟩)) := fun k => by
    simp only [w]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hlogN : log (N k) = 2 ^ (k + 1) * log 2 := by simp [N, Real.log_pow]
    have hloga : log (a k) ≤ 0 := log_nonpos (ha0 k).le (by
      simp only [a]
      rw [div_div, div_le_one (by positivity)]
      linarith [one_le_pow₀ (M₀ := ℝ) (a := 2) one_le_two (n := k)])
    have hak : a k * 2 ^ (k + 1) = 1 := by
      simp only [a]
      field_simp
      ring
    simp only [negMulLog]
    rw [log_div (ha0 k).ne' (hN0 k).ne', hlogN]
    have : (N k : ℝ) * (-(a k / N k) * (log (a k) - 2 ^ (k + 1) * log 2)) =
        log 2 * (a k * 2 ^ (k + 1)) - a k * log (a k) := by
      field_simp [(hN0 k).ne']
      ring
    rw [this, hak]
    nlinarith [ha0 k]
  rw [tsum_sigma', eq_top_iff]
  calc ∞ = ∑' _ : ℕ, ENNReal.ofReal (log 2) :=
        (ENNReal.tsum_const_eq_top_of_ne_zero
          (ENNReal.ofReal_pos.mpr (log_pos one_lt_two)).ne').symm
    _ ≤ _ := tsum_le_tsum hblock

end Real
