/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Products that converge to the exponential

In a real Banach algebra, if `f τ = 1 + τ b + o(τ)` as `τ → 0⁺`, then `f (t / n) ^ n → exp (t b)`
for every `t > 0`. The path `τ ↦ exp (τ b)` has the same first-order behaviour, so
`f (t / n) - exp ((t / n) b) = o(1 / n)`, and the telescoping bound
`‖xⁿ - yⁿ‖ ≤ n Mⁿ ‖x - y‖` with `M = 1 + C t / n`, `Mⁿ ≤ exp (C t)`, gives the limit.

## Main results

* `norm_pow_sub_pow_le_of_le`: the telescoping bound.
* `tendsto_pow_exp_of_tendsto_smul_sub_one`: the limit.
-/

@[expose] public section

open Filter NormedSpace
open scoped Topology

/-- Telescoping: `‖xⁿ - yⁿ‖ ≤ n Mⁿ ‖x - y‖` when `‖x‖ ≤ M`, `‖y‖ ≤ M` and `1 ≤ M`. -/
theorem norm_pow_sub_pow_le_of_le {R : Type*} [NormedRing R] [NormOneClass R] {x y : R} {M : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hM : 1 ≤ M) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * M ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by
      rw [pow_succ', pow_succ']
      noncomm_ring
    have hyn : ‖y ^ n‖ ≤ M ^ n :=
      (norm_pow_le y n).trans (pow_le_pow_left₀ (norm_nonneg _) hy n)
    have hd := norm_nonneg (x - y)
    have hM0 : 0 ≤ M := zero_le_one.trans hM
    have hMn : M ^ n ≤ M ^ n * M := le_mul_of_one_le_right (pow_nonneg hM0 n) hM
    rw [h]
    calc ‖x * (x ^ n - y ^ n) + (x - y) * y ^ n‖
        ≤ ‖x‖ * ‖x ^ n - y ^ n‖ + ‖x - y‖ * ‖y ^ n‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (n * M ^ n * ‖x - y‖) + ‖x - y‖ * M ^ n := by gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ) * M ^ (n + 1) * ‖x - y‖ := by
        push_cast
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_left hMn hd]

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- **Products that converge to the exponential**: if `(f τ - 1) / τ → b` as `τ → 0⁺`, then
`f (t / n) ^ n → exp (t b)` for every `t > 0`. -/
theorem tendsto_pow_exp_of_tendsto_smul_sub_one {f : ℝ → 𝔸} {b : 𝔸}
    (hf : Tendsto (fun τ : ℝ => τ⁻¹ • (f τ - 1)) (𝓝[>] 0) (𝓝 b)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => f (t / n) ^ n) atTop (𝓝 (exp (t • b))) := by
  set g : ℝ → 𝔸 := fun τ => exp (τ • b)
  have hg : Tendsto (fun τ : ℝ => τ⁻¹ • (g τ - 1)) (𝓝[>] 0) (𝓝 b) := by
    have h := HasDerivAt.tendsto_slope_zero_right (hasDerivAt_exp_smul_const (𝕂 := ℝ) b 0)
    simpa [g] using h
  have htn : Tendsto (fun n : ℕ => t / n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat t, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_pos ht (Nat.cast_pos.mpr hn)
  set C := ‖b‖ + 1
  -- both `f (t / n)` and `g (t / n)` have norm at most `1 + C t / n`
  have hbound : ∀ h : ℝ → 𝔸, Tendsto (fun τ : ℝ => τ⁻¹ • (h τ - 1)) (𝓝[>] 0) (𝓝 b) →
      ∀ᶠ n : ℕ in atTop, ‖h (t / n)‖ ≤ 1 + C * (t / n) := by
    intro h hh
    have h1 : ∀ᶠ τ in 𝓝[>] (0 : ℝ), ‖τ⁻¹ • (h τ - 1)‖ < C :=
      hh.norm.eventually (gt_mem_nhds (by simp [C]))
    filter_upwards [htn.eventually h1, eventually_gt_atTop 0] with n hn hn0
    have hτ : 0 < t / n := div_pos ht (Nat.cast_pos.mpr hn0)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hτ] at hn
    have h2 := (inv_mul_lt_iff₀ hτ).mp hn
    calc ‖h (t / n)‖ = ‖1 + (h (t / n) - 1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖(1 : 𝔸)‖ + ‖h (t / n) - 1‖ := norm_add_le _ _
      _ ≤ 1 + C * (t / n) := by rw [norm_one, mul_comm]; linarith
  -- `n (f (t / n) - g (t / n)) → 0`
  have hdiff : Tendsto (fun n : ℕ => (n : ℝ) • (f (t / n) - g (t / n))) atTop (𝓝 0) := by
    have h := ((hf.sub hg).comp htn).const_smul t
    rw [sub_self, smul_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp only [Function.comp_apply, ← smul_sub, sub_sub_sub_cancel_right, smul_smul]
    congr 1
    field_simp
  have hgn : ∀ n : ℕ, 0 < n → g (t / n) ^ n = exp (t • b) := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
    simp only [g]
    rw [← exp_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_div_cancel₀ _ hn']
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => Real.exp (C * t) * ‖(n : ℝ) • (f (t / n) - g (t / n))‖)
      atTop (𝓝 0) := by
    simpa using hdiff.norm.const_mul (Real.exp (C * t))
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hbound f hf, hbound g hg, eventually_gt_atTop 0] with n hfn hgn' hn
  have hτ : 0 < t / n := div_pos ht (Nat.cast_pos.mpr hn)
  have hC : 0 ≤ C := by positivity
  have hM : 1 ≤ 1 + C * (t / n) := le_add_of_nonneg_right (by positivity)
  have hMn : (1 + C * (t / n)) ^ n ≤ Real.exp (C * t) := by
    calc (1 + C * (t / n)) ^ n ≤ Real.exp (C * (t / n)) ^ n := by
          gcongr
          linarith [Real.add_one_le_exp (C * (t / n))]
      _ = Real.exp (C * t) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  rw [← hgn n hn, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]
  calc ‖f (t / n) ^ n - g (t / n) ^ n‖
      ≤ n * (1 + C * (t / n)) ^ n * ‖f (t / n) - g (t / n)‖ :=
        norm_pow_sub_pow_le_of_le hfn hgn' hM n
    _ ≤ Real.exp (C * t) * (n * ‖f (t / n) - g (t / n)‖) := by
        have := norm_nonneg (f (t / n) - g (t / n))
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith [mul_nonneg this (norm_nonneg (f (t / n) - g (t / n)))]
