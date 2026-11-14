/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
import ForMathlib.Analysis.Fourier.PaleyWiener
import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# A chirp on the Fourier side destroys bounded support

If `f` and `g` in `L²(ℝ)` both vanish outside a bounded set and
`𝓕 g ξ = exp (-i a ξ²) 𝓕 f ξ` with `a ≠ 0`, then `f = 0`. In quantum mechanics: the free
evolution `e^{-itH₀}`, `t ≠ 0`, takes no nonzero state of bounded support to one of bounded
support.

The proof. By the easy half of the Paley–Wiener theorem, `𝓕 f` and `𝓕 g` extend to entire
functions `G` and `H` of exponential type, and `H z = exp (-i a z²) G z` on `ℂ` by the identity
theorem. Along the line `ℝ ω` with `ω² = i sign a` the factor `exp (-i a z²)` is
`exp (|a| s²)`, along `i ℝ ω` it is `exp (-|a| s²)`. So `k s = G (s ω) H (s ω)` decays like
`exp (-|a| s²)` on both axes and is of exponential type; by the Phragmén–Lindelöf principle it
vanishes on the right half-plane. Since `k = exp (|a| s²) G (s ω)²`, `G` vanishes on an open set,
so everywhere, and `f = 0` by Fourier uniqueness.

## Main results

* `Real.ae_eq_zero_of_fourier_eq_cexp_mul`: the statement above.
-/

open MeasureTheory Set Complex Filter Topology Asymptotics
open scoped Real FourierTransform

public section

namespace Real

private lemma bound_of_lt_abs {f : ℝ → ℂ} {R : ℝ} (hR : ∀ᵐ x, R < |x| → f x = 0) :
    ∀ᵐ x, x ∉ Ioc (-(|R| + 1)) (|R| + 1) → f x = 0 := by
  filter_upwards [hR] with x hx hxI
  refine hx ?_
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hxI
  rcases hxI with h | h
  · rw [abs_of_neg (by linarith [abs_nonneg R])]; linarith [le_abs_self R]
  · rw [abs_of_pos (by linarith [abs_nonneg R])]; linarith [le_abs_self R]

private lemma integrableOn_Ioc {f : ℝ → ℂ} (hf : MemLp f 2) (a b : ℝ) :
    IntegrableOn f (Ioc a b) := by
  have : IsFiniteMeasure (volume.restrict (Ioc a b)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact (hf.restrict _).integrable one_le_two

/-- `-|a| y² + 2 K |y| ≤ K² / |a|`. -/
private lemma quad_le {a K y : ℝ} (ha : 0 < a) : -a * y ^ 2 + 2 * K * |y| ≤ K ^ 2 / a := by
  rw [le_div_iff₀ ha, ← sq_abs y]
  nlinarith [sq_nonneg (a * |y| - K)]

/-- **A chirp on the Fourier side destroys bounded support.** If `f, g ∈ L²(ℝ)` vanish almost
everywhere outside `[-R, R]`, `a ≠ 0`, and `𝓕 g ξ = exp (-i a ξ²) 𝓕 f ξ` for all `ξ`, then
`f = 0` almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_cexp_mul {f g : ℝ → ℂ} (hf : MemLp f 2) (hg : MemLp g 2)
    {R : ℝ} (hfR : ∀ᵐ x, R < |x| → f x = 0) (hgR : ∀ᵐ x, R < |x| → g x = 0) {a : ℝ}
    (ha : a ≠ 0) (h : ∀ ξ : ℝ, 𝓕 g ξ = cexp ((-(a * ξ ^ 2) : ℝ) * I) * 𝓕 f ξ) :
    f =ᵐ[volume] 0 := by
  set B := |R| + 1
  obtain ⟨G, hGd, hGf, hGb⟩ := exists_differentiable_fourier_eq (integrableOn_Ioc hf (-B) B)
    (bound_of_lt_abs hfR)
  obtain ⟨H, hHd, hHg, hHb⟩ := exists_differentiable_fourier_eq (integrableOn_Ioc hg (-B) B)
    (bound_of_lt_abs hgR)
  set K := 2 * π * max |-B| |B|
  set Cf := ∫ x in Ioc (-B) B, ‖f x‖
  set Cg := ∫ x in Ioc (-B) B, ‖g x‖
  have hCf : 0 ≤ Cf := integral_nonneg fun _ => norm_nonneg _
  have hCg : 0 ≤ Cg := integral_nonneg fun _ => norm_nonneg _
  have hK : 0 ≤ K := by positivity
  -- `H z = exp (-i a z²) G z` on `ℂ`.
  have hHG : ∀ z, H z = cexp (-(a : ℂ) * z ^ 2 * I) * G z := by
    have hA : AnalyticOnNhd ℂ H univ := fun z _ => hHd.analyticAt z
    have hA' : AnalyticOnNhd ℂ (fun z => cexp (-(a : ℂ) * z ^ 2 * I) * G z) univ :=
      fun z _ => ((by fun_prop : Differentiable ℂ fun z : ℂ => cexp (-(a : ℂ) * z ^ 2 * I)).mul
        hGd).analyticAt z
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), H z = cexp (-(a : ℂ) * z ^ 2 * I) * G z := by
      have h1 : ∀ᶠ ξ : ℝ in 𝓝[≠] 0, H ξ = cexp (-(a : ℂ) * (ξ : ℂ) ^ 2 * I) * G ξ :=
        Eventually.of_forall fun ξ => by
          rw [← hHg, ← hGf, h ξ]
          congr 2
          push_cast
          ring
      have h2 : Tendsto (fun ξ : ℝ => (ξ : ℂ)) (𝓝[≠] 0) (𝓝[≠] (0 : ℂ)) :=
        continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun ξ hξ => by
          simpa using hξ
      exact h2.frequently h1.frequently
    exact fun z => hA.eqOn_of_preconnected_of_frequently_eq hA' isPreconnected_univ
      (mem_univ 0) hfreq (mem_univ z)
  -- The direction `ω` with `ω² = i sign a`.
  set σ : ℝ := if 0 < a then 1 else -1
  have hσ2 : σ ^ 2 = 1 := by
    simp only [σ]; split_ifs <;> norm_num
  have hσa : σ * a = |a| := by
    simp only [σ]
    split_ifs with h
    · rw [one_mul, abs_of_pos h]
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.1 h) ha)]; ring
  have hs2 : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((√2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
  set ω : ℂ := (1 + σ * I) / ((√2 : ℝ) : ℂ)
  have hω2 : ω ^ 2 = σ * I := by
    have hσ2' : (σ : ℂ) ^ 2 = 1 := by exact_mod_cast hσ2
    rw [div_pow, hs2]
    field_simp
    linear_combination (I ^ 2) * hσ2' + I_sq
  have hωn : ‖ω‖ = 1 := by
    have : ‖(1 : ℂ) + σ * I‖ = √2 := by
      rw [norm_def, normSq_apply]
      congr 1
      simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_zero, add_zero, add_im, one_im, mul_im, zero_add]
      nlinarith [hσ2]
    rw [norm_div, this, norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 two_pos),
      div_self (Real.sqrt_pos.2 two_pos).ne']
  have hω0 : ω ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hωn; exact zero_ne_one hωn
  have hexp (s : ℂ) : cexp (-(a : ℂ) * (s * ω) ^ 2 * I) = cexp (((|a| : ℝ) : ℂ) * s ^ 2) := by
    congr 1
    rw [mul_pow, hω2, ← hσa]
    push_cast
    linear_combination (-(a : ℂ) * σ * s ^ 2) * I_sq
  have hnorm (s : ℂ) : ‖s * ω‖ = ‖s‖ := by rw [norm_mul, hωn, mul_one]
  -- `k s = G (s ω) H (s ω)`.
  set k : ℂ → ℂ := fun s => G (s * ω) * H (s * ω)
  have hkd : Differentiable ℂ k :=
    (hGd.comp (differentiable_id.mul_const ω)).mul (hHd.comp (differentiable_id.mul_const ω))
  have hkb (s : ℂ) : ‖k s‖ ≤ Cf * Cg * Real.exp (2 * K * ‖s‖) := by
    have h1 := hGb (s * ω)
    have h2 := hHb (s * ω)
    rw [hnorm] at h1 h2
    calc ‖k s‖ = ‖G (s * ω)‖ * ‖H (s * ω)‖ := norm_mul _ _
      _ ≤ (Cf * Real.exp (K * ‖s‖)) * (Cg * Real.exp (K * ‖s‖)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = Cf * Cg * Real.exp (2 * K * ‖s‖) := by
        rw [show 2 * K * ‖s‖ = K * ‖s‖ + K * ‖s‖ by ring, Real.exp_add]; ring
  -- On the real axis, `‖k x‖ ≤ Cg² exp (2K|x| - |a| x²)`.
  have hkre (x : ℝ) : ‖k x‖ ≤ Cg ^ 2 * Real.exp (2 * K * |x| - |a| * x ^ 2) := by
    have hH := hHG (x * ω)
    rw [hexp] at hH
    have he : ‖cexp (((|a| : ℝ) : ℂ) * (x : ℂ) ^ 2)‖ = Real.exp (|a| * x ^ 2) := by
      rw [← ofReal_pow, ← ofReal_mul, norm_exp_ofReal]
    have hG' : ‖G (x * ω)‖ = Real.exp (-(|a| * x ^ 2)) * ‖H (x * ω)‖ := by
      rw [hH, norm_mul, he, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    have h2 := hHb (x * ω)
    rw [hnorm, norm_real, Real.norm_eq_abs] at h2
    calc ‖k x‖ = ‖G (x * ω)‖ * ‖H (x * ω)‖ := norm_mul _ _
      _ = Real.exp (-(|a| * x ^ 2)) * ‖H (x * ω)‖ ^ 2 := by rw [hG']; ring
      _ ≤ Real.exp (-(|a| * x ^ 2)) * (Cg * Real.exp (K * |x|)) ^ 2 := by
        gcongr
      _ = Cg ^ 2 * Real.exp (2 * K * |x| - |a| * x ^ 2) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        rw [show 2 * K * |x| - |a| * x ^ 2 = -(|a| * x ^ 2) + ((2 : ℕ) * (K * |x|)) by
          push_cast; ring, Real.exp_add]
        ring
  -- On the imaginary axis, `k` is bounded.
  have hkim (y : ℝ) : ‖k (y * I)‖ ≤ Cf ^ 2 * Real.exp (K ^ 2 / |a|) := by
    have hH := hHG ((y * I) * ω)
    rw [hexp] at hH
    have he : ‖cexp (((|a| : ℝ) : ℂ) * ((y : ℂ) * I) ^ 2)‖ = Real.exp (-(|a| * y ^ 2)) := by
      rw [mul_pow, I_sq, show ((|a| : ℝ) : ℂ) * ((y : ℂ) ^ 2 * -1) = ((-(|a| * y ^ 2) : ℝ) : ℂ) by
        push_cast; ring, norm_exp_ofReal]
    have h1 := hGb ((y * I) * ω)
    rw [hnorm, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at h1
    calc ‖k (y * I)‖ = ‖G (y * I * ω)‖ * ‖H (y * I * ω)‖ := norm_mul _ _
      _ = Real.exp (-(|a| * y ^ 2)) * ‖G (y * I * ω)‖ ^ 2 := by rw [hH, norm_mul, he]; ring
      _ ≤ Real.exp (-(|a| * y ^ 2)) * (Cf * Real.exp (K * |y|)) ^ 2 := by gcongr
      _ = Cf ^ 2 * Real.exp (-|a| * y ^ 2 + 2 * K * |y|) := by
        rw [mul_pow, ← Real.exp_nat_mul,
          show -|a| * y ^ 2 + 2 * K * |y| = -(|a| * y ^ 2) + ((2 : ℕ) * (K * |y|)) by
            push_cast; ring, Real.exp_add]
        ring
      _ ≤ Cf ^ 2 * Real.exp (K ^ 2 / |a|) := by
        gcongr
        exact quad_le (abs_pos.2 ha)
  -- Superexponential decay on the positive real axis.
  have hdecay : SuperpolynomialDecay atTop Real.exp fun x : ℝ => ‖k x‖ := by
    intro n
    have hq : Tendsto (fun x : ℝ => (n + 2 * K) * x - |a| * x ^ 2) atTop atBot := by
      have ha' : 0 < |a| / 2 := by positivity
      have h1 : Tendsto (fun x : ℝ => -(|a| / 2 * x ^ 2) + (n + 2 * K) ^ 2 / (2 * |a|)) atTop
          atBot :=
        tendsto_atBot_add_const_right _ _
          (tendsto_neg_atTop_atBot.comp ((tendsto_pow_atTop two_ne_zero).const_mul_atTop ha'))
      refine tendsto_atBot_mono (fun x => ?_) h1
      have hpos : 0 < |a| := abs_pos.2 ha
      have : (n + 2 * K) * x - |a| / 2 * x ^ 2 ≤ (n + 2 * K) ^ 2 / (2 * |a|) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (|a| * x - (n + 2 * K))]
      linarith
    have hlim : Tendsto (fun x : ℝ => Cg ^ 2 * Real.exp ((n + 2 * K) * x - |a| * x ^ 2)) atTop
        (𝓝 0) := by
      simpa using (Real.tendsto_exp_atBot.comp hq).const_mul (Cg ^ 2)
    refine squeeze_zero' (Eventually.of_forall fun x => by positivity) ?_ hlim
    filter_upwards [eventually_ge_atTop 0] with x hx
    have := hkre x
    rw [abs_of_nonneg hx] at this
    calc Real.exp x ^ n * ‖k x‖ ≤ Real.exp x ^ n * (Cg ^ 2 * Real.exp (2 * K * x - |a| * x ^ 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = Cg ^ 2 * Real.exp ((n + 2 * K) * x - |a| * x ^ 2) := by
        rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
        congr 2
        ring
  -- Phragmén–Lindelöf: `k = 0` on the closed right half-plane.
  have hk0 := PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay
    hkd.diffContOnCl ⟨1, one_lt_two, 2 * K, IsBigO.of_bound (Cf * Cg)
      (Eventually.of_forall fun s => by
        rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hkb s)⟩
    hdecay ⟨_, hkim⟩
  -- So `G` vanishes near `ω`, hence everywhere.
  have hGz : ∀ z, 0 < (z * ω⁻¹).re → G z = 0 := by
    intro z hz
    have h0 := hk0 (show 0 ≤ (z * ω⁻¹).re from hz.le)
    have hzω : z * ω⁻¹ * ω = z := by field_simp
    simp only [k, Pi.zero_apply, hzω] at h0
    rw [hHG z] at h0
    have hc : cexp (-(a : ℂ) * z ^ 2 * I) ≠ 0 := Complex.exp_ne_zero _
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exact (mul_eq_zero.1 h).resolve_left hc
  have hGnhds : G =ᶠ[𝓝 ω] 0 := by
    have hopen : IsOpen {z : ℂ | 0 < (z * ω⁻¹).re} :=
      isOpen_lt continuous_const (continuous_re.comp (continuous_id.mul continuous_const))
    have hmem : ω ∈ {z : ℂ | 0 < (z * ω⁻¹).re} := by
      rw [Set.mem_ofPred_eq, mul_inv_cancel₀ hω0, one_re]
      exact one_pos
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact hGz z hz
  have hGa : AnalyticOnNhd ℂ G univ := fun z _ => hGd.analyticAt z
  have hG0 := hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (mem_univ ω) hGnhds
  exact ae_eq_zero_of_fourier_eq_zero_of_lt_abs hf hfR (S := 0) fun ξ _ => by
    rw [hGf, hG0 (mem_univ _), Pi.zero_apply]

end Real
