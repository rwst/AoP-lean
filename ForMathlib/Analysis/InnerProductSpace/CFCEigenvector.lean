/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# The continuous functional calculus on eigenvectors

For a self-adjoint operator `T` on a complex Hilbert space of any dimension, an eigenvector `v`
with `T v = μ v` and a function `g` continuous on the spectrum, `g(T) v = g(μ) v`.

With `h = g - g(μ)`, which vanishes at `μ`, continuity and compactness of the spectrum give
`h(t)² ≤ ε + C (t - μ)²` on the spectrum for every `ε > 0`. Monotonicity of the functional
calculus gives `h(T)² ≤ ε + C (T - μ)²`, and evaluating at `v` gives `‖h(T) v‖² ≤ ε ‖v‖²`.

## Main results

* `ContinuousLinearMap.cfc_apply_eq_smul_of_apply_eq_smul`
-/

@[expose] public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The functional calculus on an eigenvector**: if `T v = μ v`, then `g(T) v = g(μ) v` for
every `g` continuous on the spectrum of the self-adjoint operator `T`. -/
theorem cfc_apply_eq_smul_of_apply_eq_smul {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {g : ℝ → ℝ}
    (hg : ContinuousOn g (spectrum ℝ T)) {v : E} {μ : ℝ} (hv : T v = (μ : ℂ) • v) :
    cfc g T v = (g μ : ℂ) • v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  set a : E →L[ℂ] E := T - algebraMap ℝ (E →L[ℂ] E) μ
  have hav : a v = 0 := by
    rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, hv,
      Complex.coe_smul,
      sub_self]
  have hμ : μ ∈ spectrum ℝ T := by
    rw [spectrum.mem_iff]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_left_inv
    apply hv0
    have h1 : (algebraMap ℝ (E →L[ℂ] E) μ - T) v = 0 := by
      rw [← neg_sub, neg_apply, hav, neg_zero]
    calc v = (b * (algebraMap ℝ (E →L[ℂ] E) μ - T)) v := by rw [hb, one_apply_eq_self]
      _ = b ((algebraMap ℝ (E →L[ℂ] E) μ - T) v) := rfl
      _ = 0 := by rw [h1, map_zero]
  set h : ℝ → ℝ := fun t => g t - g μ
  have hh : ContinuousOn h (spectrum ℝ T) := hg.sub continuousOn_const
  obtain ⟨M, hM⟩ :=
    (ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) T).exists_bound_of_continuousOn hh
  set B := cfc h T
  have hB : IsSelfAdjoint B := cfc_predicate h T
  have key : ∀ ε > 0, ‖B v‖ ^ 2 ≤ ε * ‖v‖ ^ 2 := by
    intro ε hε
    obtain ⟨δ, hδ, hδh⟩ := Metric.continuousWithinAt_iff.mp (hh μ hμ) (√ε) (Real.sqrt_pos.mpr hε)
    set C := M ^ 2 / δ ^ 2
    have hC : 0 ≤ C := by positivity
    have hbound : ∀ t ∈ spectrum ℝ T, h t ^ 2 ≤ ε + C * (t - μ) ^ 2 := by
      intro t ht
      by_cases htμ : dist t μ < δ
      · have h1 := hδh ht htμ
        simp only [h, sub_self, Real.dist_eq, sub_zero] at h1
        have h2 : h t ^ 2 < ε := by
          calc h t ^ 2 = |g t - g μ| ^ 2 := (sq_abs _).symm
            _ < √ε ^ 2 := by gcongr
            _ = ε := Real.sq_sqrt hε.le
        nlinarith [sq_nonneg (t - μ)]
      · push Not at htμ
        rw [Real.dist_eq] at htμ
        have hM' : h t ^ 2 ≤ M ^ 2 := by
          have h1 := hM t ht
          rw [Real.norm_eq_abs] at h1
          nlinarith [abs_nonneg (h t), sq_abs (h t)]
        have hd2 : δ ^ 2 ≤ (t - μ) ^ 2 := by nlinarith [abs_nonneg (t - μ), sq_abs (t - μ)]
        have h3 : M ^ 2 ≤ C * (t - μ) ^ 2 := by
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg M]
        linarith
    have hmono : cfc (fun t => h t ^ 2) T ≤ cfc (fun t => ε + C * (t - μ) ^ 2) T :=
      cfc_mono hbound (hh.pow 2)
    have hpoly : cfc (fun t => ε + C * (t - μ) ^ 2) T =
        algebraMap ℝ (E →L[ℂ] E) ε + C • a ^ 2 := by
      rw [cfc_add (a := T) (fun _ => ε) (fun t => C * (t - μ) ^ 2), cfc_const ε T,
        cfc_const_mul C (fun t => (t - μ) ^ 2) T, cfc_pow (fun t => t - μ) 2 T,
        cfc_sub (fun t => t) (fun _ => μ) T, cfc_id' ℝ T, cfc_const μ T]
    have hsq : cfc (fun t => h t ^ 2) T = B * B := by
      rw [cfc_pow h 2 T hh, sq]
    have hle := (nonneg_iff_isPositive.mp (sub_nonneg.mpr hmono)).re_inner_nonneg_right v
    rw [sub_apply, inner_sub_right, map_sub, sub_nonneg, hpoly, hsq] at hle
    have hl : RCLike.re ⟪v, (B * B) v⟫_ℂ = ‖B v‖ ^ 2 := by
      change RCLike.re ⟪v, B (B v)⟫_ℂ = _
      have e : ⟪B v, B v⟫_ℂ = ⟪v, B (B v)⟫_ℂ := hB.isSymmetric v (B v)
      rw [← e]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hr : RCLike.re ⟪v, (algebraMap ℝ (E →L[ℂ] E) ε + C • a ^ 2) v⟫_ℂ = ε * ‖v‖ ^ 2 := by
      have ha2 : (a ^ 2) v = 0 := by
        rw [sq]
        change a (a v) = 0
        rw [hav, map_zero]
      rw [add_apply, smul_apply, ha2, smul_zero, add_zero, Algebra.algebraMap_eq_smul_one,
        smul_apply, one_apply_eq_self, ← Complex.coe_smul, inner_smul_right,
        inner_self_eq_norm_sq_to_K]
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
      norm_cast
    rw [hl, hr] at hle
    exact hle
  have hBv : B v = 0 := by
    have hpos : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.mpr hv0; positivity
    have h0 : ‖B v‖ ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      have h1 := key (‖B v‖ ^ 2 / (2 * ‖v‖ ^ 2)) (by positivity)
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at h1
      nlinarith
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h0 (sq_nonneg _)))
  have hgh : cfc g T = cfc (fun t => h t + g μ) T := cfc_congr fun t _ => by simp [h]
  rw [hgh, cfc_add (a := T) h (fun _ => g μ) hh, cfc_const (g μ) T, add_apply, hBv, zero_add,
    Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, Complex.coe_smul]

end ContinuousLinearMap
