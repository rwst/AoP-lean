/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.PositiveTrace
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong convergence against a Hilbert–Schmidt operator

An operator `S` on a Hilbert space is Hilbert–Schmidt when `∑ᵢ ‖S eᵢ‖² < ∞` for a Hilbert basis
`eᵢ`, that is, when `tr (S S†) < ∞`. Composing with such an `S` turns strong convergence into
norm convergence: if the operators `D a` are uniformly bounded and `D a x → 0` for every `x`, then
`‖D a S‖ → 0`. The proof bounds `‖D a S‖² ≤ ∑ᵢ ‖D a (S eᵢ)‖²` and applies dominated convergence
to the sum (Tannery's theorem).

Consequently a strongly differentiable family of operators that is Lipschitz in operator norm
becomes differentiable in operator norm after composing with a Hilbert–Schmidt operator. For a
density operator `ρ`, `√ρ` is Hilbert–Schmidt.

## Main results

* `ContinuousLinearMap.sq_norm_le_tsum_norm_apply_sq`: `‖R‖² ≤ ∑ᵢ ‖R eᵢ‖²`.
* `ContinuousLinearMap.tendsto_mul_of_tendsto_apply`: uniformly bounded strong convergence to `0`
  gives `D a S → 0` in norm.
* `ContinuousLinearMap.hasDerivAt_mul_of_hasDerivAt_apply`: `t ↦ F t S` is differentiable in
  operator norm.
-/

@[expose] public section

open Filter Topology
open scoped ENNReal

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

/-- The operator norm is at most the Hilbert–Schmidt norm: `‖R‖² ≤ ∑ᵢ ‖R eᵢ‖²`. -/
theorem sq_norm_le_tsum_norm_apply_sq {R : E →L[ℂ] E} (hR : posTrace (R * star R) ≠ ⊤)
    (b : HilbertBasis ι ℂ E) : ‖R‖ ^ 2 ≤ ∑' i, ‖R (b i)‖ ^ 2 := by
  have h := norm_le_toReal_posTrace (mul_star_self_nonneg R) hR
  rw [CStarRing.norm_self_mul_star, posTrace_mul_star R b,
    ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top] at h
  simpa only [sq, ENNReal.toReal_ofReal (mul_self_nonneg _)] using h

/-- **Strong convergence against a Hilbert–Schmidt operator is norm convergence.** If the
operators `D a` are eventually bounded by `C` and `D a x → 0` for every `x`, and
`tr (S S†) < ∞`, then `D a S → 0` in operator norm. -/
theorem tendsto_mul_of_tendsto_apply {α : Type*} {l : Filter α} {D : α → E →L[ℂ] E}
    {S : E →L[ℂ] E} (hS : posTrace (S * star S) ≠ ⊤) {C : ℝ} (hC : ∀ᶠ a in l, ‖D a‖ ≤ C)
    (hD : ∀ x, Tendsto (fun a => D a x) l (𝓝 0)) : Tendsto (fun a => D a * S) l (𝓝 0) := by
  set b := posTraceBasis E
  have hSb := hS
  rw [posTrace_mul_star S b] at hSb
  have hsum : Summable fun i => C ^ 2 * ‖S (b i)‖ ^ 2 := by
    refine (ENNReal.summable_toReal hSb).mul_left (C ^ 2) |>.congr fun i => ?_
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
  have hle : ∀ a, ‖D a‖ ≤ C → ∀ i, ‖D a (S (b i))‖ ^ 2 ≤ C ^ 2 * ‖S (b i)‖ ^ 2 :=
    fun a ha i => by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))) 2
  have hlim : Tendsto (fun a => ∑' i, ‖D a (S (b i))‖ ^ 2) l (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (f := fun a i => ‖D a (S (b i))‖ ^ 2)
      (g := fun _ => 0) hsum (fun i => by simpa using ((hD (S (b i))).norm.pow 2))
      (hC.mono fun a ha i => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact hle a ha i)
    simpa only [tsum_zero] using this
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hC.mono fun a ha => ?_) (by simpa using (Real.continuous_sqrt.tendsto 0).comp hlim)
  have hfin : posTrace (D a * S * star (D a * S)) ≠ ⊤ := by
    rw [posTrace_mul_star _ b]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C ^ 2)) hSb)
      ((tsum_le_tsum fun i => ?_).trans ENNReal.tsum_mul_left.le)
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hle a ha i)
  rw [← abs_norm]
  exact Real.abs_le_sqrt (sq_norm_le_tsum_norm_apply_sq hfin b)

/-- **Norm derivative against a Hilbert–Schmidt operator.** If `t ↦ F t x` has derivative
`F' x` at `t` for every `x`, and `‖F s - F t‖ ≤ C |s - t|` near `t`, then `s ↦ F s S` is
differentiable at `t` in operator norm for every `S` with `tr (S S†) < ∞`. -/
theorem hasDerivAt_mul_of_hasDerivAt_apply {F : ℝ → E →L[ℂ] E} {F' S : E →L[ℂ] E} {t C : ℝ}
    (hF : ∀ x, HasDerivAt (F · x) (F' x) t) (hC : ∀ᶠ s in 𝓝 t, ‖F s - F t‖ ≤ C * |s - t|)
    (hS : posTrace (S * star S) ≠ ⊤) : HasDerivAt (fun s => F s * S) (F' * S) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  set D : ℝ → E →L[ℂ] E := fun s => slope F t s - F'
  have hD : Tendsto (fun s => D s * S) (𝓝[≠] t) (𝓝 0) := by
    refine tendsto_mul_of_tendsto_apply hS (C := C + ‖F'‖) ?_ fun x => ?_
    · filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with s hs hst
      refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
      have hpos : 0 < |s - t| := abs_pos.mpr (sub_ne_zero.mpr hst)
      rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs, inv_mul_le_iff₀ hpos,
        mul_comm]
      exact hs
    · have h := (hF x).tendsto_slope.sub_const (F' x)
      rw [sub_self] at h
      refine h.congr fun s => ?_
      simp only [D, slope_def_module, sub_apply, smul_apply]
  have h := hD.add_const (F' * S)
  rw [zero_add] at h
  refine h.congr fun s => ?_
  simp only [D, slope_def_module, sub_mul, smul_mul_assoc, sub_add_cancel]

end ContinuousLinearMap
