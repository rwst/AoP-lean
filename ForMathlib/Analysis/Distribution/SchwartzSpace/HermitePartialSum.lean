/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteReal
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Schwartz

/-!
# Hermite expansions converge in `𝓢(ℝ)`

The partial sums `Sₘ f = ∑_{n < m} ⟪ψₙ, f⟫ ψₙ` of the Hermite expansion of a Schwartz function
`f` on `ℝ` converge to `f` in the Schwartz topology. So the Hermite functions span a dense
subspace of `𝓢(ℝ)`.

The coefficients of `Sₘ f - f` are `0` below `m` and `-⟪ψₙ, f⟫` from `m` on, and the latter are
rapidly decreasing (`SchwartzMap.exists_toLp_eq_iff`); convergence in `𝓢(ℝ)` is convergence of
the coefficients in every weighted supremum (`SchwartzMap.tendsto_iff_inner_hermiteFunctionLp`).

## Main definitions

* `SchwartzMap.hermite n`: the Hermite function `ψₙ` as a complex Schwartz function;
* `SchwartzMap.hermiteSum m f`: the partial sum `∑_{n < m} ⟪ψₙ, f⟫ ψₙ`.

## Main results

* `SchwartzMap.toLp_hermite`: `ψₙ` is the `n`-th vector of the Hermite basis of `L²(ℝ)`;
* `SchwartzMap.tendsto_hermiteSum`: `Sₘ f → f` in `𝓢(ℝ)`.

## References

* B. Simon, Distributions and their Hermite expansions, J. Math. Phys. 12 (1971) 140–148.
-/

open Filter Topology MeasureTheory TauCeti
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace SchwartzMap

/-- The Hermite function `ψₙ`, as a complex Schwartz function. -/
def hermite (n : ℕ) : 𝓢(ℝ, ℂ) :=
  bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)
    (Function.HasTemperateGrowth.const (1 : ℂ)) (hermiteSchwartzMap n)

@[simp]
lemma hermite_apply (n : ℕ) (x : ℝ) : hermite n x = (hermiteFunction n x : ℂ) := by
  simp [hermite, bilinLeftCLM_apply]

theorem toLp_hermite (n : ℕ) : (hermite n).toLp 2 = hermiteFunctionLp ℂ n := by
  refine Lp.ext ?_
  filter_upwards [(hermite n).coeFn_toLp 2 volume, coeFn_hermiteFunctionLp (𝕜 := ℂ) n]
    with x h1 h2
  rw [h1, h2, hermite_apply]
  rfl

/-- The partial sum `Sₘ f = ∑_{n < m} ⟪ψₙ, f⟫ ψₙ` of the Hermite expansion. -/
def hermiteSum (m : ℕ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  ∑ n ∈ Finset.range m, ⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ • hermite n

lemma inner_hermiteFunctionLp_toLp_hermiteSum (m n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ⟪hermiteFunctionLp ℂ n, (hermiteSum m f).toLp 2⟫_ℂ =
      if n < m then ⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ else 0 := by
  have ho := (hermiteHilbertBasis ℂ).orthonormal
  rw [coe_hermiteHilbertBasis] at ho
  rw [hermiteSum, ← toLpCLM_apply (𝕜 := ℂ), map_sum, inner_sum]
  simp only [map_smul, toLpCLM_apply, toLp_hermite, inner_smul_right,
    orthonormal_iff_ite.1 ho, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_range]

/-- **The Hermite expansion of a Schwartz function converges in `𝓢(ℝ)`.** -/
theorem tendsto_hermiteSum (f : 𝓢(ℝ, ℂ)) : Tendsto (fun m => hermiteSum m f) atTop (𝓝 f) := by
  rw [tendsto_iff_inner_hermiteFunctionLp]
  intro K ε hε
  obtain ⟨C, hC⟩ := (exists_toLp_eq_iff (f.toLp 2)).1 ⟨f, rfl⟩ (K + 1)
  have hev : ∀ᶠ m : ℕ in atTop, C ≤ ε * ((m : ℝ) + 1) :=
    (tendsto_atTop.1 ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).const_mul_atTop
      hε) C)
  filter_upwards [hev] with m hm n
  rw [← toLpCLM_apply (𝕜 := ℂ), map_sub, inner_sub_right, toLpCLM_apply, toLpCLM_apply,
    inner_hermiteFunctionLp_toLp_hermiteSum]
  split_ifs with hn
  · simp [hε.le]
  · set a := ((n : ℝ) + 1) ^ K * ‖⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ‖
    have ha : 0 ≤ a := by positivity
    have hmn : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (not_lt.1 hn)
    have hCn : a * ((n : ℝ) + 1) ≤ C := by
      have := hC n
      rw [pow_succ] at this
      linarith [show a * ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ K * ((n : ℝ) + 1) *
        ‖⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ‖ by ring]
    rw [zero_sub, norm_neg]
    have h1 : a * ((m : ℝ) + 1) ≤ ε * ((m : ℝ) + 1) :=
      (mul_le_mul_of_nonneg_left hmn ha).trans (hCn.trans hm)
    exact le_of_mul_le_mul_right h1 (by positivity)

end SchwartzMap
