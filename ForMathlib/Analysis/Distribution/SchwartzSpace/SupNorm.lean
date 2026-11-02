/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.WeightedPlancherel

/-!
# A Sobolev bound for the values of a Schwartz function

On a finite-dimensional real inner product space `V` of dimension `n`, the values of a Schwartz
function are bounded by `L²` norms of the function and of its derivatives of order `N > n/2`
along an orthonormal basis. This is the Sobolev embedding `H^N ⊆ L^∞`, for Schwartz functions.

The proof writes `g = 𝓕 (𝓕⁻ g)`, so that `‖g x‖ ≤ ∫ ‖𝓕⁻ g‖`, and bounds that integral with
`SchwartzMap.exists_integral_norm_fourierInv_le` (TauCeti), the `L¹` bound for inverse Fourier
transforms from the weighted Plancherel identity.

## Main results

* `SchwartzMap.exists_norm_le_toLp_two`: for `2N > n`, there is `C` with
  `‖g x‖ ≤ C (‖g‖_{L²} + ∑ᵢ ‖∂_{bᵢ}^N g‖_{L²})` for all `g` and `x`.
-/

open scoped FourierTransform SchwartzMap LineDeriv
open FourierTransform MeasureTheory Module

public section

namespace SchwartzMap

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Sobolev bound: for `2N > dim V`, the values of a Schwartz function are bounded by the `L²`
norms of the function and of its `N`-th derivatives along an orthonormal basis. -/
theorem exists_norm_le_toLp_two {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V) {N : ℕ}
    (hN : finrank ℝ V < 2 * N) :
    ∃ C, 0 ≤ C ∧ ∀ (g : 𝓢(V, H)) (x : V),
      ‖g x‖ ≤ C * (‖g.toLp 2‖ + ∑ i, ‖((∂_{b i})^[N] g).toLp 2‖) := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_norm_fourierInv_le (H := H) b hN
  refine ⟨C, hC0, fun g x => ?_⟩
  have h1 := hC g 1 one_pos
  simp only [Real.one_rpow, one_mul] at h1
  have key : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → √(∑ i, a i ^ 2) ≤ ∑ i, a i := fun a ha =>
    Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun i _ => ha i,
      Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => ha i⟩
  have hsq := key (fun i => ‖((∂_{b i})^[N] g).toLp 2‖) fun _ => norm_nonneg _
  have h2 := norm_fourier_apply_le_toLp_one (𝓕⁻ g) x
  rw [fourier_fourierInv_eq, norm_toLp_one] at h2
  have h3 : ‖g.toLp 2‖ + √(∑ i, ‖((∂_{b i})^[N] g).toLp 2‖ ^ 2) ≤
      ‖g.toLp 2‖ + ∑ i, ‖((∂_{b i})^[N] g).toLp 2‖ := add_le_add_right hsq _
  exact h2.trans (h1.trans (mul_le_mul_of_nonneg_left h3 hC0))

end SchwartzMap
