/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import InconsistentConvergence
public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteReal
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator

/-!
# Inconsistent convergence: the oscillator

The brief reads `ℓ²(ℕ)`, with `|n⟩ = δₙ`, as the state space of the harmonic oscillator, and the
Schwartz sequence space `S(ℕ)` as its Schwartz space. This module makes the reading explicit, in
position space `L²(ℝ)` with `m = ω = ħ = 1`, through the Hermite functions `ψₙ` and their Hilbert
basis of `L²(ℝ)` (`TauCeti.hermiteHilbertBasis`).

* The unitary `U : ℓ²(ℕ) ≃ L²(ℝ)` of the Hermite basis sends `|n⟩` to `ψₙ`
  (`hermiteUnitary_level`), and `ψₙ` solves `-ψₙ''/2 + x²/2 ψₙ = (n + 1/2) ψₙ`: `|n⟩` is the
  oscillator eigenstate with `n` quanta (`oscillator_level`).
* Under `U`, `S(ℕ)`, the sequences with `sup_n (n + 1)^K |xₙ| < ∞` for every `K`, becomes the
  Schwartz space: `U x` is a Schwartz function iff `x` is rapidly decreasing
  (`exists_schwartz_iff`), and Schwartz functions converge in `𝓢(ℝ)` iff their coefficient
  sequences converge in every seminorm `sup_n (n + 1)^K |xₙ|` (`tendsto_schwartz_iff`). The
  space `S(ℕ)` is described by these seminorms; it is not constructed as a topological space.
* So the states of the brief are Schwartz functions, `U eʲ ∈ 𝓢(ℝ)` (`exists_schwartz_e`), and
  `U eʲ → ψ₀` in `L²(ℝ)` (`tendsto_hermiteUnitary_e`), but the Schwartz functions `U eʲ` have no
  limit in `𝓢(ℝ)` (`not_tendsto_schwartz_e`).

The equivalence of Schwartz functions and rapidly decreasing Hermite coefficients, with its
topology, is `SchwartzMap.exists_toLp_eq_iff` and `SchwartzMap.tendsto_iff_inner_hermiteFunctionLp`
in `ForMathlib`, transferred from the multi-index Hermite expansions on `ℝ¹`.

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.
-/

open MeasureTheory Filter Topology TauCeti
open scoped SchwartzMap InnerProductSpace

@[expose] public noncomputable section

namespace InconsistentConvergence

/-- The unitary `U : ℓ²(ℕ) ≃ L²(ℝ)` of the Hermite basis, `U |n⟩ = ψₙ`. -/
def hermiteUnitary : H ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) := (hermiteHilbertBasis ℂ).repr.symm

theorem hermiteUnitary_level (n : ℕ) : hermiteUnitary (level n) = hermiteFunctionLp ℂ n := by
  rw [hermiteUnitary, level, HilbertBasis.repr_symm_single, coe_hermiteHilbertBasis]

/-- The coordinates of `U⁻¹ g` are the Hermite coefficients `⟪ψₙ, g⟫` of `g`. -/
theorem hermiteUnitary_symm_apply (g : Lp ℂ 2 (volume : Measure ℝ)) (n : ℕ) :
    hermiteUnitary.symm g n = ⟪hermiteFunctionLp ℂ n, g⟫_ℂ := by
  rw [hermiteUnitary, LinearIsometryEquiv.symm_symm, hermiteHilbertBasis_repr_apply]

/-- **The oscillator.** `U |n⟩` is the Hermite function `ψₙ`, which solves the stationary
Schrödinger equation of the harmonic oscillator, `-ψₙ''/2 + x²/2 ψₙ = (n + 1/2) ψₙ`. -/
theorem oscillator_level (n : ℕ) :
    (hermiteUnitary (level n) : ℝ → ℂ) =ᵐ[volume] (fun x => (hermiteFunction n x : ℂ)) ∧
      ∀ x : ℝ, -deriv (deriv (hermiteFunction n)) x / 2 + x ^ 2 / 2 * hermiteFunction n x =
        (n + 1 / 2) * hermiteFunction n x := by
  refine ⟨?_, fun x => ?_⟩
  · rw [hermiteUnitary_level]
    filter_upwards [coeFn_hermiteFunctionLp (𝕜 := ℂ) n] with x hx
    simpa using hx
  · linear_combination hermiteFunction_oscillator n x / 2

/-- **`S(ℕ)` becomes the Schwartz space.** `U x` is a Schwartz function iff `x` is rapidly
decreasing, `sup_n (n + 1)^K |xₙ| < ∞` for every `K`. -/
theorem exists_schwartz_iff (x : H) :
    (∃ f : 𝓢(ℝ, ℂ), f.toLp 2 = hermiteUnitary x) ↔
      ∀ K : ℕ, ∃ C : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) ^ K * ‖x n‖ ≤ C := by
  rw [SchwartzMap.exists_toLp_eq_iff]
  simp only [← hermiteUnitary_symm_apply, LinearIsometryEquiv.symm_apply_apply]

/-- **The topology of `S(ℕ)` becomes that of `𝓢(ℝ)`.** Schwartz functions `f j` converge to `g`
in `𝓢(ℝ)` iff the coefficient sequences `U⁻¹ (f j)` converge to `U⁻¹ g` in every seminorm
`sup_n (n + 1)^K |xₙ|` of `S(ℕ)`. -/
theorem tendsto_schwartz_iff {α : Type*} {l : Filter α} {f : α → 𝓢(ℝ, ℂ)} {g : 𝓢(ℝ, ℂ)} :
    Tendsto f l (𝓝 g) ↔ ∀ K : ℕ, ∀ ε > 0, ∀ᶠ j in l, ∀ n : ℕ,
      ((n : ℝ) + 1) ^ K *
        ‖hermiteUnitary.symm ((f j).toLp 2) n - hermiteUnitary.symm (g.toLp 2) n‖ ≤ ε := by
  rw [SchwartzMap.tendsto_iff_inner_hermiteFunctionLp]
  have h : ∀ j n, ⟪hermiteFunctionLp ℂ n, (f j - g).toLp 2⟫_ℂ =
      hermiteUnitary.symm ((f j).toLp 2) n - hermiteUnitary.symm (g.toLp 2) n := by
    intro j n
    have hsub : (f j - g).toLp 2 (volume : Measure ℝ) =
        (f j).toLp 2 volume - g.toLp 2 volume := by
      simpa using map_sub (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)) (f j) g
    rw [hermiteUnitary_symm_apply, hermiteUnitary_symm_apply, ← inner_sub_right, hsub]
  simp only [h]

/-- Every `U eʲ` is a Schwartz function, since `eʲ` is finitely supported. -/
theorem exists_schwartz_e (j : ℕ) : ∃ f : 𝓢(ℝ, ℂ), f.toLp 2 = hermiteUnitary (e j) := by
  rw [exists_schwartz_iff]
  intro K
  refine ⟨((j : ℝ) + 1) ^ K * (‖(amp₀ j : ℂ)‖ + ‖(ampⱼ j : ℂ)‖), fun n => ?_⟩
  by_cases hn : n = 0 ∨ n = j
  · have hnj : ((n : ℝ) + 1) ^ K ≤ ((j : ℝ) + 1) ^ K := by
      have : (n : ℝ) ≤ j := by rcases hn with rfl | rfl <;> simp
      gcongr
    refine mul_le_mul hnj ?_ (norm_nonneg _) (by positivity)
    rw [e_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
    · rw [norm_mul]
      split_ifs <;> simp
  · simp only [not_or] at hn
    rw [e_apply_of_ne hn.1 hn.2, norm_zero, mul_zero]
    positivity

/-- `U eʲ → U |0⟩ = ψ₀` in `L²(ℝ)`. -/
theorem tendsto_hermiteUnitary_e :
    Tendsto (fun j => hermiteUnitary (e j)) atTop (𝓝 (hermiteFunctionLp ℂ 0)) := by
  rw [← hermiteUnitary_level]
  exact (hermiteUnitary.continuous.tendsto _).comp tendsto_e

/-- **No limit in `𝓢(ℝ)`.** The Schwartz functions `U eʲ` converge to `ψ₀` in `L²(ℝ)`, but they
have no limit in `𝓢(ℝ)`. -/
theorem not_tendsto_schwartz_e :
    ¬ ∃ (φ : ℕ → 𝓢(ℝ, ℂ)) (g : 𝓢(ℝ, ℂ)),
      (∀ j, (φ j).toLp 2 = hermiteUnitary (e j)) ∧ Tendsto φ atTop (𝓝 g) := by
  rintro ⟨φ, g, hφ, hlim⟩
  have hL2 : Tendsto (fun j => (φ j).toLp 2) atTop (𝓝 (g.toLp 2)) := by
    have := ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).continuous.tendsto g).comp hlim
    simpa only [Function.comp_def, SchwartzMap.toLpCLM_apply] using this
  have hg : g.toLp 2 = hermiteUnitary ground := by
    refine tendsto_nhds_unique hL2 ?_
    simp only [hφ]
    exact (hermiteUnitary.continuous.tendsto _).comp tendsto_e
  obtain ⟨j, hj, hj1⟩ := ((tendsto_schwartz_iff.1 hlim 1 1 one_pos).and
    (eventually_ge_atTop 1)).exists
  have hj0 : j ≠ 0 := by omega
  have h := hj j
  have ha0 : 0 ≤ ampⱼ j := Real.sqrt_nonneg _
  rw [hφ, hg, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply,
    e_apply_self hj0, level_apply] at h
  simp only [hj0, ite_false, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha0,
    pow_one] at h
  have ha : ampⱼ j ^ 2 * j = 1 := by
    rw [ampⱼ_sq]
    field_simp
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  nlinarith [mul_le_mul h h (by positivity) zero_le_one]

end InconsistentConvergence
