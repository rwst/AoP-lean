/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LocallyConvex.Barrelled

/-!
# Strong derivatives of operator families

A family `T t` of operators on a Banach space is *strongly differentiable* at `t₀` when
`t ↦ T t x` is differentiable at `t₀` for every vector `x`. By the Banach–Steinhaus theorem the
derivatives `x ↦ (T · x)'(t₀)` then form a bounded operator. For a family of unitaries on a Hilbert
space with `U t₀ = 1`, that operator is skew-adjoint.

## Main results

* `ContinuousLinearMap.exists_hasDerivAt_apply`: the strong derivative is a bounded operator.
* `star_eq_neg_of_hasDerivAt_apply_of_mem_unitary`: the strong derivative at `t₀` of a family of
  unitaries with `U t₀ = 1` is skew-adjoint.
-/

@[expose] public section

open scoped InnerProductSpace Topology
open Filter

/-- **The strong derivative is bounded.** If `t ↦ T t x` is differentiable at `t₀` for every `x`,
then the derivatives are the values of one bounded operator. -/
theorem ContinuousLinearMap.exists_hasDerivAt_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {T : ℝ → E →L[ℂ] F} {t₀ : ℝ} (h : ∀ x, DifferentiableAt ℝ (fun t => T t x) t₀) :
    ∃ A : E →L[ℂ] F, ∀ x, HasDerivAt (fun t => T t x) (A x) t₀ := by
  let g : ℝ → E →L[ℂ] F := fun s => s⁻¹ • (T (t₀ + s) - T t₀)
  have hg : Tendsto (fun s x => g s x) (𝓝[≠] 0) (𝓝 fun x => deriv (fun t => T t x) t₀) :=
    tendsto_pi_nhds.2 fun x => by
      simpa [g] using hasDerivAt_iff_tendsto_slope_zero.1 (h x).hasDerivAt
  exact ⟨continuousLinearMapOfTendsto g hg, fun x => (h x).hasDerivAt⟩

/-- The strong derivative at `t₀` of a family of unitaries with `U t₀ = 1` is skew-adjoint. -/
theorem star_eq_neg_of_hasDerivAt_apply_of_mem_unitary {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {U : ℝ → H →L[ℂ] H} {A : H →L[ℂ] H} {t₀ : ℝ}
    (hU : ∀ t, U t ∈ unitary (H →L[ℂ] H)) (h₀ : U t₀ = 1)
    (hA : ∀ x, HasDerivAt (fun t => U t x) (A x) t₀) : star A = -A := by
  refine (((-A).eq_adjoint_iff A).2 fun x y => ?_).symm
  have h1 := (hA x).inner ℂ (hA y)
  have h2 : (fun t => ⟪U t x, U t y⟫_ℂ) = fun _ => ⟪x, y⟫_ℂ :=
    funext fun t => Unitary.inner_map_map ⟨U t, hU t⟩ x y
  rw [h2, h₀] at h1
  have := h1.unique (hasDerivAt_const t₀ _)
  simp only [one_apply_eq_self] at this
  rw [neg_apply, inner_neg_left, neg_eq_iff_add_eq_zero, add_comm]
  exact this
