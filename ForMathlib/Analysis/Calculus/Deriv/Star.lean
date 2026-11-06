/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Derivatives of unitary paths in a normed star algebra

## Main results

* `star_eq_neg_of_hasDerivAt_of_mem_unitary`: the derivative at `t₀` of a path of unitaries with
  `U t₀ = 1` is skew-adjoint;
* `star_mul_star_eq_neg_of_hasDerivAt_of_mem_unitary`: for any `U t₀`, `U'(t₀) U(t₀)†` is
  skew-adjoint;
* `star_mul_self_eq_of_hasDerivAt`: if `U' = X U` with `X t` skew-adjoint, then `U† U` is
  constant. With `X t = (iħ)⁻¹ H t` this says that the Schrödinger equation preserves isometries.
-/

@[expose] public section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [StarRing 𝔸] [StarModule ℝ 𝔸]
  [ContinuousStar 𝔸]

theorem star_eq_neg_of_hasDerivAt_of_mem_unitary {U : ℝ → 𝔸} {A : 𝔸} {t₀ : ℝ}
    (hU : ∀ t, U t ∈ unitary 𝔸) (h₀ : U t₀ = 1) (hA : HasDerivAt U A t₀) : star A = -A := by
  have h1 : HasDerivAt (fun t => star (U t) * U t) (star A * U t₀ + star (U t₀) * A) t₀ :=
    hA.star.mul hA
  have h2 : (fun t => star (U t) * U t) = fun _ => 1 :=
    funext fun t => (Unitary.mem_iff.mp (hU t)).1
  rw [h2] at h1
  have := h1.unique (hasDerivAt_const t₀ 1)
  rw [h₀, star_one, mul_one, one_mul] at this
  exact eq_neg_of_add_eq_zero_left this

theorem star_mul_star_eq_neg_of_hasDerivAt_of_mem_unitary {U : ℝ → 𝔸} {A : 𝔸} {t₀ : ℝ}
    (hU : ∀ t, U t ∈ unitary 𝔸) (hA : HasDerivAt U A t₀) :
    star (A * star (U t₀)) = -(A * star (U t₀)) := by
  have h1 : HasDerivAt (fun t => star (U t) * U t) (star A * U t₀ + star (U t₀) * A) t₀ :=
    hA.star.mul hA
  have h2 : (fun t => star (U t) * U t) = fun _ => 1 :=
    funext fun t => (Unitary.mem_iff.mp (hU t)).1
  rw [h2] at h1
  have h := eq_neg_of_add_eq_zero_left (h1.unique (hasDerivAt_const t₀ 1))
  have hu := (Unitary.mem_iff.mp (hU t₀)).2
  calc star (A * star (U t₀)) = U t₀ * (star A * U t₀) * star (U t₀) := by
        simp only [star_mul, star_star, mul_assoc, hu, mul_one]
    _ = -(A * star (U t₀)) := by
        rw [h]
        simp only [mul_neg, neg_mul, ← mul_assoc, hu, one_mul]

theorem star_mul_self_eq_of_hasDerivAt {U X : ℝ → 𝔸} (hX : ∀ t, star (X t) = -X t)
    (hU : ∀ t, HasDerivAt U (X t * U t) t) (s t : ℝ) :
    star (U t) * U t = star (U s) * U s := by
  have hd : ∀ t, HasDerivAt (fun s => star (U s) * U s) 0 t := by
    intro t
    convert (hU t).star.mul (hU t) using 1
    rw [star_mul, hX, mul_neg, neg_mul, mul_assoc, neg_add_cancel]
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t s
