/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Complex.Norm

/-!
# A complex number is determined by its distances to three points

Three circles centred at `0`, `c` and `-I * c` with `c ≠ 0` meet in at most one point: if `z` and
`w` have the same distances to `0`, `c` and `-I * c`, then `z = w`. The first two distances fix
`re (z * conj c)`, the first and third fix `im (z * conj c)`.

For real `c` there is a conjugate form: if the third condition is replaced by
`‖z + I * c‖ = ‖w - I * c‖`, then `w = conj z`.

This is the rigidity step in proofs of Wigner's theorem on symmetry transformations.

## Main results

* `Complex.eq_of_norm_eq_of_norm_sub_eq_of_norm_add_I_mul_eq`: the three-circle lemma.
* `Complex.eq_conj_of_norm_eq_of_norm_sub_eq_of_norm_add_I_mul_eq`: its conjugate form for real
  centres.
* `Complex.eq_I_or_eq_neg_I_of_norm_eq_one_of_norm_one_sub`: the two-circle case `‖z‖ = 1`,
  `‖1 - z‖ = √2`.
-/

public section

open ComplexConjugate

namespace Complex

/-- If `z` and `w` have the same distances to `0`, `c` and `-I * c`, and `c ≠ 0`, then
`z = w`. -/
theorem eq_of_norm_eq_of_norm_sub_eq_of_norm_add_I_mul_eq {z w c : ℂ} (hc : c ≠ 0)
    (h₀ : ‖z‖ = ‖w‖) (h₁ : ‖z - c‖ = ‖w - c‖) (h₂ : ‖z + I * c‖ = ‖w + I * c‖) : z = w := by
  have sq : ∀ {u v : ℂ}, ‖u‖ = ‖v‖ → normSq u = normSq v := fun h => by
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq, h]
  have h₀' := sq h₀
  have h₁' := sq h₁
  have h₂' := sq h₂
  rw [normSq_sub, normSq_sub, h₀'] at h₁'
  have hIc : conj (I * c) = -I * conj c := by simp
  rw [normSq_add, normSq_add, h₀', hIc] at h₂'
  refine mul_right_cancel₀ ((map_ne_zero _).2 hc) (ext (by linarith) ?_)
  have hI : ∀ u : ℂ, (u * (-I * conj c)).re = (u * conj c).im := fun u => by
    simp; ring
  rw [hI, hI] at h₂'
  linarith

/-- Conjugate form of the three-circle lemma: if `c` is real and non-zero, `‖z‖ = ‖w‖`,
`‖z - c‖ = ‖w - c‖` and `‖z + I * c‖ = ‖w - I * c‖`, then `w = conj z`. -/
theorem eq_conj_of_norm_eq_of_norm_sub_eq_of_norm_add_I_mul_eq {z w : ℂ} {c : ℝ} (hc : c ≠ 0)
    (h₀ : ‖z‖ = ‖w‖) (h₁ : ‖z - c‖ = ‖w - c‖) (h₂ : ‖z + I * c‖ = ‖w - I * c‖) :
    w = conj z := by
  have key : z = conj w := by
    refine eq_of_norm_eq_of_norm_sub_eq_of_norm_add_I_mul_eq (ofReal_ne_zero.2 hc) ?_ ?_ ?_
    · rw [h₀, norm_conj]
    · rw [h₁, ← norm_conj (w - c), map_sub, conj_ofReal]
    · rw [h₂, ← norm_conj (w - I * c), map_sub, map_mul, conj_I, conj_ofReal, neg_mul,
        sub_neg_eq_add]
  rw [key, conj_conj]

/-- The unit circle meets the circle of radius `√2` around `1` in `I` and `-I`. -/
theorem eq_I_or_eq_neg_I_of_norm_eq_one_of_norm_one_sub {z : ℂ} (h₀ : ‖z‖ = 1)
    (h₁ : ‖1 - z‖ = √2) : z = I ∨ z = -I := by
  have h₀' : normSq z = 1 := by rw [normSq_eq_norm_sq, h₀, one_pow]
  have h₁' : normSq (1 - z) = 2 := by
    rw [normSq_eq_norm_sq, h₁, Real.sq_sqrt zero_le_two]
  rw [normSq_sub, h₀', map_one, one_mul, conj_re] at h₁'
  have hre : z.re = 0 := by linarith
  rw [normSq_apply, hre, zero_mul, zero_add] at h₀'
  rcases mul_self_eq_one_iff.1 h₀' with him | him
  · exact Or.inl (ext hre (by simp [him]))
  · exact Or.inr (ext (by simp [hre]) (by simp [him]))

end Complex
