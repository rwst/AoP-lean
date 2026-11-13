/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Double commutators with a self-adjoint element

Let `x` be a self-adjoint element of a complex C⋆-algebra and `c = x a - a x`. If `c` commutes
with `x`, then `c = 0` (`IsSelfAdjoint.commute_of_commute_commutator`). This is the self-adjoint
case of the Kleinecke–Shirokov theorem, which in general only makes `c` quasinilpotent.

The proof conjugates by the unitaries `exp(i t x)`. Since `c` commutes with `x`, the conjugate is
`exp(i t x) a exp(-i t x) = a + i t c` (`IsSelfAdjoint.exp_smul_mul_mul_exp_smul_neg`), and it has
norm at most `‖a‖`. Hence `|t| ‖c‖ ≤ 2 ‖a‖` for every real `t`, and `c = 0`.

## References

* D. C. Kleinecke, *On operator commutators*, Proc. Amer. Math. Soc. 8 (1957) 535–536.
-/

@[expose] public section

open NormedSpace Complex

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- If `[y, a]` commutes with `y`, then `exp(u y) a exp(-u y) = a + u [y, a]`. -/
theorem Commute.exp_smul_mul_mul_exp_smul_neg {y a : A} (h : Commute y (y * a - a * y)) (u : ℂ) :
    NormedSpace.exp (u • y) * a * NormedSpace.exp (u • -y) = a + u • (y * a - a * y) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
  set d := y * a - a * y
  set E : ℂ → A := fun u => NormedSpace.exp (u • y)
  set E' : ℂ → A := fun u => NormedSpace.exp (u • -y)
  let G : ℂ → A := fun u => E u * a * E' u - u • d
  have hG : ∀ u, HasDerivAt G 0 u := by
    intro u
    have h1 := ((hasDerivAt_exp_smul_const y u).mul_const a).mul
      (hasDerivAt_exp_smul_const' (-y) u)
    have h2 := (hasDerivAt_id u).smul_const d
    convert h1.sub h2 using 1
    · rfl
    have hd : Commute d (E' u) := by
      simpa only [E', smul_neg] using ((h.symm.smul_right u).neg_right).exp_right
    have he : E u * E' u = 1 := by
      change NormedSpace.exp (u • y) * NormedSpace.exp (u • -y) = 1
      rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl _).neg_right, add_neg_cancel,
        NormedSpace.exp_zero]
    have : E u * y * a * E' u + E u * a * (-y * E' u) = E u * d * E' u := by
      simp only [d]
      noncomm_ring
    simp only [one_smul]
    rw [this, mul_assoc, hd.eq, ← mul_assoc, he, one_mul, sub_self]
  have hc := is_const_of_deriv_eq_zero (fun u => (hG u).differentiableAt)
    (fun u => (hG u).deriv) u 0
  simp only [G, E, E', zero_smul, NormedSpace.exp_zero, mul_one, one_mul,
    sub_zero] at hc
  exact sub_eq_iff_eq_add.mp hc

variable [StarRing A] [CStarRing A] [StarModule ℂ A]

/-- **Double commutators with a self-adjoint element**: if `x` is self-adjoint and commutes with
`x a - a x`, then it commutes with `a`. -/
theorem IsSelfAdjoint.commute_of_commute_commutator {x a : A} (hx : IsSelfAdjoint x)
    (h : Commute x (x * a - a * x)) : Commute x a := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim (x * a) (a * x)
  set c := x * a - a * x
  set y := I • x
  have hy : Commute y (y * a - a * y) := by
    have : y * a - a * y = I • c := by
      simp only [y, c, smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [this]
    exact (h.smul_left I).smul_right I
  have hu : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • y) ∈ unitary A := fun t => by
    let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℂ A
    refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ?_
    rw [show (t : ℂ) • y = I • ((t : ℂ) • x) from smul_comm _ _ _]
    exact I_smul_mem_skewAdjoint_iff_isSelfAdjoint.mpr
      ((show IsSelfAdjoint (t : ℂ) from Complex.conj_ofReal t).smul hx)
  have hb : ∀ t : ℝ, |t| * ‖c‖ ≤ 2 * ‖a‖ := by
    intro t
    have he := hy.exp_smul_mul_mul_exp_smul_neg (t : ℂ)
    have hn : ‖NormedSpace.exp ((t : ℂ) • y) * a * NormedSpace.exp ((t : ℂ) • -y)‖ ≤ ‖a‖ := by
      rw [smul_neg, ← neg_smul, ← ofReal_neg]
      refine (norm_mul_le _ _).trans ?_
      rw [CStarRing.norm_of_mem_unitary (hu (-t)), mul_one]
      refine (norm_mul_le _ _).trans ?_
      rw [CStarRing.norm_of_mem_unitary (hu t), one_mul]
    have hd : y * a - a * y = I • c := by
      simp only [y, c, smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [he, hd, smul_smul] at hn
    have h2 : ‖((t : ℂ) * I) • c‖ ≤ ‖a‖ + ‖a‖ := by
      calc ‖((t : ℂ) * I) • c‖ = ‖(a + ((t : ℂ) * I) • c) - a‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖a + ((t : ℂ) * I) • c‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ ‖a‖ + ‖a‖ := by gcongr
    rw [norm_smul, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h2
    linarith
  have hc : c = 0 := by
    by_contra hne
    have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hne
    have := hb ((2 * ‖a‖ + 1) / ‖c‖)
    rw [abs_of_pos (by positivity), div_mul_cancel₀ _ hpos.ne'] at this
    linarith
  exact sub_eq_zero.mp hc
