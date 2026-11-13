/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import InconsistentConvergence.NumberOperator
public import ForMathlib.Analysis.InnerProductSpace.UnboundedForm

/-!
# Inconsistent convergence: unbounded observables

The introduction of the brief states that an unbounded operator "is not continuous in its own
domain (i.e. small state changes can correspond to big average position changes)". This module
proves it for expectations: for every densely defined unbounded operator `A` on a complex Hilbert
space, `x ↦ ⟨x|A|x⟩` is discontinuous at every point of `D(A)`
(`LinearPMap.not_continuousAt_inner`, in `ForMathlib`), and so is the normalized expectation
`⟨x|A|x⟩ / ‖x‖²` at every nonzero point (`LinearPMap.not_continuousAt_inner_div`).

* The number operator `N` is unbounded (`exists_lt_norm_numberOp`), so `⟨N⟩` is discontinuous
  at every point of `D(N)` (`not_continuousAt_inner_numberOp`,
  `not_continuousAt_numberExp_domain`), not only at `|0⟩` as in the main file.
* The position `x̂ = (a + a†)/√2` of the oscillator, on `D(a) ∩ D(a†) = D(a†)` (`positionOp`,
  `domain_positionOp`), is unbounded, since `|(x̂ |n⟩)ₙ₊₁| = √((n + 1)/2)`
  (`exists_lt_norm_positionOp`). It is symmetric (`isFormalAdjoint_positionOp`), so by
  Hellinger–Toeplitz it is not defined on all states (`domain_positionOp_ne_top`). The average
  position `⟨x̂⟩` is discontinuous at every point of `D(x̂)` (`not_continuousAt_inner_positionOp`,
  `not_continuousAt_inner_div_positionOp`).

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.
-/

open scoped InnerProductSpace

@[expose] public noncomputable section

namespace InconsistentConvergence

/-! ### The number operator -/

lemma dense_domain_numberOp : Dense (numberOp.domain : Set H) := lp.dense_diagonalDomain _

/-- `N` is unbounded on its domain. -/
theorem exists_lt_norm_numberOp (C : ℝ) :
    ∃ x : numberOp.domain, C * ‖(x : H)‖ < ‖numberOp x‖ := by
  refine lp.exists_lt_norm_diagonal _ (fun ⟨b, hb⟩ => ?_) C
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have := hb ⟨n, rfl⟩
  simp only [Nat.abs_cast] at this
  linarith

/-- **`⟨N⟩` is discontinuous at every point of `D(N)`.** -/
theorem not_continuousAt_inner_numberOp (x₀ : numberOp.domain) :
    ¬ ContinuousAt (fun x : numberOp.domain => ⟪(x : H), numberOp x⟫_ℂ) x₀ :=
  LinearPMap.not_continuousAt_inner dense_domain_numberOp exists_lt_norm_numberOp x₀

/-- The weighted sum `numberExp`, restricted to `D(N)`, is discontinuous at every point. -/
theorem not_continuousAt_numberExp_domain (x₀ : numberOp.domain) :
    ¬ ContinuousAt (fun x : numberOp.domain => numberExp x) x₀ := fun h =>
  not_continuousAt_inner_numberOp x₀ <| by
    simpa only [Function.comp_def, inner_numberOp] using
      Complex.continuous_ofReal.continuousAt.comp h

/-! ### The position -/

lemma creationDomain_le_annihilationDomain : creation.domain ≤ annihilation.domain :=
  fun x hx => mem_annihilationDomain.2 <| (mem_creationDomain.1 hx).mono' fun n => by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    gcongr
    linarith

/-- The position `x̂ = (a + a†)/√2` of the oscillator (`m = ω = ħ = 1`), on `D(a) ∩ D(a†)`. -/
def positionOp : H →ₗ.[ℂ] H := ((√2 : ℝ) : ℂ)⁻¹ • (annihilation + creation)

/-- `D(x̂) = D(a†)`. -/
theorem domain_positionOp : positionOp.domain = creation.domain := by
  rw [positionOp, LinearPMap.smul_domain, LinearPMap.add_domain]
  exact inf_eq_right.2 creationDomain_le_annihilationDomain

lemma dense_domain_positionOp : Dense (positionOp.domain : Set H) := by
  rw [domain_positionOp]
  exact lp.dense_diagonalDomain _

lemma level_mem_domain_positionOp (n : ℕ) : level n ∈ positionOp.domain :=
  ⟨level_mem_annihilationDomain n, level_mem_creationDomain n⟩

/-- `(x̂ |n⟩)ₙ₊₁ = √(n + 1)/√2`. -/
theorem positionOp_level_apply_succ (n : ℕ) :
    positionOp ⟨level n, level_mem_domain_positionOp n⟩ (n + 1) =
      ((√2 : ℝ) : ℂ)⁻¹ * (√((n : ℝ) + 1) : ℂ) := by
  change ((√2 : ℝ) : ℂ)⁻¹ * ((√(((n + 1 : ℕ) : ℝ) + 1) : ℂ) * level n (n + 1 + 1) +
    (√((n : ℝ) + 1) : ℂ) * level n n) = _
  simp [level_apply, show n + 1 + 1 ≠ n by omega]

/-- `x̂` is unbounded on its domain. -/
theorem exists_lt_norm_positionOp (C : ℝ) :
    ∃ x : positionOp.domain, C * ‖(x : H)‖ < ‖positionOp x‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * C ^ 2)
  refine ⟨⟨level n, level_mem_domain_positionOp n⟩, ?_⟩
  have hle := lp.norm_apply_le_norm (by norm_num)
    (positionOp ⟨level n, level_mem_domain_positionOp n⟩) (n + 1)
  rw [positionOp_level_apply_succ, norm_mul, norm_inv, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _),
    inv_mul_eq_div] at hle
  have hlevel : ‖level n‖ = 1 := by rw [level, lp.norm_single (by norm_num), norm_one]
  change C * ‖level n‖ < _
  rw [hlevel, mul_one]
  refine lt_of_lt_of_le ?_ hle
  rcases le_or_gt C 0 with hC | hC
  · exact lt_of_le_of_lt hC (by positivity)
  · rw [lt_div_iff₀ (by positivity), Real.lt_sqrt (by positivity), mul_pow,
      Real.sq_sqrt (by norm_num)]
    linarith

/-- `x̂` is symmetric. -/
theorem isFormalAdjoint_positionOp : positionOp.IsFormalAdjoint positionOp := by
  intro x y
  have h1 := isFormalAdjoint_annihilation_creation ⟨x, x.2.1⟩ ⟨y, y.2.2⟩
  have h2 := isFormalAdjoint_annihilation_creation.symm ⟨x, x.2.2⟩ ⟨y, y.2.1⟩
  change ⟪((√2 : ℝ) : ℂ)⁻¹ • (annihilation ⟨x, x.2.1⟩ + creation ⟨x, x.2.2⟩), (y : H)⟫_ℂ =
    ⟪(x : H), ((√2 : ℝ) : ℂ)⁻¹ • (annihilation ⟨y, y.2.1⟩ + creation ⟨y, y.2.2⟩)⟫_ℂ
  rw [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, map_inv₀,
    Complex.conj_ofReal]
  simp only at h1 h2
  rw [h1, h2, add_comm]

/-- **The average position is not defined for all states**: `D(x̂) ≠ ℓ²`, by Hellinger–Toeplitz. -/
theorem domain_positionOp_ne_top : positionOp.domain ≠ ⊤ :=
  LinearPMap.domain_ne_top_of_isFormalAdjoint isFormalAdjoint_positionOp exists_lt_norm_positionOp

/-- **The average position is discontinuous at every point of its domain.** -/
theorem not_continuousAt_inner_positionOp (x₀ : positionOp.domain) :
    ¬ ContinuousAt (fun x : positionOp.domain => ⟪(x : H), positionOp x⟫_ℂ) x₀ :=
  LinearPMap.not_continuousAt_inner dense_domain_positionOp exists_lt_norm_positionOp x₀

/-- The normalized average position `⟨x|x̂|x⟩ / ‖x‖²` is discontinuous at every nonzero point of
`D(x̂)`. -/
theorem not_continuousAt_inner_div_positionOp {x₀ : positionOp.domain} (hx₀ : x₀ ≠ 0) :
    ¬ ContinuousAt
      (fun x : positionOp.domain => ⟪(x : H), positionOp x⟫_ℂ / (‖(x : H)‖ ^ 2 : ℂ)) x₀ :=
  LinearPMap.not_continuousAt_inner_div dense_domain_positionOp exists_lt_norm_positionOp hx₀

end InconsistentConvergence
