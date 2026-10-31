/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Pinching
public import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
public import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# Quantum relative entropy and pinching

## i. Overview

For density operators `ρ`, `σ` on a finite-dimensional complex Hilbert space, the relative entropy
is `D(ρ‖σ) = tr(ρ log ρ) - tr(ρ log σ)` when the support of `σ` contains that of `ρ`, and `∞`
otherwise. The logarithm is the functional calculus `cfc Real.log`; since `Real.log 0 = 0`, it is
the logarithm on the support. The value lies in `ℝ≥0∞`, as in physlib's `qRelativeEnt`.

**Klein's inequality** `D(ρ‖σ) ≥ 0`, with equality only for `ρ = σ`, is proved in eigenbases
`(uᵢ, rᵢ)` of `ρ` and `(vⱼ, sⱼ)` of `σ`. With the doubly stochastic weights `cᵢⱼ = |⟨uᵢ, vⱼ⟩|²`,
`D(ρ‖σ) = ∑ᵢⱼ cᵢⱼ (rᵢ log rᵢ - rᵢ log sⱼ - rᵢ + sⱼ) ≥ ∑ᵢⱼ cᵢⱼ (√rᵢ - √sⱼ)²`, by TauCeti's
supporting-line bound for `x log x`; the support condition handles the terms with `sⱼ = 0`. Equality
forces `rᵢ = sⱼ` whenever `⟨uᵢ, vⱼ⟩ ≠ 0`, hence `ρ vⱼ = sⱼ vⱼ` for all `j`.

For `σ` commuting with a self-adjoint `X`, both `log σ` and `log P_X(ρ)` commute with `X`, so the
trace against them only sees the pinching. This gives the **Pythagoras identity**
`D(ρ‖σ) = D(ρ‖P_X(ρ)) + D(P_X(ρ)‖σ)`, and with Klein's inequality, `P_X(ρ)` is the unique density
operator commuting with `X` closest to `ρ` in relative entropy.

## ii. Key results

- `QuantumMechanics.relEntropy`: the relative entropy `D(ρ‖σ)` in `ℝ≥0∞`.
- `QuantumMechanics.re_trace_mul_log_self`: `tr(ρ log ρ) = ∑ᵢ rᵢ log rᵢ`.
- `QuantumMechanics.re_trace_mul_log_sub_log_nonneg`,
  `QuantumMechanics.re_trace_mul_log_sub_log_eq_zero_iff`: Klein's inequality and its equality
  case.
- `QuantumMechanics.relEntropy_eq_zero_iff`: `D(ρ‖σ) = 0` iff `ρ = σ`.
- `QuantumMechanics.relEntropy_pinching`: `D(ρ‖P_X(ρ)) = tr(ρ log ρ) - tr(P_X(ρ) log P_X(ρ))`.
- `QuantumMechanics.relEntropy_eq_add`: the Pythagoras identity.
- `QuantumMechanics.relEntropy_pinching_lt`: `P_X(ρ)` is the unique closest density operator
  commuting with `X`.

## iii. Table of contents

- A. Klein's inequality
- B. Relative entropy
- C. Pinching

## iv. References

- M. Hayashi, *A Group Theoretic Approach to Quantum Information*, Springer (2017), Exercise 2.8.
- E. Carlen, *Trace inequalities and quantum entropy: an introductory course*, Contemp. Math. 529
  (2010), Theorem 2.11.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder ENNReal
open InnerProductSpace QuantumMechanics.Wigner

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E]

/-!
## A. Klein's inequality
-/

/-- The scalar inequality behind Klein's inequality, including the boundary case `s = 0`. -/
private lemma mul_sq_sqrt_sub_le {c r s : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (h0 : s = 0 → c * r = 0) :
    c * (√r - √s) ^ 2 ≤ c * (r * Real.log r - r * Real.log s - r + s) := by
  rcases hs.eq_or_lt with rfl | hs
  · have h := h0 rfl
    have : c * (√r - √0) ^ 2 = c * r := by rw [Real.sqrt_zero, sub_zero, Real.sq_sqrt hr]
    have h' : c * (r * Real.log r - r * Real.log 0 - r + 0) = c * r * (Real.log r - 1) := by
      rw [Real.log_zero]
      ring
    rw [this, h', h, zero_mul]
  · refine mul_le_mul_of_nonneg_left ?_ hc
    have := TauCeti.sq_sqrt_sub_sqrt_le_mul_log_sub_mul_log_sub hs hr
    linarith

variable {ρ σ : E →L[ℂ] E}

omit [CompleteSpace E] in
private lemma apply_eigenvectorBasis' (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) (i) :
    ρ (hρ.eigenvectorBasis rfl i) = (hρ.eigenvalues rfl i : ℂ) • hρ.eigenvectorBasis rfl i :=
  hρ.apply_eigenvectorBasis rfl i

private lemma cfc_apply_eigenvectorBasis' (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) (f : ℝ → ℝ) (i) :
    cfc f ρ (hρ.eigenvectorBasis rfl i) =
      (f (hρ.eigenvalues rfl i) : ℂ) • hρ.eigenvectorBasis rfl i :=
  ContinuousLinearMap.cfc_apply_of_apply_eq_smul f (apply_eigenvectorBasis' hρ i)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hρ)

/-- `tr(ρ f(ρ)) = ∑ᵢ rᵢ f(rᵢ)` over the eigenvalues of a self-adjoint `ρ`. -/
theorem re_trace_mul_cfc_self (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) (f : ℝ → ℝ) :
    RCLike.re (LinearMap.trace ℂ E ↑(ρ * cfc f ρ)) =
      ∑ i, hρ.eigenvalues rfl i * f (hρ.eigenvalues rfl i) := by
  rw [LinearMap.trace_eq_sum_inner _ (hρ.eigenvectorBasis rfl), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ContinuousLinearMap.coe_coe, mul_apply_eq_comp, cfc_apply_eigenvectorBasis' hρ,
    map_smul, apply_eigenvectorBasis' hρ, smul_smul, inner_smul_right,
    (hρ.eigenvectorBasis rfl).inner_eq_one, mul_one]
  simp [mul_comm]

/-- `tr(ρ log ρ) = ∑ᵢ rᵢ log rᵢ` over the eigenvalues of a self-adjoint `ρ`. -/
theorem re_trace_mul_log_self (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) :
    RCLike.re (LinearMap.trace ℂ E ↑(ρ * cfc Real.log ρ)) =
      ∑ i, hρ.eigenvalues rfl i * Real.log (hρ.eigenvalues rfl i) :=
  re_trace_mul_cfc_self hρ Real.log

/-- Klein's inequality with an explicit remainder: for density operators with
`ker σ ≤ ker ρ`, `tr(ρ (log ρ - log σ)) ≥ ∑ᵢⱼ |⟨uᵢ, vⱼ⟩|² (√rᵢ - √sⱼ)²`. -/
private lemma sum_le_re_trace_mul_log_sub_log (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)) :
    ∑ i, ∑ j, ‖⟪hρ.isPositive.isSymmetric.eigenvectorBasis rfl i,
        hσ.isPositive.isSymmetric.eigenvectorBasis rfl j⟫_ℂ‖ ^ 2 *
        (√(hρ.isPositive.isSymmetric.eigenvalues rfl i) -
          √(hσ.isPositive.isSymmetric.eigenvalues rfl j)) ^ 2 ≤
      RCLike.re (LinearMap.trace ℂ E ↑(ρ * (cfc Real.log ρ - cfc Real.log σ))) := by
  set hA := hρ.isPositive.isSymmetric
  set hB := hσ.isPositive.isSymmetric
  set u := hA.eigenvectorBasis rfl
  set v := hB.eigenvectorBasis rfl
  set r := hA.eigenvalues rfl
  set s := hB.eigenvalues rfl
  set c : _ → _ → ℝ := fun i j => ‖⟪u i, v j⟫_ℂ‖ ^ 2
  have hr0 : ∀ i, 0 ≤ r i := hρ.isPositive.nonneg_eigenvalues rfl
  have hs0 : ∀ j, 0 ≤ s j := hσ.isPositive.nonneg_eigenvalues rfl
  have hrow : ∀ i, ∑ j, c i j = 1 := fun i => by
    simp [c, v.sum_sq_norm_inner_left, u.orthonormal.1 i]
  have hcol : ∀ j, ∑ i, c i j = 1 := fun j => by
    simp [c, u.sum_sq_norm_inner_right, v.orthonormal.1 j]
  -- `⟨vⱼ, ρ vⱼ⟩ = ∑ᵢ rᵢ cᵢⱼ`
  have hρv : ∀ j, ⟪v j, ρ (v j)⟫_ℂ = ((∑ i, r i * c i j : ℝ) : ℂ) := fun j => by
    have h := congrArg (fun T : E →L[ℂ] E => ⟪v j, T (v j)⟫_ℂ) hρ.eq_sum_proj
    simp only [sum_apply, smul_apply, inner_sum, inner_smul_right, inner_proj_apply] at h
    rw [h, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_mul _ _).symm
  have hT1 := re_trace_mul_log_self hA
  have hT2 : RCLike.re (LinearMap.trace ℂ E ↑(ρ * cfc Real.log σ)) =
      ∑ j, Real.log (s j) * ∑ i, r i * c i j := by
    rw [LinearMap.trace_eq_sum_inner _ v, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ContinuousLinearMap.coe_coe, mul_apply_eq_comp]
    rw [cfc_apply_eigenvectorBasis' hB, map_smul, inner_smul_right]
    erw [hρv j]
    simp [s]
  have hsupp : ∀ i j, s j = 0 → c i j * r i = 0 := fun i j hj => by
    have hσ0 : σ (v j) = 0 := by simp [v, apply_eigenvectorBasis' hB, ← hj, s]
    have hρ0 : ρ (v j) = 0 := by
      have : v j ∈ LinearMap.ker (σ : E →ₗ[ℂ] E) := by simpa using hσ0
      simpa using hk this
    have h := hρv j
    rw [hρ0, inner_zero_right, eq_comm, Complex.ofReal_eq_zero,
      Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hr0 i) (by positivity)] at h
    rw [mul_comm]
    exact h i (Finset.mem_univ i)
  calc ∑ i, ∑ j, c i j * (√(r i) - √(s j)) ^ 2
      ≤ ∑ i, ∑ j, c i j * (r i * Real.log (r i) - r i * Real.log (s j) - r i + s j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_sq_sqrt_sub_le (by positivity) (hr0 i) (hs0 j) (hsupp i j)
    _ = RCLike.re (LinearMap.trace ℂ E ↑(ρ * (cfc Real.log ρ - cfc Real.log σ))) := by
      rw [mul_sub, ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub, hT1, hT2]
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have e1 : ∑ i, ∑ j, c i j * (r i * Real.log (r i)) = ∑ i, r i * Real.log (r i) := by
        simp [← Finset.sum_mul, hrow]
      have e2 : ∑ i, ∑ j, c i j * (r i * Real.log (s j)) =
          ∑ j, Real.log (s j) * ∑ i, r i * c i j := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      have e3 : ∑ i, ∑ j, c i j * r i = 1 := by
        simp [← Finset.sum_mul, hrow, hρ.sum_eigenvalues, r]
      have e4 : ∑ i, ∑ j, c i j * s j = 1 := by
        rw [Finset.sum_comm]
        simp [← Finset.sum_mul, hcol, hσ.sum_eigenvalues, s]
      rw [e1, e2, e3, e4]
      ring

/-- **Klein's inequality.** `tr(ρ (log ρ - log σ)) ≥ 0` for density operators with
`ker σ ≤ ker ρ`. -/
theorem re_trace_mul_log_sub_log_nonneg (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)) :
    0 ≤ RCLike.re (LinearMap.trace ℂ E ↑(ρ * (cfc Real.log ρ - cfc Real.log σ))) :=
  (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity).trans
    (sum_le_re_trace_mul_log_sub_log hρ hσ hk)

/-- **Equality in Klein's inequality.** -/
theorem re_trace_mul_log_sub_log_eq_zero_iff (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)) :
    RCLike.re (LinearMap.trace ℂ E ↑(ρ * (cfc Real.log ρ - cfc Real.log σ))) = 0 ↔ ρ = σ := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  set hA := hρ.isPositive.isSymmetric
  set hB := hσ.isPositive.isSymmetric
  set u := hA.eigenvectorBasis rfl
  set v := hB.eigenvectorBasis rfl
  set r := hA.eigenvalues rfl
  set s := hB.eigenvalues rfl
  have hle := sum_le_re_trace_mul_log_sub_log hρ hσ hk
  rw [h] at hle
  have hterm : ∀ i j, ‖⟪u i, v j⟫_ℂ‖ ^ 2 * (√(r i) - √(s j)) ^ 2 = 0 := by
    have h0 := le_antisymm hle
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
    rw [Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => by positivity] at h0
    intro i j
    exact (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity).mp
      (h0 i (Finset.mem_univ i)) j (Finset.mem_univ j)
  -- `rᵢ ⟨uᵢ, vⱼ⟩ = sⱼ ⟨uᵢ, vⱼ⟩` for all `i`, `j`
  have hcoef : ∀ i j, (r i : ℂ) * ⟪u i, v j⟫_ℂ = (s j : ℂ) * ⟪u i, v j⟫_ℂ := fun i j => by
    by_cases h0 : ⟪u i, v j⟫_ℂ = 0
    · simp [h0]
    have hrs : r i = s j := by
      have := hterm i j
      rw [mul_eq_zero, pow_eq_zero_iff two_ne_zero, pow_eq_zero_iff two_ne_zero, norm_eq_zero,
        sub_eq_zero] at this
      exact (Real.sqrt_inj (hρ.isPositive.nonneg_eigenvalues rfl i)
        (hσ.isPositive.nonneg_eigenvalues rfl j)).mp (this.resolve_left h0)
    rw [hrs]
  refine ContinuousLinearMap.coe_injective (v.toBasis.ext fun j => ?_)
  simp only [OrthonormalBasis.coe_toBasis, ContinuousLinearMap.coe_coe]
  rw [apply_eigenvectorBasis' hB]
  conv_lhs => rw [← u.sum_repr' (v j)]
  conv_rhs => rw [← u.sum_repr' (v j)]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, apply_eigenvectorBasis' hA, smul_smul, smul_smul, mul_comm, hcoef i j]

/-!
## B. Relative entropy
-/

open scoped Classical in
/-- The relative entropy `D(ρ‖σ) = tr(ρ log ρ) - tr(ρ log σ)` if `ker σ ≤ ker ρ`, and `∞`
otherwise. -/
def relEntropy (ρ σ : E →L[ℂ] E) : ℝ≥0∞ :=
  if LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E) then
    ENNReal.ofReal (RCLike.re (LinearMap.trace ℂ E ↑(ρ * (cfc Real.log ρ - cfc Real.log σ))))
  else ⊤

omit [FiniteDimensional ℂ E] in
lemma relEntropy_of_ker_le (hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)) :
    relEntropy ρ σ =
      ENNReal.ofReal
        (RCLike.re (LinearMap.trace ℂ E ↑(ρ * (cfc Real.log ρ - cfc Real.log σ)))) := by
  simp only [relEntropy, hk, ↓reduceIte]

omit [FiniteDimensional ℂ E] in
lemma relEntropy_of_not_ker_le
    (hk : ¬ LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)) :
    relEntropy ρ σ = ⊤ := by
  simp only [relEntropy, hk, ↓reduceIte]

/-- `D(ρ‖σ) = 0` iff `ρ = σ`. -/
theorem relEntropy_eq_zero_iff (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    relEntropy ρ σ = 0 ↔ ρ = σ := by
  by_cases hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)
  · rw [relEntropy_of_ker_le hk, ENNReal.ofReal_eq_zero,
      ← re_trace_mul_log_sub_log_eq_zero_iff hρ hσ hk]
    exact ⟨fun h => le_antisymm h (re_trace_mul_log_sub_log_nonneg hρ hσ hk), le_of_eq⟩
  · rw [relEntropy_of_not_ker_le hk]
    exact ⟨fun h => absurd h ENNReal.top_ne_zero, fun h => absurd (h ▸ le_rfl) hk⟩

/-!
## C. Pinching
-/

variable {X : E →L[ℂ] E}

/-- `D(ρ‖P_X(ρ)) = tr(ρ log ρ) - tr(P_X(ρ) log P_X(ρ))`; in particular it is finite. -/
theorem relEntropy_pinching (hX : IsSelfAdjoint X) (hρ : IsDensity ρ) :
    relEntropy ρ (pinching X ρ) =
      ENNReal.ofReal (RCLike.re (LinearMap.trace ℂ E ↑(ρ * cfc Real.log ρ)) -
        RCLike.re (LinearMap.trace ℂ E ↑(pinching X ρ * cfc Real.log (pinching X ρ)))) := by
  rw [relEntropy_of_ker_le (ker_pinching_le hX hρ.isPositive), mul_sub,
    ContinuousLinearMap.toLinearMap_sub, map_sub, map_sub,
    ← trace_pinching_mul_of_commute hX ρ ((commute_pinching hX ρ).cfc_real Real.log)]

/-- **Pythagoras.** For a density operator `σ` commuting with `X`,
`D(ρ‖σ) = D(ρ‖P_X(ρ)) + D(P_X(ρ)‖σ)`. -/
theorem relEntropy_eq_add (hX : IsSelfAdjoint X) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hσX : Commute σ X) :
    relEntropy ρ σ = relEntropy ρ (pinching X ρ) + relEntropy (pinching X ρ) σ := by
  have hP := isDensity_pinching hX hρ
  have hk₁ := ker_pinching_le hX hρ.isPositive
  by_cases hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)
  · have hk₂ := ker_le_ker_pinching hσX hk
    rw [relEntropy_of_ker_le hk, relEntropy_of_ker_le hk₁, relEntropy_of_ker_le hk₂,
      ← ENNReal.ofReal_add (re_trace_mul_log_sub_log_nonneg hρ hP hk₁)
        (re_trace_mul_log_sub_log_nonneg hP hσ hk₂)]
    congr 1
    have e1 := trace_pinching_mul_of_commute hX ρ ((commute_pinching hX ρ).cfc_real Real.log)
    have e2 := trace_pinching_mul_of_commute hX ρ (hσX.cfc_real Real.log)
    simp only [mul_sub, ContinuousLinearMap.toLinearMap_sub, map_sub] at e1 e2 ⊢
    rw [← e1, ← e2]
    ring
  · have hk₂ : ¬ LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (pinching X ρ : E →ₗ[ℂ] E) :=
      fun h => hk (h.trans hk₁)
    rw [relEntropy_of_not_ker_le hk, relEntropy_of_not_ker_le hk₂, add_top]

/-- **Closest commuting state in relative entropy.** Every density operator `σ ≠ P_X(ρ)`
commuting with `X` is strictly farther from `ρ` than `P_X(ρ)`. -/
theorem relEntropy_pinching_lt (hX : IsSelfAdjoint X) (hρ : IsDensity ρ) (hσ : IsDensity σ)
    (hσX : Commute σ X) (hne : σ ≠ pinching X ρ) :
    relEntropy ρ (pinching X ρ) < relEntropy ρ σ := by
  rw [relEntropy_eq_add hX hρ hσ hσX]
  refine ENNReal.lt_add_right ?_ fun h => hne ?_
  · rw [relEntropy_pinching hX hρ]
    exact ENNReal.ofReal_ne_top
  · exact ((relEntropy_eq_zero_iff (isDensity_pinching hX hρ) hσ).mp h).symm

end QuantumMechanics
