/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.RelativeEntropy
public import ForPhyslib.QuantumMechanics.VonNeumannRelativeEntropy

/-!
# Agreement of the two relative entropies in finite dimension

## i. Overview

Two relative entropies of density operators are defined in this library, both in `[0, ∞]`:

* `relEntropy ρ σ` (finite dimension): `tr(ρ (log ρ - log σ))` if `ker σ ≤ ker ρ`, else `∞`;
* `relativeEntropy ρ σ` (any dimension): Lindblad's formula
  `∑ᵢⱼ |⟨eᵢ, fⱼ⟩|² (λᵢ log λᵢ - λᵢ log μⱼ + μⱼ - λᵢ)` in eigenbases chosen once.

In finite dimension they agree on density operators. The entropy is finite there, so
`relativeEntropy` is Lindblad's formula in the eigenvector bases of `ρ` and `σ`. If
`ker σ ≤ ker ρ`, a term with `μⱼ = 0` has `|⟨eᵢ, fⱼ⟩|² λᵢ = 0`, every term is finite, and the
double sum is `tr(ρ (log ρ - log σ))`, as in the proof of Klein's inequality. Otherwise some
`fⱼ` with `μⱼ = 0` has `ρ fⱼ ≠ 0`, so some `eᵢ` with `λᵢ ≠ 0` has `⟨eᵢ, fⱼ⟩ ≠ 0`, and that term is
`+∞`.

## ii. Key results

- `QuantumMechanics.relativeEntropy_eq_relEntropy`: `relativeEntropy ρ σ = relEntropy ρ σ` for
  density operators in finite dimension.
- `QuantumMechanics.IsDensityOperator.vonNeumannEntropy_ne_top`: in finite dimension the entropy
  is finite.

## iii. Table of contents

- A. The trace as a Lindblad sum
- B. Agreement
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open InnerProductSpace QuantumMechanics.Wigner

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] {ρ σ : E →L[ℂ] E}

/-! ## A. The trace as a Lindblad sum -/

omit [CompleteSpace E] in
private lemma apply_eigenvectorBasis'' (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) (i) :
    ρ (hρ.eigenvectorBasis rfl i) = (hρ.eigenvalues rfl i : ℂ) • hρ.eigenvectorBasis rfl i :=
  hρ.apply_eigenvectorBasis rfl i

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
private lemma symm_inner (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) (x y : E) :
    ⟪ρ x, y⟫_ℂ = ⟪x, ρ y⟫_ℂ :=
  hρ x y

private lemma cfc_apply_eigenvectorBasis'' (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) (f : ℝ → ℝ) (i) :
    cfc f ρ (hρ.eigenvectorBasis rfl i) =
      (f (hρ.eigenvalues rfl i) : ℂ) • hρ.eigenvectorBasis rfl i :=
  ContinuousLinearMap.cfc_apply_of_apply_eq_smul f (apply_eigenvectorBasis'' hρ i)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hρ)

/-- For density operators with `ker σ ≤ ker ρ`, `tr(ρ (log ρ - log σ))` is Lindblad's double sum
in the eigenvector bases. -/
theorem re_trace_mul_log_sub_log_eq_sum (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    RCLike.re (LinearMap.trace ℂ E ↑(ρ * (cfc Real.log ρ - cfc Real.log σ))) =
      ∑ i, ∑ j, ‖⟪hρ.isPositive.isSymmetric.eigenvectorBasis rfl i,
          hσ.isPositive.isSymmetric.eigenvectorBasis rfl j⟫_ℂ‖ ^ 2 *
        (hρ.isPositive.isSymmetric.eigenvalues rfl i *
            Real.log (hρ.isPositive.isSymmetric.eigenvalues rfl i) -
          hρ.isPositive.isSymmetric.eigenvalues rfl i *
            Real.log (hσ.isPositive.isSymmetric.eigenvalues rfl j) -
          hρ.isPositive.isSymmetric.eigenvalues rfl i +
          hσ.isPositive.isSymmetric.eigenvalues rfl j) := by
  set hA := hρ.isPositive.isSymmetric
  set hB := hσ.isPositive.isSymmetric
  set u := hA.eigenvectorBasis rfl
  set v := hB.eigenvectorBasis rfl
  set r := hA.eigenvalues rfl
  set s := hB.eigenvalues rfl
  set c : _ → _ → ℝ := fun i j => ‖⟪u i, v j⟫_ℂ‖ ^ 2
  have hrow : ∀ i, ∑ j, c i j = 1 := fun i => by
    simp [c, v.sum_sq_norm_inner_left, u.orthonormal.1 i]
  have hcol : ∀ j, ∑ i, c i j = 1 := fun j => by
    simp [c, u.sum_sq_norm_inner_right, v.orthonormal.1 j]
  have hρv : ∀ j, ⟪v j, ρ (v j)⟫_ℂ = ((∑ i, r i * c i j : ℝ) : ℂ) := fun j => by
    have h := congrArg (fun T : E →L[ℂ] E => ⟪v j, T (v j)⟫_ℂ) hρ.eq_sum_proj
    simp only [sum_apply, smul_apply, inner_sum,
      inner_smul_right, inner_proj_apply] at h
    rw [h, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_mul _ _).symm
  have hT1 := re_trace_mul_log_self hA
  have hT2 : RCLike.re (LinearMap.trace ℂ E ↑(ρ * cfc Real.log σ)) =
      ∑ j, Real.log (s j) * ∑ i, r i * c i j := by
    rw [LinearMap.trace_eq_sum_inner _ v, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ContinuousLinearMap.coe_coe, mul_apply_eq_comp]
    rw [cfc_apply_eigenvectorBasis'' hB, map_smul, inner_smul_right]
    erw [hρv j]
    simp [s]
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

/-! ## B. Agreement -/

/-- In finite dimension the entropy of a density operator is finite. -/
theorem IsDensityOperator.vonNeumannEntropy_ne_top (hρ : IsDensityOperator ρ) :
    vonNeumannEntropy ρ ≠ ⊤ := by
  have hA := (isDensityOperator_iff_isDensity.mp hρ).isPositive.isSymmetric
  have hu : IsEigenbasis ρ (hA.eigenvectorBasis rfl).toHilbertBasis (hA.eigenvalues rfl) :=
    ⟨fun i => by rw [OrthonormalBasis.coe_toHilbertBasis]; exact apply_eigenvectorBasis'' hA i⟩
  rw [hu.vonNeumannEntropy_eq hρ, tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top

/-- **The two relative entropies agree** on density operators in finite dimension. -/
theorem relativeEntropy_eq_relEntropy (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    relativeEntropy ρ σ = relEntropy ρ σ := by
  have hρ' := isDensityOperator_iff_isDensity.mp hρ
  have hσ' := isDensityOperator_iff_isDensity.mp hσ
  set hA := hρ'.isPositive.isSymmetric
  set hB := hσ'.isPositive.isSymmetric
  set u := hA.eigenvectorBasis rfl
  set v := hB.eigenvectorBasis rfl
  set r := hA.eigenvalues rfl
  set s := hB.eigenvalues rfl
  have hu : IsEigenbasis ρ u.toHilbertBasis r :=
    ⟨fun i => by rw [OrthonormalBasis.coe_toHilbertBasis]; exact apply_eigenvectorBasis'' hA i⟩
  have hv : IsEigenbasis σ v.toHilbertBasis s :=
    ⟨fun j => by rw [OrthonormalBasis.coe_toHilbertBasis]; exact apply_eigenvectorBasis'' hB j⟩
  have hS := hρ.vonNeumannEntropy_ne_top
  have hr0 : ∀ i, 0 ≤ r i := hρ'.isPositive.nonneg_eigenvalues rfl
  have hs0 : ∀ j, 0 ≤ s j := hσ'.isPositive.nonneg_eigenvalues rfl
  rw [relativeEntropy_eq_lindbladSum hρ hσ hS hu hv, lindbladSum, tsum_fintype]
  simp only [tsum_fintype, OrthonormalBasis.coe_toHilbertBasis]
  by_cases hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)
  · rw [relEntropy_of_ker_le hk, re_trace_mul_log_sub_log_eq_sum hρ' hσ']
    -- a term with `sⱼ = 0` has `cᵢⱼ rᵢ = 0`
    have hsupp : ∀ i j, s j = 0 → ‖⟪u i, v j⟫_ℂ‖ ^ 2 * r i = 0 := fun i j hj => by
      have hσ0 : σ (v j) = 0 := by
        rw [show σ (v j) = (s j : ℂ) • v j from apply_eigenvectorBasis'' hB j, hj]
        simp
      have hρ0 : ρ (v j) = 0 := by
        have : v j ∈ LinearMap.ker (σ : E →ₗ[ℂ] E) := by simpa using hσ0
        simpa using hk this
      have h : ⟪ρ (u i), v j⟫_ℂ = 0 := by
        rw [symm_inner hA, hρ0, inner_zero_right]
      rw [apply_eigenvectorBasis'' hA i, inner_smul_left, mul_eq_zero, map_eq_zero,
        Complex.ofReal_eq_zero] at h
      rcases h with h | h
      · simp [r, h]
      · simp [show ⟪u i, v j⟫_ℂ = 0 from h]
    have hterm : ∀ i j, ENNReal.ofReal (‖⟪u i, v j⟫_ℂ‖ ^ 2) * kleinTerm (r i) (s j) =
        ENNReal.ofReal (‖⟪u i, v j⟫_ℂ‖ ^ 2 *
          (r i * Real.log (r i) - r i * Real.log (s j) - r i + s j)) := fun i j => by
      by_cases hj : s j = 0
      · have h := hsupp i j hj
        by_cases hi : r i = 0
        · simp [kleinTerm, hj, hi]
        · have hc : ‖⟪u i, v j⟫_ℂ‖ ^ 2 = 0 := (mul_eq_zero.mp h).resolve_right hi
          simp [hc]
      · simp only [kleinTerm, hj, ↓reduceIte]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    have hnonneg : ∀ i j, 0 ≤ ‖⟪u i, v j⟫_ℂ‖ ^ 2 *
        (r i * Real.log (r i) - r i * Real.log (s j) - r i + s j) := fun i j => by
      by_cases hj : s j = 0
      · have h := hsupp i j hj
        have : ‖⟪u i, v j⟫_ℂ‖ ^ 2 * (r i * Real.log (r i) - r i * Real.log (s j) - r i + s j) =
            (‖⟪u i, v j⟫_ℂ‖ ^ 2 * r i) * (Real.log (r i) - 1) := by
          rw [hj, Real.log_zero]
          ring
        rw [this, h, zero_mul]
      · have hs : 0 < s j := (hs0 j).lt_of_ne' hj
        rw [show r i * Real.log (r i) - r i * Real.log (s j) - r i + s j =
          r i * Real.log (r i) - r i * Real.log (s j) + s j - r i by ring,
          kleinReal_eq_mul_klFun (hr0 i) hs]
        exact mul_nonneg (by positivity)
          (mul_nonneg hs.le (InformationTheory.klFun_nonneg (div_nonneg (hr0 i) hs.le)))
    simp only [hterm]
    rw [ENNReal.ofReal_sum_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => hnonneg i j]
    exact Finset.sum_congr rfl fun i _ =>
      (ENNReal.ofReal_sum_of_nonneg fun j _ => hnonneg i j).symm
  · rw [relEntropy_of_not_ker_le hk]
    obtain ⟨w, hwσ, hwρ⟩ := Set.not_subset.mp hk
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hwσ hwρ
    -- some `vⱼ` with `sⱼ = 0` has `ρ vⱼ ≠ 0`
    obtain ⟨j, hj, hρj⟩ : ∃ j, s j = 0 ∧ ρ (v j) ≠ 0 := by
      by_contra! h
      refine hwρ ?_
      rw [← v.sum_repr' w, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul]
      by_cases hj : s j = 0
      · rw [h j hj, smul_zero]
      · have hc : ⟪v j, w⟫_ℂ = 0 := by
          have h1 : ⟪v j, σ w⟫_ℂ = (s j : ℂ) * ⟪v j, w⟫_ℂ := by
            rw [← symm_inner hB, apply_eigenvectorBasis'' hB j, inner_smul_left,
              Complex.conj_ofReal]
          rw [hwσ, inner_zero_right, eq_comm, mul_eq_zero, Complex.ofReal_eq_zero] at h1
          exact h1.resolve_left hj
        rw [hc, zero_smul]
    -- so some `uᵢ` with `rᵢ ≠ 0` has `⟨uᵢ, vⱼ⟩ ≠ 0`
    obtain ⟨i, hi, hij⟩ : ∃ i, r i ≠ 0 ∧ ⟪u i, v j⟫_ℂ ≠ 0 := by
      by_contra! h
      refine hρj ?_
      rw [← u.sum_repr' (v j), map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, apply_eigenvectorBasis'' hA i]
      by_cases hi : r i = 0
      · simp [r, hi]
      · rw [h i hi, zero_smul]
    refine ENNReal.sum_eq_top.mpr ⟨i, Finset.mem_univ _, ENNReal.sum_eq_top.mpr
      ⟨j, Finset.mem_univ _, ?_⟩⟩
    simp only [kleinTerm, hj, hi, ↓reduceIte]
    rw [ENNReal.mul_top]
    simpa using hij

/-- `IsDensity` form of `relativeEntropy_eq_relEntropy`. -/
theorem Wigner.IsDensity.relativeEntropy_eq_relEntropy (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    relativeEntropy ρ σ = relEntropy ρ σ :=
  QuantumMechanics.relativeEntropy_eq_relEntropy (isDensityOperator_iff_isDensity.mpr hρ)
    (isDensityOperator_iff_isDensity.mpr hσ)

end QuantumMechanics
