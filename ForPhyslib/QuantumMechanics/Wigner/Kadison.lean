/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Wigner.Density
public import ForPhyslib.QuantumMechanics.Wigner.Projection
public import ForMathlib.Analysis.InnerProductSpace.Positive

/-!
# Affine maps of density operators and Kadison's theorem

## i. Overview

A map `T` of density operators that is affine, in the sense that it preserves the mixtures
`t ρ + (1 - t) σ`, is determined by its values on the pure states. In particular, if it agrees on
pure states with conjugation by a unitary or an anti-unitary `W`, then it agrees with that
conjugation on every density operator: write `ρ = ∑ᵢ μᵢ |eᵢ⟩⟨eᵢ|` by the spectral theorem and use
affinity on the finite convex combination.

If `T` maps pure states to pure states, it does not decrease overlaps. The equal mixture of
`|ψ⟩⟨ψ|` and `|ϕ⟩⟨ϕ|` is `λ |r⟩⟨r| + (1 - λ) |s⟩⟨s|` with `r ⊥ s` unit and
`λ = (1 + |⟪ψ, ϕ⟫|) / 2`, and `⟪u, mix u⟫ ≤ λ` for every unit `u` by Bessel's inequality. Applying
`T` keeps the weight `λ` on a pure state, so the image mixture has expectation at least `λ` there,
which forces `|⟪ψ, ϕ⟫| ≤ |⟪ψ', ϕ'⟫|`. No continuity or injectivity of `T` is used.

If moreover every pure state is an image, the inequality is an equality. For an orthonormal basis
`(eⱼ)` and unit `u`, the sum `∑ⱼ ⟪u, T |eⱼ⟩⟨eⱼ| u⟫` is at least `∑ⱼ |⟪ψ, eⱼ⟫|² = 1`, where
`T |ψ⟩⟨ψ| = |u⟩⟨u|`. Summed over an orthonormal basis through `u` it equals
`∑ⱼ tr T |eⱼ⟩⟨eⱼ| = n`, so each sum is exactly `1` and the termwise inequalities are equalities.
Wigner's theorem then gives a unitary or anti-unitary `W` on pure states, and the mixed-state
extension gives `T ρ = W ρ W⁻¹` on all density operators: Kadison's theorem.

The pure states are the extreme points of the density operators. So an affine bijection of the
density operators is a bijection of the pure states, and conversely by Kadison's theorem, while
conjugation by `W` is an affine bijection with inverse conjugation by `W⁻¹`. Together these give
`kadison_tfae`. In finite dimension no continuity hypothesis is needed.

## ii. Key results

- `QuantumMechanics.Wigner.AffineOnDensities.eq_conjOp`: the mixed-state extension.
- `QuantumMechanics.Wigner.exists_mix_proj_eq`: the two-state decomposition.
- `QuantumMechanics.Wigner.sq_norm_inner_add_sq_norm_inner_le`: the upper bound
  `|⟪ψ, u⟫|² + |⟪ϕ, u⟫|² ≤ 1 + |⟪ψ, ϕ⟫|`.
- `QuantumMechanics.Wigner.AffineOnDensities.norm_inner_le`: overlaps do not shrink.
- `QuantumMechanics.Wigner.AffineOnDensities.sum_re_inner_eq_one`: Parseval averaging.
- `QuantumMechanics.Wigner.AffineOnDensities.norm_inner_eq`: overlaps are preserved.
- `QuantumMechanics.Wigner.kadison`: Kadison's theorem in finite dimension.
- `QuantumMechanics.Wigner.isPure_iff_isExtremeDensity`: the pure states are the extreme points.
- `QuantumMechanics.Wigner.AffineOnDensities.bijOnPure`: an affine bijection of the density
  operators is a bijection of the pure states.
- `QuantumMechanics.Wigner.kadison_tfae`: bijective on pure states ⇔ bijective on density
  operators ⇔ conjugation by a unitary or an anti-unitary.

## iii. Table of contents

- A. Mixed states follow from pure states
- B. Two pure states as a mixture of two orthogonal ones
- C. An upper bound for two pure states
- D. Overlaps do not shrink
- E. Parseval averaging
- F. Kadison's theorem
- G. Pure states are the extreme points
- H. Three characterizations of state automorphisms

## iv. References

- R. V. Kadison, *Transformations of states in operator theory and dynamics*, Topology 3,
  suppl. 2 (Pergamon Press, 1965), 177–198.
- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), 327–349.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open InnerProductSpace ContinuousLinearMap

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. Mixed states follow from pure states
-/

/-- **Mixed-state extension.** A map that is affine on density operators and agrees on pure states
with conjugation by a unitary or an anti-unitary `W` agrees with it on every density operator. -/
theorem AffineOnDensities.eq_conjOp [FiniteDimensional ℂ E] {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hT : AffineOnDensities T) {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ]
    {W : E ≃ₛₗᵢ[σ] E}
    (hW : ∀ ψ : E, ‖ψ‖ = 1 → T (proj ψ) = proj (W ψ)) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    T ρ = conjOp W ρ := by
  have hb := (hρ.isPositive.isSymmetric.eigenvectorBasis rfl).orthonormal.1
  rw [hρ.eq_sum_proj, hT.map_sum _ (fun i _ => hρ.isPositive.nonneg_eigenvalues rfl i)
    hρ.sum_eigenvalues (fun i _ => isDensity_proj (hb i)), conjOp_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [conjOp_ofReal_smul, conjOp_proj, hW _ (hb i)]

/-!
## B. Two pure states as a mixture of two orthogonal ones
-/

variable {ψ φ : E}

/-- **Two-state decomposition.** For unit `ψ, ϕ` with `c = ⟪ψ, ϕ⟫`, choose `|w| = 1` with
`w c = |c|` and put `r = ψ + w ϕ`, `s = ψ - w ϕ`. Then `r ⊥ s`, `‖r‖² = 2 + 2|c|`,
`‖s‖² = 2 - 2|c|` and `4 · mix(|ψ⟩⟨ψ|, |ϕ⟩⟨ϕ|) = |r⟩⟨r| + |s⟩⟨s|`. -/
lemma exists_orthogonal_mix_proj (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∃ r s : E, ⟪r, s⟫_ℂ = 0 ∧ ‖r‖ ^ 2 = 2 + 2 * ‖⟪ψ, φ⟫_ℂ‖ ∧ ‖s‖ ^ 2 = 2 - 2 * ‖⟪ψ, φ⟫_ℂ‖ ∧
      (4 : ℂ) • mix (proj ψ) (proj φ) = proj r + proj s := by
  obtain ⟨w, hw, hwc⟩ := Complex.exists_norm_eq_mul_self ⟪ψ, φ⟫_ℂ
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hcw : conj w * ⟪φ, ψ⟫_ℂ = ‖⟪ψ, φ⟫_ℂ‖ := by
    rw [← inner_conj_symm, ← map_mul, ← hwc, Complex.conj_ofReal]
  have hww : conj w * w = 1 := by rw [Complex.conj_mul', hw]; simp
  have hre : RCLike.re ⟪ψ, w • φ⟫_ℂ = ‖⟪ψ, φ⟫_ℂ‖ := by
    rw [inner_smul_right, ← hwc]; simp
  have hwφ : ‖w • φ‖ = 1 := by rw [norm_smul, hw, hφ, one_mul]
  refine ⟨ψ + w • φ, ψ - w • φ, ?_, ?_, ?_, ?_⟩
  · simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right, hψψ, hφφ]
    linear_combination hcw + hwc - hww
  · rw [@norm_add_sq ℂ, hre, hψ, hwφ]; ring
  · rw [@norm_sub_sq ℂ, hre, hψ, hwφ]; ring
  · rw [proj_add_add_proj_sub, proj_smul, hw, smul_add, smul_smul, smul_smul, smul_smul]
    norm_num

/-- A nonzero vector is a positive multiple of a unit vector. -/
lemma exists_ofReal_smul_of_ne_zero {x : E} (hx : x ≠ 0) :
    ∃ (a : ℝ) (y : E), 0 < a ∧ ‖y‖ = 1 ∧ x = (a : ℂ) • y := by
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨‖x‖, ((‖x‖ : ℂ))⁻¹ • x, ha, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ ha.ne']
  · rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast ha.ne'), one_smul]

/-- **Two-state decomposition, normalized.** `mix(|ψ⟩⟨ψ|, |ϕ⟩⟨ϕ|) = λ |r⟩⟨r| + (1 - λ) |s⟩⟨s|`
for unit vectors `r, s` and `λ = (1 + |⟪ψ, ϕ⟫|) / 2`. -/
lemma exists_mix_proj_eq (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    ∃ r s : E, ‖r‖ = 1 ∧ ‖s‖ = 1 ∧ mix (proj ψ) (proj φ) =
      (((1 + ‖⟪ψ, φ⟫_ℂ‖) / 2 : ℝ) : ℂ) • proj r +
        ((1 - (1 + ‖⟪ψ, φ⟫_ℂ‖) / 2 : ℝ) : ℂ) • proj s := by
  obtain ⟨r, s, -, hr, hs, h4⟩ := exists_orthogonal_mix_proj hψ hφ
  have hmix : mix (proj ψ) (proj φ) = (4⁻¹ : ℂ) • (proj r + proj s) := by
    rw [← h4, smul_smul]; norm_num [mix]
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := norm_nonneg ⟪ψ, φ⟫_ℂ
    simp at hr
    linarith
  obtain ⟨a, r, -, hr1, rfl⟩ := exists_ofReal_smul_of_ne_zero hr0
  rw [norm_smul, hr1, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hr
  rcases eq_or_ne s 0 with rfl | hs0
  · refine ⟨r, ψ, hr1, hψ, ?_⟩
    rw [hmix, proj_smul, Complex.norm_real, Real.norm_eq_abs, sq_abs, hr]
    have : ‖⟪ψ, φ⟫_ℂ‖ = 1 := by simp at hs; linarith
    rw [this]
    ext x
    simp
    module
  obtain ⟨b, s, -, hs1, rfl⟩ := exists_ofReal_smul_of_ne_zero hs0
  rw [norm_smul, hs1, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hs
  refine ⟨r, s, hr1, hs1, ?_⟩
  rw [hmix, proj_smul, proj_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, hr, hs, smul_add, smul_smul, smul_smul]
  congr 2 <;> push_cast <;> ring

/-!
## C. An upper bound for two pure states
-/

/-- Bessel's inequality for an orthonormal pair. -/
lemma sq_norm_inner_add_sq_norm_inner_le_of_orthonormal {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hxy : ⟪x, y⟫_ℂ = 0) (u : E) : ‖⟪x, u⟫_ℂ‖ ^ 2 + ‖⟪y, u⟫_ℂ‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hyx : ⟪y, x⟫_ℂ = 0 := by rw [← inner_conj_symm, hxy, map_zero]
  have hv : Orthonormal ℂ ![x, y] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hxy, hyx, inner_self_eq_norm_sq_to_K, hx, hy]
  simpa [Fin.sum_univ_two] using hv.sum_inner_products_le (s := Finset.univ) (x := u)

/-- For orthogonal `r, s` with `‖s‖ ≤ ‖r‖` and unit `u`: `|⟪r, u⟫|² + |⟪s, u⟫|² ≤ ‖r‖²`. -/
lemma sq_norm_inner_add_sq_norm_inner_le_of_orthogonal {r s u : E} (hrs : ⟪r, s⟫_ℂ = 0)
    (hsr : ‖s‖ ≤ ‖r‖) (hu : ‖u‖ = 1) : ‖⟪r, u⟫_ℂ‖ ^ 2 + ‖⟪s, u⟫_ℂ‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · have := norm_inner_le_norm (𝕜 := ℂ) r u
    rw [hu, mul_one] at this
    simpa using pow_le_pow_left₀ (norm_nonneg _) this 2
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hs0 (norm_le_zero_iff.mp (by simpa using hsr))
  obtain ⟨a, r, ha, hr1, rfl⟩ := exists_ofReal_smul_of_ne_zero hr0
  obtain ⟨b, s, hb, hs1, rfl⟩ := exists_ofReal_smul_of_ne_zero hs0
  have hab : b ≤ a := by
    simpa [norm_smul, hr1, hs1, abs_of_pos ha, abs_of_pos hb] using hsr
  have hrs' : ⟪r, s⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right] at hrs
    simpa [ha.ne', hb.ne'] using hrs
  have hB := sq_norm_inner_add_sq_norm_inner_le_of_orthonormal hr1 hs1 hrs' u
  simp only [inner_smul_left, Complex.conj_ofReal, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha, abs_of_pos hb, norm_smul, hr1, hu, mul_one, mul_pow] at hB ⊢
  have hb2 : b ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hb.le hab 2
  nlinarith [sq_nonneg ‖⟪s, u⟫_ℂ‖, sq_nonneg ‖⟪r, u⟫_ℂ‖]

/-- **Upper bound.** For unit `ψ, ϕ, u`:
`⟪u, mix(|ψ⟩⟨ψ|, |ϕ⟩⟨ϕ|) u⟫ = (|⟪ψ, u⟫|² + |⟪ϕ, u⟫|²) / 2 ≤ (1 + |⟪ψ, ϕ⟫|) / 2`. -/
theorem sq_norm_inner_add_sq_norm_inner_le {u : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hu : ‖u‖ = 1) : ‖⟪ψ, u⟫_ℂ‖ ^ 2 + ‖⟪φ, u⟫_ℂ‖ ^ 2 ≤ 1 + ‖⟪ψ, φ⟫_ℂ‖ := by
  obtain ⟨r, s, hrs, hr, hs, h4⟩ := exists_orthogonal_mix_proj hψ hφ
  have hsr : ‖s‖ ≤ ‖r‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (by
      rw [hr, hs]; linarith [norm_nonneg ⟪ψ, φ⟫_ℂ])
  have hB := sq_norm_inner_add_sq_norm_inner_le_of_orthogonal hrs hsr hu
  have key := congrArg (fun A : E →L[ℂ] E => ⟪u, A u⟫_ℂ) h4
  simp only [smul_apply, add_apply, inner_add_right, inner_smul_right, inner_proj_apply] at key
  have key' : 2 * (‖⟪ψ, u⟫_ℂ‖ ^ 2 + ‖⟪φ, u⟫_ℂ‖ ^ 2) = ‖⟪r, u⟫_ℂ‖ ^ 2 + ‖⟪s, u⟫_ℂ‖ ^ 2 := by
    have h : ((2 * (‖⟪ψ, u⟫_ℂ‖ ^ 2 + ‖⟪φ, u⟫_ℂ‖ ^ 2) : ℝ) : ℂ) =
        ((‖⟪r, u⟫_ℂ‖ ^ 2 + ‖⟪s, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      push_cast at key ⊢
      linear_combination key
    exact_mod_cast h
  linarith

/-!
## D. Overlaps do not shrink
-/

/-- **Overlaps do not shrink.** If `T` maps density operators to density operators, is affine on
them and maps pure states to pure states, then `|⟪ψ, ϕ⟫| ≤ |⟪ψ', ϕ'⟫|` whenever
`T |ψ⟩⟨ψ| = |ψ'⟩⟨ψ'|` and `T |ϕ⟩⟨ϕ| = |ϕ'⟩⟨ϕ'|`. -/
theorem AffineOnDensities.norm_inner_le [FiniteDimensional ℂ E] {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hT : AffineOnDensities T) (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    {ψ' φ' : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hψ' : ‖ψ'‖ = 1) (hφ' : ‖φ'‖ = 1)
    (hTψ : T (proj ψ) = proj ψ') (hTφ : T (proj φ) = proj φ') :
    ‖⟪ψ, φ⟫_ℂ‖ ≤ ‖⟪ψ', φ'⟫_ℂ‖ := by
  obtain ⟨r, s, hr, hs, hmix⟩ := exists_mix_proj_eq hψ hφ
  obtain ⟨r', hr', hTr⟩ := hpure r hr
  have hc : ‖⟪ψ, φ⟫_ℂ‖ ≤ 1 := by simpa [hψ, hφ] using norm_inner_le_norm (𝕜 := ℂ) ψ φ
  have hc0 := norm_nonneg ⟪ψ, φ⟫_ℂ
  have hT1 : T (mix (proj ψ) (proj φ)) = mix (proj ψ') (proj φ') := by
    have h := hT _ _ (isDensity_proj hψ) (isDensity_proj hφ) (1 / 2) (by norm_num) (by norm_num)
    rw [hTψ, hTφ] at h
    convert h using 3 <;> norm_num
  have hT2 := hT _ _ (isDensity_proj hr) (isDensity_proj hs) ((1 + ‖⟪ψ, φ⟫_ℂ‖) / 2)
    (by linarith) (by linarith)
  rw [← hmix, hT1, hTr] at hT2
  have hpos := (hD _ (isDensity_proj hs)).isPositive.re_inner_nonneg_right r'
  have key := congrArg (fun A : E →L[ℂ] E => (⟪r', A r'⟫_ℂ).re) hT2
  simp only [smul_apply, add_apply, inner_add_right, inner_smul_right, inner_proj_apply,
    inner_self_eq_norm_sq_to_K, hr'] at key
  have hB := sq_norm_inner_add_sq_norm_inner_le hψ' hφ' hr'
  have hre : ∀ x : ℝ, ((x : ℂ) ^ 2).re = x ^ 2 := fun x => by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  simp at key hpos
  simp only [hre] at key
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (1 + ‖⟪ψ, φ⟫_ℂ‖) / 2) hpos]

/-!
## E. Parseval averaging
-/

section Parseval

/-- A unit vector spans an orthonormal singleton. -/
lemma orthonormal_singleton {u : E} (hu : ‖u‖ = 1) : Orthonormal ℂ ((↑) : ({u} : Set E) → E) := by
  classical
  refine orthonormal_subtype_iff_ite.mpr ?_
  rintro v rfl w rfl
  simp [inner_self_eq_norm_sq_to_K, hu]

/-- Each image `T |eⱼ⟩⟨eⱼ|` has unit trace, read off in any orthonormal basis `g`. -/
lemma sum_re_inner_apply_eq_one {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) {κ : Type*} [Fintype κ]
    (g : OrthonormalBasis κ ℂ E) : ∑ k, (⟪g k, ρ (g k)⟫_ℂ).re = 1 := by
  have h := hρ.trace_eq_one
  rw [LinearMap.trace_eq_sum_inner _ g] at h
  simpa using congrArg Complex.re h

variable [FiniteDimensional ℂ E] {T : (E →L[ℂ] E) → E →L[ℂ] E}

/-- The termwise form of `AffineOnDensities.norm_inner_le` against a basis vector `eⱼ`:
`|⟪ψ, eⱼ⟫|² ≤ ⟪ψ', T |eⱼ⟩⟨eⱼ| ψ'⟫`. -/
lemma AffineOnDensities.sq_norm_inner_le_re_inner (hT : AffineOnDensities T)
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    {ψ ψ' e : E} (hψ : ‖ψ‖ = 1) (hψ' : ‖ψ'‖ = 1) (he : ‖e‖ = 1)
    (hTψ : T (proj ψ) = proj ψ') : ‖⟪ψ, e⟫_ℂ‖ ^ 2 ≤ (⟪ψ', T (proj e) ψ'⟫_ℂ).re := by
  obtain ⟨f, hf, hTf⟩ := hpure e he
  rw [hTf, inner_proj_apply, Complex.ofReal_re, norm_inner_symm f]
  exact pow_le_pow_left₀ (norm_nonneg _) (hT.norm_inner_le hD hpure hψ he hψ' hf hTψ hTf) 2

/-- **Parseval averaging.** If `T` maps the pure states onto the pure states, then for every
orthonormal basis `e` and unit `u`: `∑ⱼ ⟪u, T |eⱼ⟩⟨eⱼ| u⟫ = 1`. Each sum is at least `1` by
`AffineOnDensities.norm_inner_le` and Parseval for `e`, and summing it over an orthonormal basis
through `u` gives `∑ⱼ tr T |eⱼ⟩⟨eⱼ| = n`, so no sum can exceed `1`. -/
lemma AffineOnDensities.sum_re_inner_eq_one (hT : AffineOnDensities T)
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (honto : ∀ ψ' : E, ‖ψ'‖ = 1 → ∃ ψ : E, ‖ψ‖ = 1 ∧ T (proj ψ) = proj ψ')
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ E) {u : E} (hu : ‖u‖ = 1) :
    ∑ j, (⟪u, T (proj (e j)) u⟫_ℂ).re = 1 := by
  have hS : ∀ v : E, ‖v‖ = 1 → 1 ≤ ∑ j, (⟪v, T (proj (e j)) v⟫_ℂ).re := fun v hv => by
    obtain ⟨ψ, hψ, hTψ⟩ := honto v hv
    calc (1 : ℝ) = ∑ j, ‖⟪ψ, e j⟫_ℂ‖ ^ 2 := by rw [e.sum_sq_norm_inner_left, hψ, one_pow]
      _ ≤ _ := Finset.sum_le_sum fun j _ =>
        hT.sq_norm_inner_le_re_inner hD hpure hψ hv (e.norm_eq_one j) hTψ
  obtain ⟨w, g, hw, hg⟩ := (orthonormal_singleton hu).exists_orthonormalBasis_extension
  have hsum : ∑ _k : w, (1 : ℝ) = ∑ k, ∑ j, (⟪g k, T (proj (e j)) (g k)⟫_ℂ).re := by
    rw [Finset.sum_comm]
    simp only [fun j => sum_re_inner_apply_eq_one (hD _ (isDensity_proj (e.norm_eq_one j))) g]
    simp [← Module.finrank_eq_card_basis e.toBasis, Module.finrank_eq_card_basis g.toBasis]
  have := (Finset.sum_eq_sum_iff_of_le fun k _ => hS (g k) (g.norm_eq_one k)).mp hsum
    ⟨u, hw rfl⟩ (Finset.mem_univ _)
  simpa [hg] using this.symm

/-- **Overlaps are preserved.** If `T` maps density operators to density operators, is affine on
them and maps the pure states onto the pure states, then `|⟪ψ', ϕ'⟫| = |⟪ψ, ϕ⟫|` whenever
`T |ψ⟩⟨ψ| = |ψ'⟩⟨ψ'|` and `T |ϕ⟩⟨ϕ| = |ϕ'⟩⟨ϕ'|`. -/
theorem AffineOnDensities.norm_inner_eq (hT : AffineOnDensities T)
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (honto : ∀ ψ' : E, ‖ψ'‖ = 1 → ∃ ψ : E, ‖ψ‖ = 1 ∧ T (proj ψ) = proj ψ')
    {ψ φ ψ' φ' : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hψ' : ‖ψ'‖ = 1)
    (hTψ : T (proj ψ) = proj ψ') (hTφ : T (proj φ) = proj φ') :
    ‖⟪ψ', φ'⟫_ℂ‖ = ‖⟪ψ, φ⟫_ℂ‖ := by
  obtain ⟨w, e, hw, he⟩ := (orthonormal_singleton hφ).exists_orthonormalBasis_extension
  have h : ∑ j, ‖⟪ψ, e j⟫_ℂ‖ ^ 2 = ∑ j, (⟪ψ', T (proj (e j)) ψ'⟫_ℂ).re := by
    rw [e.sum_sq_norm_inner_left, hψ, one_pow, hT.sum_re_inner_eq_one hD hpure honto e hψ']
  have := (Finset.sum_eq_sum_iff_of_le fun j _ =>
    hT.sq_norm_inner_le_re_inner hD hpure hψ hψ' (e.norm_eq_one j) hTψ).mp h
    ⟨φ, hw rfl⟩ (Finset.mem_univ _)
  simp only [he, hTφ, inner_proj_apply, Complex.ofReal_re, norm_inner_symm φ' ψ'] at this
  exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this).symm

end Parseval

/-!
## F. Kadison's theorem
-/

/-- **Kadison's theorem** in finite dimension. A map that sends density operators to density
operators, is affine on them and maps the pure states onto the pure states is conjugation by a
unitary or an anti-unitary on every density operator. No continuity or injectivity is assumed. -/
theorem kadison [FiniteDimensional ℂ E] {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ)) (hT : AffineOnDensities T)
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (honto : ∀ ψ' : E, ‖ψ'‖ = 1 → ∃ ψ : E, ‖ψ‖ = 1 ∧ T (proj ψ) = proj ψ') :
    (∃ W : E ≃ₗᵢ[ℂ] E, ∀ ρ, IsDensity ρ → T ρ = conjOp W ρ) ∨
      (∃ W : E ≃ₗᵢ⋆[ℂ] E, ∀ ρ, IsDensity ρ → T ρ = conjOp W ρ) := by
  have htr : ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 →
      LinearMap.trace ℂ E ((T (proj ψ) * T (proj φ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((proj ψ * proj φ : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    intro ψ φ hψ hφ
    obtain ⟨ψ', hψ', hTψ⟩ := hpure ψ hψ
    obtain ⟨φ', -, hTφ⟩ := hpure φ hφ
    rw [hTψ, hTφ, trace_rankOne_mul_rankOne, trace_rankOne_mul_rankOne,
      hT.norm_inner_eq hD hpure honto hψ hφ hψ' hTψ hTφ]
  rcases wigner_rankOne T hpure htr with ⟨W, hW⟩ | ⟨W, hW⟩
  · exact Or.inl ⟨W, fun ρ hρ => hT.eq_conjOp hW hρ⟩
  · exact Or.inr ⟨W, fun ρ hρ => hT.eq_conjOp hW hρ⟩

/-!
## G. Pure states are the extreme points
-/

/-- `ρ` is a pure state: `ρ = |ψ⟩⟨ψ|` for a unit vector `ψ`. -/
def IsPure (ρ : E →L[ℂ] E) : Prop := ∃ ψ : E, ‖ψ‖ = 1 ∧ ρ = proj ψ

/-- `ρ` is an extreme point of the density operators: in every proper mixture
`ρ = t σ + (1 - t) τ` of density operators, `σ = ρ` (and so, exchanging the two, `τ = ρ`). -/
def IsExtremeDensity (ρ : E →L[ℂ] E) : Prop :=
  IsDensity ρ ∧ ∀ σ τ : E →L[ℂ] E, IsDensity σ → IsDensity τ → ∀ t : ℝ, 0 < t → t < 1 →
    ρ = (t : ℂ) • σ + ((1 - t : ℝ) : ℂ) • τ → σ = ρ

section Extreme

variable [FiniteDimensional ℂ E]

/-- **Pure ⇒ extreme.** If `|ψ⟩⟨ψ| = t σ + (1 - t) τ` with `0 < t < 1`, the quadratic form of `σ`
vanishes on `ψ^⊥`, so `σ` kills `ψ^⊥` by positivity, and `σ = |ψ⟩⟨ψ|` by the trace. -/
lemma IsPure.isExtremeDensity {ρ : E →L[ℂ] E} (h : IsPure ρ) : IsExtremeDensity ρ := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  refine ⟨isDensity_proj hψ, fun σ τ hσ hτ t ht0 ht1 hmix => ?_⟩
  refine hσ.eq_proj_of_apply_eq_zero hψ fun x hx => ?_
  have key := congrArg (fun A : E →L[ℂ] E => (⟪x, A x⟫_ℂ).re) hmix
  simp only [inner_proj_apply, hx, norm_zero, add_apply, smul_apply, inner_add_right,
    inner_smul_right, Complex.add_re, Complex.re_ofReal_mul] at key
  have h1 := hσ.isPositive.re_inner_nonneg_right x
  have h2 := hτ.isPositive.re_inner_nonneg_right x
  simp only [ContinuousLinearMap.coe_coe, RCLike.re_to_complex] at h1 h2
  have h0 : (⟪x, σ x⟫_ℂ).re = 0 := by
    norm_num at key
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) h2]
  have := hσ.isPositive.apply_eq_zero_of_re_inner_eq_zero (x := x)
    (by rw [inner_re_symm]; simpa using h0)
  simpa using this

/-- **Extreme ⇒ pure.** Write `ρ = ∑ᵢ μᵢ |eᵢ⟩⟨eᵢ|` and pick `μᵢ > 0`. If `μᵢ < 1`, then `ρ` is the
proper mixture of `|eᵢ⟩⟨eᵢ|` and the renormalized rest, so `ρ = |eᵢ⟩⟨eᵢ|`. If `μᵢ = 1`, the rest
vanishes. -/
lemma IsExtremeDensity.isPure {ρ : E →L[ℂ] E} (h : IsExtremeDensity ρ) : IsPure ρ := by
  classical
  obtain ⟨hρ, hext⟩ := h
  have hsum := hρ.eq_sum_proj
  set μ := hρ.isPositive.isSymmetric.eigenvalues rfl
  set b := hρ.isPositive.isSymmetric.eigenvectorBasis rfl
  have hμ0 : ∀ i, 0 ≤ μ i := hρ.isPositive.nonneg_eigenvalues rfl
  have hμ1 : ∑ i, μ i = 1 := hρ.sum_eigenvalues
  obtain ⟨i, hi⟩ : ∃ i, 0 < μ i := by
    by_contra! h
    linarith [Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => h i]
  have hrest : ∑ j ∈ Finset.univ.erase i, μ j = 1 - μ i := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hμ1]
  have hsplit : ρ = (μ i : ℂ) • proj (b i) +
      ∑ j ∈ Finset.univ.erase i, (μ j : ℂ) • proj (b j) := by
    rw [Finset.add_sum_erase _ (fun j => (μ j : ℂ) • proj (b j)) (Finset.mem_univ i)]
    exact hsum
  rcases lt_or_ge (μ i) 1 with hi1 | hi1
  · have hpos : 0 < 1 - μ i := by linarith
    have hτ : IsDensity (∑ j ∈ Finset.univ.erase i, ((μ j / (1 - μ i) : ℝ) : ℂ) • proj (b j)) :=
      IsDensity.sum (fun j _ => div_nonneg (hμ0 j) hpos.le)
        (by rw [← Finset.sum_div, hrest, div_self hpos.ne'])
        fun j _ => isDensity_proj (b.norm_eq_one j)
    refine ⟨b i, b.norm_eq_one i,
      (hext _ _ (isDensity_proj (b.norm_eq_one i)) hτ (μ i) hi hi1 ?_).symm⟩
    rw [hsplit, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← Complex.ofReal_mul, mul_div_cancel₀ _ hpos.ne']
  · have hnn := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ.erase i) => hμ0 j
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun j (_ : j ∈ Finset.univ.erase i) => hμ0 j).mp
      (by linarith)
    have hi' : μ i = 1 := by linarith
    refine ⟨b i, b.norm_eq_one i, ?_⟩
    rw [hsplit, Finset.sum_eq_zero fun j hj => by rw [hz j hj, Complex.ofReal_zero, zero_smul],
      add_zero, hi', Complex.ofReal_one, one_smul]

lemma isPure_iff_isExtremeDensity {ρ : E →L[ℂ] E} : IsPure ρ ↔ IsExtremeDensity ρ :=
  ⟨IsPure.isExtremeDensity, IsExtremeDensity.isPure⟩

end Extreme

/-!
## H. Three characterizations of state automorphisms
-/

/-- `T` maps the pure states bijectively onto the pure states. -/
def BijOnPure (T : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  Set.BijOn T {ρ | IsPure ρ} {ρ | IsPure ρ}

/-- `T` is conjugation by a unitary or by an anti-unitary on every density operator. -/
def ImplementedByUnitaryOrAntiunitary (T : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  (∃ W : E ≃ₗᵢ[ℂ] E, ∀ ρ, IsDensity ρ → T ρ = conjOp W ρ) ∨
    (∃ W : E ≃ₗᵢ⋆[ℂ] E, ∀ ρ, IsDensity ρ → T ρ = conjOp W ρ)

variable [FiniteDimensional ℂ E] {T : (E →L[ℂ] E) → E →L[ℂ] E}

/-- An affine bijection of the density operators maps the extreme points, which
are the pure states, bijectively onto themselves. -/
theorem AffineOnDensities.bijOnPure (hT : AffineOnDensities T)
    (hbij : Set.BijOn T {ρ | IsDensity ρ} {ρ | IsDensity ρ}) : BijOnPure T := by
  refine ⟨fun ρ hρ => ?_,
    hbij.injOn.mono fun ρ hρ => (isPure_iff_isExtremeDensity.mp hρ).1, fun ρ' hρ' => ?_⟩
  · obtain ⟨hρD, hext⟩ := isPure_iff_isExtremeDensity.mp hρ
    refine isPure_iff_isExtremeDensity.mpr
      ⟨hbij.mapsTo hρD, fun σ τ hσ hτ t ht0 ht1 hmix => ?_⟩
    obtain ⟨σ₀, hσ₀, rfl⟩ := hbij.surjOn hσ
    obtain ⟨τ₀, hτ₀, rfl⟩ := hbij.surjOn hτ
    have h : (t : ℂ) • σ₀ + ((1 - t : ℝ) : ℂ) • τ₀ = ρ :=
      hbij.injOn (hσ₀.smul_add_smul hτ₀ ht0.le ht1.le) hρD
        (by rw [hT _ _ hσ₀ hτ₀ t ht0.le ht1.le, hmix])
    rw [hext σ₀ τ₀ hσ₀ hτ₀ t ht0 ht1 h.symm]
  · obtain ⟨hρ'D, hext⟩ := isPure_iff_isExtremeDensity.mp hρ'
    obtain ⟨ρ, hρD, rfl⟩ := hbij.surjOn hρ'D
    refine ⟨ρ, isPure_iff_isExtremeDensity.mpr ⟨hρD, fun σ τ hσ hτ t ht0 ht1 hmix => ?_⟩, rfl⟩
    exact hbij.injOn hσ hρD (hext (T σ) (T τ) (hbij.mapsTo hσ) (hbij.mapsTo hτ) t ht0 ht1
      (by rw [hmix, hT _ _ hσ hτ t ht0.le ht1.le]))

/-- Conjugation by a unitary or an anti-unitary `W` is a bijection of the
density operators, with inverse conjugation by `W⁻¹`. -/
theorem bijOn_of_eq_conjOp {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ]
    (W : E ≃ₛₗᵢ[σ] E) (hW : ∀ ρ, IsDensity ρ → T ρ = conjOp W ρ) :
    Set.BijOn T {ρ | IsDensity ρ} {ρ | IsDensity ρ} := by
  refine ⟨fun ρ hρ => ?_, fun ρ hρ τ hτ h => ?_,
    fun τ hτ => ⟨conjOp W.symm τ, hτ.conjOp W.symm, ?_⟩⟩
  · show IsDensity (T ρ)
    rw [hW ρ hρ]
    exact hρ.conjOp W
  · rw [hW ρ hρ, hW τ hτ] at h
    simpa [conjOp_symm_conjOp] using congrArg (conjOp W.symm) h
  · rw [hW _ (hτ.conjOp W.symm), conjOp_conjOp_symm]

/-- **Kadison's theorem, three forms**, in finite dimension. For a map `T` that sends density operators to density
operators and is affine on them, the following are equivalent:
(i) `T` is bijective on the pure states; (ii) `T` is bijective on the density operators;
(iii) `T` is conjugation by a unitary or an anti-unitary. No continuity is assumed. -/
theorem kadison_tfae (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ)) (hT : AffineOnDensities T) :
    [BijOnPure T, Set.BijOn T {ρ | IsDensity ρ} {ρ | IsDensity ρ},
      ImplementedByUnitaryOrAntiunitary T].TFAE := by
  tfae_have 1 → 3 := fun h => kadison hD hT (fun ψ hψ => h.mapsTo ⟨ψ, hψ, rfl⟩) fun ψ' hψ' => by
    obtain ⟨_, ⟨ψ, hψ, rfl⟩, h'⟩ := h.surjOn ⟨ψ', hψ', rfl⟩
    exact ⟨ψ, hψ, h'⟩
  tfae_have 3 → 2 := by
    rintro (⟨W, hW⟩ | ⟨W, hW⟩)
    exacts [bijOn_of_eq_conjOp W hW, bijOn_of_eq_conjOp W hW]
  tfae_have 2 → 1 := hT.bijOnPure
  tfae_finish

end QuantumMechanics.Wigner
