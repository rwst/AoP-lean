/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.VonNeumannRelativeEntropy

/-!
# Lindblad's formula does not depend on the eigenbases

## i. Overview

The relative entropy `relativeEntropy ρ σ` is Lindblad's formula
`∑ᵢⱼ |⟨eᵢ, fⱼ⟩|² K(λᵢ, μⱼ)`, `K = kleinTerm`, in eigenbases `(eᵢ, λᵢ)` of `ρ` and `(fⱼ, μⱼ)` of
`σ` chosen once. Eigenbases are not unique when eigenvalues are degenerate, in particular on an
infinite-dimensional kernel. This file shows that the sum does not depend on them, with no
assumption on the entropy.

Let `Pₐ` be the orthogonal projection onto the eigenspace `ker(ρ - a)` (`eigenproj ρ a`), and
`Q_b = eigenproj σ b`. For an eigenbasis of a self-adjoint `ρ`, `Pₐ eᵢ` is `eᵢ` if `λᵢ = a` and `0`
otherwise, since eigenspaces of distinct eigenvalues are orthogonal. Grouping the sum by the
eigenvalues, all terms being in `[0, ∞]`,
`∑ᵢⱼ |⟨eᵢ, fⱼ⟩|² K(λᵢ, μⱼ) = ∑_{a,b} tr(Q_b Pₐ (Q_b Pₐ)†) K(a, b)`.
The right side involves no basis.

## ii. Key results

- `QuantumMechanics.eigenproj`: the orthogonal projection onto an eigenspace.
- `QuantumMechanics.IsEigenbasis.eigenproj_apply`: `Pₐ eᵢ = if λᵢ = a then eᵢ else 0`.
- `QuantumMechanics.IsEigenbasis.lindbladSum_eq_tsum_eigenproj`: Lindblad's sum in terms of the
  eigenprojections.
- `QuantumMechanics.IsEigenbasis.lindbladSum_eq_lindbladSum`: the sum is the same in any two
  pairs of eigenbases.
- `QuantumMechanics.relativeEntropy_eq_lindbladSum_of_isEigenbasis`: the relative entropy is
  Lindblad's formula in **any** eigenbases, with no finiteness assumption.
- `QuantumMechanics.relativeEntropy_eq_tsum_eigenproj`: a basis-free formula for it.

## iii. Table of contents

- A. Eigenprojections
- B. Grouping by eigenvalues
- C. Basis independence
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal
open ContinuousLinearMap (posTrace posTrace_mul_star)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. Eigenprojections -/

instance (ρ : E →L[ℂ] E) (a : ℝ) :
    ((ρ - (a : ℂ) • (1 : E →L[ℂ] E)).ker).HasOrthogonalProjection :=
  haveI : CompleteSpace ((ρ - (a : ℂ) • (1 : E →L[ℂ] E)).ker) :=
    (ContinuousLinearMap.isClosed_ker _).completeSpace_coe
  inferInstance

/-- The orthogonal projection onto the eigenspace `ker(ρ - a)`. -/
def eigenproj (ρ : E →L[ℂ] E) (a : ℝ) : E →L[ℂ] E :=
  ((ρ - (a : ℂ) • (1 : E →L[ℂ] E)).ker).starProjection

omit [CompleteSpace E] in
lemma mem_ker_sub_smul_one {ρ : E →L[ℂ] E} {a : ℝ} {v : E} :
    v ∈ (ρ - (a : ℂ) • (1 : E →L[ℂ] E)).ker ↔ ρ v = (a : ℂ) • v := by
  simp [sub_eq_zero]

namespace IsEigenbasis

variable {ρ : E →L[ℂ] E} {ι : Type*} {e : HilbertBasis ι ℂ E} {ev : ι → ℝ}

/-- For an eigenbasis of a self-adjoint `ρ`, `Pₐ eᵢ = eᵢ` if `λᵢ = a`, and `0` otherwise. -/
lemma eigenproj_apply (hρ : IsSelfAdjoint ρ) (he : IsEigenbasis ρ e ev) (a : ℝ) (i : ι) :
    eigenproj ρ a (e i) = if ev i = a then e i else 0 := by
  split_ifs with h
  · exact Submodule.starProjection_eq_self_iff.mpr (mem_ker_sub_smul_one.mpr (h ▸ he.apply_eq i))
  · refine (Submodule.starProjection_apply_eq_zero_iff _).mpr fun u hu => ?_
    have hu' := mem_ker_sub_smul_one.mp hu
    have h1 : ⟪ρ u, e i⟫_ℂ = ⟪u, ρ (e i)⟫_ℂ := hρ.isSymmetric u (e i)
    rw [hu', he.apply_eq, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
    have h2 : ((a : ℂ) - ev i) * ⟪u, e i⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (by exact_mod_cast sub_eq_zero.mp h3) (Ne.symm h)
    · exact h3

/-- Parseval in an eigenspace: `∑_{i : λᵢ = b} |⟨x, eᵢ⟩|² = ‖P_b x‖²`. -/
lemma tsum_ite_ofReal_norm_inner_sq (hρ : IsSelfAdjoint ρ) (he : IsEigenbasis ρ e ev) (b : ℝ)
    (x : E) :
    ∑' i, (if ev i = b then ENNReal.ofReal (‖⟪x, e i⟫_ℂ‖ ^ 2) else 0) =
      ENNReal.ofReal (‖eigenproj ρ b x‖ ^ 2) := by
  rw [← e.tsum_ofReal_norm_inner_sq (eigenproj ρ b x)]
  refine tsum_congr fun i => ?_
  rw [eigenproj, ← Submodule.inner_starProjection_left_eq_right, ← eigenproj,
    he.eigenproj_apply hρ b i, norm_inner_symm]
  split_ifs <;> simp

end IsEigenbasis

/-! ## B. Grouping by eigenvalues -/

/-- Grouping a sum `∑ᵢ Fᵢ K(gᵢ)` by the values of `g`. -/
lemma tsum_mul_eq_tsum_fiberwise {ι : Type*} (F : ι → ℝ≥0∞) (g : ι → ℝ) (K : ℝ → ℝ≥0∞) :
    ∑' i, F i * K (g i) = ∑' a, (∑' i, if g i = a then F i else 0) * K a := by
  rw [← tsum_fiberwise _ g]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_right, tsum_subtype (g ⁻¹' {a}) (fun i => F i * K (g i))]
  refine tsum_congr fun i => ?_
  by_cases h : g i = a
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

variable {ρ σ : E →L[ℂ] E} {ι κ : Type*} {e : HilbertBasis ι ℂ E} {ev : ι → ℝ}
  {f : HilbertBasis κ ℂ E} {μ : κ → ℝ}

namespace IsEigenbasis

/-- **Lindblad's sum in terms of the eigenprojections**:
`∑ᵢⱼ |⟨eᵢ, fⱼ⟩|² K(λᵢ, μⱼ) = ∑_{b,a} tr(Q_b Pₐ (Q_b Pₐ)†) K(a, b)`. -/
theorem lindbladSum_eq_tsum_eigenproj (hρ : IsSelfAdjoint ρ) (hσ : IsSelfAdjoint σ)
    (he : IsEigenbasis ρ e ev) (hf : IsEigenbasis σ f μ) :
    lindbladSum e ev f μ = ∑' b, ∑' a,
      posTrace ((eigenproj σ b * eigenproj ρ a) * star (eigenproj σ b * eigenproj ρ a)) *
        kleinTerm a b := by
  -- group `j` by `μⱼ`
  have h1 : ∀ i, ∑' j, ENNReal.ofReal (‖⟪e i, f j⟫_ℂ‖ ^ 2) * kleinTerm (ev i) (μ j) =
      ∑' b, ENNReal.ofReal (‖eigenproj σ b (e i)‖ ^ 2) * kleinTerm (ev i) b := fun i => by
    rw [tsum_mul_eq_tsum_fiberwise _ μ (kleinTerm (ev i))]
    exact tsum_congr fun b => by rw [hf.tsum_ite_ofReal_norm_inner_sq hσ b (e i)]
  rw [lindbladSum]
  simp_rw [h1]
  rw [tsum_comm]
  refine tsum_congr fun b => ?_
  -- group `i` by `λᵢ`
  rw [tsum_mul_eq_tsum_fiberwise (fun i => ENNReal.ofReal (‖eigenproj σ b (e i)‖ ^ 2)) ev
    (fun a => kleinTerm a b)]
  refine tsum_congr fun a => ?_
  congr 1
  rw [posTrace_mul_star _ e]
  refine tsum_congr fun i => ?_
  rw [mul_apply_eq_comp, he.eigenproj_apply hρ a i]
  split_ifs <;> simp

/-- **Basis independence**: Lindblad's sum is the same in any two pairs of eigenbases. -/
theorem lindbladSum_eq_lindbladSum (hρ : IsSelfAdjoint ρ) (hσ : IsSelfAdjoint σ)
    (he : IsEigenbasis ρ e ev) (hf : IsEigenbasis σ f μ) {ι' κ' : Type*}
    {e' : HilbertBasis ι' ℂ E} {ev' : ι' → ℝ} {f' : HilbertBasis κ' ℂ E} {μ' : κ' → ℝ}
    (he' : IsEigenbasis ρ e' ev') (hf' : IsEigenbasis σ f' μ') :
    lindbladSum e ev f μ = lindbladSum e' ev' f' μ' := by
  rw [he.lindbladSum_eq_tsum_eigenproj hρ hσ hf, he'.lindbladSum_eq_tsum_eigenproj hρ hσ hf']

end IsEigenbasis

/-! ## C. Basis independence of the relative entropy -/

/-- The relative entropy is Lindblad's formula in **any** eigenbases of `ρ` and `σ`; unlike
`relativeEntropy_eq_lindbladSum`, no finiteness of `S(ρ)` is assumed. -/
theorem relativeEntropy_eq_lindbladSum_of_isEigenbasis (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (he : IsEigenbasis ρ e ev) (hf : IsEigenbasis σ f μ) :
    relativeEntropy ρ σ = lindbladSum e ev f μ := by
  simp only [relativeEntropy, hρ, hσ, and_self, ↓reduceDIte]
  exact hρ.isEigenbasis.lindbladSum_eq_lindbladSum hρ.isSelfAdjoint hσ.isSelfAdjoint
    hσ.isEigenbasis he hf

/-- A basis-free formula: `D(ρ‖σ) = ∑_{b,a} tr(Q_b Pₐ (Q_b Pₐ)†) K(a, b)`, with `Pₐ` and `Q_b`
the eigenprojections of `ρ` and `σ`. -/
theorem relativeEntropy_eq_tsum_eigenproj (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) :
    relativeEntropy ρ σ = ∑' b, ∑' a,
      posTrace ((eigenproj σ b * eigenproj ρ a) * star (eigenproj σ b * eigenproj ρ a)) *
        kleinTerm a b := by
  rw [relativeEntropy_eq_lindbladSum_of_isEigenbasis hρ hσ hρ.isEigenbasis hσ.isEigenbasis]
  exact hρ.isEigenbasis.lindbladSum_eq_tsum_eigenproj hρ.isSelfAdjoint hσ.isSelfAdjoint
    hσ.isEigenbasis

end QuantumMechanics
