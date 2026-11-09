/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import ForMathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import ForPhyslib.QuantumMechanics.VonNeumannRelativeEntropy
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# The von Neumann entropy of mixtures of pure states

## i. Overview

For an orthonormal family `(ψᵢ)` in a Hilbert space of any dimension and weights `pᵢ ≥ 0` with
`∑ᵢ pᵢ = 1`, the mixture `ρ = ∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` converges in operator norm. Extending `(ψᵢ)` to a
Hilbert basis gives an eigenbasis of `ρ`, with eigenvalue `pᵢ` on `ψᵢ` and `0` on the added
vectors. So `ρ` is a density operator and its entropy is the Shannon entropy
`S(ρ) = ∑ᵢ η(pᵢ)`, `η(x) = -x log x`, in `[0, ∞]`. Conversely, every density operator is such a
mixture: of its eigenvectors with nonzero eigenvalue, a countable family since the eigenvalues
are summable.

For two unit vectors `ψ`, `ϕ` with `c = ⟨ψ, ϕ⟩`, the equal mixture `½ |ψ⟩⟨ψ| + ½ |ϕ⟩⟨ϕ|` is
diagonal in the orthogonal vectors `ψ ± ω ϕ`, where the phase `ω` makes `ω c = |c|`; the
eigenvalues are `(1 ± |c|) / 2`. Its entropy is the binary entropy `h((1 + |c|) / 2)`.

In infinite dimension the entropy can be infinite: countably many orthonormal pure states, mixed
with weights of infinite Shannon entropy, give a density operator `ρ` with `S(ρ) = ∞`.

## ii. Key results

- `QuantumMechanics.isDensityOperator_tsum_smul_proj`: `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` is a density operator.
- `QuantumMechanics.vonNeumannEntropy_tsum_smul_proj`: its entropy is `∑ᵢ η(pᵢ)`.
- `QuantumMechanics.IsDensityOperator.exists_tsum_smul_proj`: every density operator is such a
  mixture, of countably many orthonormal pure states.
- `QuantumMechanics.vonNeumannEntropy_mix_proj`: `S(½ |ψ⟩⟨ψ| + ½ |ϕ⟩⟨ϕ|) = h((1 + |⟨ψ, ϕ⟩|) / 2)`.
- `QuantumMechanics.exists_isDensityOperator_vonNeumannEntropy_eq_top`: in infinite dimension,
  some density operator has entropy `∞`.

## iii. Table of contents

- A. Mixtures of orthonormal pure states
- B. Equal mixtures of two pure states
- C. Infinite entropy

## iv. References

- M. A. Nielsen, I. L. Chuang, *Quantum Computation and Quantum Information*, Cambridge
  University Press (2000), §11.3.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder ComplexConjugate
open InnerProductSpace Real QuantumMechanics.Wigner

namespace QuantumMechanics

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. Mixtures of orthonormal pure states -/

section Orthonormal

variable {ι : Type*} {ψ : ι → E} {p : ι → ℝ}

lemma summable_smul_proj (hψ : Orthonormal ℂ ψ) (hp : Summable p) :
    Summable fun i => (p i : ℂ) • proj (ψ i) :=
  Summable.of_norm_bounded hp.abs fun i => by simp [norm_smul, hψ.1 i]

lemma hasSum_smul_proj_apply (hψ : Orthonormal ℂ ψ) (hp : Summable p) (x : E) :
    HasSum (fun i => ((p i : ℂ) * ⟪ψ i, x⟫_ℂ) • ψ i) ((∑' i, (p i : ℂ) • proj (ψ i)) x) := by
  convert (ContinuousLinearMap.apply ℂ E x).hasSum (summable_smul_proj hψ hp).hasSum using 1
  · ext i
    exact mul_smul _ _ _
  · rfl

/-- `(∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|) ψⱼ = pⱼ ψⱼ`. -/
lemma tsum_smul_proj_apply_self (hψ : Orthonormal ℂ ψ) (hp : Summable p) (j : ι) :
    (∑' i, (p i : ℂ) • proj (ψ i)) (ψ j) = (p j : ℂ) • ψ j := by
  classical
  refine (hasSum_smul_proj_apply hψ hp (ψ j)).unique ?_
  convert hasSum_ite_eq j ((p j : ℂ) • ψ j) using 2 with i
  rw [orthonormal_iff_ite.mp hψ i j]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero, zero_smul]

lemma tsum_smul_proj_apply_of_inner_eq_zero (hψ : Orthonormal ℂ ψ) (hp : Summable p) {x : E}
    (hx : ∀ i, ⟪ψ i, x⟫_ℂ = 0) : (∑' i, (p i : ℂ) • proj (ψ i)) x = 0 := by
  have h := hasSum_smul_proj_apply hψ hp x
  simp only [hx, mul_zero, zero_smul] at h
  exact h.unique hasSum_zero

/-- `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` is positive: `⟨x, ρ x⟩ = ∑ᵢ pᵢ |⟨ψᵢ, x⟩|²`. -/
lemma tsum_smul_proj_nonneg (hψ : Orthonormal ℂ ψ) (hp0 : ∀ i, 0 ≤ p i) (hp : Summable p) :
    0 ≤ ∑' i, (p i : ℂ) • proj (ψ i) := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  set ρ := ∑' i, (p i : ℂ) • proj (ψ i)
  have h := (innerSL ℂ x).hasSum (hasSum_smul_proj_apply hψ hp x)
  have e : ∀ i, innerSL ℂ x (((p i : ℂ) * ⟪ψ i, x⟫_ℂ) • ψ i) =
      ((p i * ‖⟪ψ i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [innerSL_apply_apply, inner_smul_right, ← inner_conj_symm x (ψ i), mul_assoc,
      Complex.mul_conj']
    push_cast
    ring
  simp only [e] at h
  have hre := Complex.hasSum_re h
  have him := Complex.hasSum_im h
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have him0 : (⟪x, ρ x⟫_ℂ).im = 0 := him.unique hasSum_zero
  have hre0 : 0 ≤ (⟪x, ρ x⟫_ℂ).re := hre.nonneg fun i => by have := hp0 i; positivity
  have hc : ⟪ρ x, x⟫_ℂ = ((⟪x, ρ x⟫_ℂ).re : ℂ) := by
    rw [← inner_conj_symm (ρ x) x]
    apply Complex.ext <;>
      simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, him0,
        neg_zero]
  rw [hc]
  simp [hre0]

/-- Extending `ψ` to a Hilbert basis gives an eigenbasis of `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|`, and sums over its
eigenvalues reduce to sums over the weights. -/
private lemma exists_isEigenbasis (hψ : Orthonormal ℂ ψ) (hp : Summable p) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (ev : w → ℝ),
      IsEigenbasis (∑' i, (p i : ℂ) • proj (ψ i)) b ev ∧
      ∀ F : ℝ → ℝ≥0∞, F 0 = 0 → ∑' k, F (ev k) = ∑' i, F (p i) := by
  set ρ := ∑' i, (p i : ℂ) • proj (ψ i)
  obtain ⟨w, b, hsw, hb⟩ := hψ.toSubtypeRange.exists_hilbertBasis_extension
  have hoff : ∀ v ∈ w, v ∉ Set.range ψ → ρ v = 0 := fun v hv hvr =>
    tsum_smul_proj_apply_of_inner_eq_zero hψ hp fun i => by
      have hne : (⟨ψ i, hsw ⟨i, rfl⟩⟩ : w) ≠ ⟨v, hv⟩ := fun h => hvr ⟨i, congrArg Subtype.val h⟩
      simpa [hb] using b.orthonormal.2 hne
  have hon : ∀ j, (⟪ψ j, ρ (ψ j)⟫_ℂ).re = p j := fun j => by
    rw [tsum_smul_proj_apply_self hψ hp j, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ.1 j]
    simp
  set G : (ℝ → ℝ≥0∞) → E → ℝ≥0∞ := fun F v => F (⟪v, ρ v⟫_ℂ).re
  refine ⟨w, b, fun k => (⟪(k : E), ρ k⟫_ℂ).re, ⟨fun k => ?_⟩, fun F hF => ?_⟩
  · rw [hb]
    by_cases hk : (k : E) ∈ Set.range ψ
    · obtain ⟨j, hj⟩ := hk
      rw [← hj, hon j, tsum_smul_proj_apply_self hψ hp j]
    · rw [hoff k k.2 hk]
      simp
  · have h : w.indicator (G F) = (Set.range ψ).indicator (G F) := by
      funext v
      by_cases hvr : v ∈ Set.range ψ
      · rw [Set.indicator_of_mem (hsw hvr), Set.indicator_of_mem hvr]
      · rw [Set.indicator_of_notMem hvr]
        by_cases hv : v ∈ w
        · rw [Set.indicator_of_mem hv]
          simp [G, hoff v hv hvr, hF]
        · exact Set.indicator_of_notMem hv _
    have h1 := tsum_subtype w (G F)
    have h2 := tsum_subtype (Set.range ψ) (G F)
    rw [tsum_range (G F) hψ.linearIndependent.injective] at h2
    simp only [G, hon] at h1 h2
    rw [h1, h, ← h2]

/-- A mixture `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` of orthonormal pure states is a density operator. -/
theorem isDensityOperator_tsum_smul_proj (hψ : Orthonormal ℂ ψ) (hp0 : ∀ i, 0 ≤ p i)
    (hp : HasSum p 1) : IsDensityOperator (∑' i, (p i : ℂ) • proj (ψ i)) := by
  have h0 := tsum_smul_proj_nonneg hψ hp0 hp.summable
  obtain ⟨w, b, ev, he, hF⟩ := exists_isEigenbasis hψ hp.summable
  refine isDensityOperator_iff.mpr ⟨h0, ?_⟩
  rw [he.posTrace_eq h0, hF ENNReal.ofReal ENNReal.ofReal_zero,
    ← ENNReal.ofReal_tsum_of_nonneg hp0 hp.summable, hp.tsum_eq, ENNReal.ofReal_one]

/-- The entropy of a mixture of orthonormal pure states is the Shannon entropy of the weights:
`S(∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|) = ∑ᵢ η(pᵢ)`. -/
theorem vonNeumannEntropy_tsum_smul_proj (hψ : Orthonormal ℂ ψ) (hp0 : ∀ i, 0 ≤ p i)
    (hp : HasSum p 1) :
    vonNeumannEntropy (∑' i, (p i : ℂ) • proj (ψ i)) =
      ∑' i, ENNReal.ofReal (negMulLog (p i)) := by
  obtain ⟨w, b, ev, he, hF⟩ := exists_isEigenbasis hψ hp.summable
  rw [he.vonNeumannEntropy_eq (isDensityOperator_tsum_smul_proj hψ hp0 hp),
    hF (fun x => ENNReal.ofReal (negMulLog x)) (by simp)]

end Orthonormal

/-- Every density operator is a mixture `∑ᵢ pᵢ |ψᵢ⟩⟨ψᵢ|` of countably many orthonormal pure
states: its eigenvectors with nonzero eigenvalue. -/
theorem IsDensityOperator.exists_tsum_smul_proj {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    ∃ (ι : Type u) (_ : Countable ι) (ψ : ι → E) (p : ι → ℝ), Orthonormal ℂ ψ ∧
      (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧ ∑' i, (p i : ℂ) • proj (ψ i) = ρ := by
  set e := hρ.eigenbasis
  set ev := hρ.eigenvalue
  have he : IsEigenbasis ρ e ev := hρ.isEigenbasis
  have hev0 : ∀ i, 0 ≤ ev i := fun i => (he.eigenvalue_mem_Icc hρ i).1
  have hsum : HasSum ev 1 := by
    have h1 := he.tsum_ofReal_eq_one hρ
    have hs : Summable ev := (summable_iff_tsum_ofReal_ne_top hev0).mpr (by rw [h1]; simp)
    rw [← ENNReal.ofReal_tsum_of_nonneg hev0 hs, ENNReal.ofReal_eq_one] at h1
    exact h1 ▸ hs.hasSum
  set s := Function.support ev
  have hs : Countable s := hsum.summable.countable_support.to_subtype
  set φ : s → E := fun i => e i
  set w : s → ℝ := fun i => ev i
  have hφ : Orthonormal ℂ φ := e.orthonormal.comp _ Subtype.val_injective
  have hw : HasSum w 1 := (hasSum_subtype_iff_of_support_subset subset_rfl).mpr hsum
  refine ⟨s, hs, φ, w, hφ, fun i => hev0 i, hw, ?_⟩
  refine ContinuousLinearMap.ext_on
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span) ?_
  rintro _ ⟨k, rfl⟩
  by_cases hk : k ∈ s
  · exact (tsum_smul_proj_apply_self hφ hw.summable ⟨k, hk⟩).trans (he.apply_eq k).symm
  · have hk0 : ev k = 0 := by simpa [s] using hk
    rw [tsum_smul_proj_apply_of_inner_eq_zero hφ hw.summable
      fun i => e.orthonormal.2 fun h => hk (by rw [← h]; exact i.2), he.apply_eq k, hk0]
    simp

/-! ## B. Equal mixtures of two pure states -/

/-- **The entropy of an equal mixture of two pure states** is the binary entropy of
`(1 + |⟨ψ, ϕ⟩|) / 2`. -/
theorem vonNeumannEntropy_mix_proj {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    vonNeumannEntropy (mix (proj ψ) (proj ϕ)) =
      ENNReal.ofReal (binEntropy ((1 + ‖⟪ψ, ϕ⟫_ℂ‖) / 2)) := by
  set c := ⟪ψ, ϕ⟫_ℂ with hc
  have hc1 : ‖c‖ ≤ 1 := by simpa [hψ, hϕ] using norm_inner_le_norm (𝕜 := ℂ) ψ ϕ
  have hψ0 : ψ ≠ 0 := by rintro rfl; simp at hψ
  have hϕ0 : ϕ ≠ 0 := by rintro rfl; simp at hϕ
  rcases hc1.lt_or_eq with hlt | heq
  swap
  · obtain ⟨r, -, rfl⟩ := (norm_inner_eq_norm_iff hψ0 hϕ0).mp (by rw [← hc, heq, hψ, hϕ, one_mul])
    have hr : ‖r‖ = 1 := by simpa [norm_smul, hψ] using hϕ
    have hm : mix (proj ψ) (proj (r • ψ)) = proj ψ := by
      rw [proj_smul, hr, one_pow, Complex.ofReal_one, one_smul, mix, ← add_smul]
      norm_num
    rw [hm, vonNeumannEntropy_proj hψ, heq]
    norm_num
  -- The phase `ω` with `ω c = |c|`.
  set ω : ℂ := if c = 0 then 1 else conj c / (‖c‖ : ℂ) with hω_def
  have hω : ‖ω‖ = 1 := by
    rw [hω_def]; split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr h)]
  have hωc : ω * c = ‖c‖ := by
    rw [hω_def]; split_ifs with h
    · simp [h]
    · have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      rw [div_mul_eq_mul_div, Complex.conj_mul']
      field_simp
  have hωω : conj ω * ω = 1 := by rw [Complex.conj_mul', hω]; simp
  set x := ψ + ω • ϕ
  set y := ψ - ω • ϕ
  have hin : ⟪ψ, ω • ϕ⟫_ℂ = ‖c‖ := by rw [inner_smul_right, ← hc, hωc]
  have hωϕ : ‖ω • ϕ‖ = 1 := by rw [norm_smul, hω, hϕ, one_mul]
  have hx2 : ‖x‖ ^ 2 = 2 * (1 + ‖c‖) := by
    rw [norm_add_sq (𝕜 := ℂ), hin, hψ, hωϕ]; simp; ring
  have hy2 : ‖y‖ ^ 2 = 2 * (1 - ‖c‖) := by
    rw [norm_sub_sq (𝕜 := ℂ), hin, hψ, hωϕ]; simp; ring
  have hxy : ⟪x, y⟫_ℂ = 0 := by
    have h1 : ⟪ω • ϕ, ψ⟫_ℂ = ‖c‖ := by rw [← inner_conj_symm, hin, Complex.conj_ofReal]
    have h2 : ⟪ω • ϕ, ω • ϕ⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hωϕ]; simp
    simp only [x, y, inner_add_left, inner_sub_right, hin, h1, h2, inner_self_eq_norm_sq_to_K,
      hψ]
    simp
    ring
  have hxpos : 0 < ‖x‖ := by
    refine (norm_nonneg x).lt_of_ne fun h0 => ?_
    rw [← h0] at hx2
    nlinarith [norm_nonneg c]
  have hypos : 0 < ‖y‖ := by
    refine (norm_nonneg y).lt_of_ne fun h0 => ?_
    rw [← h0] at hy2
    nlinarith
  -- The normalized eigenvectors and the eigenvalues.
  set v : Fin 2 → E := ![(‖x‖⁻¹ : ℂ) • x, (‖y‖⁻¹ : ℂ) • y]
  set q : Fin 2 → ℝ := ![(1 + ‖c‖) / 2, (1 - ‖c‖) / 2]
  have hxn : ‖(‖x‖⁻¹ : ℂ) • x‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hxpos.ne']
  have hyn : ‖(‖y‖⁻¹ : ℂ) • y‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ hypos.ne']
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [v, inner_smul_left, inner_smul_right, hxy, inner_self_eq_norm_sq_to_K,
        ← inner_conj_symm y x, hxn, hyn]
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    fin_cases i <;> simp [q] <;> linarith [norm_nonneg c]
  have hq1 : ∀ i, q i ≤ 1 := fun i => by
    fin_cases i <;> simp [q] <;> linarith [norm_nonneg c]
  have hq : HasSum q 1 := by
    convert hasSum_fintype q using 1
    simp [q, Fin.sum_univ_two]; ring
  have hmix : mix (proj ψ) (proj ϕ) = ∑' i, (q i : ℂ) • proj (v i) := by
    rw [tsum_fintype, Fin.sum_univ_two]
    simp only [v, q, Matrix.cons_val_zero, Matrix.cons_val_one, proj_smul]
    have hp := proj_add_add_proj_sub ψ (ω • ϕ)
    rw [proj_smul, hω, one_pow, Complex.ofReal_one, one_smul] at hp
    have ex : ‖(‖x‖⁻¹ : ℂ)‖ ^ 2 = (2 * (1 + ‖c‖))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_pow, hx2]
    have ey : ‖(‖y‖⁻¹ : ℂ)‖ ^ 2 = (2 * (1 - ‖c‖))⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm, inv_pow, hy2]
    have h1 : (1 + ‖c‖) ≠ 0 := by positivity
    have h2 : (1 - ‖c‖) ≠ 0 := by linarith
    rw [ex, ey, smul_smul, smul_smul]
    have e1 : (((1 + ‖c‖) / 2 : ℝ) : ℂ) * (((2 * (1 + ‖c‖))⁻¹ : ℝ) : ℂ) = 4⁻¹ := by
      push_cast; field_simp; norm_num
    have e2 : (((1 - ‖c‖) / 2 : ℝ) : ℂ) * (((2 * (1 - ‖c‖))⁻¹ : ℝ) : ℂ) = 4⁻¹ := by
      have : (1 - (‖c‖ : ℂ)) ≠ 0 := by exact_mod_cast h2
      push_cast; field_simp; norm_num
    rw [e1, e2, ← smul_add, hp, mix, smul_add, smul_smul, smul_smul]
    norm_num
  rw [hmix, vonNeumannEntropy_tsum_smul_proj hv hq0 hq, tsum_fintype, Fin.sum_univ_two,
    ← ENNReal.ofReal_add (negMulLog_nonneg (hq0 0) (hq1 0)) (negMulLog_nonneg (hq0 1) (hq1 1)),
    binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  congr 3
  simp [q]; ring

/-! ## C. Infinite entropy -/

omit [CompleteSpace E] in
/-- In infinite dimension, a countable orthonormal family with weights of infinite Shannon
entropy. -/
theorem exists_orthonormal_tsum_negMulLog_eq_top (hE : ¬ FiniteDimensional ℂ E) :
    ∃ (ι : Type u) (_ : Countable ι) (ψ : ι → E) (p : ι → ℝ), Orthonormal ℂ ψ ∧
      (∀ i, 0 ≤ p i) ∧ HasSum p 1 ∧ ∑' i, ENNReal.ofReal (negMulLog (p i)) = ∞ := by
  obtain ⟨ι, _, w, hw0, hw, hent⟩ := exists_hasSum_one_tsum_negMulLog_eq_top
  obtain ⟨ψ, hψ⟩ := exists_orthonormal_of_not_finiteDimensional (ι := ULift.{u} ι) hE
  refine ⟨ULift.{u} ι, inferInstance, ψ, w ∘ ULift.down, hψ, fun i => hw0 _,
    (Equiv.ulift.hasSum_iff (f := w)).mpr hw, ?_⟩
  rw [← hent]
  exact Equiv.ulift.tsum_eq fun i => ENNReal.ofReal (negMulLog (w i))

/-- In infinite dimension, some density operator has infinite entropy. -/
theorem exists_isDensityOperator_vonNeumannEntropy_eq_top (hE : ¬ FiniteDimensional ℂ E) :
    ∃ ρ : E →L[ℂ] E, IsDensityOperator ρ ∧ vonNeumannEntropy ρ = ∞ := by
  obtain ⟨ι, _, ψ, p, hψ, hp0, hp, hent⟩ := exists_orthonormal_tsum_negMulLog_eq_top hE
  exact ⟨_, isDensityOperator_tsum_smul_proj hψ hp0 hp,
    (vonNeumannEntropy_tsum_smul_proj hψ hp0 hp).trans hent⟩

end QuantumMechanics
