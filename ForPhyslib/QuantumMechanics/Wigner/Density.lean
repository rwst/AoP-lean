/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Density operators

## i. Overview

A density operator on a complex inner product space `E` is a positive operator of trace one. The
pure states are the rank-one projections `|ψ⟩⟨ψ|` for unit `ψ`, and the equal mixture of two
density operators is `½ ρ + ½ σ`. This file collects the basic closure properties used by the
Wigner and Kadison theorems and by the briefs built on them: finite convex combinations, maps that
are affine on density operators, conjugation `ρ ↦ W ρ W⁻¹` by a unitary or an anti-unitary `W`, and
the spectral decomposition `ρ = ∑ᵢ μᵢ |eᵢ⟩⟨eᵢ|` in finite dimension.

## ii. Key results

- `QuantumMechanics.Wigner.proj_add_add_proj_sub`: the parallelogram law for pure states.
- `QuantumMechanics.Wigner.IsDensity`: positive with trace one.
- `QuantumMechanics.Wigner.isDensity_proj`: a pure state is a density operator.
- `QuantumMechanics.Wigner.IsDensity.mix`: density operators are closed under equal mixtures.
- `QuantumMechanics.Wigner.IsDensity.sum_eigenvalues`: the eigenvalues sum to one.
- `QuantumMechanics.Wigner.IsDensity.unitary_conj`: unitary conjugation preserves density
  operators.
- `QuantumMechanics.Wigner.IsDensity.sum`: finite convex combinations of density operators.
- `QuantumMechanics.Wigner.AffineOnDensities.map_sum`: an affine map preserves them.
- `QuantumMechanics.Wigner.AffineOnDensities.map_mix`: in particular, equal mixtures.
- `QuantumMechanics.Wigner.conjOp`, `QuantumMechanics.Wigner.conjOp_proj`: conjugation by a unitary
  or an anti-unitary, and `W |ψ⟩⟨ψ| W⁻¹ = |W ψ⟩⟨W ψ|`.
- `QuantumMechanics.Wigner.norm_conjOp_le`: conjugation does not increase the operator norm.
- `QuantumMechanics.Wigner.conjOp_trans_self`: conjugating twice by `W` is conjugating by the
  linear `W ∘ W`.
- `QuantumMechanics.Wigner.IsDensity.eq_sum_proj`: the spectral decomposition.
- `QuantumMechanics.Wigner.IsDensity.conjOp`: conjugation by a unitary or an anti-unitary
  preserves density operators.
- `QuantumMechanics.Wigner.IsDensity.eq_proj_of_apply_eq_zero`: a density operator that kills
  `ψ^⊥` is `|ψ⟩⟨ψ|`.

## iii. Table of contents

- A. Pure states and equal mixtures
- B. Density operators
- C. Maps that are affine on density operators
- D. Conjugation by a unitary or an anti-unitary
- E. Finite dimension

## iv. References

- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), 327–349.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. Pure states and equal mixtures
-/

/-- The pure state `|ψ⟩⟨ψ|`. -/
abbrev proj (ψ : E) : E →L[ℂ] E := rankOne ℂ ψ ψ

lemma proj_apply (ψ x : E) : proj ψ x = ⟪ψ, x⟫_ℂ • ψ := rfl

/-- `⟪u, |ψ⟩⟨ψ| u⟫ = |⟪ψ, u⟫|²`. -/
lemma inner_proj_apply (ψ u : E) : ⟪u, proj ψ u⟫_ℂ = ((‖⟪ψ, u⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [proj_apply, inner_smul_right, ← inner_conj_symm u ψ, Complex.mul_conj']
  push_cast
  ring

/-- `|c x⟩⟨c x| = |c|² |x⟩⟨x|`. -/
lemma proj_smul (c : ℂ) (x : E) : proj (c • x) = ((‖c‖ ^ 2 : ℝ) : ℂ) • proj x := by
  ext z
  simp only [smul_apply, proj_apply, inner_smul_left, smul_smul]
  congr 1
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  ring

/-- The parallelogram law for pure states:
`|x + y⟩⟨x + y| + |x - y⟩⟨x - y| = 2 |x⟩⟨x| + 2 |y⟩⟨y|`. -/
lemma proj_add_add_proj_sub (x y : E) :
    proj (x + y) + proj (x - y) = (2 : ℂ) • proj x + (2 : ℂ) • proj y := by
  ext z
  simp only [add_apply, smul_apply, proj_apply,
    inner_add_left, inner_sub_left]
  module

/-- The equal mixture `½ ρ + ½ σ`. -/
abbrev mix (ρ σ : E →L[ℂ] E) : E →L[ℂ] E := (2⁻¹ : ℂ) • ρ + (2⁻¹ : ℂ) • σ

/-!
## B. Density operators
-/

/-- A density operator: positive with trace one. -/
structure IsDensity (ρ : E →L[ℂ] E) : Prop where
  isPositive : (ρ : E →ₗ[ℂ] E).IsPositive
  trace_eq_one : LinearMap.trace ℂ E ρ = 1

/-- Density operators are closed under equal mixtures. -/
lemma IsDensity.mix {ρ σ : E →L[ℂ] E} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    IsDensity (mix ρ σ) where
  isPositive := by
    have h2 : (0 : ℂ) ≤ 2⁻¹ := by positivity
    exact (hρ.isPositive.smul_of_nonneg h2).add (hσ.isPositive.smul_of_nonneg h2)
  trace_eq_one := by
    simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      map_add, map_smul, hρ.trace_eq_one, hσ.trace_eq_one]
    norm_num

/-- Unitary conjugation preserves density operators. -/
theorem IsDensity.unitary_conj [CompleteSpace E] {U : E →L[ℂ] E}
    (hU : U ∈ unitary (E →L[ℂ] E)) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    IsDensity (U * ρ * star U) where
  isPositive := by
    have h :=
      ((ContinuousLinearMap.isPositive_toLinearMap_iff ρ).mp hρ.isPositive).conj_adjoint U
    rw [← ContinuousLinearMap.star_eq_adjoint] at h
    exact h.toLinearMap
  trace_eq_one := by
    rw [ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
      ← ContinuousLinearMap.toLinearMap_mul, ← mul_assoc, (Unitary.mem_iff.mp hU).1, one_mul,
      hρ.trace_eq_one]

/-- A finite convex combination of density operators is a density operator. -/
lemma IsDensity.sum {ι : Type*} {s : Finset ι} {μ : ι → ℝ} {ρ : ι → E →L[ℂ] E}
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hμ1 : ∑ i ∈ s, μ i = 1) (hρ : ∀ i ∈ s, IsDensity (ρ i)) :
    IsDensity (∑ i ∈ s, (μ i : ℂ) • ρ i) where
  isPositive := by
    refine Finset.sum_induction _ (fun A : E →L[ℂ] E => (A : E →ₗ[ℂ] E).IsPositive)
      (fun A B hA hB => by simpa using hA.add hB) (by simp)
      fun i hi => ?_
    simpa using (hρ i hi).isPositive.smul_of_nonneg (by exact_mod_cast hμ i hi : (0 : ℂ) ≤ μ i)
  trace_eq_one := by
    simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul, map_sum,
      map_smul]
    rw [Finset.sum_congr rfl fun i hi => by rw [(hρ i hi).trace_eq_one]]
    simp [← Complex.ofReal_sum, hμ1]

/-- A convex combination `t ρ + (1 - t) σ` of two density operators is a density operator. -/
lemma IsDensity.smul_add_smul {ρ σ : E →L[ℂ] E} (hρ : IsDensity ρ) (hσ : IsDensity σ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : IsDensity ((t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ) := by
  have h := IsDensity.sum (s := Finset.univ) (μ := ![t, 1 - t]) (ρ := ![ρ, σ])
    (by simp [Fin.forall_fin_two, ht0, ht1]) (by simp [Fin.sum_univ_two])
    (by simp [Fin.forall_fin_two, hρ, hσ])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

/-!
## C. Maps that are affine on density operators
-/

/-- A map on operators is affine on density operators if it preserves the convex combinations
`t ρ + (1 - t) σ` of two density operators. -/
def AffineOnDensities (T : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ ρ σ, IsDensity ρ → IsDensity σ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    T ((t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ) = (t : ℂ) • T ρ + ((1 - t : ℝ) : ℂ) • T σ

/-- A map that is affine on density operators preserves their finite convex combinations. -/
theorem AffineOnDensities.map_sum {T : (E →L[ℂ] E) → E →L[ℂ] E} (hT : AffineOnDensities T)
    {ι : Type*} (s : Finset ι) {μ : ι → ℝ} {ρ : ι → E →L[ℂ] E} (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hμ1 : ∑ i ∈ s, μ i = 1) (hρ : ∀ i ∈ s, IsDensity (ρ i)) :
    T (∑ i ∈ s, (μ i : ℂ) • ρ i) = ∑ i ∈ s, (μ i : ℂ) • T (ρ i) := by
  classical
  induction s using Finset.induction_on generalizing μ with
  | empty => simp at hμ1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hμ1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hm0 : 0 ≤ ∑ i ∈ s, μ i := Finset.sum_nonneg fun i hi => hμ i (by simp [hi])
    have hma : μ a = 1 - ∑ i ∈ s, μ i := by linarith
    rcases hm0.eq_or_lt with hm | hm
    · have h0 : ∀ i ∈ s, μ i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i hi => hμ i (by simp [hi])).mp hm.symm
      have hs0 : ∀ τ : ι → E →L[ℂ] E, ∑ i ∈ s, (μ i : ℂ) • τ i = 0 := fun τ =>
        Finset.sum_eq_zero fun i hi => by simp [h0 i hi]
      rw [hs0, hs0, show μ a = 1 by linarith]
      simp
    set m := ∑ i ∈ s, μ i
    have hν1 : ∑ i ∈ s, μ i / m = 1 := by rw [← Finset.sum_div, div_self hm.ne']
    have hν : ∀ i ∈ s, 0 ≤ μ i / m := fun i hi => div_nonneg (hμ i (by simp [hi])) hm0
    have hρs : ∀ i ∈ s, IsDensity (ρ i) := fun i hi => hρ i (by simp [hi])
    have hsplit : ∀ τ : ι → E →L[ℂ] E,
        ∑ i ∈ s, (μ i : ℂ) • τ i = ((1 - μ a : ℝ) : ℂ) • ∑ i ∈ s, ((μ i / m : ℝ) : ℂ) • τ i := by
      intro τ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← Complex.ofReal_mul, hma, sub_sub_cancel, mul_div_cancel₀ _ hm.ne']
    rw [hsplit, hsplit, hT _ _ (hρ a (by simp)) (IsDensity.sum hν hν1 hρs) _
      (hμ a (by simp)) (by linarith), ih hν hν1 hρs]

/-- A map that is affine on density operators preserves their equal mixtures. -/
theorem AffineOnDensities.map_mix {T : (E →L[ℂ] E) → E →L[ℂ] E} (hT : AffineOnDensities T)
    {ρ σ : E →L[ℂ] E} (hρ : IsDensity ρ) (hσ : IsDensity σ) :
    T (mix ρ σ) = mix (T ρ) (T σ) := by
  have h := hT ρ σ hρ hσ 2⁻¹ (by norm_num) (by norm_num)
  norm_num at h
  simpa [mix, one_div] using h

/-!
## D. Conjugation by a unitary or an anti-unitary
-/

variable {σ : ℂ →+* ℂ} [RingHomInvPair σ σ]

/-- Conjugation `ρ ↦ W ρ W⁻¹` by an isometry `W` that is linear or conjugate-linear. In both cases
the result is `ℂ`-linear. -/
def conjOp (W : E ≃ₛₗᵢ[σ] E) (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  (W.toContinuousLinearEquiv : E →SL[σ] E).comp
    (ρ.comp (W.symm.toContinuousLinearEquiv : E →SL[σ] E))

variable (W : E ≃ₛₗᵢ[σ] E)

lemma conjOp_apply (ρ : E →L[ℂ] E) (x : E) : conjOp W ρ x = W (ρ (W.symm x)) := rfl

lemma conjOp_add (ρ τ : E →L[ℂ] E) : conjOp W (ρ + τ) = conjOp W ρ + conjOp W τ := by
  ext x
  simp [conjOp_apply]

lemma conjOp_sum {ι : Type*} (s : Finset ι) (ρ : ι → E →L[ℂ] E) :
    conjOp W (∑ i ∈ s, ρ i) = ∑ i ∈ s, conjOp W (ρ i) := by
  ext x
  simp [conjOp_apply]

lemma conjOp_smul (c : ℂ) (ρ : E →L[ℂ] E) : conjOp W (c • ρ) = σ c • conjOp W ρ := by
  ext x
  exact W.map_smulₛₗ c _

lemma conjOp_symm_conjOp (ρ : E →L[ℂ] E) : conjOp W.symm (conjOp W ρ) = ρ := by
  ext x
  simp [conjOp_apply]

lemma conjOp_conjOp_symm (ρ : E →L[ℂ] E) : conjOp W (conjOp W.symm ρ) = ρ := by
  ext x
  simp [conjOp_apply]

/-- Conjugation by an isometry does not increase the operator norm. -/
lemma norm_conjOp_le (ρ : E →L[ℂ] E) : ‖conjOp W ρ‖ ≤ ‖ρ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => by
    rw [conjOp_apply, LinearIsometryEquiv.norm_map, ← W.symm.norm_map x]
    exact ρ.le_opNorm _

/-- Conjugating twice by `W` is conjugating by `W ∘ W`, which is linear even when `W` is
conjugate-linear. -/
lemma conjOp_trans_self (ρ : E →L[ℂ] E) :
    conjOp (W.trans W : E ≃ₗᵢ[ℂ] E) ρ = conjOp W (conjOp W ρ) := by
  ext x
  simp [conjOp_apply, LinearIsometryEquiv.symm_trans]

omit [RingHomInvPair σ σ] in
lemma conjOp_refl (ρ : E →L[ℂ] E) : conjOp (LinearIsometryEquiv.refl ℂ E) ρ = ρ := rfl

omit [RingHomInvPair σ σ] in
/-- Conjugating by `U` and then by `V` is conjugating by `V ∘ U`. -/
lemma conjOp_trans (U V : E ≃ₗᵢ[ℂ] E) (ρ : E →L[ℂ] E) :
    conjOp (U.trans V) ρ = conjOp V (conjOp U ρ) := by
  ext x
  simp [conjOp_apply, LinearIsometryEquiv.symm_trans]

variable [RingHomIsometric σ]

lemma conjOp_ofReal_smul (r : ℝ) (ρ : E →L[ℂ] E) :
    conjOp W ((r : ℂ) • ρ) = (r : ℂ) • conjOp W ρ := by
  rw [conjOp_smul]
  obtain rfl | rfl := Complex.ringHom_eq_id_or_conj_of_isometric σ <;> simp

lemma conjOp_proj (ψ : E) : conjOp W (proj ψ) = proj (W ψ) := by
  ext x
  have h := W.toLinearIsometry.inner_map_map_semilinear ψ (W.symm x)
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, W.apply_symm_apply] at h
  rw [conjOp_apply, proj_apply, proj_apply, W.map_smulₛₗ, ← h]

/-!
## E. Finite dimension
-/

variable [FiniteDimensional ℂ E]

/-- A pure state is a density operator. -/
lemma isDensity_proj {ψ : E} (hψ : ‖ψ‖ = 1) : IsDensity (proj ψ) where
  isPositive := (isPositive_rankOne_self ψ).toLinearMap
  trace_eq_one := by
    rw [trace_rankOne, inner_self_eq_norm_sq_to_K, hψ]
    simp

/-- The eigenvalues of a density operator sum to one. -/
lemma IsDensity.sum_eigenvalues {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    ∑ i, hρ.isPositive.isSymmetric.eigenvalues rfl i = 1 := by
  rw [← hρ.isPositive.isSymmetric.re_trace_eq_sum_eigenvalues, hρ.trace_eq_one]
  simp

/-- The spectral decomposition of a density operator: `ρ = ∑ᵢ μᵢ |eᵢ⟩⟨eᵢ|` over an orthonormal
eigenbasis, with eigenvalues `μᵢ ≥ 0` that sum to one (`IsDensity.sum_eigenvalues`). -/
lemma IsDensity.eq_sum_proj {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    ρ = ∑ i, (hρ.isPositive.isSymmetric.eigenvalues rfl i : ℂ) •
      proj (hρ.isPositive.isSymmetric.eigenvectorBasis rfl i) := by
  set b := hρ.isPositive.isSymmetric.eigenvectorBasis rfl
  refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun j => ?_)
  have h := hρ.isPositive.isSymmetric.apply_eigenvectorBasis rfl j
  simp only [ContinuousLinearMap.coe_coe] at h
  simpa [b.inner_eq_ite, Complex.coe_smul] using h

/-- Conjugation by a unitary or an anti-unitary preserves density operators. -/
lemma IsDensity.conjOp {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) : IsDensity (conjOp W ρ) := by
  have hb := (hρ.isPositive.isSymmetric.eigenvectorBasis rfl).orthonormal.1
  rw [hρ.eq_sum_proj, conjOp_sum]
  simp_rw [conjOp_ofReal_smul, conjOp_proj]
  exact IsDensity.sum (fun i _ => hρ.isPositive.nonneg_eigenvalues rfl i) hρ.sum_eigenvalues
    fun i _ => isDensity_proj (by rw [W.norm_map, hb i])

/-- A density operator that kills the orthogonal complement of a unit vector `ψ` is `|ψ⟩⟨ψ|`. -/
lemma IsDensity.eq_proj_of_apply_eq_zero {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) {ψ : E}
    (hψ : ‖ψ‖ = 1) (h : ∀ x, ⟪ψ, x⟫_ℂ = 0 → ρ x = 0) : ρ = proj ψ := by
  have hperp : ∀ x, ⟪ψ, x - ⟪ψ, x⟫_ℂ • ψ⟫_ℂ = 0 := fun x => by
    simp [inner_sub_right, inner_smul_right, hψ]
  have hsymm : ∀ x y, ⟪ρ x, y⟫_ℂ = ⟪x, ρ y⟫_ℂ := hρ.isPositive.isSymmetric
  -- `ρ ψ` is a multiple of `ψ`: its component `r` orthogonal to `ψ` is orthogonal to itself.
  set c := ⟪ψ, ρ ψ⟫_ℂ
  have hc : ρ ψ = c • ψ := by
    set r := ρ ψ - c • ψ
    have hr : ⟪r, r⟫_ℂ = 0 := by
      calc ⟪r, r⟫_ℂ = ⟪r, ρ ψ⟫_ℂ - c * ⟪r, ψ⟫_ℂ := by
            rw [← inner_smul_right, ← inner_sub_right]
        _ = 0 := by
          rw [← hsymm, h r (hperp _), inner_zero_left, ← inner_conj_symm, hperp, map_zero,
            mul_zero, sub_zero]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hr)
  have hρc : ρ = c • proj ψ := by
    ext x
    have hx := h _ (hperp x)
    rw [map_sub, map_smul, hc, sub_eq_zero] at hx
    rw [hx, smul_apply, proj_apply, smul_smul, smul_smul, mul_comm]
  have h1 := hρ.trace_eq_one
  rw [hρc, ContinuousLinearMap.toLinearMap_smul, map_smul, (isDensity_proj hψ).trace_eq_one,
    smul_eq_mul, mul_one] at h1
  rw [hρc, h1, one_smul]

end QuantumMechanics.Wigner
