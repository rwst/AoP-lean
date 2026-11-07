/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.VonNeumannEntropy
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Unitarily equivalent quantum models

## i. Overview

A unitary `e : E ≃ₗᵢ[ℂ] F` between complex Hilbert spaces carries the quantum model built on `E`
onto the one built on `F`. It maps rays to rays, density operators to density operators by
`ρ ↦ e ρ e⁻¹`, and self-adjoint operators, bounded or not, to self-adjoint operators by
`T ↦ e T e⁻¹`; each of these maps is a bijection, with inverse induced by `e⁻¹`. The trace of
positive operators and the von Neumann entropy are preserved. Conjugation of bounded operators is
Mathlib's `LinearIsometryEquiv.conjStarAlgEquiv`; for partially defined operators it is
`QuantumMechanics.conjLinearPMap`, and it commutes with taking adjoints.

## ii. Key results

- `QuantumMechanics.mapRays`: the bijection `ℙ(E) ≃ ℙ(F)`.
- `QuantumMechanics.posTrace_conjStarAlgEquiv`: `tr (e T e⁻¹) = tr T` for `T ≥ 0`.
- `QuantumMechanics.isDensityOperator_conjStarAlgEquiv_iff`: density operators correspond.
- `QuantumMechanics.IsDensityOperator.vonNeumannEntropy_conjStarAlgEquiv`: the entropy is
  preserved.
- `QuantumMechanics.isSelfAdjoint_conjStarAlgEquiv_iff`: bounded self-adjoint operators
  correspond.
- `QuantumMechanics.bijective_conjLinearPMap`: `T ↦ e T e⁻¹` is a bijection.
- `QuantumMechanics.adjoint_conjLinearPMap`: `(e T e⁻¹)† = e T† e⁻¹` for densely defined `T`.
- `QuantumMechanics.isSelfAdjoint_conjLinearPMap_iff`: self-adjoint operators correspond.

## iii. Table of contents

- A. Rays
- B. Density operators and entropy
- C. Bounded self-adjoint operators
- D. Partially defined operators

## iv. References

- M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press (1980), §VIII.1.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder LinearPMap LinearAlgebra.Projectivization
open ContinuousLinearMap (posTrace posTraceBasis posTrace_eq_tsum)

namespace QuantumMechanics

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (e : E ≃ₗᵢ[ℂ] F)

/-! ## A. Rays -/

/-- A unitary induces a bijection between the rays. -/
def mapRays : ℙ ℂ E ≃ ℙ ℂ F where
  toFun := Projectivization.map (e.toLinearEquiv : E →ₗ[ℂ] F) e.injective
  invFun := Projectivization.map (e.symm.toLinearEquiv : F →ₗ[ℂ] E) e.symm.injective
  left_inv p := by
    induction p using Projectivization.ind
    simp [Projectivization.map_mk]
  right_inv p := by
    induction p using Projectivization.ind
    simp [Projectivization.map_mk]

omit [CompleteSpace E] [CompleteSpace F] in
lemma mapRays_mk (v : E) (hv : v ≠ 0) :
    mapRays e (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (e v) (e.map_ne_zero_iff.mpr hv) :=
  Projectivization.map_mk _ e.injective v hv

/-! ## B. Density operators and entropy -/

variable {e}

lemma conjStarAlgEquiv_nonneg {T : E →L[ℂ] E} (hT : 0 ≤ T) : 0 ≤ e.conjStarAlgEquiv T := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive] at hT ⊢
  refine ⟨?_, fun y => ?_⟩
  · simpa using (hT.isSelfAdjoint.map e.conjStarAlgEquiv).isSymmetric
  · have := hT.re_inner_nonneg_right (e.symm y)
    rw [← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply] at this
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, ← inner_conj_symm, RCLike.conj_re]
    exact this

/-- The Hilbert basis `e ∘ b` of `F`. -/
def mapHilbertBasis {ι : Type*} (b : HilbertBasis ι ℂ E) : HilbertBasis ι ℂ F :=
  ⟨e.symm.trans b.repr⟩

omit [CompleteSpace E] [CompleteSpace F] in
lemma mapHilbertBasis_apply {ι : Type*} (b : HilbertBasis ι ℂ E) (i : ι) :
    mapHilbertBasis (e := e) b i = e (b i) := by
  classical
  rw [← HilbertBasis.repr_symm_single, ← HilbertBasis.repr_symm_single b]
  rfl

/-- Conjugation by a unitary preserves the trace of a positive operator. -/
theorem posTrace_conjStarAlgEquiv {T : E →L[ℂ] E} (hT : 0 ≤ T) :
    posTrace (e.conjStarAlgEquiv T) = posTrace T := by
  rw [posTrace_eq_tsum (conjStarAlgEquiv_nonneg hT) (mapHilbertBasis (e := e) (posTraceBasis E)),
    posTrace_eq_tsum hT (posTraceBasis E)]
  simp [mapHilbertBasis_apply]

theorem IsDensityOperator.conjStarAlgEquiv {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (e.conjStarAlgEquiv ρ) :=
  isDensityOperator_iff.mpr ⟨conjStarAlgEquiv_nonneg hρ.nonneg, by
    rw [posTrace_conjStarAlgEquiv hρ.nonneg, hρ.posTrace_eq_one]⟩

/-- Density operators on `E` and on `F` correspond under `ρ ↦ e ρ e⁻¹`. -/
theorem isDensityOperator_conjStarAlgEquiv_iff {ρ : E →L[ℂ] E} :
    IsDensityOperator (e.conjStarAlgEquiv ρ) ↔ IsDensityOperator ρ := by
  refine ⟨fun h => ?_, IsDensityOperator.conjStarAlgEquiv⟩
  have := h.conjStarAlgEquiv (e := e.symm)
  rwa [← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply] at this

lemma continuous_conjStarAlgEquiv : Continuous (e.conjStarAlgEquiv) :=
  e.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous

/-- The von Neumann entropy is preserved under `ρ ↦ e ρ e⁻¹`. -/
theorem IsDensityOperator.vonNeumannEntropy_conjStarAlgEquiv {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    vonNeumannEntropy (e.conjStarAlgEquiv ρ) = vonNeumannEntropy ρ := by
  have hρ' := hρ.conjStarAlgEquiv (e := e)
  rw [vonNeumannEntropy, ← StarAlgHomClass.map_cfc e.conjStarAlgEquiv Real.negMulLog ρ
    (hφ := continuous_conjStarAlgEquiv) (ha := hρ.isSelfAdjoint) (hφa := hρ'.isSelfAdjoint),
    posTrace_conjStarAlgEquiv hρ.cfc_negMulLog_nonneg, vonNeumannEntropy]

/-! ## C. Bounded self-adjoint operators -/

/-- Bounded self-adjoint operators on `E` and on `F` correspond under `T ↦ e T e⁻¹`. -/
theorem isSelfAdjoint_conjStarAlgEquiv_iff {T : E →L[ℂ] E} :
    IsSelfAdjoint (e.conjStarAlgEquiv T) ↔ IsSelfAdjoint T :=
  ⟨fun h => by simpa only [StarAlgEquiv.symm_apply_apply] using h.map e.conjStarAlgEquiv.symm,
    fun h => h.map _⟩

/-! ## D. Partially defined operators -/

variable (e) in
/-- Conjugation `T ↦ e T e⁻¹` of a partially defined operator, with domain `e (D(T))`. -/
def conjLinearPMap (T : E →ₗ.[ℂ] E) : F →ₗ.[ℂ] F where
  domain := T.domain.map (e.toLinearEquiv : E →ₗ[ℂ] F)
  toFun := (e.toLinearEquiv : E →ₗ[ℂ] F) ∘ₗ T.toFun ∘ₗ
    (T.domain.equivMapOfInjective _ e.injective).symm.toLinearMap

omit [CompleteSpace E] [CompleteSpace F] in
lemma mem_domain_conjLinearPMap {T : E →ₗ.[ℂ] E} {y : F} :
    y ∈ (conjLinearPMap e T).domain ↔ e.symm y ∈ T.domain := by
  simp only [conjLinearPMap, Submodule.mem_map]
  exact ⟨fun ⟨x, hx, h⟩ => by simpa [← h] using hx,
    fun h => ⟨_, h, by simp⟩⟩

omit [CompleteSpace E] [CompleteSpace F] in
lemma conjLinearPMap_apply {T : E →ₗ.[ℂ] E} (y : (conjLinearPMap e T).domain) :
    conjLinearPMap e T y =
      e (T ⟨e.symm y, mem_domain_conjLinearPMap.mp y.2⟩) := by
  obtain ⟨y, hy⟩ := y
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  show e (T ((T.domain.equivMapOfInjective _ e.injective).symm ⟨e x, hy⟩)) = _
  congr 2
  rw [LinearEquiv.symm_apply_eq]
  ext
  simp

omit [CompleteSpace E] [CompleteSpace F] in
lemma dense_domain_conjLinearPMap {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E)) :
    Dense ((conjLinearPMap e T).domain : Set F) := by
  have : ((conjLinearPMap e T).domain : Set F) = e '' T.domain := by
    ext y
    simp [conjLinearPMap]
  rw [this]
  exact e.toHomeomorph.surjective.denseRange.dense_image e.continuous hT

/-- Conjugation by a unitary commutes with taking adjoints. -/
theorem adjoint_conjLinearPMap {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E)) :
    (conjLinearPMap e T)† = conjLinearPMap e T† := by
  have hS := dense_domain_conjLinearPMap (e := e) hT
  have key : ∀ a b, ⟪a, e b⟫_ℂ = ⟪e.symm a, b⟫_ℂ := fun a b => by
    rw [← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have key' : ∀ a b, ⟪e a, b⟫_ℂ = ⟪a, e.symm b⟫_ℂ := fun a b => by
    rw [← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
  have hdom : ∀ y : F, y ∈ (conjLinearPMap e T)†.domain ↔ y ∈ (conjLinearPMap e T†).domain := by
    intro y
    rw [mem_domain_conjLinearPMap]
    constructor
    · intro hy
      refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨e.symm ((conjLinearPMap e T)† ⟨y, hy⟩),
        fun x => ?_⟩
      have hx : e x ∈ (conjLinearPMap e T).domain := by
        rw [mem_domain_conjLinearPMap]
        simp
      have h := LinearPMap.adjoint_isFormalAdjoint hS ⟨y, hy⟩ ⟨e x, hx⟩
      rw [← e.inner_map_map, LinearIsometryEquiv.apply_symm_apply]
      simp only at h
      rw [h, conjLinearPMap_apply, ← e.symm.inner_map_map]
      simp
    · intro hy
      refine LinearPMap.mem_adjoint_domain_of_exists _
        ⟨e (T† ⟨e.symm y, hy⟩), fun x => ?_⟩
      have h := LinearPMap.adjoint_isFormalAdjoint hT ⟨e.symm y, hy⟩
        ⟨e.symm x, mem_domain_conjLinearPMap.mp x.2⟩
      rw [conjLinearPMap_apply, key, key']
      exact h
  refine LinearPMap.ext (Submodule.ext hdom) fun y hy hy' => ?_
  refine LinearPMap.adjoint_apply_eq hS _ fun x => ?_
  rw [conjLinearPMap_apply, conjLinearPMap_apply, key, key']
  have h := LinearPMap.adjoint_isFormalAdjoint hT ⟨e.symm y, (mem_domain_conjLinearPMap.mp hy')⟩
    ⟨e.symm x, mem_domain_conjLinearPMap.mp x.2⟩
  simpa using h

omit [CompleteSpace E] [CompleteSpace F] in
lemma conjLinearPMap_symm_conjLinearPMap (T : E →ₗ.[ℂ] E) :
    conjLinearPMap e.symm (conjLinearPMap e T) = T := by
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => ?_
  · simp [mem_domain_conjLinearPMap]
  · rw [conjLinearPMap_apply, conjLinearPMap_apply]
    simp

omit [CompleteSpace E] [CompleteSpace F] in
/-- `T ↦ e T e⁻¹` is a bijection between the partially defined operators on `E` and on `F`. -/
theorem bijective_conjLinearPMap : Function.Bijective (conjLinearPMap (E := E) e) :=
  Function.bijective_iff_has_inverse.mpr ⟨conjLinearPMap e.symm,
    conjLinearPMap_symm_conjLinearPMap, conjLinearPMap_symm_conjLinearPMap (e := e.symm)⟩

theorem IsSelfAdjoint.conjLinearPMap {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (conjLinearPMap e T) := by
  rw [LinearPMap.isSelfAdjoint_def, adjoint_conjLinearPMap hT.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp hT]

/-- Self-adjoint operators on `E` and on `F` correspond under `T ↦ e T e⁻¹`. -/
theorem isSelfAdjoint_conjLinearPMap_iff {T : E →ₗ.[ℂ] E} :
    IsSelfAdjoint (conjLinearPMap e T) ↔ IsSelfAdjoint T := by
  refine ⟨fun h => ?_, IsSelfAdjoint.conjLinearPMap⟩
  simpa [conjLinearPMap_symm_conjLinearPMap] using IsSelfAdjoint.conjLinearPMap (e := e.symm) h

end QuantumMechanics
