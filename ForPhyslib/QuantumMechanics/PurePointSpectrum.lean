/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DiscreteObservable

/-!
# Bounded observables with pure point spectrum

## i. Overview

A bounded operator `X` has *pure point spectrum* when its eigenvectors span a dense subspace
(`HasPurePointSpectrum`). Let `eigenproj X a` be the orthogonal projection onto the eigenspace
`ker(X - a)`, which is `0` unless `a` is an eigenvalue.

For self-adjoint `X` the eigenspaces are pairwise orthogonal. With pure point spectrum they form a
Hilbert sum, so `∑ₐ eigenproj X a = 1` strongly, and `X = ∑ₐ a · eigenproj X a`, indexed by all of
`ℝ`, is an eigendecomposition (`IsSelfAdjoint.isEigenDecomposition_eigenproj`). Conversely, every
eigendecomposition `X = ∑ᵢ xᵢ Pᵢ` has `Pᵢ = eigenproj X xᵢ` and `eigenproj X a = 0` for every `a`
not among the `xᵢ` (`IsEigenDecomposition.eigenproj_eq`, `IsEigenDecomposition.eigenproj_eq_zero`),
and `X` has pure point spectrum. So an observable with pure point spectrum has exactly one
eigendecomposition up to reindexing and zero projections, and the pinching `∑ᵢ Pᵢ ρ Pᵢ` is
determined by `X` alone (`IsEigenDecomposition.pinching_eq_pinching`).

## ii. Key results

- `QuantumMechanics.eigenproj`, `QuantumMechanics.HasPurePointSpectrum`.
- `IsSelfAdjoint.isEigenDecomposition_eigenproj`: existence.
- `QuantumMechanics.IsEigenDecomposition.eigenproj_eq`,
  `QuantumMechanics.IsEigenDecomposition.eigenproj_eq_zero`: uniqueness.
- `QuantumMechanics.IsEigenDecomposition.hasPurePointSpectrum`,
  `QuantumMechanics.hasPurePointSpectrum_iff_isEigenDecomposition`,
  `QuantumMechanics.hasPurePointSpectrum_iff_hasSum_eigenproj`.
- `QuantumMechanics.IsEigenDecomposition.comp_equiv`: reindexing.
- `QuantumMechanics.IsEigenDecomposition.hasSum_pinching_eigenproj`,
  `QuantumMechanics.IsEigenDecomposition.pinching_eq_pinching`: the pinching depends only on `X`.

## iii. Table of contents

- A. Eigenprojections
- B. Existence
- C. Uniqueness
- D. The pinching depends only on the observable
-/

@[expose] public noncomputable section

open scoped InnerProductSpace
open Filter Topology

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. Eigenprojections -/

instance (ρ : E →L[ℂ] E) (a : ℝ) : CompleteSpace (ρ - (a : ℂ) • (1 : E →L[ℂ] E)).ker :=
  (ContinuousLinearMap.isClosed_ker _).completeSpace_coe

/-- The orthogonal projection onto the eigenspace `ker(ρ - a)`. -/
def eigenproj (ρ : E →L[ℂ] E) (a : ℝ) : E →L[ℂ] E :=
  (ρ - (a : ℂ) • (1 : E →L[ℂ] E)).ker.starProjection

omit [CompleteSpace E] in
lemma mem_ker_sub_smul_one {ρ : E →L[ℂ] E} {a : ℝ} {v : E} :
    v ∈ (ρ - (a : ℂ) • (1 : E →L[ℂ] E)).ker ↔ ρ v = (a : ℂ) • v := by
  simp [sub_eq_zero]

lemma isStarProjection_eigenproj (ρ : E →L[ℂ] E) (a : ℝ) : IsStarProjection (eigenproj ρ a) :=
  isStarProjection_starProjection

lemma apply_eigenproj (ρ : E →L[ℂ] E) (a : ℝ) (v : E) :
    ρ (eigenproj ρ a v) = (a : ℂ) • eigenproj ρ a v :=
  mem_ker_sub_smul_one.mp (Submodule.starProjection_apply_mem _ v)

lemma eigenproj_apply_of_apply_eq {ρ : E →L[ℂ] E} {a : ℝ} {v : E} (hv : ρ v = (a : ℂ) • v) :
    eigenproj ρ a v = v :=
  Submodule.starProjection_eq_self_iff.mpr (mem_ker_sub_smul_one.mpr hv)

/-- The `HasPurePointSpectrum` predicate: the eigenvectors span a dense subspace. -/
def HasPurePointSpectrum (X : E →L[ℂ] E) : Prop :=
  ⊤ ≤ (⨆ a : ℝ, (X - (a : ℂ) • (1 : E →L[ℂ] E)).ker).topologicalClosure

/-! ## B. Existence -/

section Existence

variable {X : E →L[ℂ] E}

/-- For self-adjoint `X`, eigenvectors of distinct eigenvalues are orthogonal. -/
lemma _root_.IsSelfAdjoint.inner_eq_zero_of_apply_eq (hX : IsSelfAdjoint X) {a b : ℝ} (hab : a ≠ b)
    {u w : E} (hu : X u = (a : ℂ) • u) (hw : X w = (b : ℂ) • w) : ⟪u, w⟫_ℂ = 0 := by
  have h1 : ⟪X u, w⟫_ℂ = ⟪u, X w⟫_ℂ := hX.isSymmetric u w
  rw [hu, hw, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
  have h2 : ((a : ℂ) - b) * ⟪u, w⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (by exact_mod_cast sub_eq_zero.mp h3) hab
  · exact h3

lemma _root_.IsSelfAdjoint.orthogonalFamily_ker (hX : IsSelfAdjoint X) :
    OrthogonalFamily ℂ (fun a : ℝ => (X - (a : ℂ) • (1 : E →L[ℂ] E)).ker)
      fun a => (X - (a : ℂ) • (1 : E →L[ℂ] E)).ker.subtypeₗᵢ := by
  intro a b hab u w
  exact hX.inner_eq_zero_of_apply_eq hab (mem_ker_sub_smul_one.mp u.2)
    (mem_ker_sub_smul_one.mp w.2)

lemma _root_.IsSelfAdjoint.eigenproj_apply_eigenproj (hX : IsSelfAdjoint X) {a b : ℝ} (hab : a ≠ b)
    (v : E) : eigenproj X a (eigenproj X b v) = 0 :=
  (Submodule.starProjection_apply_eq_zero_iff _).mpr fun _ hu =>
    hX.inner_eq_zero_of_apply_eq hab (mem_ker_sub_smul_one.mp hu) (apply_eigenproj X b v)

/-- With pure point spectrum, `∑ₐ eigenproj X a v = v`. -/
lemma _root_.IsSelfAdjoint.hasSum_eigenproj (hX : IsSelfAdjoint X) (hpp : HasPurePointSpectrum X)
    (v : E) : HasSum (fun a : ℝ => eigenproj X a v) v := by
  set V : ℝ → Submodule ℂ E := fun a => (X - (a : ℂ) • (1 : E →L[ℂ] E)).ker
  have hV := IsHilbertSum.mkInternal V hX.orthogonalFamily_ker hpp
  set w := hV.linearIsometryEquiv v
  have hsum : HasSum (fun a => ((w a : V a) : E)) v := by
    simpa [w] using hV.hasSum_linearIsometryEquiv_symm w
  have hw : ∀ a, ((w a : V a) : E) = eigenproj X a v := fun a => by
    refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (w a).2 fun u hu => ?_).symm
    have h1 : HasSum (fun b => ⟪((w b : V b) : E), u⟫_ℂ) ⟪v, u⟫_ℂ :=
      hsum.mapL (innerSLFlip ℂ u)
    have h2 : (fun b => ⟪((w b : V b) : E), u⟫_ℂ) = fun b => if b = a then ⟪((w a : V a) : E), u⟫_ℂ
        else 0 := funext fun b => by
      split_ifs with h
      · subst h; rfl
      · exact hX.inner_eq_zero_of_apply_eq h (mem_ker_sub_smul_one.mp (w b).2)
          (mem_ker_sub_smul_one.mp hu)
    rw [h2] at h1
    rw [inner_sub_left, ← (hasSum_ite_eq a _).unique h1, sub_self]
  simpa only [hw] using hsum

/-- **Existence**: a self-adjoint `X` with pure point spectrum is `∑ₐ a · eigenproj X a`. -/
theorem _root_.IsSelfAdjoint.isEigenDecomposition_eigenproj (hX : IsSelfAdjoint X)
    (hpp : HasPurePointSpectrum X) : IsEigenDecomposition X (eigenproj X) id where
  isResolutionOfIdentity :=
    { isStarProjection := isStarProjection_eigenproj X
      mul_eq_zero := fun a b hab => by
        ext v
        exact hX.eigenproj_apply_eigenproj hab v
      hasSum := hX.hasSum_eigenproj hpp }
  injective := Function.injective_id
  mul_eq := fun a => by
    ext v
    exact apply_eigenproj X a v

/-- Pure point spectrum when the eigenprojections sum to the identity strongly. -/
theorem hasPurePointSpectrum_of_hasSum_eigenproj
    (h : ∀ v, HasSum (fun a : ℝ => eigenproj X a v) v) : HasPurePointSpectrum X := by
  set V := ⨆ a : ℝ, (X - (a : ℂ) • (1 : E →L[ℂ] E)).ker
  intro v _
  have hmem : ∀ a, eigenproj X a v ∈ V := fun a =>
    Submodule.mem_iSup_of_mem a (Submodule.starProjection_apply_mem _ v)
  exact V.isClosed_topologicalClosure.mem_of_tendsto (h v)
    (Eventually.of_forall fun _ => V.le_topologicalClosure (V.sum_mem fun a _ => hmem a))

/-- For self-adjoint `X`, pure point spectrum means `∑ₐ eigenproj X a = 1` strongly. -/
theorem hasPurePointSpectrum_iff_hasSum_eigenproj (hX : IsSelfAdjoint X) :
    HasPurePointSpectrum X ↔ ∀ v, HasSum (fun a : ℝ => eigenproj X a v) v :=
  ⟨hX.hasSum_eigenproj, hasPurePointSpectrum_of_hasSum_eigenproj⟩

end Existence

/-! ## C. Uniqueness -/

namespace IsEigenDecomposition

variable {ι : Type*} {X : E →L[ℂ] E} {P : ι → E →L[ℂ] E} {x : ι → ℝ}
  (hX : IsEigenDecomposition X P x)
include hX

/-- Reindexing an eigendecomposition along an equivalence. -/
theorem comp_equiv {κ : Type*} (e : κ ≃ ι) : IsEigenDecomposition X (P ∘ e) (x ∘ e) where
  isResolutionOfIdentity :=
    { isStarProjection := fun k => hX.isResolutionOfIdentity.isStarProjection (e k)
      mul_eq_zero := fun _ _ h => hX.isResolutionOfIdentity.mul_eq_zero _ _ (e.injective.ne h)
      hasSum := fun v => e.hasSum_iff.mpr (hX.isResolutionOfIdentity.hasSum v) }
  injective := hX.injective.comp e.injective
  mul_eq := fun k => hX.mul_eq (e k)

/-- An eigenvector for `a` is killed by every `Pⱼ` with `xⱼ ≠ a`. -/
lemma apply_eq_zero_of_apply_eq {a : ℝ} {u : E} (hu : X u = (a : ℂ) • u) {j : ι} (hj : x j ≠ a) :
    P j u = 0 := by
  have h1 : P j (X u) = (x j : ℂ) • P j u := by
    rw [← mul_apply_eq_comp, hX.mul_eq', smul_apply]
  rw [hu, map_smul] at h1
  have h2 : ((a : ℂ) - x j) • P j u = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact absurd (by exact_mod_cast (sub_eq_zero.mp h3).symm) hj
  · exact h3

/-- **Uniqueness**: `Pᵢ` is the eigenprojection of `X` for `xᵢ`. -/
theorem eigenproj_eq (i : ι) : eigenproj X (x i) = P i := by
  have hP := hX.isResolutionOfIdentity
  ext v
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun u hu => ?_
  · rw [mem_ker_sub_smul_one, ← mul_apply_eq_comp, hX.mul_eq i,
      smul_apply]
  · have hu' := mem_ker_sub_smul_one.mp hu
    have hPu : P i u = u := by
      have h := hP.hasSum u
      have h0 : ∀ j, j ≠ i → P j u = 0 := fun j hj =>
        hX.apply_eq_zero_of_apply_eq hu' fun h' => hj (hX.injective h')
      exact (hasSum_single i h0).unique h
    rw [← hPu, ← hP.inner_apply_left, map_sub, hP.apply_apply, sub_self, inner_zero_left]

/-- **Uniqueness**: `X` has no eigenvalue outside the `xᵢ`. -/
theorem eigenproj_eq_zero {a : ℝ} (ha : a ∉ Set.range x) : eigenproj X a = 0 := by
  have hP := hX.isResolutionOfIdentity
  ext v
  have hu := apply_eigenproj X a v
  have h0 : ∀ j, P j (eigenproj X a v) = 0 := fun j =>
    hX.apply_eq_zero_of_apply_eq hu fun h => ha ⟨j, h⟩
  have h := hP.hasSum (eigenproj X a v)
  simp only [h0] at h
  exact h.unique hasSum_zero

/-- An observable with an eigendecomposition has pure point spectrum. -/
theorem hasPurePointSpectrum : HasPurePointSpectrum X := by
  have hP := hX.isResolutionOfIdentity
  set V := ⨆ a : ℝ, (X - (a : ℂ) • (1 : E →L[ℂ] E)).ker
  intro v _
  have hmem : ∀ i, P i v ∈ V := fun i =>
    Submodule.mem_iSup_of_mem (x i) (by
      rw [mem_ker_sub_smul_one, ← mul_apply_eq_comp, hX.mul_eq i,
        smul_apply])
  exact V.isClosed_topologicalClosure.mem_of_tendsto (hP.hasSum v)
    (Eventually.of_forall fun _ => V.le_topologicalClosure (V.sum_mem fun i _ => hmem i))

/-! ## D. The pinching depends only on the observable -/

/-- The pinching in terms of the eigenprojections of `X`: `P(ρ) v = ∑ₐ Pₐ ρ Pₐ v`, `a ∈ ℝ`. -/
theorem hasSum_pinching_eigenproj (ρ : E →L[ℂ] E) (v : E) :
    HasSum (fun a : ℝ => eigenproj X a (ρ (eigenproj X a v)))
      (hX.isResolutionOfIdentity.pinching ρ v) := by
  have h := hX.isResolutionOfIdentity.hasSum_pinching_apply ρ v
  simp only [← hX.eigenproj_eq] at h
  refine (hX.injective.hasSum_iff fun a ha => ?_).mp h
  simp [hX.eigenproj_eq_zero ha]

/-- **The pinching depends only on the observable**: two eigendecompositions of `X` give the same
pinching. -/
theorem pinching_eq_pinching {κ : Type*} {Q : κ → E →L[ℂ] E} {y : κ → ℝ}
    (hY : IsEigenDecomposition X Q y) (ρ : E →L[ℂ] E) :
    hX.isResolutionOfIdentity.pinching ρ = hY.isResolutionOfIdentity.pinching ρ := by
  ext v
  exact (hX.hasSum_pinching_eigenproj ρ v).unique (hY.hasSum_pinching_eigenproj ρ v)

end IsEigenDecomposition

/-- For self-adjoint `X`, pure point spectrum means `X = ∑ₐ a · eigenproj X a`. -/
theorem hasPurePointSpectrum_iff_isEigenDecomposition {X : E →L[ℂ] E} (hX : IsSelfAdjoint X) :
    HasPurePointSpectrum X ↔ IsEigenDecomposition X (eigenproj X) id :=
  ⟨hX.isEigenDecomposition_eigenproj, fun h => h.hasPurePointSpectrum⟩

end QuantumMechanics
