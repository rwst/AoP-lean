/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.HilbertBasisMaps
public import ForMathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Wigner maps

## i. Overview

A unit vector of a complex inner product space `E` represents a pure state, and two unit vectors
represent the same state when they differ by a phase. The transition probability between the
states of unit vectors `v` and `w` is `‖⟪v, w⟫‖ ^ 2`. A *Wigner map* is a function `f : E → E` that
preserves `‖⟪v, w⟫‖` for all unit vectors `v`, `w`. Wigner's theorem says that such an `f` agrees up
to a phase on every unit vector with a linear or a conjugate-linear isometry, which is unitary or
anti-unitary in finite dimension.

This file sets up the vocabulary for the proof: equality up to phase, Wigner maps and their closure
under composition, and the way a fixed ray turns into a test vector. Unitaries and anti-unitaries
are Wigner maps, in particular coordinatewise conjugation in a Hilbert basis.

## ii. Key results

- `QuantumMechanics.Wigner.PhaseEq`: `x = c • y` for some `c` of norm one.
- `QuantumMechanics.Wigner.IsWignerMap`: preservation of `‖⟪v, w⟫‖` on unit vectors.
- `QuantumMechanics.Wigner.IsWignerMap.norm_inner_of_phaseEq`: if `f u` equals `u'` up to phase,
  then `‖⟪u', f v⟫‖ = ‖⟪u, v⟫‖` for every unit vector `v`.
- `QuantumMechanics.Wigner.IsWignerMap.norm_inner_basis_apply`: if `f` fixes the rays of a
  Hilbert basis, it preserves the moduli of all coordinates in that basis.
- `QuantumMechanics.Wigner.isWignerMap_conjLinearIsometryEquiv`: anti-unitaries are Wigner maps.

## iii. Table of contents

- A. Equality up to phase
- B. Wigner maps
- C. Anti-unitaries

## iv. References

- Gy. P. Gehér, *An elementary proof for the non-bijective version of Wigner's theorem*,
  Phys. Lett. A 378 (2014), 2054–2057.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. Equality up to phase
-/

/-- `x` equals `y` up to a phase: `x = c • y` for a complex number `c` of norm one. On unit
vectors this says that `x` and `y` represent the same pure state. -/
def PhaseEq (x y : E) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ x = c • y

namespace PhaseEq

variable {x y z : E}

@[refl]
lemma refl (x : E) : PhaseEq x x :=
  ⟨1, norm_one, (one_smul ℂ x).symm⟩

lemma rfl : PhaseEq x x :=
  refl x

@[symm]
lemma symm (h : PhaseEq x y) : PhaseEq y x := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc₀ : c ≠ 0 := by rw [← norm_ne_zero_iff, hc]; exact one_ne_zero
  exact ⟨c⁻¹, by rw [norm_inv, hc, inv_one], by rw [smul_smul, inv_mul_cancel₀ hc₀, one_smul]⟩

@[trans]
lemma trans (h₁ : PhaseEq x y) (h₂ : PhaseEq y z) : PhaseEq x z := by
  obtain ⟨c, hc, rfl⟩ := h₁
  obtain ⟨d, hd, rfl⟩ := h₂
  exact ⟨c * d, by rw [norm_mul, hc, hd, one_mul], by rw [smul_smul]⟩

lemma smul_left {c : ℂ} (hc : ‖c‖ = 1) (h : PhaseEq x y) : PhaseEq (c • x) y :=
  trans ⟨c, hc, Eq.refl _⟩ h

lemma of_smul_left {c : ℂ} (hc : ‖c‖ = 1) (h : PhaseEq (c • x) y) : PhaseEq x y :=
  trans (symm ⟨c, hc, Eq.refl _⟩) h

lemma norm_eq (h : PhaseEq x y) : ‖x‖ = ‖y‖ := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [norm_smul, hc, one_mul]

lemma norm_inner_left (h : PhaseEq x y) (z : E) : ‖⟪x, z⟫_ℂ‖ = ‖⟪y, z⟫_ℂ‖ := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [inner_smul_left, norm_mul, Complex.norm_conj, hc, one_mul]

lemma norm_inner_right (h : PhaseEq x y) (z : E) : ‖⟪z, x⟫_ℂ‖ = ‖⟪z, y⟫_ℂ‖ := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [inner_smul_right, norm_mul, hc, one_mul]

/-- A linear map preserves equality up to phase. -/
lemma map_linear (W : E →ₗ[ℂ] E) (h : PhaseEq x y) : PhaseEq (W x) (W y) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, W.map_smul c y⟩

/-- A conjugate-linear map preserves equality up to phase. -/
lemma map_conjLinear (W : E →ₗ⋆[ℂ] E) (h : PhaseEq x y) : PhaseEq (W x) (W y) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨conj c, by rw [Complex.norm_conj, hc], W.map_smulₛₗ c y⟩

end PhaseEq

/-- `f` agrees with `g` up to phase on every unit vector. The phase may depend on the vector. -/
def PhaseEqOnSphere (f g : E → E) : Prop :=
  ∀ v : E, ‖v‖ = 1 → PhaseEq (f v) (g v)

/-- Reduction along a unitary: if `W⁻¹ ∘ f` agrees with `g` up to phase, then `f` agrees with
`W ∘ g`. -/
lemma PhaseEqOnSphere.of_symm_comp_linear {f g : E → E} (W : E ≃ₗᵢ[ℂ] E)
    (h : PhaseEqOnSphere (W.symm ∘ f) g) : PhaseEqOnSphere f (W ∘ g) := fun v hv => by
  simpa using (h v hv).map_linear W.toLinearEquiv.toLinearMap

/-- Reduction along an anti-unitary: if `W⁻¹ ∘ f` agrees with `g` up to phase, then `f` agrees
with `W ∘ g`. -/
lemma PhaseEqOnSphere.of_symm_comp_conjLinear {f g : E → E} (W : E ≃ₗᵢ⋆[ℂ] E)
    (h : PhaseEqOnSphere (W.symm ∘ f) g) : PhaseEqOnSphere f (W ∘ g) := fun v hv => by
  simpa using (h v hv).map_conjLinear W.toLinearEquiv.toLinearMap

/-!
## B. Wigner maps
-/

/-- A *Wigner map* preserves the modulus of the inner product of any two unit vectors, that is,
the transition probabilities between pure states. No linearity, continuity or bijectivity is
assumed. -/
def IsWignerMap (f : E → E) : Prop :=
  ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 → ‖⟪f v, f w⟫_ℂ‖ = ‖⟪v, w⟫_ℂ‖

lemma norm_inner_self_eq_one {v : E} (hv : ‖v‖ = 1) : ‖⟪v, v⟫_ℂ‖ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, hv]
  simp

lemma isWignerMap_id : IsWignerMap (id : E → E) :=
  fun _ _ _ _ => Eq.refl _

/-- A map that preserves the modulus of every inner product is a Wigner map. -/
lemma isWignerMap_of_norm_inner_map {f : E → E} (h : ∀ x y : E, ‖⟪f x, f y⟫_ℂ‖ = ‖⟪x, y⟫_ℂ‖) :
    IsWignerMap f :=
  fun v w _ _ => h v w

lemma isWignerMap_linearIsometryEquiv (W : E ≃ₗᵢ[ℂ] E) : IsWignerMap W :=
  isWignerMap_of_norm_inner_map fun x y => by rw [LinearIsometryEquiv.inner_map_map]

namespace IsWignerMap

variable {f g : E → E}

/-- A Wigner map sends unit vectors to unit vectors. -/
lemma norm_apply (hf : IsWignerMap f) {v : E} (hv : ‖v‖ = 1) : ‖f v‖ = 1 := by
  have h := hf v v hv hv
  rw [norm_inner_self_eq_one hv, inner_self_eq_norm_sq_to_K] at h
  rw [norm_pow, RCLike.norm_ofReal, abs_norm] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h

lemma comp (hf : IsWignerMap f) (hg : IsWignerMap g) : IsWignerMap (f ∘ g) :=
  fun v w hv hw => (hf (g v) (g w) (hg.norm_apply hv) (hg.norm_apply hw)).trans (hg v w hv hw)

/-- A Wigner map sends orthogonal unit vectors to orthogonal unit vectors. -/
lemma inner_eq_zero (hf : IsWignerMap f) {v w : E} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h : ⟪v, w⟫_ℂ = 0) : ⟪f v, f w⟫_ℂ = 0 := by
  rw [← norm_eq_zero, hf v w hv hw, h, norm_zero]

/-- A Wigner map sends an orthonormal family to an orthonormal family. -/
lemma orthonormal_comp (hf : IsWignerMap f) {ι : Type*} {b : ι → E} (hb : Orthonormal ℂ b) :
    Orthonormal ℂ (f ∘ b) :=
  ⟨fun i => hf.norm_apply (hb.1 i), fun _ _ hij => hf.inner_eq_zero (hb.1 _) (hb.1 _) (hb.2 hij)⟩

/-- **A fixed ray is a test vector.** If `f u` equals `u'` up to phase, then pairing with `u'`
after `f` gives the same modulus as pairing with `u` before. -/
lemma norm_inner_of_phaseEq (hf : IsWignerMap f) {u u' v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : PhaseEq (f u) u') : ‖⟪u', f v⟫_ℂ‖ = ‖⟪u, v⟫_ℂ‖ := by
  rw [← h.norm_inner_left, hf u v hu hv]

/-- If `f` fixes the rays of a Hilbert basis, then the coordinates of `f v` and of `v` have the
same moduli. -/
lemma norm_inner_basis_apply (hf : IsWignerMap f) {ι : Type*} (b : HilbertBasis ι ℂ E)
    (hb : ∀ k, PhaseEq (f (b k)) (b k)) {v : E} (hv : ‖v‖ = 1) (k : ι) :
    ‖⟪b k, f v⟫_ℂ‖ = ‖⟪b k, v⟫_ℂ‖ :=
  hf.norm_inner_of_phaseEq (b.orthonormal.1 k) hv (hb k)

end IsWignerMap

/-!
## C. Anti-unitaries
-/

/-- An anti-unitary is a Wigner map. -/
lemma isWignerMap_conjLinearIsometryEquiv (W : E ≃ₗᵢ⋆[ℂ] E) : IsWignerMap W :=
  isWignerMap_of_norm_inner_map fun x y => by
    rw [LinearIsometryEquiv.inner_map_map_conj, Complex.norm_conj]

end QuantumMechanics.Wigner
