/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Wigner.Rigidity
public import Mathlib.LinearAlgebra.Center

/-!
# Wigner's theorem

## i. Overview

Let `E` be a complex Hilbert space of any dimension and `f : E → E` a map that preserves
`‖⟪v, w⟫‖` for all unit vectors `v`, `w`. Then there is a linear or a conjugate-linear isometry
`U` such that, for every unit vector `v`, `f v = c • U v` for some `c` of norm one. Neither
bijectivity nor continuity of `f` is assumed. If every ray is the image of a ray, `U` is onto, so
it is a unitary or an anti-unitary; in finite dimension this is automatic.

The proof follows Gehér: move `f` by the adjoint of an isometry `V` until it fixes the rays of a
Hilbert basis, by a diagonal unitary `D` until it also fixes the rays of `(b i₀ - b k) / √2`, and,
if needed, by the coordinatewise conjugation `J` until it fixes the rays of
`(b i₀ + I • b k) / √2`. A map that fixes these rays fixes every ray, so `f` agrees with `V ∘ D`
or `V ∘ D ∘ J`. Two changes from Gehér: the pairs `(i₀, k)` are star-shaped around one index, and
the vectors with vanishing `i₀`-coordinate are handled by Cauchy–Schwarz instead of a density
argument.

## ii. Key results

- `QuantumMechanics.Wigner.IsWignerMap.exists_linearIsometry_or_conjLinearIsometry`: the theorem
  in any dimension, with isometries.
- `QuantumMechanics.Wigner.IsWignerMap.exists_unitary_or_antiunitary_of_surjective`: unitary or
  anti-unitary when every ray is reached.
- `QuantumMechanics.Wigner.IsWignerMap.exists_unitary_or_antiunitary`: unitary or anti-unitary in
  finite dimension.
- `QuantumMechanics.Wigner.wigner_isometry`, `QuantumMechanics.Wigner.wigner`: the same, with the
  definitions unfolded.
- `QuantumMechanics.Wigner.PhaseEqOnSphere.exists_eq_smul_of_unitary` and
  `QuantumMechanics.Wigner.PhaseEqOnSphere.exists_eq_smul_of_antiunitary`: in finite dimension the
  operator is unique up to one phase.

## iii. Table of contents

- A. Wigner's theorem
- B. Unitaries and anti-unitaries
- C. Uniqueness up to phase

## iv. References

- Gy. P. Gehér, *An elementary proof for the non-bijective version of Wigner's theorem*,
  Phys. Lett. A 378 (2014), 2054–2057.
- V. Bargmann, *Note on Wigner's theorem on symmetry operations*, J. Math. Phys. 5 (1964),
  862–868, §6.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. Wigner's theorem
-/

/-- Reduction along an isometry: if `V (W v) = f v` on unit vectors and `W` agrees with `g` up to
phase, then `f` agrees with `V ∘ g`. -/
lemma PhaseEqOnSphere.of_apply_eq {f g W : E → E} (V : E →ₗ[ℂ] E)
    (hV : ∀ v, ‖v‖ = 1 → V (W v) = f v) (h : PhaseEqOnSphere W g) : PhaseEqOnSphere f (V ∘ g) :=
  fun v hv => by simpa [hV v hv] using (h v hv).map_linear V

namespace IsWignerMap

variable {f : E → E}

/-- The anti-unitary branch: if `D⁻¹ ∘ f` sends every `vecAddI b i₀ k` to `vecSubI b i₀ k`, then
`f` agrees with `D ∘ J` up to phase. -/
lemma phaseEqOnSphere_of_flips {ι : Type*} [DecidableEq ι] {b : HilbertBasis ι ℂ E} {i₀ : ι}
    (D : E ≃ₗᵢ[ℂ] E) (hf : IsWignerMap (D.symm ∘ f))
    (hb : ∀ k, PhaseEq ((D.symm ∘ f) (b k)) (b k))
    (hsub : ∀ k, k ≠ i₀ → PhaseEq ((D.symm ∘ f) (vecSub b i₀ k)) (vecSub b i₀ k))
    (hflip : ∀ k, k ≠ i₀ → PhaseEq ((D.symm ∘ f) (vecAddI b i₀ k)) (vecSubI b i₀ k)) :
    PhaseEqOnSphere f (b.conjugation.trans D) := by
  set J := b.conjugation
  have hJ : IsWignerMap (J.symm ∘ D.symm ∘ f) :=
    (isWignerMap_conjLinearIsometryEquiv J.symm).comp hf
  have mapJ : ∀ {x y : E}, PhaseEq x y → PhaseEq (J.symm x) (J.symm y) := fun h =>
    h.map_conjLinear J.symm.toLinearEquiv.toLinearMap
  have hR : FixesResolving (J.symm ∘ D.symm ∘ f) b i₀ :=
    { basis := fun k => by
        simpa [J] using mapJ (hb k)
      sub := fun k hk => by
        simpa [J, conjugation_vecSub] using mapJ (hsub k hk)
      addI := fun k hk => by
        simpa [J, conjugation_vecSubI] using mapJ (hflip k hk) }
  have h := ((hJ.phaseEqOnSphere_id hR).of_symm_comp_conjLinear J).of_symm_comp_linear D
  intro v hv
  simpa using h v hv

/-- **Wigner's theorem**, non-bijective, in any dimension: a Wigner map on a Hilbert space agrees
up to phase on unit vectors with a linear or a conjugate-linear isometry. -/
theorem exists_linearIsometry_or_conjLinearIsometry [CompleteSpace E] (hf : IsWignerMap f) :
    (∃ U : E →ₗᵢ[ℂ] E, PhaseEqOnSphere f U) ∨ (∃ U : E →ₗᵢ⋆[ℂ] E, PhaseEqOnSphere f U) := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  rcases isEmpty_or_nonempty w with hw | ⟨⟨i₀⟩⟩
  · refine Or.inl ⟨LinearIsometry.id, fun v hv => absurd hv ?_⟩
    rw [b.ext_inner (x := v) (y := 0) fun i => isEmptyElim i, norm_zero]
    exact zero_ne_one
  obtain ⟨V, hg, hb, hV⟩ := hf.exists_isometry_basis b
  set g := V.toContinuousLinearMap.adjoint ∘ f
  have hb₁ : ∀ k, PhaseEq (g (b k)) (b k) := fun k => by
    rw [show g (b k) = b k from hb k]
  obtain ⟨D, hD₁, hD₂⟩ := hg.exists_phaseEq_vecSub hb₁ i₀
  have hg₂ : IsWignerMap (D.symm ∘ g) := (isWignerMap_linearIsometryEquiv D.symm).comp hg
  have hV' : ∀ v, ‖v‖ = 1 → V.toLinearMap (g v) = f v := hV
  rcases hg₂.fixes_or_flips hD₁ hD₂ with hadd | hflip
  · refine Or.inl ⟨V.comp D.toLinearIsometry, fun v hv => ?_⟩
    have h := ((hg₂.phaseEqOnSphere_id ⟨hD₁, hD₂, hadd⟩).of_symm_comp_linear D).of_apply_eq
      V.toLinearMap hV'
    simpa using h v hv
  · refine Or.inr ⟨V.comp (b.conjugation.trans D).toLinearIsometry, fun v hv => ?_⟩
    have h := (phaseEqOnSphere_of_flips D hg₂ hD₁ hD₂ hflip).of_apply_eq V.toLinearMap hV'
    simpa using h v hv

end IsWignerMap

/-- **Wigner's theorem** in any dimension, with the definitions unfolded: if `f : E → E` preserves
`‖⟪v, w⟫‖` for all unit vectors `v` and `w`, then there is a linear or a conjugate-linear
isometry `U` with `f v = c • U v` for every unit vector `v` and some `c` of norm one depending on
`v`. -/
theorem wigner_isometry [CompleteSpace E] {f : E → E}
    (hf : ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 → ‖⟪f v, f w⟫_ℂ‖ = ‖⟪v, w⟫_ℂ‖) :
    (∃ U : E →ₗᵢ[ℂ] E, ∀ v, ‖v‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ f v = c • U v) ∨
      (∃ U : E →ₗᵢ⋆[ℂ] E, ∀ v, ‖v‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ f v = c • U v) :=
  IsWignerMap.exists_linearIsometry_or_conjLinearIsometry hf

/-!
## B. Unitaries and anti-unitaries
-/

/-- If every ray is the image of a ray, an isometry that agrees with `f` up to phase is onto. -/
lemma PhaseEqOnSphere.surjective {f : E → E} {σ : ℂ →+* ℂ} [RingHomInvPair σ σ]
    {U : E →ₛₗᵢ[σ] E} (h : PhaseEqOnSphere f U)
    (hs : ∀ w : E, ‖w‖ = 1 → ∃ v, ‖v‖ = 1 ∧ PhaseEq (f v) w) : Function.Surjective U := by
  intro y
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨0, map_zero U⟩
  obtain ⟨v, hv, hfv⟩ := hs _ (norm_smul_inv_norm (𝕜 := ℂ) hy)
  obtain ⟨c, -, hc⟩ := hfv.symm.trans (h v hv)
  have hy₀ : (‖y‖ : ℂ) ≠ 0 := by simpa using hy
  refine ⟨σ ((‖y‖ : ℂ) * c) • v, ?_⟩
  rw [U.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂, mul_smul, ← hc]
  exact smul_inv_smul₀ hy₀ y

/-- In finite dimension every linear or conjugate-linear isometry of `E` is onto. -/
lemma surjective_of_finiteDimensional [FiniteDimensional ℂ E] {σ : ℂ →+* ℂ} [RingHomIsometric σ]
    (U : E →ₛₗᵢ[σ] E) : Function.Surjective U :=
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  (LinearMap.injective_iff_surjective
    (f := (U.toLinearMap.toAddMonoidHom.toRealLinearMap U.continuous).toLinearMap)).mp U.injective

namespace IsWignerMap

variable {f : E → E}

/-- **Wigner's theorem** for a Wigner map that reaches every ray: it agrees up to phase on unit
vectors with a unitary or an anti-unitary. -/
theorem exists_unitary_or_antiunitary_of_surjective [CompleteSpace E] (hf : IsWignerMap f)
    (hs : ∀ w : E, ‖w‖ = 1 → ∃ v, ‖v‖ = 1 ∧ PhaseEq (f v) w) :
    (∃ U : E ≃ₗᵢ[ℂ] E, PhaseEqOnSphere f U) ∨ (∃ U : E ≃ₗᵢ⋆[ℂ] E, PhaseEqOnSphere f U) := by
  rcases hf.exists_linearIsometry_or_conjLinearIsometry with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨LinearIsometryEquiv.ofSurjective U (hU.surjective hs), hU⟩
  · exact Or.inr ⟨LinearIsometryEquiv.ofSurjective U (hU.surjective hs), hU⟩

/-- **Wigner's theorem**, finite-dimensional and non-bijective: a Wigner map agrees up to phase
on unit vectors with a unitary or an anti-unitary operator. -/
theorem exists_unitary_or_antiunitary [FiniteDimensional ℂ E] (hf : IsWignerMap f) :
    (∃ U : E ≃ₗᵢ[ℂ] E, PhaseEqOnSphere f U) ∨ (∃ U : E ≃ₗᵢ⋆[ℂ] E, PhaseEqOnSphere f U) := by
  have := FiniteDimensional.complete ℂ E
  rcases hf.exists_linearIsometry_or_conjLinearIsometry with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨LinearIsometryEquiv.ofSurjective U (surjective_of_finiteDimensional U), hU⟩
  · exact Or.inr ⟨LinearIsometryEquiv.ofSurjective U (surjective_of_finiteDimensional U), hU⟩

end IsWignerMap

/-- **Wigner's theorem** in finite dimension, with the definitions unfolded: if `f : E → E`
preserves `‖⟪v, w⟫‖` for all unit vectors `v` and `w`, then there is a unitary or an anti-unitary
`U` with `f v = c • U v` for every unit vector `v` and some `c` of norm one depending on `v`. -/
theorem wigner [FiniteDimensional ℂ E] {f : E → E}
    (hf : ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 → ‖⟪f v, f w⟫_ℂ‖ = ‖⟪v, w⟫_ℂ‖) :
    (∃ U : E ≃ₗᵢ[ℂ] E, ∀ v, ‖v‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ f v = c • U v) ∨
      (∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ v, ‖v‖ = 1 → ∃ c : ℂ, ‖c‖ = 1 ∧ f v = c • U v) :=
  IsWignerMap.exists_unitary_or_antiunitary hf

/-!
## C. Uniqueness up to phase
-/

/-- A linear map that fixes every ray is the identity times one phase. -/
lemma PhaseEqOnSphere.exists_eq_smul_of_linear [FiniteDimensional ℂ E] (W : E →ₗ[ℂ] E)
    (hW : PhaseEqOnSphere W id) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, W x = c • x := by
  have h : ∀ v, ∃ c : ℂ, W v = c • v := by
    intro v
    rcases eq_or_ne v 0 with rfl | hv
    · exact ⟨1, by simp⟩
    obtain ⟨c, -, hc⟩ := hW _ (norm_smul_inv_norm (𝕜 := ℂ) hv)
    rw [map_smul, id, smul_comm c] at hc
    exact ⟨c, smul_right_injective E (by simpa using hv) hc⟩
  obtain ⟨a, ha⟩ := W.exists_eq_smul_id_of_forall_notLinearIndependent fun v => by
    obtain ⟨c, hc⟩ := h v
    rw [LinearIndependent.pair_iff, hc]
    push Not
    exact ⟨c, -1, by simp, by norm_num⟩
  have hax : ∀ x, W x = a • x := fun x => by simp [ha]
  by_cases hu : ∃ u : E, ‖u‖ = 1
  · obtain ⟨u, hu⟩ := hu
    refine ⟨a, ?_, hax⟩
    have := (hW u hu).norm_eq
    rwa [hax, norm_smul, id, hu, mul_one] at this
  · push Not at hu
    refine ⟨1, norm_one, fun x => ?_⟩
    obtain rfl : x = 0 := by
      by_contra hx
      exact hu _ (norm_smul_inv_norm (𝕜 := ℂ) hx)
    simp

variable [FiniteDimensional ℂ E] {f : E → E}

/-- **Uniqueness**: two unitaries that agree with `f` up to phase on unit vectors differ by one
phase. -/
theorem PhaseEqOnSphere.exists_eq_smul_of_unitary {U U' : E ≃ₗᵢ[ℂ] E}
    (h : PhaseEqOnSphere f U) (h' : PhaseEqOnSphere f U') :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, U' x = c • U x := by
  obtain ⟨c, hc, hW⟩ := exists_eq_smul_of_linear (U'.trans U.symm).toLinearEquiv.toLinearMap
    fun v hv => by
      simpa using (((h v hv).symm.trans (h' v hv)).map_linear
        U.symm.toLinearEquiv.toLinearMap).symm
  refine ⟨c, hc, fun x => ?_⟩
  simpa using congrArg U (hW x)

/-- **Uniqueness**: two anti-unitaries that agree with `f` up to phase on unit vectors differ by
one phase. -/
theorem PhaseEqOnSphere.exists_eq_smul_of_antiunitary {U U' : E ≃ₗᵢ⋆[ℂ] E}
    (h : PhaseEqOnSphere f U) (h' : PhaseEqOnSphere f U') :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, U' x = c • U x := by
  obtain ⟨c, hc, hW⟩ := exists_eq_smul_of_linear (U'.trans U.symm).toLinearEquiv.toLinearMap
    fun v hv => by
      simpa using (((h v hv).symm.trans (h' v hv)).map_conjLinear
        U.symm.toLinearEquiv.toLinearMap).symm
  refine ⟨conj c, by rw [Complex.norm_conj, hc], fun x => ?_⟩
  simpa [LinearIsometryEquiv.map_smulₛₗ] using congrArg U (hW x)

end QuantumMechanics.Wigner
