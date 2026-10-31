/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Calculus.Deriv.ContinuousLinearMapApply
public import ForPhyslib.QuantumMechanics.Wigner.Kadison
public import Physlib.Mathematics.ForMathlib.OneParameterSubgroups.Unitary

/-!
# One-parameter groups of state automorphisms

## i. Overview

A time evolution `Φ t` of density operators with `Φ (s + t) = Φ s ∘ Φ t` for `s, t ≥ 0`, in which
every `Φ t` is conjugation by a unitary or an anti-unitary (Kadison's theorem), is in fact
conjugation by a unitary for every `t ≥ 0`. If `Φ (t / 2)` is conjugation by `W`, then
`Φ t = Φ (t / 2) ∘ Φ (t / 2)` is conjugation by `W ∘ W`, and `W ∘ W` is linear whether `W` is
linear or conjugate-linear. No case split on the dimension is needed.

The unitaries `U t` are fixed only up to phase, and need not form a group. Their conjugations
`adL (U t) : X ↦ U t X (U t)⁻¹` on all operators do not see the phase: two conjugations that agree
on density operators agree everywhere, because the pure states span all operators. So
`t ↦ adL (U t)` is a semigroup on `t ≥ 0`, which extends to a group `A` on `ℝ`. Continuity of
`t ↦ Φ t ρ` at `0⁺` gives continuity of `t ↦ A t X` at `0⁺` for every `X` by linearity, at `0⁻`
because `‖A h X - X‖ ≤ ‖A (-h) X - X‖`, and everywhere by the group law. In finite dimension this
is norm continuity of `A`.

A norm-continuous group in a Banach algebra is `A t = exp (t L)` with `L = A' 0`. Differentiating
`A t (X Y) = A t X * A t Y` and `A t X⋆ = (A t X)⋆` at `0` shows that `L` is a `⋆`-derivation, and
every derivation of the operators is inner, `L = [K, ·]`. The `⋆`-property makes `K + K⋆` central,
so the skew-adjoint part `K₀ = (K - K⋆) / 2` has the same commutator. Then `V t = exp (t K₀)` is a
norm-continuous unitary group, and `t ↦ V t (·) (V t)⋆` is a continuous group with the same
derivative `L` at `0` as `A`, so the two agree. This removes the phases altogether: `Φ t` is
conjugation by `V t` with `V 0 = 1` and `V (s + t) = V s V t` exactly.

## ii. Key results

- `QuantumMechanics.Wigner.ImplementedByUnitaryOrAntiunitary.exists_unitary_of_eq_comp`: the square
  of a unitary or anti-unitary conjugation is a unitary conjugation.
- `QuantumMechanics.Wigner.exists_unitary_of_map_add`: every `Φ t` with `t ≥ 0` is a unitary
  conjugation.
- `QuantumMechanics.Wigner.exists_map_add_of_nonneg`: a semigroup on `t ≥ 0` extends to `ℝ`.
- `QuantumMechanics.Wigner.span_isPure_eq_top`: the pure states span all operators.
- `QuantumMechanics.Wigner.adL_eq_of_conjOp_eq`: conjugation is determined by its values on
  density operators.
- `QuantumMechanics.Wigner.exists_addChar_adL`: the phase-free continuous one-parameter group.
- `QuantumMechanics.Wigner.deriv_apply_mul_of_eq_adL`,
  `QuantumMechanics.Wigner.deriv_apply_star_of_eq_adL`: its generator is a `⋆`-derivation.
- `QuantumMechanics.Wigner.exists_unitaryOneParameterGroup_of_addChar`: the lift to a unitary
  one-parameter group.
- `QuantumMechanics.Wigner.exists_unitaryOneParameterGroup`: a continuous semigroup of unitary or
  anti-unitary conjugations is conjugation by a norm-continuous unitary one-parameter group.

## iii. Table of contents

- A. Anti-unitaries are excluded by composition
- B. Extending a semigroup from `t ≥ 0` to all `t`
- C. Conjugation as an operator on operators
- D. The phase-free group
- E. The generator is a `⋆`-derivation
- F. The unitary lift

## iv. References

- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), 327–349.
-/

@[expose] public noncomputable section

namespace QuantumMechanics.Wigner

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. Anti-unitaries are excluded by composition
-/

section Composition

variable [FiniteDimensional ℂ E]

/-- If `Φ = Ψ ∘ Ψ` on density operators and `Ψ` is conjugation by a unitary or an anti-unitary
`W`, then `Φ` is conjugation by the unitary `W ∘ W`. -/
theorem ImplementedByUnitaryOrAntiunitary.exists_unitary_of_eq_comp
    {Φ Ψ : (E →L[ℂ] E) → E →L[ℂ] E} (hΨ : ImplementedByUnitaryOrAntiunitary Ψ)
    (hcomp : ∀ ρ, IsDensity ρ → Φ ρ = Ψ (Ψ ρ)) :
    ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ρ, IsDensity ρ → Φ ρ = conjOp U ρ := by
  rcases hΨ with ⟨W, hW⟩ | ⟨W, hW⟩ <;>
    exact ⟨W.trans W, fun ρ hρ => by
      rw [hcomp ρ hρ, hW ρ hρ, hW _ (hρ.conjOp W), conjOp_trans_self]⟩

/-- **Each `Φ t` is unitary.** If every `Φ t` with `t ≥ 0` is conjugation by a unitary or an
anti-unitary and `Φ (s + t) = Φ s ∘ Φ t` on density operators, then every `Φ t` with `t ≥ 0` is
conjugation by a unitary, since `Φ t = Φ (t / 2) ∘ Φ (t / 2)`. -/
theorem exists_unitary_of_map_add {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (hΦ : ∀ t ≥ 0, ImplementedByUnitaryOrAntiunitary (Φ t))
    (hadd : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ (s + t) ρ = Φ s (Φ t ρ)) {t : ℝ}
    (ht : 0 ≤ t) : ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ρ, IsDensity ρ → Φ t ρ = conjOp U ρ :=
  (hΦ (t / 2) (by positivity)).exists_unitary_of_eq_comp fun ρ hρ => by
    rw [← hadd _ (by positivity) _ (by positivity) ρ hρ, add_halves]

end Composition

/-!
## B. Extending a semigroup from `t ≥ 0` to all `t`
-/

/-- A family `f t` of group elements with `f 0 = 1` and `f (s + t) = f s * f t` for `s, t ≥ 0`
extends to a homomorphism on all of `ℝ`, by `t ↦ (f (-t))⁻¹` for `t < 0`. The values commute,
since `f s * f t = f (s + t) = f t * f s`. -/
theorem exists_map_add_of_nonneg {G : Type*} [Group G] {f : ℝ → G}
    (hf : ∀ s ≥ 0, ∀ t ≥ 0, f (s + t) = f s * f t) :
    ∃ g : ℝ → G, (∀ s t, g (s + t) = g s * g t) ∧ ∀ t ≥ 0, g t = f t := by
  classical
  have hc : ∀ s ≥ 0, ∀ t ≥ 0, Commute (f s) (f t) := fun s hs t ht => by
    rw [Commute, SemiconjBy, ← hf s hs t ht, ← hf t ht s hs, add_comm]
  have hsub : ∀ a b, 0 ≤ a → a ≤ b → f (b - a) = (f a)⁻¹ * f b := fun a b ha hab => by
    rw [eq_inv_mul_iff_mul_eq, ← hf a ha _ (sub_nonneg.mpr hab), add_sub_cancel]
  refine ⟨fun t => if 0 ≤ t then f t else (f (-t))⁻¹, fun s t => ?_, fun t ht => by simp [ht]⟩
  rcases le_or_gt 0 s with hs | hs <;> rcases le_or_gt 0 t with ht | ht
  · simp only [hs, ht, add_nonneg hs ht, ↓reduceIte]
    exact hf s hs t ht
  · simp only [hs, ht.not_ge, ↓reduceIte]
    split_ifs with hst
    · rw [show s + t = s - -t by ring, hsub (-t) s (by linarith) (by linarith)]
      exact ((hc s hs (-t) (by linarith)).inv_right).eq.symm
    · rw [show -(s + t) = -t - s by ring, hsub s (-t) hs (by linarith), mul_inv_rev, inv_inv]
      exact ((hc s hs (-t) (by linarith)).inv_right).eq.symm
  · simp only [hs.not_ge, ht, ↓reduceIte]
    split_ifs with hst
    · rw [show s + t = t - -s by ring, hsub (-s) t (by linarith) (by linarith)]
    · rw [show -(s + t) = -s - t by ring, hsub t (-s) ht (by linarith), mul_inv_rev, inv_inv]
  · simp only [hs.not_ge, ht.not_ge, (add_neg hs ht).not_ge, ↓reduceIte,
      show -(s + t) = -s + -t by ring,
      hf (-s) (by linarith) (-t) (by linarith), mul_inv_rev]
    exact ((hc (-s) (by linarith) (-t) (by linarith)).inv_inv).eq.symm

/-!
## C. Conjugation as an operator on operators
-/

/-- Conjugation `X ↦ U X U⁻¹` by a unitary `U`, as a continuous linear map on operators. -/
def adL (U : E ≃ₗᵢ[ℂ] E) : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := conjOp U
      map_add' := conjOp_add U
      map_smul' := conjOp_smul U } 1 fun X => by simpa using norm_conjOp_le U X

lemma adL_apply (U : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E) : adL U X = conjOp U X := rfl

lemma adL_trans (U V : E ≃ₗᵢ[ℂ] E) : adL (U.trans V) = adL V * adL U := by
  ext1 X
  exact conjOp_trans U V X

lemma adL_refl : adL (LinearIsometryEquiv.refl ℂ E) = 1 := by
  ext1 X
  exact conjOp_refl X

lemma adL_mul (U : E ≃ₗᵢ[ℂ] E) (X Y : E →L[ℂ] E) : adL U (X * Y) = adL U X * adL U Y := by
  ext x
  simp [adL_apply, conjOp_apply]

/-- `adL U` as a unit, with inverse `adL U⁻¹`. -/
def adUnit (U : E ≃ₗᵢ[ℂ] E) : ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E)ˣ where
  val := adL U
  inv := adL U.symm
  val_inv := by rw [← adL_trans, LinearIsometryEquiv.symm_trans_self, adL_refl]
  inv_val := by rw [← adL_trans, LinearIsometryEquiv.self_trans_symm, adL_refl]

section Span

variable [FiniteDimensional ℂ E]

/-- The pure states span all operators: `|x⟩⟨y|` is a combination of four `|v⟩⟨v|` by
polarization, and every operator is `∑ⱼ |X bⱼ⟩⟨bⱼ|` for an orthonormal basis `b`. -/
lemma span_isPure_eq_top : Submodule.span ℂ {ρ : E →L[ℂ] E | IsPure ρ} = ⊤ := by
  set S := Submodule.span ℂ {ρ : E →L[ℂ] E | IsPure ρ}
  have hproj : ∀ v : E, proj v ∈ S := fun v => by
    rcases eq_or_ne v 0 with rfl | hv
    · simp [proj]
    have hu : ‖(‖v‖ : ℂ)⁻¹ • v‖ = 1 := by simpa using norm_smul_inv_norm (𝕜 := ℂ) hv
    have h : proj v = ((‖v‖ ^ 2 : ℝ) : ℂ) • proj ((‖v‖ : ℂ)⁻¹ • v) := by
      rw [proj_smul, smul_smul, ← Complex.ofReal_mul, norm_inv, Complex.norm_real,
        Real.norm_eq_abs, abs_norm, inv_pow, mul_inv_cancel₀ (by positivity), Complex.ofReal_one,
        one_smul]
    rw [h]
    exact S.smul_mem _ (Submodule.subset_span ⟨_, hu, rfl⟩)
  have hrank : ∀ x y : E, rankOne ℂ x y ∈ S := fun x y => by
    have h : rankOne ℂ x y = (4 : ℂ)⁻¹ • ((4 : ℂ) • rankOne ℂ x y) := by
      rw [smul_smul]
      norm_num
    rw [h, rankOne_polarization]
    exact S.smul_mem _ (S.sub_mem (S.add_mem (S.sub_mem (hproj _) (hproj _))
      (S.smul_mem _ (hproj _))) (S.smul_mem _ (hproj _)))
  refine eq_top_iff.mpr fun X _ => ?_
  let b := stdOrthonormalBasis ℂ E
  have hX : X = ∑ j, rankOne ℂ (X (b j)) (b j) := by
    ext z
    simp only [sum_apply, rankOne_apply, ← map_smul,
      ← map_sum, b.sum_repr']
  rw [hX]
  exact S.sum_mem fun j _ => hrank _ _

/-- Conjugations that agree on density operators agree on all operators, so `adL U` does not
depend on the phase of `U`. -/
lemma adL_eq_of_conjOp_eq {U V : E ≃ₗᵢ[ℂ] E}
    (h : ∀ ρ, IsDensity ρ → conjOp U ρ = conjOp V ρ) : adL U = adL V := by
  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on span_isPure_eq_top ?_)
  rintro _ ⟨ψ, hψ, rfl⟩
  exact h _ (isDensity_proj hψ)

/-!
## D. The phase-free group
-/

open Filter in
/-- **The phase-free group.** Let `Φ` be a family of maps on operators with `Φ 0 = id`,
`Φ (s + t) = Φ s ∘ Φ t` and `t ↦ Φ t ρ` continuous at `0⁺` on density operators, and with every
`Φ t`, `t ≥ 0`, a unitary conjugation. Then there is a norm-continuous one-parameter group
`A : ℝ → End(End(E))` of unitary conjugations `A t = adL U` with `A t ρ = Φ t ρ` for `t ≥ 0` and
density operators `ρ`. The phases of the unitaries never enter: `adL U` determines and is
determined by `Φ t` on density operators. -/
theorem exists_addChar_adL {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (hU : ∀ t ≥ 0, ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ρ, IsDensity ρ → Φ t ρ = conjOp U ρ)
    (h0 : ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ)
    (hadd : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ (s + t) ρ = Φ s (Φ t ρ))
    (hcont : ∀ ρ, IsDensity ρ → ContinuousWithinAt (fun t => Φ t ρ) (Set.Ici 0) 0) :
    ∃ A : AddChar ℝ ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E), Continuous A ∧
      (∀ t, ∃ U : E ≃ₗᵢ[ℂ] E, A t = adL U) ∧ ∀ t ≥ 0, ∀ ρ, IsDensity ρ → A t ρ = Φ t ρ := by
  choose! U hU using hU
  -- the group law on `t ≥ 0`, in the group of units
  have hf : ∀ s ≥ 0, ∀ t ≥ 0, adUnit (U (s + t)) = adUnit (U s) * adUnit (U t) :=
    fun s hs t ht => Units.ext <| by
      change adL _ = adL _ * adL _
      rw [← adL_trans]
      refine adL_eq_of_conjOp_eq fun ρ hρ => ?_
      rw [← hU _ (add_nonneg hs ht) ρ hρ, hadd s hs t ht ρ hρ, hU t ht ρ hρ,
        hU s hs _ (hρ.conjOp _), conjOp_trans]
  obtain ⟨g, hg, hgf⟩ := exists_map_add_of_nonneg (f := fun t => adUnit (U t)) hf
  have hg0 : g 0 = 1 := by
    rw [hgf 0 le_rfl]
    refine Units.ext ((adL_eq_of_conjOp_eq fun ρ hρ => ?_).trans adL_refl)
    rw [← hU 0 le_rfl ρ hρ, h0 ρ hρ, conjOp_refl]
  let A : AddChar ℝ ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) :=
    { toFun := fun t => (g t : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E)
      map_zero_eq_one' := by simp [hg0]
      map_add_eq_mul' := fun s t => by rw [hg s t, Units.val_mul] }
  have hA : ∀ t, A t = (g t : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) := fun _ => rfl
  have hAd : ∀ t, ∃ V : E ≃ₗᵢ[ℂ] E, A t = adL V := fun t => by
    rcases le_or_gt 0 t with ht | ht
    · exact ⟨U t, by rw [hA, hgf t ht]; rfl⟩
    · refine ⟨(U (-t)).symm, ?_⟩
      have h : g t = (g (-t))⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hg, add_neg_cancel, hg0])
      rw [hA, h, hgf (-t) (by linarith)]
      rfl
  have hAΦ : ∀ t ≥ 0, ∀ ρ, IsDensity ρ → A t ρ = Φ t ρ := fun t ht ρ hρ => by
    rw [hA, hgf t ht, hU t ht ρ hρ]
    rfl
  have hA1 : ∀ X, A 0 X = X := fun X => by simp
  -- continuity at `0⁺` on each operator, from the pure states by linearity
  have hR : ∀ X, ContinuousWithinAt (fun h => A h X) (Set.Ici 0) 0 := fun X => by
    have hX : X ∈ Submodule.span ℂ {ρ : E →L[ℂ] E | IsPure ρ} := by
      rw [span_isPure_eq_top]
      trivial
    induction hX using Submodule.span_induction with
    | mem X hX =>
      obtain ⟨ψ, hψ, rfl⟩ := hX
      have hd := isDensity_proj hψ
      refine (hcont _ hd).congr (fun h hh => hAΦ h hh _ hd) ?_
      rw [hA1, h0 _ hd]
    | zero => simpa using continuousWithinAt_const
    | add X Y _ _ hX hY =>
      simp only [map_add]
      exact hX.add hY
    | smul c X _ hX =>
      simp only [map_smul]
      exact hX.const_smul c
  -- `‖A h X - X‖ ≤ ‖A (-h) X - X‖`, since `A h` is a contraction and `A h (A (-h) X) = X`
  have hbound : ∀ h X, ‖A h X - X‖ ≤ ‖A (-h) X - X‖ := fun h X => by
    obtain ⟨V, hV⟩ := hAd h
    have : A h X - X = A h (X - A (-h) X) := by
      rw [map_sub, ← mul_apply_eq_comp, ← AddChar.map_add_eq_mul, add_neg_cancel,
        hA1]
    rw [this, norm_sub_rev, hV, adL_apply]
    exact norm_conjOp_le V _
  have hc0 : ∀ X, ContinuousAt (fun h => A h X) 0 := fun X => by
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, hR X⟩
    have hL : ContinuousWithinAt (fun h => A (-h) X) (Set.Iic 0) 0 :=
      (hR X).comp_of_eq continuous_neg.continuousWithinAt (fun h hh => neg_nonneg.mpr hh) neg_zero
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at hL ⊢
    simp only [neg_zero, hA1] at hL ⊢
    exact squeeze_zero (fun _ => norm_nonneg _) (fun h => hbound h X) hL
  -- continuity everywhere, from `A s = A t * A (s - t)`
  refine ⟨A, continuous_clm_apply.mpr fun X => continuous_iff_continuousAt.mpr fun t => ?_,
    hAd, hAΦ⟩
  have h : ContinuousAt (fun s => A t (A (s - t) X)) t :=
    (A t).continuous.continuousAt.comp
      ((hc0 X).comp_of_eq (continuous_sub_right t).continuousAt (sub_self t))
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show A s X = A t (A (s - t) X)
  rw [← mul_apply_eq_comp, ← AddChar.map_add_eq_mul, add_sub_cancel]

end Span

/-!
## E. The generator is a `⋆`-derivation
-/

/-- A continuous one-parameter group in a Banach algebra has derivative `deriv A 0` at `0`. -/
lemma hasDerivAt_addChar {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (A : AddChar ℝ 𝔸) (hA : Continuous A) : HasDerivAt A (deriv A 0) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (deriv A 0) 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h.congr_of_eventuallyEq
    (.of_forall fun t => OneParameterSubgroup.apply_eq_exp_smul_deriv A hA t)

section Generator

variable [CompleteSpace E]

lemma adL_eq_mul_mul_star (U : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E) :
    adL U X = (U : E →L[ℂ] E) * X * star (U : E →L[ℂ] E) := by
  ext x
  simp [adL_apply, conjOp_apply]

lemma adL_star (U : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E) : adL U (star X) = star (adL U X) := by
  simp only [adL_eq_mul_mul_star, star_mul, star_star, mul_assoc]

variable (A : AddChar ℝ ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E)) (hA : Continuous A)
  (hAd : ∀ t, ∃ U : E ≃ₗᵢ[ℂ] E, A t = adL U)
include hA hAd

/-- The generator of a continuous group of conjugations is a derivation. -/
theorem deriv_apply_mul_of_eq_adL (X Y : E →L[ℂ] E) :
    deriv A 0 (X * Y) = deriv A 0 X * Y + X * deriv A 0 Y := by
  have hd := hasDerivAt_addChar (𝔸 := (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) A hA
  have h := (hd.clm_apply_const X).fun_mul (hd.clm_apply_const Y)
  simp only [AddChar.map_zero_eq_one, one_apply_eq_self] at h
  refine (hd.clm_apply_const (X * Y)).unique (h.congr_of_eventuallyEq (.of_forall fun t => ?_))
  obtain ⟨U, hU⟩ := hAd t
  simp [hU, adL_mul]

/-- The generator of a continuous group of conjugations commutes with the adjoint. -/
theorem deriv_apply_star_of_eq_adL (X : E →L[ℂ] E) :
    deriv A 0 (star X) = star (deriv A 0 X) := by
  have hd := hasDerivAt_addChar (𝔸 := (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) A hA
  refine (hd.clm_apply_const (star X)).unique
    ((hd.clm_apply_const X).star.congr_of_eventuallyEq (.of_forall fun t => ?_))
  obtain ⟨U, hU⟩ := hAd t
  simp [hU, adL_star]

end Generator

/-!
## F. The unitary lift
-/

section Lift

variable [CompleteSpace E]

open Complex in
/-- A continuous group of conjugations `A t = adL (U t)` is conjugation by a norm-continuous
unitary one-parameter group. -/
theorem exists_unitaryOneParameterGroup_of_addChar
    (A : AddChar ℝ ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E)) (hA : Continuous A)
    (hAd : ∀ t, ∃ U : E ≃ₗᵢ[ℂ] E, A t = adL U) :
    ∃ V : UnitaryOneParameterGroup E, ∀ t X, A t X = V t * X * star (V t) := by
  set L := deriv A 0
  obtain ⟨K, hK⟩ := exists_eq_mul_sub_mul_of_map_mul L (deriv_apply_mul_of_eq_adL A hA hAd)
  have hc : ∀ X, (K + star K) * X = X * (K + star K) := fun X => by
    have h := deriv_apply_star_of_eq_adL A hA hAd (star X)
    rw [star_star, hK, hK, star_sub, star_mul, star_mul, star_star,
      sub_eq_sub_iff_add_eq_add] at h
    rw [add_mul, mul_add, h, add_comm]
  set K₀ := (2⁻¹ : ℂ) • (K - star K)
  have hH : IsSelfAdjoint (I • K₀) := by
    simp only [IsSelfAdjoint, star_smul, K₀, star_sub, star_star, conj_I, RCLike.star_def,
      map_inv₀, map_ofNat]
    module
  set V := UnitaryOneParameterGroup.ofSelfAdjoint hH
  have hV0 : V 0 = 1 := AddChar.map_zero_eq_one _
  have hV : HasDerivAt V K₀ 0 := by
    have h := V.hasDerivAt 0
    rwa [UnitaryOneParameterGroup.generator_ofSelfAdjoint, hV0, one_mul, smul_smul, I_mul_I,
      neg_one_smul, neg_neg] at h
  have hVs : HasDerivAt (fun s => star (V s)) (-K₀) 0 := by
    have h := V.hasDerivAt_star 0
    rwa [UnitaryOneParameterGroup.generator_ofSelfAdjoint, hV0, star_one, one_mul, smul_smul,
      I_mul_I, neg_one_smul] at h
  -- `B t = V t (·) (V t)⋆` is a continuous group with derivative `L` at `0`.
  let B : AddChar ℝ ((E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) :=
    { toFun t := ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) (V t) (star (V t))
      map_zero_eq_one' := by ext X x; simp [hV0]
      map_add_eq_mul' s t := by ext X x; simp [AddChar.map_add_eq_mul, mul_assoc] }
  have hB : Continuous B :=
    ((ContinuousLinearMap.mulLeftRight ℂ _).continuous.comp V.continuous).clm_apply
      (continuous_star.comp V.continuous)
  have hBL : deriv B 0 = L := by
    ext1 X
    have hd := hasDerivAt_addChar (𝔸 := (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) B hB
    refine (hd.clm_apply_const X).unique (((hV.mul_const X).fun_mul hVs).congr_deriv ?_)
    rw [hK, hV0, star_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg]
    have h := hc X
    rw [add_mul, mul_add] at h
    simp only [K₀, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, eq_sub_of_add_eq' h]
    module
  have hexp :=
    OneParameterSubgroup.apply_eq_exp_smul_deriv (E := (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E)
  refine ⟨V, fun t X => ?_⟩
  show A t X = B t X
  rw [hexp A hA t, hexp B hB t, hBL]

variable [FiniteDimensional ℂ E]

/-- A continuous semigroup of unitary or anti-unitary conjugations of the density operators is
conjugation by a norm-continuous unitary one-parameter group. -/
theorem exists_unitaryOneParameterGroup {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (hΦ : ∀ t ≥ 0, ImplementedByUnitaryOrAntiunitary (Φ t))
    (h0 : ∀ ρ, IsDensity ρ → Φ 0 ρ = ρ)
    (hadd : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ (s + t) ρ = Φ s (Φ t ρ))
    (hcont : ∀ ρ, IsDensity ρ → ContinuousWithinAt (fun t => Φ t ρ) (Set.Ici 0) 0) :
    ∃ V : UnitaryOneParameterGroup E,
      ∀ t ≥ 0, ∀ ρ, IsDensity ρ → Φ t ρ = V t * ρ * star (V t) := by
  obtain ⟨A, hA, hAd, hAΦ⟩ :=
    exists_addChar_adL (fun t ht => exists_unitary_of_map_add hΦ hadd ht) h0 hadd hcont
  obtain ⟨V, hV⟩ := exists_unitaryOneParameterGroup_of_addChar A hA hAd
  exact ⟨V, fun t ht ρ hρ => by rw [← hAΦ t ht ρ hρ, hV]⟩

end Lift

end QuantumMechanics.Wigner
