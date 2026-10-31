/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Complex.ThreeCircles
public import ForPhyslib.QuantumMechanics.Wigner.Basic

/-!
# Normalizing a Wigner map on a resolving set

## i. Overview

Fix a Hilbert basis `b` of a complex Hilbert space of any dimension and an index `i₀`. For
`k ≠ i₀` consider the unit vectors

* `vecSub b i₀ k = (b i₀ - b k) / √2`,
* `vecAddI b i₀ k = (b i₀ + I • b k) / √2` and `vecSubI b i₀ k = (b i₀ - I • b k) / √2`.

Together with the basis they form Gehér's resolving set, here paired star-shaped around `i₀`
instead of along a chain. This file composes a Wigner map `f` with the adjoint of an isometry and
with a diagonal unitary until it fixes the rays of `b` and of every `vecSub b i₀ k`, and shows
that then `f (vecAddI b i₀ k)` is `vecAddI b i₀ k` or `vecSubI b i₀ k` up to phase.
Coordinatewise conjugation in `b` exchanges the two alternatives and fixes everything else.

## ii. Key results

- `QuantumMechanics.Wigner.IsWignerMap.exists_isometry_basis`: an isometry `V` with
  `V (b k) = f (b k)` and `V (V† (f v)) = f v`, so that `V† ∘ f` is a Wigner map fixing every
  `b k`.
- `QuantumMechanics.Wigner.IsWignerMap.exists_phaseEq_vecSub`: a diagonal unitary `D` such that
  `D⁻¹ ∘ f` also fixes the rays of the `vecSub b i₀ k`.
- `QuantumMechanics.Wigner.IsWignerMap.phaseEq_vecAddI_or`: then `f (vecAddI b i₀ k)` is
  `vecAddI b i₀ k` or `vecSubI b i₀ k` up to phase.
- `QuantumMechanics.Wigner.conjugation_vecAddI`: conjugation exchanges `vecAddI` and `vecSubI`.

## iii. Table of contents

- A. The test vectors
- B. Fixing the basis
- C. Fixing the phases
- D. The choice between `I` and `-I`
- E. Conjugation

## iv. References

- Gy. P. Gehér, *An elementary proof for the non-bijective version of Wigner's theorem*,
  Phys. Lett. A 378 (2014), 2054–2057.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Complex (I)

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} (b : HilbertBasis ι ℂ E)

/-!
## A. The test vectors
-/

/-- `(b i - b k) / √2`. -/
def vecSub (i k : ι) : E :=
  ((√2 : ℝ) : ℂ)⁻¹ • (b i - b k)

/-- `(b i + I • b k) / √2`. -/
def vecAddI (i k : ι) : E :=
  ((√2 : ℝ) : ℂ)⁻¹ • (b i + I • b k)

/-- `(b i - I • b k) / √2`. -/
def vecSubI (i k : ι) : E :=
  ((√2 : ℝ) : ℂ)⁻¹ • (b i - I • b k)

lemma sqrt_two_inv_mul_self : ((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]

lemma conj_sqrt_two_inv : conj ((√2 : ℝ) : ℂ)⁻¹ = ((√2 : ℝ) : ℂ)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

lemma sqrt_two_inv_ne_zero : ((√2 : ℝ) : ℂ)⁻¹ ≠ 0 := by
  simp

lemma norm_sqrt_two_inv : ‖((√2 : ℝ) : ℂ)⁻¹‖ = (√2)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2)]

lemma norm_eq_one_of_inner_self_eq_one {x : E} (h : ⟪x, x⟫_ℂ = 1) : ‖x‖ = 1 := by
  have h' := congrArg norm h
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm, norm_one] at h'
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'

/-- Two vectors are equal up to phase if their coordinates are, with one common phase. -/
lemma phaseEq_of_inner_basis {x y : E} {c : ℂ} (hc : ‖c‖ = 1)
    (h : ∀ j, ⟪b j, x⟫_ℂ = c * ⟪b j, y⟫_ℂ) : PhaseEq x y := by
  exact ⟨c, hc, b.ext_inner fun j => by rw [h, inner_smul_right]⟩

lemma inner_vecSub_left (i k : ι) (x : E) :
    ⟪vecSub b i k, x⟫_ℂ = ((√2 : ℝ) : ℂ)⁻¹ * (⟪b i, x⟫_ℂ - ⟪b k, x⟫_ℂ) := by
  rw [vecSub, inner_smul_left, inner_sub_left, conj_sqrt_two_inv]

lemma inner_vecAddI_left (i k : ι) (x : E) :
    ⟪vecAddI b i k, x⟫_ℂ = ((√2 : ℝ) : ℂ)⁻¹ * (⟪b i, x⟫_ℂ - I * ⟪b k, x⟫_ℂ) := by
  rw [vecAddI, inner_smul_left, inner_add_left, inner_smul_left, conj_sqrt_two_inv,
    Complex.conj_I]
  ring

lemma inner_vecSubI_left (i k : ι) (x : E) :
    ⟪vecSubI b i k, x⟫_ℂ = ((√2 : ℝ) : ℂ)⁻¹ * (⟪b i, x⟫_ℂ + I * ⟪b k, x⟫_ℂ) := by
  rw [vecSubI, inner_smul_left, inner_sub_left, inner_smul_left, conj_sqrt_two_inv,
    Complex.conj_I]
  ring

variable [DecidableEq ι]

lemma inner_basis_basis (j i : ι) : ⟪b j, b i⟫_ℂ = if j = i then 1 else 0 :=
  orthonormal_iff_ite.1 b.orthonormal j i

lemma inner_basis_vecSub (j i k : ι) :
    ⟪b j, vecSub b i k⟫_ℂ =
      ((√2 : ℝ) : ℂ)⁻¹ * ((if j = i then 1 else 0) - if j = k then 1 else 0) := by
  rw [vecSub, inner_smul_right, inner_sub_right, inner_basis_basis, inner_basis_basis]

lemma inner_basis_vecAddI (j i k : ι) :
    ⟪b j, vecAddI b i k⟫_ℂ =
      ((√2 : ℝ) : ℂ)⁻¹ * ((if j = i then 1 else 0) + I * if j = k then 1 else 0) := by
  rw [vecAddI, inner_smul_right, inner_add_right, inner_smul_right, inner_basis_basis,
    inner_basis_basis]

lemma inner_basis_vecSubI (j i k : ι) :
    ⟪b j, vecSubI b i k⟫_ℂ =
      ((√2 : ℝ) : ℂ)⁻¹ * ((if j = i then 1 else 0) - I * if j = k then 1 else 0) := by
  rw [vecSubI, inner_smul_right, inner_sub_right, inner_smul_right, inner_basis_basis,
    inner_basis_basis]

omit [DecidableEq ι] in
variable {b} in
lemma norm_vecSub {i k : ι} (hik : i ≠ k) : ‖vecSub b i k‖ = 1 := by
  classical
  refine norm_eq_one_of_inner_self_eq_one ?_
  rw [inner_vecSub_left, inner_basis_vecSub, inner_basis_vecSub]
  simp only [hik, hik.symm, ↓reduceIte]
  linear_combination 2 * sqrt_two_inv_mul_self

omit [DecidableEq ι] in
variable {b} in
lemma norm_vecAddI {i k : ι} (hik : i ≠ k) : ‖vecAddI b i k‖ = 1 := by
  classical
  refine norm_eq_one_of_inner_self_eq_one ?_
  rw [inner_vecAddI_left, inner_basis_vecAddI, inner_basis_vecAddI]
  simp only [hik, hik.symm, ↓reduceIte]
  linear_combination (1 - I * I) * sqrt_two_inv_mul_self - 2⁻¹ * Complex.I_mul_I

omit [DecidableEq ι] in
variable {b} in
lemma norm_vecSubI {i k : ι} (hik : i ≠ k) : ‖vecSubI b i k‖ = 1 := by
  classical
  refine norm_eq_one_of_inner_self_eq_one ?_
  rw [inner_vecSubI_left, inner_basis_vecSubI, inner_basis_vecSubI]
  simp only [hik, hik.symm, ↓reduceIte]
  linear_combination (1 - I * I) * sqrt_two_inv_mul_self - 2⁻¹ * Complex.I_mul_I

/-!
## B. Fixing the basis
-/

namespace IsWignerMap

variable {f : E → E}

omit [DecidableEq ι] in
variable [CompleteSpace E] in
/-- **Step 2.** The images `f (b k)` form an orthonormal family, so an isometry `V` sends `b k` to
`f (b k)`. By Parseval, `‖V† (f v)‖ = ‖v‖ = ‖f v‖`, so `f v` lies in the range of `V`, and
`V† ∘ f` is a Wigner map that fixes every `b k`. In finite dimension `V` is unitary; in general
it need not be onto. -/
lemma exists_isometry_basis (hf : IsWignerMap f) :
    ∃ V : E →ₗᵢ[ℂ] E, IsWignerMap (V.toContinuousLinearMap.adjoint ∘ f) ∧
      (∀ k, V.toContinuousLinearMap.adjoint (f (b k)) = b k) ∧
      ∀ v, ‖v‖ = 1 → V (V.toContinuousLinearMap.adjoint (f v)) = f v := by
  set V := b.isometryOfOrthonormal (hf.orthonormal_comp b.orthonormal)
  set A := V.toContinuousLinearMap.adjoint
  have hAV : ∀ x, A (V x) = x := fun x => ext_inner_left ℂ fun z => by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact V.inner_map_map z x
  have hVb : ∀ k, V (b k) = f (b k) := fun k => b.isometryOfOrthonormal_apply_basis _ k
  have hrange : ∀ v, ‖v‖ = 1 → V (A (f v)) = f v := fun v hv => by
    refine V.apply_adjoint_apply_of_norm_eq ?_
    have h1 := b.hasSum_norm_inner_sq (A (f v))
    have hk : (fun k => ‖⟪b k, A (f v)⟫_ℂ‖ ^ 2) = fun k => ‖⟪b k, v⟫_ℂ‖ ^ 2 := funext fun k => by
      rw [ContinuousLinearMap.adjoint_inner_right]
      change ‖⟪V (b k), f v⟫_ℂ‖ ^ 2 = _
      rw [hVb, hf _ _ (b.orthonormal.1 k) hv]
    rw [hk] at h1
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [h1.unique (b.hasSum_norm_inner_sq v), hv, hf.norm_apply hv]
  refine ⟨V, fun v w hv hw => ?_, fun k => by rw [← hVb, hAV], hrange⟩
  rw [Function.comp_apply, Function.comp_apply, ← V.inner_map_map, hrange v hv, hrange w hw,
    hf v w hv hw]

/-!
## C. Fixing the phases
-/

variable {b}

/-- If `f` fixes the rays of the basis, then `f` sends `vecSub b i₀ k` to a vector supported on
`b i₀` and `b k`, with both coordinates of modulus `1 / √2`. -/
lemma inner_basis_apply_vecSub (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k))
    {i₀ k : ι} (hk : k ≠ i₀) (j : ι) :
    ‖⟪b j, f (vecSub b i₀ k)⟫_ℂ‖ =
      ‖((√2 : ℝ) : ℂ)⁻¹ * ((if j = i₀ then 1 else 0) - if j = k then 1 else 0)‖ := by
  rw [hf.norm_inner_basis_apply b hb (norm_vecSub hk.symm), inner_basis_vecSub]

variable [CompleteSpace E] in
/-- **Step 3.** If `f` fixes the rays of the basis, a diagonal unitary `D` makes `D⁻¹ ∘ f` fix
also the rays of every `vecSub b i₀ k`. -/
lemma exists_phaseEq_vecSub (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k)) (i₀ : ι) :
    ∃ D : E ≃ₗᵢ[ℂ] E, (∀ k, PhaseEq (D.symm (f (b k))) (b k)) ∧
      ∀ k, k ≠ i₀ → PhaseEq (D.symm (f (vecSub b i₀ k))) (vecSub b i₀ k) := by
  set s : ℂ := ((√2 : ℝ) : ℂ)⁻¹
  have hs : ‖s‖ = (√2)⁻¹ := norm_sqrt_two_inv
  have hs₀ : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  set α : ι → ℂ := fun k => ⟪b i₀, f (vecSub b i₀ k)⟫_ℂ
  set β : ι → ℂ := fun k => ⟪b k, f (vecSub b i₀ k)⟫_ℂ
  have hα : ∀ k, k ≠ i₀ → ‖α k‖ = (√2)⁻¹ := fun k hk => by
    simpa [Ne.symm hk, hs, abs_of_nonneg (Real.sqrt_nonneg 2)] using
      inner_basis_apply_vecSub hf hb hk i₀
  have hβ : ∀ k, k ≠ i₀ → ‖β k‖ = (√2)⁻¹ := fun k hk => by
    simpa [hk, hs, abs_of_nonneg (Real.sqrt_nonneg 2)] using
      inner_basis_apply_vecSub hf hb hk k
  set δ : ι → ℂ := fun k => if k = i₀ then 1 else -(β k / α k)
  have hδ : ∀ k, ‖δ k‖ = 1 := fun k => by
    by_cases hk : k = i₀
    · simp [δ, hk]
    · simp only [δ, hk, ↓reduceIte, norm_neg, norm_div, hα k hk, hβ k hk]
      exact div_self hs₀
  refine ⟨b.phaseUnitary δ hδ, fun k => ?_, fun k hk => ?_⟩
  · refine ((hb k).map_linear (b.phaseUnitary δ hδ).symm.toLinearEquiv.toLinearMap).trans ?_
    refine ⟨(δ k)⁻¹, by rw [norm_inv, hδ, inv_one], ?_⟩
    exact b.phaseUnitary_symm_apply_basis δ hδ k
  · have hα₀ : α k ≠ 0 := by rw [← norm_ne_zero_iff, hα k hk]; exact hs₀
    refine phaseEq_of_inner_basis b (c := √2 * α k) ?_ fun j => ?_
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2), hα k hk,
        mul_inv_cancel₀ (by positivity)]
    rw [b.inner_basis_phaseUnitary_symm, inner_basis_vecSub]
    by_cases hj₀ : j = i₀
    · subst hj₀
      simp only [δ, ↓reduceIte, Ne.symm hk, inv_one, one_mul, sub_zero, mul_one]
      field_simp
      rfl
    by_cases hjk : j = k
    · subst hjk
      have hβ₀ : β j ≠ 0 := by rw [← norm_ne_zero_iff, hβ j hk]; exact hs₀
      simp only [δ, hk, ↓reduceIte, zero_sub, mul_neg, mul_one]
      change (-(β j / α j))⁻¹ * β j = _
      field_simp
    · have h0 : ⟪b j, f (vecSub b i₀ k)⟫_ℂ = 0 := by
        simpa [hj₀, hjk] using inner_basis_apply_vecSub hf hb hk j
      simp [h0, hj₀, hjk]

/-!
## D. The choice between `I` and `-I`
-/

/-- **Step 4.** If `f` fixes the rays of the basis and of `vecSub b i₀ k`, then
`f (vecAddI b i₀ k)` is `vecAddI b i₀ k` or `vecSubI b i₀ k` up to phase. -/
lemma phaseEq_vecAddI_or (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k)) {i₀ k : ι}
    (hk : k ≠ i₀) (hsub : PhaseEq (f (vecSub b i₀ k)) (vecSub b i₀ k)) :
    PhaseEq (f (vecAddI b i₀ k)) (vecAddI b i₀ k) ∨
      PhaseEq (f (vecAddI b i₀ k)) (vecSubI b i₀ k) := by
  set s : ℂ := ((√2 : ℝ) : ℂ)⁻¹
  have hs : ‖s‖ = (√2)⁻¹ := norm_sqrt_two_inv
  have hs₀ : (√2 : ℝ)⁻¹ ≠ 0 := by positivity
  have hsq : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt zero_le_two
  set w := f (vecAddI b i₀ k)
  have hmod : ∀ j, ‖⟪b j, w⟫_ℂ‖ = ‖⟪b j, vecAddI b i₀ k⟫_ℂ‖ :=
    hf.norm_inner_basis_apply b hb (norm_vecAddI hk.symm)
  set α := ⟪b i₀, w⟫_ℂ
  set β := ⟪b k, w⟫_ℂ
  have hα : ‖α‖ = (√2)⁻¹ := by
    simpa [inner_basis_vecAddI, Ne.symm hk, hs, abs_of_nonneg (Real.sqrt_nonneg 2)] using hmod i₀
  have hβ : ‖β‖ = (√2)⁻¹ := by
    simpa [inner_basis_vecAddI, hk, hs, abs_of_nonneg (Real.sqrt_nonneg 2)] using hmod k
  have hα₀ : α ≠ 0 := by rw [← norm_ne_zero_iff, hα]; exact hs₀
  have hsub' : ‖α - β‖ = 1 := by
    have h := hf.norm_inner_of_phaseEq (norm_vecSub hk.symm) (norm_vecAddI (b := b) hk.symm) hsub
    rw [inner_vecSub_left, inner_vecSub_left, inner_basis_vecAddI, inner_basis_vecAddI] at h
    simp only [↓reduceIte, hk, Ne.symm hk, norm_mul] at h
    have h1I : ‖(1 : ℂ) - I * 1‖ = √2 := by
      rw [show (1 : ℂ) - I * 1 = ((1 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_add_mul_I]
      norm_num
    rw [show s * (1 + I * 0) - s * (0 + I * 1) = s * (1 - I * 1) by ring, norm_mul, hs, h1I,
      inv_mul_cancel₀ (by positivity)] at h
    exact mul_left_cancel₀ hs₀ h
  set ε := β / α with hεdef
  have hε : ‖ε‖ = 1 := by rw [norm_div, hα, hβ, div_self hs₀]
  have hε' : ‖1 - ε‖ = √2 := by
    rw [show 1 - ε = (α - β) / α by rw [hεdef]; field_simp, norm_div, hsub', hα, one_div, inv_inv]
  have hc : ‖(√2 : ℂ) * α‖ = 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg 2), hα,
      mul_inv_cancel₀ (by positivity)]
  have hβε : β = ε * α := by rw [hεdef, div_mul_cancel₀ _ hα₀]
  have coords : ∀ j, j ≠ i₀ → j ≠ k → ⟪b j, w⟫_ℂ = 0 := fun j hj₀ hjk => by
    simpa [inner_basis_vecAddI, hj₀, hjk] using hmod j
  have key : ∀ j, ⟪b j, w⟫_ℂ = (√2 : ℂ) * α *
      (s * ((if j = i₀ then 1 else 0) + ε * if j = k then 1 else 0)) := fun j => by
    have h2 : (√2 : ℂ) * s = 1 := by simp [s]
    by_cases hj₀ : j = i₀
    · subst hj₀; simp only [↓reduceIte, Ne.symm hk]; linear_combination (-α) * h2
    by_cases hjk : j = k
    · subst hjk; simp only [↓reduceIte, hj₀]; linear_combination hβε - ε * α * h2
    · simp [coords j hj₀ hjk, hj₀, hjk]
  rcases Complex.eq_I_or_eq_neg_I_of_norm_eq_one_of_norm_one_sub hε hε' with h | h
  · exact Or.inl (phaseEq_of_inner_basis b hc fun j => by rw [key, h, inner_basis_vecAddI])
  · refine Or.inr (phaseEq_of_inner_basis b hc fun j => ?_)
    rw [key, h, inner_basis_vecSubI, neg_mul, ← sub_eq_add_neg]

end IsWignerMap

/-!
## E. Conjugation
-/

omit [DecidableEq ι] in
lemma conjugation_vecSub (i k : ι) : b.conjugation (vecSub b i k) = vecSub b i k := by
  rw [vecSub, LinearIsometryEquiv.map_smulₛₗ, map_sub, HilbertBasis.conjugation_basis,
    HilbertBasis.conjugation_basis, conj_sqrt_two_inv]

omit [DecidableEq ι] in
lemma conjugation_vecAddI (i k : ι) : b.conjugation (vecAddI b i k) = vecSubI b i k := by
  rw [vecAddI, vecSubI, LinearIsometryEquiv.map_smulₛₗ, map_add, LinearIsometryEquiv.map_smulₛₗ,
    HilbertBasis.conjugation_basis, HilbertBasis.conjugation_basis, conj_sqrt_two_inv,
    Complex.conj_I, neg_smul, ← sub_eq_add_neg]

omit [DecidableEq ι] in
lemma conjugation_vecSubI (i k : ι) : b.conjugation (vecSubI b i k) = vecAddI b i k := by
  rw [← conjugation_vecAddI, HilbertBasis.conjugation_conjugation]

end QuantumMechanics.Wigner
