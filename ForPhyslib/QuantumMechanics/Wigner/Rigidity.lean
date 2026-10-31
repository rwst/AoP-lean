/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.PhaseUnitary
public import ForPhyslib.QuantumMechanics.Wigner.Normalize

/-!
# Rigidity of a normalized Wigner map

## i. Overview

Let `f` be a Wigner map that fixes the rays of a Hilbert basis `b` and of every
`vecSub b i₀ k`. By the three-circle lemma, the coordinates of `f v` (with the phase chosen so
that the `i₀`-coordinates agree) are determined by the moduli of their pairings with `b k`,
`vecSub b i₀ k` and the image of `vecAddI b i₀ k`. Two consequences:

* the alternatives of `QuantumMechanics.Wigner.IsWignerMap.phaseEq_vecAddI_or` cannot be mixed:
  either `f` fixes every `vecAddI b i₀ k` or it sends every one to `vecSubI b i₀ k` (step 6);
* if `f` fixes every `vecAddI b i₀ k` too, then `f v` equals `v` up to phase for every unit
  vector `v` (step 7). For `⟪b i₀, v⟫ ≠ 0` this is the three-circle lemma coordinate by
  coordinate; for `⟪b i₀, v⟫ = 0` it follows from equality in Cauchy–Schwarz.

## ii. Key results

- `QuantumMechanics.Wigner.FixesResolving`: `f` fixes the rays of the resolving set around `i₀`.
- `QuantumMechanics.Wigner.IsWignerMap.not_mixed`: no `k₁` fixed and `k₂` flipped.
- `QuantumMechanics.Wigner.IsWignerMap.fixes_or_flips`: all fixed or all flipped.
- `QuantumMechanics.Wigner.IsWignerMap.phaseEqOnSphere_id`: a Wigner map fixing the resolving set
  agrees with the identity up to phase on unit vectors.

## iii. Table of contents

- A. Coordinates from three moduli
- B. Three-coordinate test vectors
- C. No mixed signs
- D. The identity on rays

## iv. References

- Gy. P. Gehér, *An elementary proof for the non-bijective version of Wigner's theorem*,
  Phys. Lett. A 378 (2014), 2054–2057.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexConjugate
open Complex (I)

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*} [DecidableEq ι] {b : HilbertBasis ι ℂ E}

/-- `f` fixes, up to phase, the basis vectors and the vectors `vecSub b i₀ k` and
`vecAddI b i₀ k` for `k ≠ i₀`. -/
structure FixesResolving (f : E → E) (b : HilbertBasis ι ℂ E) (i₀ : ι) : Prop where
  basis : ∀ k, PhaseEq (f (b k)) (b k)
  sub : ∀ k, k ≠ i₀ → PhaseEq (f (vecSub b i₀ k)) (vecSub b i₀ k)
  addI : ∀ k, k ≠ i₀ → PhaseEq (f (vecAddI b i₀ k)) (vecAddI b i₀ k)

/-!
## A. Coordinates from three moduli
-/

omit [DecidableEq ι] in
lemma norm_eq_of_norm_sqrt_two_inv_mul {x y : ℂ}
    (h : ‖((√2 : ℝ) : ℂ)⁻¹ * x‖ = ‖((√2 : ℝ) : ℂ)⁻¹ * y‖) : ‖x‖ = ‖y‖ := by
  rw [norm_mul, norm_mul] at h
  exact mul_left_cancel₀ (norm_ne_zero_iff.2 sqrt_two_inv_ne_zero) h

omit [DecidableEq ι] in
lemma norm_I_mul_sub {x z : ℂ} : ‖z + I * x‖ = ‖x - I * z‖ := by
  rw [show z + I * x = I * (x - I * z) by ring_nf; rw [Complex.I_sq]; ring, norm_mul,
    Complex.norm_I, one_mul]

namespace IsWignerMap

variable {f : E → E}

omit [DecidableEq ι] in
/-- Pairing a test vector with a rephased image. -/
lemma norm_inner_smul_apply (hf : IsWignerMap f) {u u' v : E} {c : ℂ} (hc : ‖c‖ = 1)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h : PhaseEq (f u) u') :
    ‖⟪u', c • f v⟫_ℂ‖ = ‖⟪u, v⟫_ℂ‖ := by
  rw [inner_smul_right, norm_mul, hc, one_mul, hf.norm_inner_of_phaseEq hu hv h]

omit [DecidableEq ι] in
/-- **The coordinate lemma.** If `f` fixes `b k`, `vecSub b i₀ k` and `vecAddI b i₀ k`, and the
phase of `f v` is chosen so that its `i₀`-coordinate is that of `v`, which is non-zero, then the
`k`-coordinates agree too. -/
lemma inner_basis_smul_apply_eq (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k))
    {i₀ k : ι} (hk : k ≠ i₀) (hsub : PhaseEq (f (vecSub b i₀ k)) (vecSub b i₀ k))
    (hadd : PhaseEq (f (vecAddI b i₀ k)) (vecAddI b i₀ k)) {v : E} (hv : ‖v‖ = 1) {c : ℂ}
    (hc : ‖c‖ = 1) (h₀ : ⟪b i₀, c • f v⟫_ℂ = ⟪b i₀, v⟫_ℂ) (hv₀ : ⟪b i₀, v⟫_ℂ ≠ 0) :
    ⟪b k, c • f v⟫_ℂ = ⟪b k, v⟫_ℂ := by
  have e₀ := hf.norm_inner_smul_apply hc (b.orthonormal.1 k) hv (hb k)
  have e₁ := hf.norm_inner_smul_apply hc (norm_vecSub hk.symm) hv hsub
  have e₂ := hf.norm_inner_smul_apply hc (norm_vecAddI hk.symm) hv hadd
  rw [inner_vecSub_left, inner_vecSub_left, h₀] at e₁
  rw [inner_vecAddI_left, inner_vecAddI_left, h₀] at e₂
  refine Complex.eq_of_norm_eq_of_norm_sub_eq_of_norm_add_I_mul_eq hv₀ e₀ ?_ ?_
  · rw [norm_sub_rev, norm_sub_rev ⟪b k, v⟫_ℂ]
    exact norm_eq_of_norm_sqrt_two_inv_mul e₁
  · rw [norm_I_mul_sub, norm_I_mul_sub]
    exact norm_eq_of_norm_sqrt_two_inv_mul e₂

omit [DecidableEq ι] in
/-- **The coordinate lemma, conjugate form.** If `f` fixes `b k` and `vecSub b i₀ k` but sends
`vecAddI b i₀ k` to `vecSubI b i₀ k`, and the common `i₀`-coordinate is real and non-zero, then
the `k`-coordinate of the rephased `f v` is the conjugate of that of `v`. -/
lemma inner_basis_smul_apply_eq_conj (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k))
    {i₀ k : ι} (hk : k ≠ i₀) (hsub : PhaseEq (f (vecSub b i₀ k)) (vecSub b i₀ k))
    (hflip : PhaseEq (f (vecAddI b i₀ k)) (vecSubI b i₀ k)) {v : E} (hv : ‖v‖ = 1) {c : ℂ}
    (hc : ‖c‖ = 1) {t : ℝ} (ht : t ≠ 0) (h₀ : ⟪b i₀, c • f v⟫_ℂ = t) (hv₀ : ⟪b i₀, v⟫_ℂ = t) :
    ⟪b k, c • f v⟫_ℂ = conj ⟪b k, v⟫_ℂ := by
  have e₀ := hf.norm_inner_smul_apply hc (b.orthonormal.1 k) hv (hb k)
  have e₁ := hf.norm_inner_smul_apply hc (norm_vecSub hk.symm) hv hsub
  have e₂ := hf.norm_inner_smul_apply hc (norm_vecAddI hk.symm) hv hflip
  rw [inner_vecSub_left, inner_vecSub_left, h₀, hv₀] at e₁
  rw [inner_vecSubI_left, inner_vecAddI_left, h₀, hv₀] at e₂
  refine Complex.eq_conj_of_norm_eq_of_norm_sub_eq_of_norm_add_I_mul_eq ht e₀.symm ?_ ?_
  · rw [norm_sub_rev, norm_sub_rev ⟪b k, c • f v⟫_ℂ]
    exact (norm_eq_of_norm_sqrt_two_inv_mul e₁).symm
  · have h₁ : ‖⟪b k, v⟫_ℂ + I * t‖ = ‖(t : ℂ) - I * ⟪b k, v⟫_ℂ‖ := norm_I_mul_sub
    have h₂ : ‖⟪b k, c • f v⟫_ℂ - I * t‖ = ‖(t : ℂ) + I * ⟪b k, c • f v⟫_ℂ‖ := by
      rw [show ⟪b k, c • f v⟫_ℂ - I * t = -I * (t + I * ⟪b k, c • f v⟫_ℂ) by
        ring_nf; rw [Complex.I_sq]; ring, norm_mul, norm_neg, Complex.norm_I, one_mul]
    rw [h₁, h₂]
    exact (norm_eq_of_norm_sqrt_two_inv_mul e₂).symm

omit [DecidableEq ι] in
/-- The phase that makes the `i₀`-coordinate of `f v` equal to that of `v`. -/
lemma exists_smul_inner_basis_eq (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k))
    {i₀ : ι} {v : E} (hv : ‖v‖ = 1) (hv₀ : ⟪b i₀, v⟫_ℂ ≠ 0) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ⟪b i₀, c • f v⟫_ℂ = ⟪b i₀, v⟫_ℂ := by
  have hn := hf.norm_inner_basis_apply b hb hv i₀
  have hw₀ : ⟪b i₀, f v⟫_ℂ ≠ 0 := by rw [← norm_ne_zero_iff, hn, norm_ne_zero_iff]; exact hv₀
  refine ⟨⟪b i₀, v⟫_ℂ / ⟪b i₀, f v⟫_ℂ, ?_, ?_⟩
  · rw [norm_div, hn, div_self (norm_ne_zero_iff.2 hv₀)]
  · rw [inner_smul_right, div_mul_cancel₀ _ hw₀]

omit [DecidableEq ι] in
lemma inner_basis_apply_eq_zero (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k))
    {v : E} (hv : ‖v‖ = 1) {c : ℂ} (hc : ‖c‖ = 1) {j : ι} (hj : ⟪b j, v⟫_ℂ = 0) :
    ⟪b j, c • f v⟫_ℂ = 0 := by
  rw [← norm_eq_zero, hf.norm_inner_smul_apply hc (b.orthonormal.1 j) hv (hb j), hj, norm_zero]

end IsWignerMap

/-!
## B. Three-coordinate test vectors
-/

variable (b) in
/-- `(b i + p • b j + q • b k) / √3`. -/
def vec3 (i j k : ι) (p q : ℂ) : E :=
  ((√3 : ℝ) : ℂ)⁻¹ • (b i + p • b j + q • b k)

omit [DecidableEq ι] in
lemma sqrt_three_inv_mul_self : ((√3 : ℝ) : ℂ)⁻¹ * ((√3 : ℝ) : ℂ)⁻¹ = 3⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num), Complex.ofReal_ofNat]

omit [DecidableEq ι] in
lemma conj_sqrt_three_inv : conj ((√3 : ℝ) : ℂ)⁻¹ = ((√3 : ℝ) : ℂ)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

variable (b) in
lemma inner_basis_vec3 (l i j k : ι) (p q : ℂ) :
    ⟪b l, vec3 b i j k p q⟫_ℂ = ((√3 : ℝ) : ℂ)⁻¹ *
      ((if l = i then 1 else 0) + p * (if l = j then 1 else 0) + q * if l = k then 1 else 0) := by
  rw [vec3, inner_smul_right, inner_add_right, inner_add_right, inner_smul_right,
    inner_smul_right, inner_basis_basis, inner_basis_basis, inner_basis_basis]

omit [DecidableEq ι] in
variable (b) in
lemma inner_vec3_left (i j k : ι) (p q : ℂ) (z : E) :
    ⟪vec3 b i j k p q, z⟫_ℂ = ((√3 : ℝ) : ℂ)⁻¹ *
      (⟪b i, z⟫_ℂ + conj p * ⟪b j, z⟫_ℂ + conj q * ⟪b k, z⟫_ℂ) := by
  rw [vec3, inner_smul_left, inner_add_left, inner_add_left, inner_smul_left, inner_smul_left,
    conj_sqrt_three_inv]

omit [DecidableEq ι] in
lemma norm_vec3 {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {p q : ℂ} (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1) : ‖vec3 b i j k p q‖ = 1 := by
  classical
  refine norm_eq_one_of_inner_self_eq_one ?_
  rw [inner_vec3_left, inner_basis_vec3, inner_basis_vec3, inner_basis_vec3]
  simp only [hij, hik, hjk, hij.symm, hik.symm, hjk.symm, ↓reduceIte]
  have hp' : conj p * p = 1 := by rw [Complex.conj_mul', hp]; norm_num
  have hq' : conj q * q = 1 := by rw [Complex.conj_mul', hq]; norm_num
  linear_combination (1 + conj p * p + conj q * q) * sqrt_three_inv_mul_self +
    3⁻¹ * hp' + 3⁻¹ * hq'

/-!
## C. No mixed signs
-/

namespace IsWignerMap

variable {f : E → E}

/-- With `k₁` fixed and `k₂` flipped, `f` sends `vec3 b i₀ k₁ k₂ p q` for real `1 / √3` in the
`i₀`-coordinate to `vec3 b i₀ k₁ k₂ p (conj q)` up to phase. -/
lemma phaseEq_vec3 (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k)) {i₀ k₁ k₂ : ι}
    (h₁ : k₁ ≠ i₀) (h₂ : k₂ ≠ i₀) (h₁₂ : k₁ ≠ k₂)
    (hsub₁ : PhaseEq (f (vecSub b i₀ k₁)) (vecSub b i₀ k₁))
    (hsub₂ : PhaseEq (f (vecSub b i₀ k₂)) (vecSub b i₀ k₂))
    (hadd : PhaseEq (f (vecAddI b i₀ k₁)) (vecAddI b i₀ k₁))
    (hflip : PhaseEq (f (vecAddI b i₀ k₂)) (vecSubI b i₀ k₂)) {p q : ℂ} (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1) : PhaseEq (f (vec3 b i₀ k₁ k₂ p q)) (vec3 b i₀ k₁ k₂ p (conj q)) := by
  set v := vec3 b i₀ k₁ k₂ p q
  have hv : ‖v‖ = 1 := norm_vec3 h₁.symm h₂.symm h₁₂ hp hq
  have hv₀ : ⟪b i₀, v⟫_ℂ = ((√3⁻¹ : ℝ) : ℂ) := by
    simp [v, inner_basis_vec3, h₁.symm, h₂.symm]
  have ht : (√3⁻¹ : ℝ) ≠ 0 := by positivity
  have hv₀' : ⟪b i₀, v⟫_ℂ ≠ 0 := by rw [hv₀]; exact_mod_cast ht
  obtain ⟨c, hc, h₀⟩ := hf.exists_smul_inner_basis_eq hb hv hv₀'
  refine (PhaseEq.of_smul_left hc ?_)
  refine phaseEq_of_inner_basis b (c := 1) norm_one fun j => ?_
  rw [one_mul]
  by_cases hj₀ : j = i₀
  · subst hj₀; rw [h₀]; simp [v, inner_basis_vec3, h₁.symm, h₂.symm]
  by_cases hj₁ : j = k₁
  · subst hj₁
    rw [hf.inner_basis_smul_apply_eq hb h₁ hsub₁ hadd hv hc h₀ hv₀']
    simp [v, inner_basis_vec3, h₁, h₁₂]
  by_cases hj₂ : j = k₂
  · subst hj₂
    rw [hf.inner_basis_smul_apply_eq_conj hb h₂ hsub₂ hflip hv hc ht (h₀.trans hv₀) hv₀]
    simp [v, inner_basis_vec3, h₂, h₁₂.symm]
  · rw [hf.inner_basis_apply_eq_zero hb hv hc (by simp [v, inner_basis_vec3, hj₀, hj₁, hj₂])]
    simp [inner_basis_vec3, hj₀, hj₁, hj₂]

/-- **Step 6.** `f` cannot fix `vecAddI b i₀ k₁` and flip `vecAddI b i₀ k₂`: on
`x = vec3 b i₀ k₁ k₂ 1 1` and `y = vec3 b i₀ k₁ k₂ I I` it would turn `‖⟪x, y⟫‖ = √5 / 3` into
`1 / 3`. -/
lemma not_mixed (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k)) {i₀ k₁ k₂ : ι}
    (h₁ : k₁ ≠ i₀) (h₂ : k₂ ≠ i₀) (h₁₂ : k₁ ≠ k₂)
    (hsub₁ : PhaseEq (f (vecSub b i₀ k₁)) (vecSub b i₀ k₁))
    (hsub₂ : PhaseEq (f (vecSub b i₀ k₂)) (vecSub b i₀ k₂))
    (hadd : PhaseEq (f (vecAddI b i₀ k₁)) (vecAddI b i₀ k₁))
    (hflip : PhaseEq (f (vecAddI b i₀ k₂)) (vecSubI b i₀ k₂)) : False := by
  have hI : ‖I‖ = 1 := Complex.norm_I
  have hx := hf.phaseEq_vec3 hb h₁ h₂ h₁₂ hsub₁ hsub₂ hadd hflip norm_one norm_one
  have hy := hf.phaseEq_vec3 hb h₁ h₂ h₁₂ hsub₁ hsub₂ hadd hflip hI hI
  have h := hf _ _ (norm_vec3 (b := b) h₁.symm h₂.symm h₁₂ norm_one norm_one)
    (norm_vec3 (b := b) h₁.symm h₂.symm h₁₂ hI hI)
  rw [hx.norm_inner_left, hy.norm_inner_right, inner_vec3_left, inner_vec3_left,
    inner_basis_vec3, inner_basis_vec3, inner_basis_vec3, inner_basis_vec3, inner_basis_vec3,
    inner_basis_vec3] at h
  simp only [h₁, h₂, h₁₂, h₁.symm, h₂.symm, h₁₂.symm, ↓reduceIte, map_one, Complex.conj_I,
    one_mul, mul_one, mul_zero, add_zero, zero_add] at h
  rw [show ((√3 : ℝ) : ℂ)⁻¹ * (((√3 : ℝ) : ℂ)⁻¹ + ((√3 : ℝ) : ℂ)⁻¹ * I +
      ((√3 : ℝ) : ℂ)⁻¹ * -I) = ((√3 : ℝ) : ℂ)⁻¹ * ((√3 : ℝ) : ℂ)⁻¹ * 1 by ring,
    show ((√3 : ℝ) : ℂ)⁻¹ * (((√3 : ℝ) : ℂ)⁻¹ + ((√3 : ℝ) : ℂ)⁻¹ * I +
      ((√3 : ℝ) : ℂ)⁻¹ * I) = ((√3 : ℝ) : ℂ)⁻¹ * ((√3 : ℝ) : ℂ)⁻¹ * (1 + 2 * I) by ring,
    sqrt_three_inv_mul_self, norm_mul, norm_mul] at h
  have h5 := congrArg (· ^ 2) (mul_left_cancel₀ (by norm_num) h)
  simp only [norm_one, one_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h5
  norm_num at h5

/-- All `vecAddI b i₀ k` are fixed, or all are flipped. -/
lemma fixes_or_flips (hf : IsWignerMap f) (hb : ∀ k, PhaseEq (f (b k)) (b k)) {i₀ : ι}
    (hsub : ∀ k, k ≠ i₀ → PhaseEq (f (vecSub b i₀ k)) (vecSub b i₀ k)) :
    (∀ k, k ≠ i₀ → PhaseEq (f (vecAddI b i₀ k)) (vecAddI b i₀ k)) ∨
      (∀ k, k ≠ i₀ → PhaseEq (f (vecAddI b i₀ k)) (vecSubI b i₀ k)) := by
  by_contra h
  push Not at h
  obtain ⟨⟨k₁, hk₁, hn₁⟩, ⟨k₂, hk₂, hn₂⟩⟩ := h
  have hflip := (hf.phaseEq_vecAddI_or hb hk₁ (hsub k₁ hk₁)).resolve_left hn₁
  have hadd := (hf.phaseEq_vecAddI_or hb hk₂ (hsub k₂ hk₂)).resolve_right hn₂
  have h₂₁ : k₂ ≠ k₁ := by rintro rfl; exact hn₂ hflip
  exact hf.not_mixed hb hk₂ hk₁ h₂₁ (hsub k₂ hk₂) (hsub k₁ hk₁) hadd hflip

/-!
## D. The identity on rays
-/

omit [DecidableEq ι] in
/-- **Step 7, first case.** If `f` fixes the resolving set and `⟪b i₀, v⟫ ≠ 0`, then `f v`
equals `v` up to phase. -/
lemma phaseEq_self_of_inner_ne_zero (hf : IsWignerMap f) {i₀ : ι}
    (hR : FixesResolving f b i₀) {v : E} (hv : ‖v‖ = 1) (hv₀ : ⟪b i₀, v⟫_ℂ ≠ 0) :
    PhaseEq (f v) v := by
  obtain ⟨c, hc, h₀⟩ := hf.exists_smul_inner_basis_eq hR.basis hv hv₀
  refine PhaseEq.of_smul_left hc (phaseEq_of_inner_basis b (c := 1) norm_one fun j => ?_)
  rw [one_mul]
  by_cases hj : j = i₀
  · rw [hj, h₀]
  · exact hf.inner_basis_smul_apply_eq hR.basis hj (hR.sub j hj) (hR.addI j hj) hv hc h₀ hv₀

omit [DecidableEq ι] in
/-- **Step 7.** A Wigner map that fixes the resolving set agrees with the identity up to phase
on unit vectors. For `⟪b i₀, v⟫ = 0`, the vector `u = (v + b i₀) / √2` is fixed by the first
case, and `‖⟪u, f v⟫‖ = ‖⟪u, v⟫‖` forces `‖⟪v, f v⟫‖ = 1`. -/
lemma phaseEqOnSphere_id (hf : IsWignerMap f) {i₀ : ι} (hR : FixesResolving f b i₀) :
    PhaseEqOnSphere f id := by
  intro v hv
  show PhaseEq (f v) v
  by_cases hv₀ : ⟪b i₀, v⟫_ℂ = 0
  swap
  · exact hf.phaseEq_self_of_inner_ne_zero hR hv hv₀
  set s : ℂ := ((√2 : ℝ) : ℂ)⁻¹
  set u : E := s • (v + b i₀)
  have hvv : ⟪v, v⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; norm_num
  have hvb : ⟪v, b i₀⟫_ℂ = 0 := by rw [← inner_conj_symm, hv₀, map_zero]
  have hbb : ⟪b i₀, b i₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i₀]; norm_num
  have hu : ‖u‖ = 1 := by
    refine norm_eq_one_of_inner_self_eq_one ?_
    simp only [u, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, hvv, hvb,
      hv₀, hbb, s, conj_sqrt_two_inv]
    linear_combination 2 * sqrt_two_inv_mul_self
  have hu₀ : ⟪b i₀, u⟫_ℂ ≠ 0 := by
    simp only [u, inner_smul_right, inner_add_right, hv₀, hbb, zero_add, mul_one]
    exact sqrt_two_inv_ne_zero
  have hfu := hf.phaseEq_self_of_inner_ne_zero hR hu hu₀
  have hfv₀ : ⟪b i₀, f v⟫_ℂ = 0 := by
    simpa using hf.inner_basis_apply_eq_zero hR.basis hv norm_one hv₀
  have h := hf.norm_inner_of_phaseEq hu hv hfu
  simp only [u, inner_smul_left, inner_add_left, hvv, hv₀, hfv₀, add_zero, norm_mul,
    norm_one] at h
  have h1 : ‖⟪v, f v⟫_ℂ‖ = 1 := mul_left_cancel₀ (by simp [s]) h
  exact exists_norm_eq_one_smul_of_norm_inner_eq_one (hf.norm_apply hv) hv
    (by rw [norm_inner_symm, h1])

end IsWignerMap

end QuantumMechanics.Wigner
