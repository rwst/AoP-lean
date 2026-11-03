/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Wigner.AffineExtension
public import ForPhyslib.QuantumMechanics.Wigner.Kadison

/-!
# Kadison's theorem for maps injective on pure states

## i. Overview

In finite dimension, a map `T` of the density operators that is affine, maps pure states to pure
states and is injective on them is already conjugation by a unitary or an anti-unitary, and so a
bijection of the pure states. Compactness of the pure states alone would not give this; the proof
here is algebraic and uses no topology.

The key step is that orthogonal pure states have orthogonal images. Let `ψ ⊥ φ` be unit vectors
with `T |ψ⟩⟨ψ| = |a⟩⟨a|` and `T |φ⟩⟨φ| = |b⟩⟨b|`, and let `L` be the linear extension of `T`
(`AffineOnDensities.exists_linearMap`). Then
`A z = L |ψ + z φ⟩⟨ψ + z φ| = |a⟩⟨a| + |z|² |b⟩⟨b| + z N + z̄ N'` with
`N = L |φ⟩⟨ψ|` and `N' = L |ψ⟩⟨φ|`, and `A z ^ 2 = (1 + |z|²) A z` because `A z` is
`1 + |z|²` times a pure state. Comparing coefficients of `z` gives
`|a⟩⟨a| N + N |a⟩⟨a| = N` and `|b⟩⟨b| N + N |b⟩⟨b| = N`, and `N² = 0`. Such an `N` is
`|N a⟩⟨a|` or `|a⟩⟨N† a|`, and likewise for `b`; comparing the two forms shows `N = 0` unless
`a ⊥ b` or `|⟪a, b⟫| = 1`. The same holds for `N'`, and `N = N' = 0` leaves
`A 1 = |a⟩⟨a| + |b⟩⟨b|`, which is twice a pure state only if `|⟪a, b⟫| = 1`. Injectivity
excludes `|⟪a, b⟫| = 1`.

With orthogonality, the images of an orthonormal basis are orthonormal, so Bessel's inequality
takes the place of surjectivity in the Parseval averaging of
`QuantumMechanics.Wigner.Kadison`: overlaps are preserved, and Wigner's theorem applies.

## ii. Key results

- `QuantumMechanics.Wigner.mul_add_mul_eq_of_sq_eq`: the coefficient comparison.
- `QuantumMechanics.Wigner.eq_zero_of_mul_add_mul_eq`: the two-pole lemma.
- `QuantumMechanics.Wigner.AffineOnDensities.inner_eq_zero_of_injOn`: orthogonality is
  preserved.
- `QuantumMechanics.Wigner.AffineOnDensities.norm_inner_eq_of_injOn`: overlaps are preserved.
- `QuantumMechanics.Wigner.AffineOnDensities.implemented_of_injOn`: Kadison's theorem for maps
  injective on pure states.
- `QuantumMechanics.Wigner.AffineOnDensities.bijOnPure_of_injOn`: such a map is a bijection of
  the pure states.

## iii. Table of contents

- A. Operator identities from purity
- B. Orthogonality is preserved
- C. Kadison's theorem for injective maps
-/

public section

open scoped InnerProductSpace ComplexConjugate
open InnerProductSpace Complex

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. Operator identities from purity
-/

/-- **Coefficient comparison.** If `P` and `Q` are idempotent and
`A z = P + |z|² Q + z N + z̄ N'` satisfies `A z ^ 2 = (1 + |z|²) A z` for every `z`, then
`P N + N P = N`, `Q N + N Q = N` and `N² = 0`. The odd part in `z` at `z = 1, 2, i, 2i` gives the
first two, the even part at `z = 1, i, 1 + i` the third. -/
lemma mul_add_mul_eq_of_sq_eq {P Q N N' : E →L[ℂ] E} (hP : P * P = P) (hQ : Q * Q = Q)
    (h : ∀ z : ℂ, (P + (z * conj z) • Q + z • N + conj z • N') *
      (P + (z * conj z) • Q + z • N + conj z • N') =
      (1 + z * conj z) • (P + (z * conj z) • Q + z • N + conj z • N')) :
    P * N + N * P = N ∧ Q * N + N * Q = N ∧ N * N = 0 := by
  have hodd : ∀ z : ℂ, z • (P * N + N * P - N) + conj z • (P * N' + N' * P - N') +
      (z * conj z * z) • (Q * N + N * Q - N) +
      (z * conj z * conj z) • (Q * N' + N' * Q - N') = 0 := by
    intro z
    have h1 := h z
    have h2 := h (-z)
    simp only [map_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hP, hQ] at h1 h2
    linear_combination (norm := module) (1 / 2 : ℂ) • h1 - (1 / 2 : ℂ) • h2
  have heven : ∀ z : ℂ, (z * conj z) • (P * Q + Q * P + N * N' + N' * N - P - Q) +
      (z * z) • (N * N) + (conj z * conj z) • (N' * N') = 0 := by
    intro z
    have h1 := h z
    have h2 := h (-z)
    simp only [map_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hP, hQ] at h1 h2
    linear_combination (norm := module) (1 / 2 : ℂ) • h1 + (1 / 2 : ℂ) • h2
  have o1 := hodd 1
  have o2 := hodd 2
  have oi := hodd I
  have o2i := hodd (2 * I)
  have e1 := heven 1
  have ei := heven I
  have e3 := heven (1 + I)
  simp only [map_one, map_ofNat, map_mul, map_add, conj_I, mul_one] at o1 o2 oi o2i e1 ei e3
  have hA1 : (12 * I) • (P * N + N * P - N) = 0 := by
    linear_combination (norm := module) (8 * I) • o1 - I • o2 + (8 : ℂ) • oi - o2i
  have hA3 : (-12 * (I * I * I)) • (Q * N + N * Q - N) = 0 := by
    linear_combination (norm := module) (-(I * I * I)) • o2 + (2 * (I * I * I)) • o1 + o2i -
      (2 : ℂ) • oi
  have hN : (4 * (I * I * I)) • (N * N) = 0 := by
    linear_combination (norm := module) (I * I * (I - 1)) • e1 + (I - I * I) • ei + (I * I) • e3
  exact ⟨sub_eq_zero.mp ((smul_eq_zero.mp hA1).resolve_left (by simp [I_ne_zero])),
    sub_eq_zero.mp ((smul_eq_zero.mp hA3).resolve_left (by simp [I_ne_zero])),
    (smul_eq_zero.mp hN).resolve_left (by simp [I_ne_zero])⟩

/-- If `|a⟩⟨a| N + N |a⟩⟨a| = N` and `N² = 0`, then `⟪a, N a⟫ = 0` and `N` is `|N a⟩⟨a|` or
`|a⟩⟨N† a|`. -/
lemma inner_apply_self_eq_zero_and {a : E} (ha : ‖a‖ = 1) {N : E →L[ℂ] E}
    (hNa : proj a * N + N * proj a = N) (hN : N * N = 0) :
    ⟪a, N a⟫_ℂ = 0 ∧ ((∀ x, N x = ⟪a, x⟫_ℂ • N a) ∨ ∀ x, N x = ⟪a, N x⟫_ℂ • a) := by
  have hx : ∀ x, ⟪a, N x⟫_ℂ • a + ⟪a, x⟫_ℂ • N a = N x := fun x => by
    simpa [proj_apply] using congrArg (· x) hNa
  have haa : ⟪a, a⟫_ℂ = 1 := by simp [inner_self_eq_norm_sq_to_K, ha]
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have h0 : ⟪a, N a⟫_ℂ = 0 := by
    have := hx a
    rw [haa, one_smul, add_eq_right, smul_eq_zero] at this
    exact this.resolve_right ha0
  refine ⟨h0, ?_⟩
  have h2 : ∀ x, ⟪a, N x⟫_ℂ • N a = 0 := fun x => by
    have := hx (N x)
    have hNN : N (N x) = 0 := by simpa using congrArg (· x) hN
    rwa [hNN, inner_zero_right, zero_smul, zero_add] at this
  by_cases hn : N a = 0
  · exact Or.inr fun x => by simpa [hn] using (hx x).symm
  · exact Or.inl fun x => by
      simpa [(smul_eq_zero.mp (h2 x)).resolve_right hn] using (hx x).symm

/-- **The two-pole lemma.** Let `a`, `b` be unit vectors that are neither orthogonal nor
parallel. An operator `N` with `N² = 0` that satisfies `P N + N P = N` for both `P = |a⟩⟨a|` and
`P = |b⟩⟨b|` is zero. -/
lemma eq_zero_of_mul_add_mul_eq {a b : E} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {N : E →L[ℂ] E}
    (hNa : proj a * N + N * proj a = N) (hNb : proj b * N + N * proj b = N) (hN : N * N = 0)
    (h0 : ⟪a, b⟫_ℂ ≠ 0) (h1 : ‖⟪a, b⟫_ℂ‖ ≠ 1) : N = 0 := by
  obtain ⟨ha0, hA⟩ := inner_apply_self_eq_zero_and ha hNa hN
  obtain ⟨hb0, hB⟩ := inner_apply_self_eq_zero_and hb hNb hN
  have hba : ⟪b, a⟫_ℂ = conj ⟪a, b⟫_ℂ := (inner_conj_symm b a).symm
  have hc : (1 : ℂ) - conj ⟪a, b⟫_ℂ * ⟪a, b⟫_ℂ ≠ 0 := by
    rw [mul_comm, mul_conj', sub_ne_zero, ne_comm]
    intro h
    have h' : ‖⟪a, b⟫_ℂ‖ ^ 2 = 1 := by exact_mod_cast h
    exact h1 ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h')
  have h0' : conj ⟪a, b⟫_ℂ ≠ 0 := (map_ne_zero _).mpr h0
  ext x
  rw [zero_apply]
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · have e2 : N a = (conj ⟪a, b⟫_ℂ * ⟪a, b⟫_ℂ) • N a := by
      rw [mul_smul, ← hA b, ← hba, ← hB a]
    have e : (1 - conj ⟪a, b⟫_ℂ * ⟪a, b⟫_ℂ) • N a = 0 := by
      rw [sub_smul, one_smul, ← e2, sub_self]
    rw [hA x, (smul_eq_zero.mp e).resolve_left hc, smul_zero]
  · have e : ⟪a, b⟫_ℂ • N a = 0 := by rw [← hA b, hB b, hb0, zero_smul]
    rw [hA x, (smul_eq_zero.mp e).resolve_left h0, smul_zero]
  · have e : conj ⟪a, b⟫_ℂ • N b = 0 := by rw [← hba, ← hB a, hA a, ha0, zero_smul]
    rw [hB x, (smul_eq_zero.mp e).resolve_left h0', smul_zero]
  · have e1 := congrArg (⟪a, ·⟫_ℂ) (hB x)
    have e2 := congrArg (⟪b, ·⟫_ℂ) (hA x)
    simp only [inner_smul_right] at e1 e2
    rw [hba] at e2
    have e : (1 - conj ⟪a, b⟫_ℂ * ⟪a, b⟫_ℂ) * ⟪a, N x⟫_ℂ = 0 := by
      linear_combination e1 + ⟪a, b⟫_ℂ * e2
    rw [hA x, (mul_eq_zero.mp e).resolve_left hc, zero_smul]

/-!
## B. Orthogonality is preserved
-/

/-- `|x + z y⟩⟨x + z y|` expanded. -/
lemma proj_add_smul (x y : E) (z : ℂ) :
    proj (x + z • y) = proj x + (z * conj z) • proj y + z • rankOne ℂ y x +
      conj z • rankOne ℂ x y := by
  ext w
  simp only [rankOne_apply, add_apply, smul_apply,
    inner_add_left, inner_smul_left, add_smul, smul_add, smul_smul]
  module

/-- Unit vectors with `|⟪x, y⟫| = 1` give the same pure state. -/
lemma proj_eq_of_norm_inner_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : ‖⟪x, y⟫_ℂ‖ = 1) : proj x = proj y := by
  obtain ⟨c, hc, rfl⟩ := exists_norm_eq_one_smul_of_norm_inner_eq_one hx hy h
  rw [proj_smul, hc]
  simp

variable [FiniteDimensional ℂ E] {T : (E →L[ℂ] E) → E →L[ℂ] E}

/-- The linear extension `L` of `T` maps `|v⟩⟨v|` to `‖v‖²` times a pure state. -/
lemma linearMap_proj_mul_self (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    {L : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E} (hL : ∀ ρ, IsDensity ρ → L ρ = T ρ) (v : E) :
    L (proj v) * L (proj v) = ((‖v‖ ^ 2 : ℝ) : ℂ) • L (proj v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hv
  set u := (‖v‖ : ℂ)⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, norm_ne_zero_iff.mpr hv]
  have hvu : v = (‖v‖ : ℂ) • u := by simp [u, smul_smul, hn]
  obtain ⟨u', hu', hTu⟩ := hpure u hu
  have hp : L (proj v) = ((‖v‖ ^ 2 : ℝ) : ℂ) • proj u' := by
    conv_lhs => rw [hvu]
    rw [proj_smul, map_smul, hL _ (isDensity_proj hu), hTu]
    simp
  rw [hp, smul_mul_smul_comm, (isIdempotentElem_rankOne_self hu').eq, smul_smul]

/-- Purity along the line `ψ + z φ`: with `A z = L |ψ + z φ⟩⟨ψ + z φ|`,
`A z ^ 2 = (1 + |z|²) A z`. -/
lemma linearMap_proj_add_smul_mul_self
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    {L : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E} (hL : ∀ ρ, IsDensity ρ → L ρ = T ρ) {ψ φ : E}
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hψφ : ⟪ψ, φ⟫_ℂ = 0) (z : ℂ) :
    (T (proj ψ) + (z * conj z) • T (proj φ) + z • L (rankOne ℂ φ ψ) +
        conj z • L (rankOne ℂ ψ φ)) *
      (T (proj ψ) + (z * conj z) • T (proj φ) + z • L (rankOne ℂ φ ψ) +
        conj z • L (rankOne ℂ ψ φ)) =
      (1 + z * conj z) • (T (proj ψ) + (z * conj z) • T (proj φ) + z • L (rankOne ℂ φ ψ) +
        conj z • L (rankOne ℂ ψ φ)) := by
  have h := linearMap_proj_mul_self hpure hL (ψ + z • φ)
  have hn : ((‖ψ + z • φ‖ ^ 2 : ℝ) : ℂ) = 1 + z * conj z := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ψ (z • φ)
      (by rw [inner_smul_right, hψφ, mul_zero])
    rw [sq, this, norm_smul, hψ, hφ, mul_conj']
    push_cast
    ring
  rwa [proj_add_smul, map_add, map_add, map_add, map_smul, map_smul, map_smul,
    hL _ (isDensity_proj hψ), hL _ (isDensity_proj hφ), hn] at h

/-- **Orthogonality is preserved.** If `T` is affine on density operators, maps pure states to
pure states and is injective on them, then it maps orthogonal pure states to orthogonal ones.
Purity of the images of `|ψ + z φ⟩⟨ψ + z φ|` gives the identities of
`mul_add_mul_eq_of_sq_eq` for `N = L |φ⟩⟨ψ|` and, exchanging `ψ` and `φ`, for `L |ψ⟩⟨φ|`. If
`⟪a, b⟫ ≠ 0`, injectivity gives `|⟪a, b⟫| ≠ 1`, both operators vanish by
`eq_zero_of_mul_add_mul_eq`, and then the image `|a⟩⟨a| + |b⟩⟨b|` of `|ψ + φ⟩⟨ψ + φ|` is not
twice a pure state. -/
theorem AffineOnDensities.inner_eq_zero_of_injOn (hT : AffineOnDensities T)
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (hinj : Set.InjOn T {ρ | IsPure ρ}) {ψ φ a b : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hψφ : ⟪ψ, φ⟫_ℂ = 0) (hTψ : T (proj ψ) = proj a)
    (hTφ : T (proj φ) = proj b) : ⟪a, b⟫_ℂ = 0 := by
  have := FiniteDimensional.complete ℂ E
  obtain ⟨L, hL⟩ := hT.exists_linearMap
  by_contra h0
  have h1 : ‖⟪a, b⟫_ℂ‖ ≠ 1 := by
    intro h
    have hne : proj ψ ≠ proj φ := by
      intro e
      have := congrArg (fun A : E →L[ℂ] E => ⟪ψ, A ψ⟫_ℂ) e
      simp [inner_self_eq_norm_sq_to_K, hψ, (inner_eq_zero_symm (𝕜 := ℂ)).mp hψφ] at this
    exact hne (hinj ⟨ψ, hψ, rfl⟩ ⟨φ, hφ, rfl⟩
      (by rw [hTψ, hTφ, proj_eq_of_norm_inner_eq_one ha hb h]))
  have hφψ : ⟪φ, ψ⟫_ℂ = 0 := (inner_eq_zero_symm (𝕜 := ℂ)).mp hψφ
  have hF := linearMap_proj_add_smul_mul_self hpure hL hψ hφ hψφ
  have hF' := linearMap_proj_add_smul_mul_self hpure hL hφ hψ hφψ
  rw [hTψ, hTφ] at hF hF'
  have hPa : proj a * proj a = proj a := isIdempotentElem_rankOne_self ha
  have hPb : proj b * proj b = proj b := isIdempotentElem_rankOne_self hb
  obtain ⟨hN1, hN2, hN3⟩ := mul_add_mul_eq_of_sq_eq hPa hPb hF
  obtain ⟨hN1', hN2', hN3'⟩ := mul_add_mul_eq_of_sq_eq hPb hPa hF'
  have hN := eq_zero_of_mul_add_mul_eq ha hb hN1 hN2 hN3 h0 h1
  have hN' := eq_zero_of_mul_add_mul_eq hb ha hN1' hN2' hN3'
    (by rwa [← inner_conj_symm, map_ne_zero]) (by rwa [norm_inner_symm])
  have e := hF 1
  simp only [map_one, mul_one, one_smul, hN, hN', smul_zero, add_zero, add_mul, mul_add,
    hPa, hPb] at e
  have e' := congrArg (fun A : E →L[ℂ] E => ⟪a, A a⟫_ℂ) e
  simp only [add_apply, smul_apply, mul_apply_eq_comp, map_smul,
    rankOne_apply, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, ha,
    RCLike.ofReal_one, one_pow, mul_one, one_mul] at e'
  have hX : ⟪b, a⟫_ℂ * ⟪a, b⟫_ℂ = 1 := by linear_combination e'
  rw [← inner_conj_symm b a, conj_mul'] at hX
  exact h1 ((pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by exact_mod_cast hX))

/-!
## C. Kadison's theorem for injective maps
-/

/-- **Overlaps are preserved.** If `T` maps density operators to density operators, is affine on
them, maps pure states to pure states and is injective on them, then `|⟪ψ', ϕ'⟫| = |⟪ψ, ϕ⟫|`
whenever `T |ψ⟩⟨ψ| = |ψ'⟩⟨ψ'|` and `T |ϕ⟩⟨ϕ| = |ϕ'⟩⟨ϕ'|`. The images of an orthonormal basis
`(eⱼ)` through `ϕ` are orthonormal, so Bessel's inequality bounds `∑ⱼ ⟪ψ', T |eⱼ⟩⟨eⱼ| ψ'⟫` by
`1 = ∑ⱼ |⟪ψ, eⱼ⟫|²`, and the termwise inequalities of `AffineOnDensities.norm_inner_le` are
equalities. -/
theorem AffineOnDensities.norm_inner_eq_of_injOn (hT : AffineOnDensities T)
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (hinj : Set.InjOn T {ρ | IsPure ρ}) {ψ φ ψ' φ' : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hψ' : ‖ψ'‖ = 1) (hTψ : T (proj ψ) = proj ψ') (hTφ : T (proj φ) = proj φ') :
    ‖⟪ψ', φ'⟫_ℂ‖ = ‖⟪ψ, φ⟫_ℂ‖ := by
  obtain ⟨w, e, hw, he⟩ := (orthonormal_singleton hφ).exists_orthonormalBasis_extension
  choose f hf hTf using fun j => hpure (e j) (e.norm_eq_one j)
  have hfo : Orthonormal ℂ f := ⟨hf, fun i j hij => hT.inner_eq_zero_of_injOn hpure hinj
    (e.norm_eq_one i) (e.norm_eq_one j) (hf i) (hf j) (e.orthonormal.2 hij) (hTf i) (hTf j)⟩
  have hle : ∑ j, (⟪ψ', T (proj (e j)) ψ'⟫_ℂ).re ≤ ∑ j, ‖⟪ψ, e j⟫_ℂ‖ ^ 2 := by
    simp only [hTf, inner_proj_apply, Complex.ofReal_re]
    rw [e.sum_sq_norm_inner_left, hψ]
    simpa [hψ'] using hfo.sum_inner_products_le (s := Finset.univ) ψ'
  have h : ∑ j, ‖⟪ψ, e j⟫_ℂ‖ ^ 2 = ∑ j, (⟪ψ', T (proj (e j)) ψ'⟫_ℂ).re :=
    le_antisymm (Finset.sum_le_sum fun j _ =>
      hT.sq_norm_inner_le_re_inner hD hpure hψ hψ' (e.norm_eq_one j) hTψ) hle
  have := (Finset.sum_eq_sum_iff_of_le fun j _ =>
    hT.sq_norm_inner_le_re_inner hD hpure hψ hψ' (e.norm_eq_one j) hTψ).mp h
    ⟨φ, hw rfl⟩ (Finset.mem_univ _)
  simp only [he, hTφ, inner_proj_apply, Complex.ofReal_re, norm_inner_symm φ' ψ'] at this
  exact ((pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this).symm

/-- **Kadison's theorem for injective maps.** A map that sends density operators to density
operators, is affine on them, maps pure states to pure states and is injective on them is
conjugation by a unitary or an anti-unitary on every density operator. -/
theorem AffineOnDensities.implemented_of_injOn (hT : AffineOnDensities T)
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (hinj : Set.InjOn T {ρ | IsPure ρ}) : ImplementedByUnitaryOrAntiunitary T := by
  have htr : ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 →
      LinearMap.trace ℂ E ((T (proj ψ) * T (proj φ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((proj ψ * proj φ : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    intro ψ φ hψ hφ
    obtain ⟨ψ', hψ', hTψ⟩ := hpure ψ hψ
    obtain ⟨φ', -, hTφ⟩ := hpure φ hφ
    rw [hTψ, hTφ, trace_rankOne_mul_rankOne, trace_rankOne_mul_rankOne,
      hT.norm_inner_eq_of_injOn hD hpure hinj hψ hφ hψ' hTψ hTφ]
  rcases wigner_rankOne T hpure htr with ⟨W, hW⟩ | ⟨W, hW⟩
  · exact Or.inl ⟨W, fun ρ hρ => hT.eq_conjOp hW hρ⟩
  · exact Or.inr ⟨W, fun ρ hρ => hT.eq_conjOp hW hρ⟩

/-- **Injectivity suffices.** In finite dimension, a map that sends density operators to density
operators, is affine on them, maps pure states to pure states and is injective on them is a
bijection of the pure states. -/
theorem AffineOnDensities.bijOnPure_of_injOn (hT : AffineOnDensities T)
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (hinj : Set.InjOn T {ρ | IsPure ρ}) : BijOnPure T := by
  rcases hT.implemented_of_injOn hD hpure hinj with ⟨W, hW⟩ | ⟨W, hW⟩
  exacts [hT.bijOnPure (bijOn_of_eq_conjOp W hW), hT.bijOnPure (bijOn_of_eq_conjOp W hW)]

end QuantumMechanics.Wigner
