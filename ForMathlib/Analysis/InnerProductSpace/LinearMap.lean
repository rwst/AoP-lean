/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Conjugate-linear isometries, polarization of rank-one operators, inner derivations

A conjugate-linear isometry conjugates the inner product: `⟪f x, f y⟫ = conj ⟪x, y⟫`. This is the
conjugate-linear counterpart of `LinearIsometry.inner_map_map`, and is proved the same way, by
polarization.

Over `ℂ`, a norm-preserving ring endomorphism is the identity or conjugation, so an isometry that
is semilinear over it applies it to the inner product. This covers unitaries and anti-unitaries at
once.

Over `ℂ`, the rank-one operator `|x⟩⟨y|` is a combination of the four operators `|v⟩⟨v|` with
`v = x + iᵐ y`, which is the operator form of the polarization identity.

Every continuous derivation `L` of the bounded operators on an inner product space is inner,
`L X = K X - X K`. For a unit vector `e`, put `K x = L |x⟩⟨e| e`. Applying `L` to
`X |x⟩⟨e| = |X x⟩⟨e|` and evaluating at `e` gives `K (X x) = L X x + X (K x)`.

## Main results

* `LinearIsometry.inner_map_map_conj`
* `LinearIsometryEquiv.inner_map_map_conj`
* `Complex.ringHom_eq_id_or_conj_of_isometric`
* `LinearIsometry.inner_map_map_semilinear`
* `InnerProductSpace.rankOne_polarization`
* `InnerProductSpace.exists_eq_mul_sub_mul_of_map_mul`
-/

@[expose] public section

open RCLike ComplexConjugate

variable {𝕜 E E' : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- A conjugate-linear isometry conjugates the inner product. -/
theorem LinearIsometry.inner_map_map_conj (f : E →ₗᵢ⋆[𝕜] E') (x y : E) :
    ⟪f x, f y⟫ = conj ⟪x, y⟫ := by
  have h₁ : ‖f x + f y‖ = ‖x + y‖ := by rw [← map_add, f.norm_map]
  have h₂ : ‖f x - f y‖ = ‖x - y‖ := by rw [← map_sub, f.norm_map]
  have h₃ : ‖f x - (I : 𝕜) • f y‖ = ‖x + (I : 𝕜) • y‖ := by
    rw [← f.norm_map (x + (I : 𝕜) • y), map_add, map_smulₛₗ, conj_I, neg_smul, ← sub_eq_add_neg]
  have h₄ : ‖f x + (I : 𝕜) • f y‖ = ‖x - (I : 𝕜) • y‖ := by
    rw [← f.norm_map (x - (I : 𝕜) • y), map_sub, map_smulₛₗ, conj_I, neg_smul, sub_neg_eq_add]
  rw [inner_eq_sum_norm_sq_div_four (f x), h₁, h₂, h₃, h₄, inner_eq_sum_norm_sq_div_four x y]
  simp only [map_div₀, map_add, map_sub, map_mul, map_pow, conj_ofReal, conj_I, map_ofNat]
  ring

/-- A conjugate-linear isometric equivalence conjugates the inner product. -/
theorem LinearIsometryEquiv.inner_map_map_conj (f : E ≃ₗᵢ⋆[𝕜] E') (x y : E) :
    ⟪f x, f y⟫ = conj ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map_conj x y

/-- A norm-preserving ring endomorphism of `ℂ` is the identity or complex conjugation. -/
theorem Complex.ringHom_eq_id_or_conj_of_isometric (σ : ℂ →+* ℂ) [RingHomIsometric σ] :
    σ = RingHom.id ℂ ∨ σ = starRingEnd ℂ :=
  Complex.ringHom_eq_id_or_conj_of_continuous σ.isometry.continuous

/-- An isometry over a norm-preserving ring endomorphism `σ` of `ℂ` applies `σ` to the inner
product. -/
theorem LinearIsometry.inner_map_map_semilinear {F F' : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace ℂ F] [SeminormedAddCommGroup F'] [InnerProductSpace ℂ F'] {σ : ℂ →+* ℂ}
    [RingHomIsometric σ] (f : F →ₛₗᵢ[σ] F') (x y : F) :
    inner ℂ (f x) (f y) = σ (inner ℂ x y) := by
  obtain rfl | rfl := Complex.ringHom_eq_id_or_conj_of_isometric σ
  · exact f.inner_map_map x y
  · exact f.inner_map_map_conj x y

namespace InnerProductSpace

variable {F : Type*} [SeminormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Polarization for rank-one operators: `|x⟩⟨y|` is a combination of the operators `|v⟩⟨v|`. -/
theorem rankOne_polarization (x y : F) :
    (4 : ℂ) • rankOne ℂ x y = rankOne ℂ (x + y) (x + y) - rankOne ℂ (x - y) (x - y) +
      Complex.I • rankOne ℂ (x + Complex.I • y) (x + Complex.I • y) -
        Complex.I • rankOne ℂ (x - Complex.I • y) (x - Complex.I • y) := by
  ext z
  simp only [smul_apply, sub_apply, add_apply, rankOne_apply, inner_add_left,
    inner_sub_left, inner_smul_left, Complex.conj_I]
  linear_combination (norm := module)
    (2 * inner ℂ y z * Complex.I_sq) • x - (2 * inner ℂ x z * Complex.I_sq) • y

/-- Every continuous derivation of the bounded operators on an inner product space is inner. -/
theorem exists_eq_mul_sub_mul_of_map_mul {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (L : (G →L[𝕜] G) →L[𝕜] G →L[𝕜] G)
    (hL : ∀ X Y, L (X * Y) = L X * Y + X * L Y) :
    ∃ K : G →L[𝕜] G, ∀ X, L X = K * X - X * K := by
  cases subsingleton_or_nontrivial G with
  | inl _ => exact ⟨0, fun X => by ext x; exact Subsingleton.elim _ _⟩
  | inr _ =>
    obtain ⟨v, hv⟩ := exists_ne (0 : G)
    set e := ((‖v‖⁻¹ : ℝ) : 𝕜) • v
    have he : ‖e‖ = 1 := by simp [e, norm_smul, hv]
    refine ⟨(ContinuousLinearMap.apply 𝕜 G e).comp (L.comp ((rankOne 𝕜).flip e)), fun X => ?_⟩
    ext x
    have h := congr($(hL X (rankOne 𝕜 x e)) e)
    simp only [ContinuousLinearMap.mul_def, comp_rankOne, add_apply,
      ContinuousLinearMap.comp_apply, rankOne_apply, inner_self_eq_norm_sq_to_K, he] at h
    simp [ContinuousLinearMap.mul_def, h]

end InnerProductSpace
