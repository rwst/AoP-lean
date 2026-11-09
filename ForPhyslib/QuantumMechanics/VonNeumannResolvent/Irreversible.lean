/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.VonNeumannResolvent.Cayley
public import ForPhyslib.QuantumMechanics.Wigner.Kadison

/-!
# The resolvent of the von Neumann equation is not unitary

Let `L ρ = -i (K ρ - ρ K)` be the von Neumann generator of a self-adjoint `K` on a
finite-dimensional complex Hilbert space, and `Ψ τ = (1 - τ L)⁻¹` its resolvent. Unless `K` is a
multiple of the identity, and `τ ≠ 0`, the finite process `Ψ τ` is not unitary.

*Purity decreases.* Writing `ρ = (1 - τ L) σ` with `σ = Ψ τ ρ`, the skewness of `L` for the
Hilbert–Schmidt inner product gives `tr (ρ† ρ) = tr (σ† σ) + τ² tr ((L σ)† (L σ))`. So the purity
`tr ρ²` of a self-adjoint `ρ` strictly decreases unless `L ρ = 0`. A pure state has purity one, so
`Ψ τ` maps a pure state `|ψ⟩⟨ψ|` to a mixed one unless `ψ` is an eigenvector of `K`.

*The inverse is not positive.* `Ψ τ` is a linear bijection with inverse `1 - τ L`, so it is undone
by a positive map only if `1 - τ L` is positive. It is not: if `ψ` is a unit vector, `X` is
`(1 - τ L) |ψ⟩⟨ψ|` and `v` any vector, then
`re ⟨v, X v⟩ = |⟨ψ, v⟩|² - 2 τ im (⟨ψ, v⟩ ⟨v, K ψ⟩)`. For `u = K ψ - ⟨ψ, K ψ⟩ ψ ≠ 0` and
`v = ψ - i (τ ‖u‖²)⁻¹ u` this is `-1`.

*Generic `K`.* If every vector is an eigenvector of `K`, then `K` is a multiple of the identity;
and if it is, `L = 0` and `Ψ τ` is the identity.

## Main results

* `QuantumMechanics.re_trace_star_mul_self_vonNeumannResolvent_lt`: purity strictly decreases.
* `QuantumMechanics.not_isPure_vonNeumannResolvent`: `Ψ τ` maps a pure state with `L ρ ≠ 0` to a
  state that is not pure.
* `QuantumMechanics.not_nonneg_vonNeumannStep_proj`: `1 - τ L` is not positive.
* `QuantumMechanics.exists_isPure_not_isPure_vonNeumannResolvent`: for `K` not a multiple of the
  identity, some pure state is mapped to a mixed one, and `1 - τ L` maps it to a non-positive
  operator.
* `QuantumMechanics.forall_isPure_vonNeumannResolvent_iff`: `Ψ τ` maps pure states to pure states
  iff `K` is a multiple of the identity.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace QuantumMechanics.Wigner Complex

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] {K : E →L[ℂ] E}

/-! ## A. The Hilbert–Schmidt norm -/

omit [FiniteDimensional ℂ E] in
/-- `tr (A† A) = ∑ ‖A bᵢ‖²` in an orthonormal basis `b`. -/
lemma re_trace_star_mul_self {ι : Type*} [Fintype ι] (A : E →L[ℂ] E)
    (b : OrthonormalBasis ι ℂ E) : re (LinearMap.trace ℂ E ↑(star A * A)) = ∑ i, ‖A (b i)‖ ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ b, re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

lemma re_trace_star_mul_self_pos {A : E →L[ℂ] E} (hA : A ≠ 0) :
    0 < re (LinearMap.trace ℂ E ↑(star A * A)) := by
  rw [re_trace_star_mul_self A (stdOrthonormalBasis ℂ E)]
  obtain ⟨i, hi⟩ : ∃ i, A (stdOrthonormalBasis ℂ E i) ≠ 0 := by
    by_contra! h
    exact hA (ContinuousLinearMap.coe_injective
      ((stdOrthonormalBasis ℂ E).toBasis.ext fun i => by simpa using h i))
  exact Finset.sum_pos' (fun j _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩

/-- A pure state has purity one. -/
lemma re_trace_star_proj_mul_proj {ψ : E} (hψ : ‖ψ‖ = 1) :
    re (LinearMap.trace ℂ E ↑(star (proj ψ) * proj ψ)) = 1 := by
  rw [(isStarProjection_rankOne_self hψ).isSelfAdjoint.star_eq,
    (isStarProjection_rankOne_self hψ).isIdempotentElem.eq, trace_rankOne,
    inner_self_eq_norm_sq_to_K, hψ]
  simp

/-! ## B. Purity decreases -/

variable (V : UnitaryOneParameterGroup E)

/-- `tr (ρ† ρ) = tr ((Ψ τ ρ)† (Ψ τ ρ)) + τ² tr ((L Ψ τ ρ)† (L Ψ τ ρ))`. -/
theorem re_trace_star_mul_self_eq_vonNeumannResolvent (τ : ℝ) (ρ : E →L[ℂ] E) :
    re (LinearMap.trace ℂ E ↑(star ρ * ρ)) =
      re (LinearMap.trace ℂ E
          ↑(star (vonNeumannResolvent V τ ρ) * vonNeumannResolvent V τ ρ)) +
        τ ^ 2 * re (LinearMap.trace ℂ E
          ↑(star (vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ)) *
            vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ))) := by
  have h : vonNeumannStep V.generator τ (vonNeumannResolvent V τ ρ) = ρ :=
    vonNeumannResolvent_sub V τ ρ
  conv_lhs => rw [← h, trace_star_vonNeumannStep_mul V.generator_isSelfAdjoint]
  rw [add_re, ← ofReal_pow, re_ofReal_mul]

/-- **Purity strictly decreases** under `Ψ τ` unless `τ = 0` or `L ρ = 0`. -/
theorem re_trace_star_mul_self_vonNeumannResolvent_lt {τ : ℝ} (hτ : τ ≠ 0) {ρ : E →L[ℂ] E}
    (hρ : vonNeumannGenerator V.generator ρ ≠ 0) :
    re (LinearMap.trace ℂ E ↑(star (vonNeumannResolvent V τ ρ) * vonNeumannResolvent V τ ρ)) <
      re (LinearMap.trace ℂ E ↑(star ρ * ρ)) := by
  rw [re_trace_star_mul_self_eq_vonNeumannResolvent V τ ρ, lt_add_iff_pos_right]
  refine mul_pos (by positivity) (re_trace_star_mul_self_pos fun h => hρ ?_)
  have hΨ := vonNeumannResolvent_sub V τ ρ
  rw [h, smul_zero, sub_zero] at hΨ
  rwa [← hΨ]

/-- **`Ψ τ` maps pure states to mixed ones**: if `ρ` is pure, `τ ≠ 0` and `L ρ ≠ 0`, then
`Ψ τ ρ` is not pure. -/
theorem not_isPure_vonNeumannResolvent {τ : ℝ} (hτ : τ ≠ 0) {ρ : E →L[ℂ] E} (hρ : IsPure ρ)
    (hL : vonNeumannGenerator V.generator ρ ≠ 0) : ¬ IsPure (vonNeumannResolvent V τ ρ) := by
  obtain ⟨ψ, hψ, rfl⟩ := hρ
  rintro ⟨φ, hφ, he⟩
  have h := re_trace_star_mul_self_vonNeumannResolvent_lt V hτ hL
  rw [he, re_trace_star_proj_mul_proj hφ, re_trace_star_proj_mul_proj hψ] at h
  exact lt_irrefl _ h

/-! ## C. The inverse is not positive -/

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
/-- `L |ψ⟩⟨ψ| ≠ 0` unless `ψ` is an eigenvector of `K`. -/
lemma vonNeumannGenerator_proj_ne_zero {ψ : E} (hψ : ‖ψ‖ = 1) (h : ∀ c : ℂ, K ψ ≠ c • ψ) :
    vonNeumannGenerator K (proj ψ) ≠ 0 := by
  intro h0
  apply h ⟪ψ, K ψ⟫_ℂ
  have h1 := congr($h0 ψ)
  simpa [vonNeumannGenerator_apply, proj_apply, inner_self_eq_norm_sq_to_K, hψ, sub_eq_zero]
    using h1

omit [FiniteDimensional ℂ E] in
/-- The quadratic form of `(1 - τ L) |ψ⟩⟨ψ|`:
`re ⟨v, X v⟩ = |⟨ψ, v⟩|² - 2 τ im (⟨ψ, v⟩ ⟨v, K ψ⟩)`. -/
lemma re_inner_vonNeumannStep_proj_apply (hK : IsSelfAdjoint K) (τ : ℝ) (ψ v : E) :
    re ⟪v, vonNeumannStep K τ (proj ψ) v⟫_ℂ =
      ‖⟪ψ, v⟫_ℂ‖ ^ 2 - 2 * τ * im (⟪ψ, v⟫_ℂ * ⟪v, K ψ⟫_ℂ) := by
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK
  have hKv : ⟪ψ, K v⟫_ℂ = starRingEnd ℂ ⟪v, K ψ⟫_ℂ := by
    rw [inner_conj_symm]
    exact (hsym ψ v).symm
  have hvψ : ⟪v, ψ⟫_ℂ = starRingEnd ℂ ⟪ψ, v⟫_ℂ := (inner_conj_symm v ψ).symm
  simp only [vonNeumannStep_apply, vonNeumannGenerator_apply, sub_apply, smul_apply,
    mul_apply_eq_comp, proj_apply, map_smul,
    inner_sub_right, inner_smul_right, hKv, hvψ, ← coe_smul]
  simp only [sub_re, mul_re, mul_im, sub_im, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im,
    conj_re, conj_im, Complex.sq_norm, normSq_apply]
  ring

omit [FiniteDimensional ℂ E] in
/-- **The inverse `1 - τ L` of `Ψ τ` is not positive**: it maps the pure state `|ψ⟩⟨ψ|` to a
non-positive operator unless `τ = 0` or `ψ` is an eigenvector of `K`. -/
theorem not_nonneg_vonNeumannStep_proj (hK : IsSelfAdjoint K) {τ : ℝ} (hτ : τ ≠ 0) {ψ : E}
    (hψ : ‖ψ‖ = 1) (h : ∀ c : ℂ, K ψ ≠ c • ψ) : ¬ 0 ≤ vonNeumannStep K τ (proj ψ) := by
  intro hpos
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hK
  set k := ⟪ψ, K ψ⟫_ℂ with hk
  have hkim : k.im = 0 := by
    refine conj_eq_iff_im.mp ?_
    rw [hk, inner_conj_symm]
    exact hsym ψ ψ
  set u := K ψ - k • ψ with hu
  have hu0 : u ≠ 0 := sub_ne_zero.mpr (h k)
  have hψu : ⟪ψ, u⟫_ℂ = 0 := by
    rw [hu, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp [hk]
  have huψ : ⟪u, ψ⟫_ℂ = 0 := by rw [← inner_conj_symm, hψu, map_zero]
  have huK : ⟪u, K ψ⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    have : K ψ = u + k • ψ := by rw [hu, sub_add_cancel]
    rw [this, inner_add_right, inner_smul_right, huψ, inner_self_eq_norm_sq_to_K]
    simp
  set t : ℝ := -(τ * ‖u‖ ^ 2)⁻¹
  set v := ψ + ((t : ℂ) * I) • u
  have h1 : ⟪ψ, v⟫_ℂ = 1 := by
    simp [v, inner_add_right, inner_smul_right, hψu, inner_self_eq_norm_sq_to_K, hψ]
  have h2 : im ⟪v, K ψ⟫_ℂ = τ⁻¹ := by
    have hu2 : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hu0)
    simp only [v, inner_add_left, inner_smul_left, huK, add_im, ← hk, hkim, map_mul, conj_ofReal,
      conj_I, mul_im, mul_re, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im, t]
    field_simp
    ring
  have key := re_inner_vonNeumannStep_proj_apply hK τ ψ v
  rw [h1, one_mul, h2, norm_one, mul_assoc, mul_inv_cancel₀ hτ] at key
  have := (ContinuousLinearMap.nonneg_iff_isPositive.mp hpos).re_inner_nonneg_right v
  rw [RCLike.re_to_complex] at this
  norm_num at key
  linarith

/-! ## D. Generic generators -/

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
/-- If `K` is not a multiple of the identity, some unit vector is not an eigenvector of `K`. -/
lemma exists_forall_apply_ne_smul (hK : ∀ c : ℂ, K ≠ c • 1) :
    ∃ ψ : E, ‖ψ‖ = 1 ∧ ∀ c : ℂ, K ψ ≠ c • ψ := by
  by_contra! h
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
    (f := (K : E →ₗ[ℂ] E)) fun v hv => by
    rcases eq_or_ne v 0 with rfl | hv0
    · exact hv.ne_zero 0 rfl
    obtain ⟨c, hc⟩ := h _ (norm_smul_inv_norm (𝕜 := ℂ) hv0)
    rw [map_smul, smul_comm] at hc
    have hc' : K v = c • v :=
      smul_right_injective E (inv_ne_zero (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv0))) hc
    exact (LinearIndependent.pair_iff' hv0).mp hv c (by rw [ContinuousLinearMap.coe_coe, hc'])
  refine hK a (ContinuousLinearMap.coe_injective ?_)
  rw [ha]
  rfl

/-- If `K` is a multiple of the identity, `Ψ τ` is the identity. -/
theorem vonNeumannResolvent_eq_self_of_eq_smul {c : ℂ} (hc : V.generator = c • 1) (τ : ℝ)
    (ρ : E →L[ℂ] E) : vonNeumannResolvent V τ ρ = ρ := by
  have hL : vonNeumannGenerator V.generator ρ = 0 := by
    rw [vonNeumannGenerator_apply, hc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, sub_self,
      smul_zero]
  have h := vonNeumannResolvent_vonNeumannStep V τ ρ
  rwa [vonNeumannStep_apply, hL, smul_zero, sub_zero] at h

/-- **The finite process is not unitary.** If `τ ≠ 0` and `K` is not a multiple of the identity,
some pure state `ρ` is mapped by `Ψ τ` to a mixed state, and by the inverse `1 - τ L` to a
non-positive operator. -/
theorem exists_isPure_not_isPure_vonNeumannResolvent {τ : ℝ} (hτ : τ ≠ 0)
    (hK : ∀ c : ℂ, V.generator ≠ c • 1) :
    ∃ ρ, IsPure ρ ∧ IsDensity (vonNeumannResolvent V τ ρ) ∧
      ¬ IsPure (vonNeumannResolvent V τ ρ) ∧ ¬ 0 ≤ vonNeumannStep V.generator τ ρ := by
  obtain ⟨ψ, hψ, h⟩ := exists_forall_apply_ne_smul hK
  exact ⟨proj ψ, ⟨ψ, hψ, rfl⟩, isDensity_vonNeumannResolvent V τ (isDensity_proj hψ),
    not_isPure_vonNeumannResolvent V hτ ⟨ψ, hψ, rfl⟩ (vonNeumannGenerator_proj_ne_zero hψ h),
    not_nonneg_vonNeumannStep_proj V.generator_isSelfAdjoint hτ hψ h⟩

/-- For `τ ≠ 0`, `Ψ τ` maps pure states to pure states iff `K` is a multiple of the identity. -/
theorem forall_isPure_vonNeumannResolvent_iff {τ : ℝ} (hτ : τ ≠ 0) :
    (∀ ρ, IsPure ρ → IsPure (vonNeumannResolvent V τ ρ)) ↔ ∃ c : ℂ, V.generator = c • 1 := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ ρ hρ => by
    rwa [vonNeumannResolvent_eq_self_of_eq_smul V hc]⟩
  by_contra! hK
  obtain ⟨ρ, hρ, -, hn, -⟩ := exists_isPure_not_isPure_vonNeumannResolvent V hτ hK
  exact hn (h ρ hρ)

end QuantumMechanics
