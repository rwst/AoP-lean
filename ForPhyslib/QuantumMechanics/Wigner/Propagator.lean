/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import ForPhyslib.QuantumMechanics.Wigner.Density
public import ForPhyslib.QuantumMechanics.Wigner.Differentiable
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A differentiable propagator on an interval

## i. Overview

Let `Φ t`, for `t` in an open interval `I`, be maps on operators that are induced on pure states
by unitaries, with `t ↦ Φ t P` differentiable on `I` for every rank-one projection `P`. Then a
single family of unitaries `V t`, differentiable at every `t ∈ I`, induces all of them. This is
the global form of `QuantumMechanics.Wigner.exists_unitary_differentiableAt`, which chooses the
phases near one time.

Locally, after conjugating by a unitary that induces `Φ τ`, the family is the identity at `τ`,
and the explicit choice of `QuantumMechanics.Wigner.unitaryOf` is differentiable near `τ`.
Multiplying by a branch of `det(U t)^(-1/n)`, `n = dim E`, makes the determinant one. Two such
sections that induce the same maps differ by a scalar `c t` with `c t ^ n = 1`, and `c` is
continuous, so on a preconnected set it is a constant root of unity. The local sections then glue
along `I` by a connectedness argument: the set of points reached by a section from a fixed time is
open, and it is closed in `I` because a local section near a limit point can be matched to it by a
constant root of unity on the overlap.

## ii. Key results

- `QuantumMechanics.Wigner.eq_inner_smul_of_proj_eq`: two unitaries with the same action on pure
  states differ by the phase `⟪u e, v e⟫`.
- `QuantumMechanics.Wigner.IsDetOneSection.exists_eq_smul`: two determinant-one sections differ
  by a constant root of unity on a preconnected set.
- `QuantumMechanics.Wigner.eventually_isDetOneSection`: a determinant-one section near each time.
- `QuantumMechanics.Wigner.exists_isDetOneSection`: a determinant-one section on an open
  interval.

## iii. Table of contents

- A. Determinants of unitaries
- B. Uniqueness up to a root of unity
- C. Local sections
- D. Gluing along an interval

## iv. References

- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), Sec. 7.
-/

@[expose] public section

open scoped InnerProductSpace Topology
open InnerProductSpace Filter

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

/-!
## A. Determinants of unitaries
-/

lemma norm_det_of_mem_unitary {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) : ‖u.det‖ = 1 := by
  have h := (Unitary.linearIsometryEquiv ⟨u, hu⟩).toLinearIsometry.normDet_eq_one
  rwa [LinearMap.normDet_eq_norm_det] at h

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma det_smul (c : ℂ) (u : E →L[ℂ] E) : (c • u).det = c ^ Module.finrank ℂ E * u.det :=
  LinearMap.det_smul c (u : E →ₗ[ℂ] E)

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma det_mul (u v : E →L[ℂ] E) : (u * v).det = u.det * v.det :=
  LinearMap.det_comp (u : E →ₗ[ℂ] E) (v : E →ₗ[ℂ] E)

omit [CompleteSpace E] in
/-- An `n`-th root of `x⁻¹`, for `n = dim E`: `(x ^ (-1/n)) ^ n = x⁻¹`. -/
lemma cpow_neg_inv_finrank_pow [Nontrivial E] (x : ℂ) :
    (x ^ (-(Module.finrank ℂ E : ℂ)⁻¹)) ^ Module.finrank ℂ E = x⁻¹ := by
  have hn : (Module.finrank ℂ E : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  rw [← Complex.cpow_nat_mul, mul_neg, mul_inv_cancel₀ hn, Complex.cpow_neg_one]

omit [CompleteSpace E] in
lemma norm_eq_one_of_pow_finrank [Nontrivial E] {c : ℂ} {x : ℂ} (hc : c ^ Module.finrank ℂ E = x)
    (hx : ‖x‖ = 1) : ‖c‖ = 1 := by
  have : ‖c‖ ^ Module.finrank ℂ E = 1 := by rw [← norm_pow, hc, hx]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) Module.finrank_pos.ne').mp this

omit [FiniteDimensional ℂ E] in
lemma smul_mem_unitary {c : ℂ} (hc : ‖c‖ = 1) {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) :
    c • u ∈ unitary (E →L[ℂ] E) := by
  refine Unitary.smul_mem_of_mem ?_ hu
  rw [Unitary.mem_iff, Complex.star_def, mul_comm _ (starRingEnd ℂ _), and_self]
  exact conj_mul_self_of_norm_eq_one hc

/-- A unitary times a phase has determinant one. -/
lemma exists_det_smul_eq_one [Nontrivial E] {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (c • u).det = 1 := by
  have hd := norm_det_of_mem_unitary hu
  have hc := cpow_neg_inv_finrank_pow (E := E) u.det
  refine ⟨_, norm_eq_one_of_pow_finrank hc (by rw [norm_inv, hd, inv_one]), ?_⟩
  rw [det_smul, hc, inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hd]; exact one_ne_zero))]

/-!
## B. Uniqueness up to a root of unity
-/

omit [FiniteDimensional ℂ E] in
/-- Two unitaries with the same action on pure states differ by the phase `⟪u e, v e⟫`, for any
unit vector `e`. -/
lemma eq_inner_smul_of_proj_eq {u v : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E))
    (hv : v ∈ unitary (E →L[ℂ] E)) (h : ∀ ψ : E, ‖ψ‖ = 1 → proj (u ψ) = proj (v ψ)) {e : E}
    (he : ‖e‖ = 1) : v = ⟪u e, v e⟫_ℂ • u := by
  set U := Unitary.linearIsometryEquiv ⟨u, hu⟩
  set V := Unitary.linearIsometryEquiv ⟨v, hv⟩
  have hU : ∀ ψ : E, ‖ψ‖ = 1 → conjOp U (rankOne ℂ ψ ψ) = rankOne ℂ (U ψ) (U ψ) :=
    fun ψ _ => conjOp_proj U ψ
  have hV : ∀ ψ : E, ‖ψ‖ = 1 → conjOp U (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ) :=
    fun ψ hψ => (conjOp_proj U ψ).trans (h ψ hψ)
  ext x
  have hx := congrArg (fun T : E →L[ℂ] E => T (v e))
    ((polMap_eq hU x e).symm.trans (polMap_eq hV x e))
  have hve : ⟪v e, v e⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, ContinuousLinearMap.norm_map_of_mem_unitary hv, he]
    simp
  simp only [rankOne_apply] at hx
  change ⟪u e, v e⟫_ℂ • u x = ⟪v e, v e⟫_ℂ • v x at hx
  rw [hve, one_smul] at hx
  rw [smul_apply, hx]

/-- `V` is a section of determinant one of `Φ` at `t`: `V t` is a unitary of determinant one that
induces `Φ t` on pure states, and `V` is differentiable at `t`. -/
def IsDetOneSection (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) (V : ℝ → E →L[ℂ] E) (t : ℝ) : Prop :=
  V t ∈ unitary (E →L[ℂ] E) ∧ (V t).det = 1 ∧
    (∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (V t ψ)) ∧ DifferentiableAt ℝ V t

variable {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {V W : ℝ → E →L[ℂ] E} {t : ℝ}

omit [FiniteDimensional ℂ E] in
lemma IsDetOneSection.congr (h : IsDetOneSection Φ V t) (hVW : V =ᶠ[𝓝 t] W) :
    IsDetOneSection Φ W t := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have he : V t = W t := hVW.eq_of_nhds
  exact ⟨he ▸ h₁, he ▸ h₂, he ▸ h₃, h₄.congr_of_eventuallyEq hVW.symm⟩

lemma IsDetOneSection.smul [Nontrivial E] (h : IsDetOneSection Φ V t) {c : ℂ}
    (hc : c ^ Module.finrank ℂ E = 1) : IsDetOneSection Φ (fun s => c • V s) t := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := h
  have hc1 : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hc Module.finrank_pos.ne'
  refine ⟨smul_mem_unitary hc1 h₁, by rw [det_smul, hc, h₂, one_mul], fun ψ hψ => ?_,
    h₄.const_smul c⟩
  rw [h₃ ψ hψ, smul_apply, proj_smul, hc1]
  simp

/-- **Uniqueness**: two sections of determinant one differ by a constant `n`-th root of unity on
a preconnected set. -/
lemma IsDetOneSection.exists_eq_smul [Nontrivial E] {S : Set ℝ} (hS : IsPreconnected S)
    (hV : ∀ t ∈ S, IsDetOneSection Φ V t) (hW : ∀ t ∈ S, IsDetOneSection Φ W t) :
    ∃ c : ℂ, c ^ Module.finrank ℂ E = 1 ∧ ∀ t ∈ S, W t = c • V t := by
  classical
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  set n := Module.finrank ℂ E
  have hn : 0 < n := Module.finrank_pos
  let c : ℝ → ℂ := fun t => ⟪V t e, W t e⟫_ℂ
  have hc : ∀ t ∈ S, W t = c t • V t := fun t ht =>
    eq_inner_smul_of_proj_eq (hV t ht).1 (hW t ht).1
      (fun ψ hψ => ((hV t ht).2.2.1 ψ hψ).symm.trans ((hW t ht).2.2.1 ψ hψ)) he
  have hpow : ∀ t ∈ S, c t ^ n = 1 := fun t ht => by
    have h := (hW t ht).2.1
    rwa [hc t ht, det_smul, (hV t ht).2.1, mul_one] at h
  have hcont : ContinuousOn c S := fun t ht => by
    have hap : ∀ X : ℝ → E →L[ℂ] E, ContinuousAt X t → ContinuousAt (fun s => X s e) t :=
      fun X hX => (ContinuousLinearMap.apply ℂ E e).continuous.continuousAt.comp hX
    exact ((hap V (hV t ht).2.2.2.continuousAt).inner
      (hap W (hW t ht).2.2.2.continuousAt)).continuousWithinAt
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨1, one_pow _, fun t ht => ht.elim⟩
  refine ⟨c s₀, hpow s₀ hs₀, fun t ht => ?_⟩
  have hmaps : Set.MapsTo c S (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ) := fun t ht => by
    simpa [Polynomial.mem_nthRootsFinset hn] using hpow t ht
  rw [hc t ht, hS.constant_of_mapsTo (Finset.finite_toSet _).isDiscrete hcont hmaps ht hs₀]

/-- Two sections of determinant one that agree at one point of a preconnected set agree on it. -/
lemma IsDetOneSection.eqOn [Nontrivial E] {S : Set ℝ} (hS : IsPreconnected S)
    (hV : ∀ t ∈ S, IsDetOneSection Φ V t) (hW : ∀ t ∈ S, IsDetOneSection Φ W t) {τ : ℝ}
    (hτ : τ ∈ S) (h : V τ = W τ) : ∀ t ∈ S, V t = W t := by
  obtain ⟨c, -, hc⟩ := IsDetOneSection.exists_eq_smul hS hV hW
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  have hne : V τ e ≠ 0 := by
    rw [← norm_ne_zero_iff, ContinuousLinearMap.norm_map_of_mem_unitary (hV τ hτ).1, he]
    exact one_ne_zero
  have h1 : c = 1 := by
    have := congrArg (fun X : E →L[ℂ] E => X e) ((hc τ hτ).symm.trans h.symm)
    simp only [smul_apply] at this
    exact smul_left_injective ℂ hne (this.trans (one_smul ℂ _).symm)
  intro t ht
  rw [hc t ht, h1, one_smul]

/-!
## C. Local sections
-/

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
/-- A map induced on pure states by a unitary sends pure states to pure states. -/
lemma exists_proj_of_implemented {F : (E →L[ℂ] E) → E →L[ℂ] E} {U : E ≃ₗᵢ[ℂ] E}
    (hU : ∀ ψ : E, ‖ψ‖ = 1 → F (proj ψ) = proj (U ψ)) :
    ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ F (rankOne ℂ ψ ψ) = rankOne ℂ ψ' ψ' :=
  fun ψ hψ => ⟨U ψ, by rw [U.norm_map, hψ], hU ψ hψ⟩

omit [CompleteSpace E] in
/-- A map induced on pure states by a unitary preserves transition probabilities. -/
lemma trace_eq_of_implemented {F : (E →L[ℂ] E) → E →L[ℂ] E} {U : E ≃ₗᵢ[ℂ] E}
    (hU : ∀ ψ : E, ‖ψ‖ = 1 → F (proj ψ) = proj (U ψ)) :
    ∀ ψ ϕ : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      LinearMap.trace ℂ E ((F (rankOne ℂ ψ ψ) * F (rankOne ℂ ϕ ϕ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((rankOne ℂ ψ ψ * rankOne ℂ ϕ ϕ : E →L[ℂ] E) : E →ₗ[ℂ] E) :=
  fun ψ ϕ hψ hϕ => by
    rw [hU ψ hψ, hU ϕ hϕ, trace_rankOne_mul_rankOne, trace_rankOne_mul_rankOne,
      LinearIsometryEquiv.inner_map_map]

omit [FiniteDimensional ℂ E] in
lemma linearIsometryEquiv_mem_unitary (U : E ≃ₗᵢ[ℂ] E) :
    (U : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) :=
  (Unitary.linearIsometryEquiv.symm U).2

omit [FiniteDimensional ℂ E] in
/-- `u |ψ⟩⟨ψ| u† = |u ψ⟩⟨u ψ|` for a unitary `u`. -/
lemma mul_proj_mul_star_of_mem_unitary {u : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E)) (ψ : E) :
    u * proj ψ * star u = proj (u ψ) := by
  rw [mul_mul_star_eq_conjOp ⟨u, hu⟩, conjOp_proj]
  rfl

/-- **Local sections of determinant one.** Let every `Φ t` be induced on pure states by a unitary,
and let `t ↦ Φ t P` be differentiable near `τ` for every rank-one projection `P`. Then near `τ`
there is a section of determinant one of `Φ`. -/
theorem eventually_isDetOneSection [Nontrivial E] {τ : ℝ}
    (himp : ∀ t, ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (U ψ))
    (hd : ∀ᶠ t in 𝓝 τ, ∀ ψ : E, ‖ψ‖ = 1 → DifferentiableAt ℝ (fun s => Φ s (proj ψ)) t) :
    ∃ V : ℝ → E →L[ℂ] E, ∀ᶠ t in 𝓝 τ, IsDetOneSection Φ V t := by
  obtain ⟨U₀, hU₀⟩ := himp τ
  obtain ⟨a, ha, hdetA⟩ := exists_det_smul_eq_one (linearIsometryEquiv_mem_unitary U₀)
  set A : E →L[ℂ] E := a • (U₀ : E →L[ℂ] E)
  have hA : A ∈ unitary (E →L[ℂ] E) := smul_mem_unitary ha (linearIsometryEquiv_mem_unitary U₀)
  have hA' : star A ∈ unitary (E →L[ℂ] E) := Unitary.star_mem hA
  set B := Unitary.linearIsometryEquiv ⟨star A, hA'⟩
  -- The family conjugated back to the identity at `τ`.
  let Φ' : ℝ → (E →L[ℂ] E) → E →L[ℂ] E := fun s ρ => star A * Φ s ρ * A
  have himp' : ∀ t, ∀ ψ : E, ‖ψ‖ = 1 → Φ' t (proj ψ) = proj (((himp t).choose.trans B) ψ) :=
    fun t ψ hψ => by
      have h := mul_proj_mul_star_of_mem_unitary hA' ((himp t).choose ψ)
      rw [star_star] at h
      simp only [Φ', (himp t).choose_spec ψ hψ, h]
      rfl
  have h₀ : ∀ ψ : E, ‖ψ‖ = 1 → Φ' τ (rankOne ℂ ψ ψ) = rankOne ℂ ψ ψ := fun ψ hψ => by
    have h := mul_proj_mul_star_of_mem_unitary hA' (A ψ)
    rw [star_star, ← mul_apply_eq_comp, Unitary.star_mul_self_of_mem hA, one_apply_eq_self] at h
    have hAψ : proj (U₀ ψ) = proj (A ψ) := by
      rw [smul_apply, proj_smul, ha]
      simp
    simp only [Φ', hU₀ ψ hψ, hAψ, h]
  have hd' : ∀ t, (∀ ψ : E, ‖ψ‖ = 1 → DifferentiableAt ℝ (fun s => Φ s (proj ψ)) t) →
      ∀ ψ : E, ‖ψ‖ = 1 → DifferentiableAt ℝ (fun s => Φ' s (rankOne ℂ ψ ψ)) t :=
    fun t h ψ hψ => ((h ψ hψ).const_mul (star A)).mul_const A
  obtain ⟨S, hS, hS₀, hSimp, -, hSd⟩ := exists_unitary_differentiableAt
    (fun t => exists_proj_of_implemented (himp' t)) (fun t => trace_eq_of_implemented (himp' t))
    h₀ (hd' τ hd.self_of_nhds)
  -- Normalize the determinant by a branch of `det(S t)^(-1/n)`.
  set n := Module.finrank ℂ E
  let g : ℝ → ℂ := fun t => (S t).det
  have hg : ∀ t, DifferentiableAt ℝ S t → DifferentiableAt ℝ g t := fun t h =>
    ((ContinuousLinearMap.contDiff_det (n := 1)).differentiable one_ne_zero (S t)
      |>.restrictScalars ℝ).comp t h
  have hg₀ : g τ = 1 := by
    simp only [g, hS₀]
    exact LinearMap.det_id
  have hslit : ∀ᶠ t in 𝓝 τ, g t ∈ Complex.slitPlane :=
    (hg τ (hSd.self_of_nhds (hd' τ hd.self_of_nhds))).continuousAt.eventually_mem
      (Complex.isOpen_slitPlane.mem_nhds (by rw [hg₀]; exact Complex.one_mem_slitPlane))
  let k : ℂ := -(n : ℂ)⁻¹
  clear_value A
  refine ⟨fun t => A * ((g t ^ k) • S t), ?_⟩
  filter_upwards [hSimp, hSd, hd, hslit] with t hSimpt hSdt hdt hslitt
  have hgt : ‖g t‖ = 1 := norm_det_of_mem_unitary (hS t)
  have hck : (g t ^ k) ^ n = (g t)⁻¹ := cpow_neg_inv_finrank_pow (g t)
  have hc1 : ‖g t ^ k‖ = 1 := norm_eq_one_of_pow_finrank hck (by rw [norm_inv, hgt, inv_one])
  have hSdt' := hSdt (hd' t hdt)
  refine ⟨mul_mem hA (smul_mem_unitary hc1 (hS t)), ?_, fun ψ hψ => ?_, ?_⟩
  · rw [det_mul, hdetA, one_mul, det_smul, hck]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hgt]; exact one_ne_zero))
  · have h₁ : Φ t (proj ψ) = A * Φ' t (proj ψ) * star A := by
      simp only [Φ', ← mul_assoc, Unitary.mul_star_self_of_mem hA, one_mul]
      rw [mul_assoc, Unitary.mul_star_self_of_mem hA, mul_one]
    rw [h₁, hSimpt ψ hψ, mul_proj_mul_star_of_mem_unitary hA]
    change proj (A (S t ψ)) = proj (A ((g t ^ k) • S t ψ))
    rw [map_smul, proj_smul, hc1]
    simp
  · exact (differentiableAt_const A).mul
      ((((differentiableAt_id.cpow_const hslitt).restrictScalars ℝ).comp t (hg t hSdt')).smul
        hSdt')

/-!
## D. Gluing along an interval
-/

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
/-- **Gluing local sections along an interval.** Let `P t V` be a property of `V : ℝ → X` at `t`
that only depends on the germ of `V` at `t` and is kept when `V` is multiplied by an element of
`μ`. Suppose that any two families with the property on a preconnected set differ there by an
element of `μ`, and agree on it if they agree at one point. If every point of an open
preconnected `I` has a family with the property near it, then one family has it on all of `I`. -/
theorem _root_.IsPreconnected.exists_forall_of_eventually {X M : Type*} [SMul M X] [Nonempty X]
    {I : Set ℝ} (hI : IsPreconnected I) {P : ℝ → (ℝ → X) → Prop} {μ : Set M}
    (hcongr : ∀ t V W, P t V → V =ᶠ[𝓝 t] W → P t W)
    (hsmul : ∀ t V, ∀ c ∈ μ, P t V → P t (fun s => c • V s))
    (huniq : ∀ S : Set ℝ, IsPreconnected S → ∀ V W, (∀ t ∈ S, P t V) → (∀ t ∈ S, P t W) →
      ∃ c ∈ μ, ∀ t ∈ S, V t = c • W t)
    (heq : ∀ S : Set ℝ, IsPreconnected S → ∀ V W, (∀ t ∈ S, P t V) → (∀ t ∈ S, P t W) →
      ∀ τ ∈ S, V τ = W τ → ∀ t ∈ S, V t = W t)
    (hloc : ∀ τ ∈ I, ∃ V, ∀ᶠ t in 𝓝 τ, P t V) :
    ∃ V : ℝ → X, ∀ t ∈ I, P t V := by
  classical
  rcases I.eq_empty_or_nonempty with rfl | ⟨τ₀, hτ₀⟩
  · exact ⟨fun _ => Classical.arbitrary X, fun t ht => ht.elim⟩
  have hball : ∀ τ ∈ I, ∃ V, ∃ ε > 0, ∀ t ∈ Metric.ball τ ε, P t V := fun τ hτ => by
    obtain ⟨V, hV⟩ := hloc τ hτ
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff_ball.mp hV
    exact ⟨V, ε, hε, h⟩
  have hinter : ∀ J J' : Set ℝ, IsPreconnected J → IsPreconnected J' →
      IsPreconnected (J ∩ J') := fun J J' hJ hJ' => by
    rw [isPreconnected_iff_ordConnected] at hJ hJ' ⊢
    exact hJ.inter hJ'
  obtain ⟨W₀, ε₀, hε₀, hW₀⟩ := hball τ₀ hτ₀
  -- A witness for `t`: an open preconnected `J ∋ τ₀, t` and a family with `P` on `J` that agrees
  -- with `W₀` at `τ₀`.
  let Wit : ℝ → Set ℝ → (ℝ → X) → Prop := fun t J V =>
    IsOpen J ∧ IsPreconnected J ∧ τ₀ ∈ J ∧ t ∈ J ∧ V τ₀ = W₀ τ₀ ∧ ∀ s ∈ J, P s V
  let D : Set ℝ := {t | ∃ J V, Wit t J V}
  have hagree : ∀ t J V J' V', Wit t J V → Wit t J' V' → V t = V' t := by
    rintro t J V J' V' ⟨-, hJ, h₀, ht, hV₀, hV⟩ ⟨-, hJ', h₀', ht', hV₀', hV'⟩
    exact heq _ (hinter J J' hJ hJ') V V' (fun s hs => hV s hs.1) (fun s hs => hV' s hs.2) τ₀
      ⟨h₀, h₀'⟩ (hV₀.trans hV₀'.symm) t ⟨ht, ht'⟩
  have hwit : ∀ t J V, Wit t J V → ∀ s ∈ J, Wit s J V :=
    fun t J V hW s hs => ⟨hW.1, hW.2.1, hW.2.2.1, hs, hW.2.2.2.2⟩
  have hDo : IsOpen D := isOpen_iff_forall_mem_open.mpr fun t ⟨J, V, hW⟩ =>
    ⟨J, fun s hs => ⟨J, V, hwit t J V hW s hs⟩, hW.1, hW.2.2.2.1⟩
  have hτ₀D : τ₀ ∈ D := ⟨_, W₀, Metric.isOpen_ball, (convex_ball τ₀ ε₀).isPreconnected,
    Metric.mem_ball_self hε₀, Metric.mem_ball_self hε₀, rfl, hW₀⟩
  -- `D` is closed in `I`: near a limit point, a local family matches a witness up to `μ`.
  have hcl : closure D ∩ I ⊆ D := by
    rintro t ⟨htD, htI⟩
    obtain ⟨W, ε, hε, hW⟩ := hball t htI
    obtain ⟨s, ⟨J, V, hJo, hJ, h₀, hsJ, hV₀, hV⟩, hts⟩ := Metric.mem_closure_iff.mp htD ε hε
    have hsB : s ∈ Metric.ball t ε := Metric.mem_ball'.mpr hts
    have hB := (convex_ball t ε).isPreconnected
    obtain ⟨c, hc, hcV⟩ := huniq _ (hinter _ _ hJ hB) V W (fun u hu => hV u hu.1)
      (fun u hu => hW u hu.2)
    refine ⟨J ∪ Metric.ball t ε, fun u => if u ∈ J then V u else c • W u,
      hJo.union Metric.isOpen_ball, hJ.union' ⟨s, hsJ, hsB⟩ hB, Or.inl h₀,
      Or.inr (Metric.mem_ball_self hε), by simp [h₀, hV₀], fun u hu => ?_⟩
    by_cases huJ : u ∈ J
    · refine hcongr u V _ (hV u huJ) ?_
      filter_upwards [hJo.mem_nhds huJ] with v hv
      simp [hv]
    · have hu' : u ∈ Metric.ball t ε := hu.resolve_left huJ
      refine hcongr u _ _ (hsmul u W c hc (hW u hu')) ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hu'] with v hv
      by_cases hvJ : v ∈ J
      · simp [hvJ, hcV v ⟨hvJ, hv⟩]
      · simp [hvJ]
  have hID : I ⊆ D := hI.subset_of_closure_inter_subset hDo ⟨τ₀, hτ₀, hτ₀D⟩ hcl
  -- The glued family: at each point, the value of any witness.
  refine ⟨fun t => if h : t ∈ D then h.choose_spec.choose t else W₀ t, fun t ht => ?_⟩
  obtain ⟨J, V, hW⟩ := hID ht
  refine hcongr t V _ (hW.2.2.2.2.2 t hW.2.2.2.1) ?_
  filter_upwards [hW.1.mem_nhds hW.2.2.2.1] with u hu
  have huD : u ∈ D := ⟨J, V, hwit t J V hW u hu⟩
  simp only [huD, dite_true]
  exact hagree u J V _ _ (hwit t J V hW u hu) huD.choose_spec.choose_spec

/-- **A differentiable propagator on an interval.** Let every `Φ t` be induced on pure states by a
unitary, and let `t ↦ Φ t P` be differentiable at every point of an open preconnected `I`, for
every rank-one projection `P`. Then one section of determinant one of `Φ` is defined on all of
`I`. -/
theorem exists_isDetOneSection [Nontrivial E] {I : Set ℝ} (hI : IsPreconnected I) (hIo : IsOpen I)
    (himp : ∀ t, ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (U ψ))
    (hd : ∀ t ∈ I, ∀ ψ : E, ‖ψ‖ = 1 → DifferentiableAt ℝ (fun s => Φ s (proj ψ)) t) :
    ∃ V : ℝ → E →L[ℂ] E, ∀ t ∈ I, IsDetOneSection Φ V t :=
  hI.exists_forall_of_eventually (μ := {c : ℂ | c ^ Module.finrank ℂ E = 1})
    (fun _ _ _ h hVW => h.congr hVW) (fun _ _ _ hc h => h.smul hc)
    (fun _ hS _ _ hV hW => IsDetOneSection.exists_eq_smul hS hW hV)
    (fun _ hS _ _ hV hW _ hτ h => IsDetOneSection.eqOn hS hV hW hτ h)
    (fun _ hτ => eventually_isDetOneSection himp
      (Filter.mem_of_superset (hIo.mem_nhds hτ) fun t ht => hd t ht))

end QuantumMechanics.Wigner
