/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Wigner.Continuity
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Choosing the phase differentiably

## i. Overview

Wigner's theorem gives the unitary `U t` behind `Φ t` only up to a phase, and an arbitrary choice
of phases need not depend differentiably on `t`. In finite dimension there is an explicit choice.
Extend `Φ` from rank-one projections to all `|v⟩⟨v|` by homogeneity and to all `|x⟩⟨y|` by
polarization; if `Φ` is induced by `U`, the extension sends `|x⟩⟨y|` to `|U x⟩⟨U y|`. For an
orthonormal basis `b` and an index `i`,
`∑ₖ |U b k⟩⟨U b i| |b i⟩⟨b k| = ⟪U b i, b i⟫ U`, so dividing by `|⟪U b i, b i⟫|` fixes the phase by
`⟪b i, U b i⟫ > 0`. The resulting operator is a finite expression in values of `Φ` on rank-one
projections and in `re ⟪b i, Φ (|b i⟩⟨b i|) b i⟫ = |⟪U b i, b i⟫|²`. It is unitary where this
number is positive, which holds near `t₀` when `Φ t₀` is the identity, and it is differentiable at
`t₀` when each `t ↦ Φ t P` is.

In any dimension the sum over a basis is not available in operator norm. One vector at a time,
`(|U x⟩⟨U e|) e = ⟪U e, e⟫ U x` for a fixed unit vector `e`, so `x ↦ |⟪U e, e⟫|⁻¹ (|U x⟩⟨U e|) e`
is the same unitary, and `t ↦ U t x` is differentiable at `t₀` for each `x`.

## ii. Key results

- `QuantumMechanics.Wigner.unitaryOf_eq`: the explicit operator is `U` times a phase.
- `QuantumMechanics.Wigner.exists_unitary_differentiableAt`: a family that is differentiable at
  `t₀` and the identity there is induced near `t₀` by unitaries `U t` with `U t₀ = 1` and
  `t ↦ U t` differentiable at `t₀`.
- `QuantumMechanics.Wigner.exists_unitary_differentiableAt_apply`: in any dimension, the same with
  `t ↦ U t x` differentiable at `t₀` for every `x`.

## iii. Table of contents

- A. The explicit operator
- B. Differentiability
- C. The differentiable family of unitaries

## iv. References

- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), Lemmas 7.3–7.5.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate Topology
open InnerProductSpace

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. The explicit operator
-/

section Extension

variable (Φ : (E →L[ℂ] E) → E →L[ℂ] E)

/-- `Φ` extended homogeneously from rank-one projections to all `|v⟩⟨v|`:
`|v⟩⟨v| ↦ ‖v‖² Φ (|v/‖v‖⟩⟨v/‖v‖|)`. -/
noncomputable def projMap (v : E) : E →L[ℂ] E :=
  ((‖v‖ ^ 2 : ℝ) : ℂ) • Φ (rankOne ℂ ((‖v‖ : ℂ)⁻¹ • v) ((‖v‖ : ℂ)⁻¹ • v))

/-- `Φ` extended to all `|x⟩⟨y|` by polarization. -/
noncomputable def polMap (x y : E) : E →L[ℂ] E :=
  (4 : ℂ)⁻¹ • (projMap Φ (x + y) - projMap Φ (x - y) +
    Complex.I • projMap Φ (x + Complex.I • y) - Complex.I • projMap Φ (x - Complex.I • y))

/-- `re ⟪e, Φ (|e⟩⟨e|) e⟫`, which is `|⟪U e, e⟫|²` when `Φ` is induced by `U`. -/
noncomputable def phaseNorm (e : E) : ℝ :=
  (⟪e, projMap Φ e e⟫_ℂ).re

/-- The candidate operator: `|⟪U b i, b i⟫|⁻¹ ∑ₖ |U b k⟩⟨U b i| |b i⟩⟨b k|`, written through `Φ`. -/
noncomputable def unitaryOf {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (i : ι) :
    E →L[ℂ] E :=
  (√(phaseNorm Φ (b i)))⁻¹ • ∑ k, (polMap Φ (b k) (b i)).comp (rankOne ℂ (b i) (b k))

/-- The candidate in any dimension, one vector at a time:
`x ↦ |⟪U e, e⟫|⁻¹ (|U x⟩⟨U e|) e`, written through `Φ`. -/
noncomputable def unitaryApply (e x : E) : E :=
  (√(phaseNorm Φ e))⁻¹ • polMap Φ x e e

lemma sum_rankOne_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] E) :
    ∑ k, rankOne ℂ (A (b k)) (b k) = A := by
  ext z
  conv_rhs => rw [← b.sum_repr' z]
  simp [map_sum, map_smul]

variable {Φ} {V : E ≃ₗᵢ[ℂ] E}

lemma projMap_eq (hV : ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ)) (v : E) :
    projMap Φ v = rankOne ℂ (V v) (V v) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [projMap]
  have : (‖v‖ : ℂ) ≠ 0 := by simpa using hv
  have hu : ‖(‖v‖ : ℂ)⁻¹ • v‖ = 1 := by simpa using norm_smul_inv_norm (𝕜 := ℂ) hv
  rw [projMap, hV _ hu]
  ext z
  simp only [smul_apply, rankOne_apply, map_smul, inner_smul_left, smul_smul, Complex.conj_inv,
    Complex.conj_ofReal]
  congr 1
  push_cast
  field_simp

lemma polMap_eq (hV : ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ)) (x y : E) :
    polMap Φ x y = rankOne ℂ (V x) (V y) := by
  simp only [polMap, projMap_eq hV, LinearIsometryEquiv.map_add, LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.map_smul]
  rw [← rankOne_polarization, smul_smul]
  norm_num

lemma phaseNorm_eq (hV : ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ)) (e : E) :
    phaseNorm Φ e = ‖⟪V e, e⟫_ℂ‖ ^ 2 := by
  rw [phaseNorm, projMap_eq hV, rankOne_apply, inner_smul_right, ← inner_conj_symm e (V e),
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

lemma unitaryOf_eq (hV : ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ))
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (i : ι) :
    unitaryOf Φ b i = ((‖⟪V (b i), b i⟫_ℂ‖ : ℂ)⁻¹ * ⟪V (b i), b i⟫_ℂ) • (V : E →L[ℂ] E) := by
  simp only [unitaryOf, phaseNorm_eq hV, Real.sqrt_sq (norm_nonneg _), polMap_eq hV,
    rankOne_comp_rankOne, ← Finset.smul_sum]
  rw [← sum_rankOne_basis b (V : E →L[ℂ] E), mul_smul, ← Complex.ofReal_inv, Complex.coe_smul]
  rfl

lemma unitaryApply_eq (hV : ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ)) (e x : E) :
    unitaryApply Φ e x = ((‖⟪V e, e⟫_ℂ‖ : ℂ)⁻¹ * ⟪V e, e⟫_ℂ) • V x := by
  rw [unitaryApply, phaseNorm_eq hV, Real.sqrt_sq (norm_nonneg _), polMap_eq hV, rankOne_apply,
    ← Complex.coe_smul, smul_smul, Complex.ofReal_inv]

/-- Where `phaseNorm Φ e > 0`, the phase `⟪V e, e⟫ / |⟪V e, e⟫|` times `V` is a unitary that
induces `Φ`. -/
lemma phase_smul_mem_unitary [CompleteSpace E]
    (hV : ∀ ψ, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ))
    {e : E} (hpos : 0 < phaseNorm Φ e) :
    ((‖⟪V e, e⟫_ℂ‖ : ℂ)⁻¹ * ⟪V e, e⟫_ℂ) • (V : E →L[ℂ] E) ∈ unitary (E →L[ℂ] E) ∧
      ∀ ψ : E, ‖ψ‖ = 1 → Φ (rankOne ℂ ψ ψ) =
        rankOne ℂ ((((‖⟪V e, e⟫_ℂ‖ : ℂ)⁻¹ * ⟪V e, e⟫_ℂ) • (V : E →L[ℂ] E)) ψ)
          ((((‖⟪V e, e⟫_ℂ‖ : ℂ)⁻¹ * ⟪V e, e⟫_ℂ) • (V : E →L[ℂ] E)) ψ) := by
  have hw : ⟪V e, e⟫_ℂ ≠ 0 := fun h => by
    rw [phaseNorm_eq hV, h] at hpos
    norm_num at hpos
  have hc : ‖(‖⟪V e, e⟫_ℂ‖ : ℂ)⁻¹ * ⟪V e, e⟫_ℂ‖ = 1 := by
    simpa using norm_smul_inv_norm (𝕜 := ℂ) hw
  refine ⟨Unitary.smul_mem_of_mem ?_ (Unitary.linearIsometryEquiv.symm V).2, fun ψ hψ => ?_⟩
  · rw [Unitary.mem_iff, Complex.star_def, mul_comm _ (conj _), and_self]
    exact conj_mul_self_of_norm_eq_one hc
  · rw [hV ψ hψ, smul_apply]
    exact (PhaseEq.rankOne_self ⟨_, hc, rfl⟩).symm

end Extension

/-!
## B. Differentiability
-/

section Family

variable {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {t₀ : ℝ}
  (hd : ∀ ψ : E, ‖ψ‖ = 1 → DifferentiableAt ℝ (fun t => Φ t (rankOne ℂ ψ ψ)) t₀)
include hd

lemma differentiableAt_projMap (v : E) : DifferentiableAt ℝ (fun t => projMap (Φ t) v) t₀ := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [projMap]
  have hu : ‖(‖v‖ : ℂ)⁻¹ • v‖ = 1 := by simpa using norm_smul_inv_norm (𝕜 := ℂ) hv
  exact (hd _ hu).const_smul ((‖v‖ ^ 2 : ℝ) : ℂ)

lemma differentiableAt_polMap (x y : E) : DifferentiableAt ℝ (fun t => polMap (Φ t) x y) t₀ := by
  have h := differentiableAt_projMap hd
  exact ((((h _).sub (h _)).add ((h _).const_smul Complex.I)).sub
    ((h _).const_smul Complex.I)).const_smul (4 : ℂ)⁻¹

lemma differentiableAt_phaseNorm (e : E) : DifferentiableAt ℝ (fun t => phaseNorm (Φ t) e) t₀ :=
  (Complex.reCLM.comp (((innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ E e)).restrictScalars ℝ)
    |>.differentiableAt).comp t₀ (differentiableAt_projMap hd e)

lemma differentiableAt_unitaryOf {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (i : ι)
    (h : 0 < phaseNorm (Φ t₀) (b i)) : DifferentiableAt ℝ (fun t => unitaryOf (Φ t) b i) t₀ := by
  refine ((differentiableAt_phaseNorm hd _).sqrt h.ne' |>.inv (Real.sqrt_pos.mpr h).ne').smul ?_
  refine DifferentiableAt.fun_sum fun k _ => ?_
  exact (((ContinuousLinearMap.compL ℂ E E E).flip (rankOne ℂ (b i) (b k))).restrictScalars ℝ
    |>.differentiableAt).comp t₀ (differentiableAt_polMap hd _ _)

lemma differentiableAt_unitaryApply (e x : E) (h : 0 < phaseNorm (Φ t₀) e) :
    DifferentiableAt ℝ (fun t => unitaryApply (Φ t) e x) t₀ :=
  ((differentiableAt_phaseNorm hd _).sqrt h.ne' |>.inv (Real.sqrt_pos.mpr h).ne').smul
    ((((ContinuousLinearMap.apply ℂ E e).restrictScalars ℝ).differentiableAt).comp t₀
      (differentiableAt_polMap hd x e))

end Family

/-!
## C. The differentiable family of unitaries
-/

/-- **Differentiable choice of the phase.** Let `Φ t` send rank-one projections to rank-one
projections and preserve `tr (P Q)` between them, let `Φ t₀` fix every rank-one projection, and let
`t ↦ Φ t P` be differentiable at `t₀` for every rank-one projection `P`. Then there is a family of
unitaries `U t`, with `U t₀ = 1` and differentiable at `t₀`, that induces `Φ t` for `t` near
`t₀`. -/
theorem exists_unitary_differentiableAt [FiniteDimensional ℂ E] [CompleteSpace E]
    {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {t₀ : ℝ}
    (hP : ∀ t, ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ Φ t (rankOne ℂ ψ ψ) = rankOne ℂ ψ' ψ')
    (htr : ∀ t, ∀ ψ ϕ : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      LinearMap.trace ℂ E ((Φ t (rankOne ℂ ψ ψ) * Φ t (rankOne ℂ ϕ ϕ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((rankOne ℂ ψ ψ * rankOne ℂ ϕ ϕ : E →L[ℂ] E) : E →ₗ[ℂ] E))
    (h₀ : ∀ ψ : E, ‖ψ‖ = 1 → Φ t₀ (rankOne ℂ ψ ψ) = rankOne ℂ ψ ψ)
    (hd : ∀ ψ : E, ‖ψ‖ = 1 → DifferentiableAt ℝ (fun t => Φ t (rankOne ℂ ψ ψ)) t₀) :
    ∃ U : ℝ → E →L[ℂ] E, (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧ U t₀ = 1 ∧
      (∀ᶠ t in 𝓝 t₀, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (U t ψ) (U t ψ)) ∧
      DifferentiableAt ℝ U t₀ := by
  classical
  set b := stdOrthonormalBasis ℂ E
  rcases isEmpty_or_nonempty (Fin (Module.finrank ℂ E)) with hι | ⟨⟨i⟩⟩
  · refine ⟨fun _ => 1, fun _ => one_mem _, rfl, .of_forall fun t ψ hψ => absurd hψ ?_,
      differentiableAt_const _⟩
    rw [← b.sum_repr' ψ, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact zero_ne_one
  -- Where `Φ t` is induced by `V`, the candidate is `V` times a phase.
  have key : ∀ t (V : E ≃ₗᵢ[ℂ] E), (∀ ψ, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ)) →
      0 < phaseNorm (Φ t) (b i) → unitaryOf (Φ t) b i ∈ unitary (E →L[ℂ] E) ∧
        ∀ ψ : E, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) =
          rankOne ℂ (unitaryOf (Φ t) b i ψ) (unitaryOf (Φ t) b i ψ) := by
    intro t V hV hpos
    rw [unitaryOf_eq hV]
    exact phase_smul_mem_unitary hV hpos
  have h₁ : phaseNorm (Φ t₀) (b i) = 1 := by
    rw [phaseNorm_eq (V := LinearIsometryEquiv.refl ℂ E) h₀]
    simp
  have hpos : ∀ᶠ t in 𝓝 t₀, 0 < phaseNorm (Φ t) (b i) :=
    (differentiableAt_phaseNorm hd _).continuousAt.eventually (lt_mem_nhds (by simp [h₁]))
  have hU := eventually_exists_unitary hP htr h₀ fun ψ hψ => (hd ψ hψ).continuousAt
  have hF : ∀ᶠ t in 𝓝 t₀, unitaryOf (Φ t) b i ∈ unitary (E →L[ℂ] E) ∧
      ∀ ψ : E, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) =
        rankOne ℂ (unitaryOf (Φ t) b i ψ) (unitaryOf (Φ t) b i ψ) := by
    filter_upwards [hU, hpos] with t ⟨V, hV⟩ ht
    exact key t V hV ht
  have hF₀ : unitaryOf (Φ t₀) b i = 1 := by
    rw [unitaryOf_eq (V := LinearIsometryEquiv.refl ℂ E) h₀]
    simp
    rfl
  refine ⟨fun t => if unitaryOf (Φ t) b i ∈ unitary (E →L[ℂ] E) then unitaryOf (Φ t) b i else 1,
    fun t => ?_, ?_, ?_, ?_⟩
  · dsimp only
    split_ifs with h
    exacts [h, one_mem _]
  · simp [hF₀]
  · filter_upwards [hF] with t ht
    simpa only [ht.1, ↓reduceIte] using ht.2
  · refine (differentiableAt_unitaryOf hd b i (by rw [h₁]; exact one_pos)).congr_of_eventuallyEq ?_
    filter_upwards [hF] with t ht
    simp only [ht.1, ↓reduceIte]

/-- **Differentiable choice of the phase, in any dimension.** Let `Φ t` be induced by unitaries
for `t` near `t₀`, let `Φ t₀` fix every rank-one projection, and let `t ↦ Φ t P` be
differentiable at `t₀` for every rank-one projection `P`. Then there is a family of unitaries
`U t`, with `U t₀ = 1` and `t ↦ U t x` differentiable at `t₀` for every `x`, that induces `Φ t`
for `t` near `t₀`. -/
theorem exists_unitary_differentiableAt_apply [CompleteSpace E]
    {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {t₀ : ℝ}
    (hU : ∀ᶠ t in 𝓝 t₀, ∃ V : E ≃ₗᵢ[ℂ] E,
      ∀ ψ, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ))
    (h₀ : ∀ ψ : E, ‖ψ‖ = 1 → Φ t₀ (rankOne ℂ ψ ψ) = rankOne ℂ ψ ψ)
    (hd : ∀ ψ : E, ‖ψ‖ = 1 → DifferentiableAt ℝ (fun t => Φ t (rankOne ℂ ψ ψ)) t₀) :
    ∃ U : ℝ → E →L[ℂ] E, (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧ U t₀ = 1 ∧
      (∀ᶠ t in 𝓝 t₀, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (U t ψ) (U t ψ)) ∧
      ∀ x, DifferentiableAt ℝ (fun t => U t x) t₀ := by
  classical
  by_cases hE : ∃ e : E, ‖e‖ = 1
  swap
  · exact ⟨fun _ => 1, fun _ => one_mem _, rfl, .of_forall fun t ψ hψ => absurd ⟨ψ, hψ⟩ hE,
      fun _ => differentiableAt_const _⟩
  obtain ⟨e, he⟩ := hE
  have h₁ : phaseNorm (Φ t₀) e = 1 := by
    rw [phaseNorm_eq (V := LinearIsometryEquiv.refl ℂ E) h₀]
    simp [he]
  have hpos : ∀ᶠ t in 𝓝 t₀, 0 < phaseNorm (Φ t) e :=
    (differentiableAt_phaseNorm hd _).continuousAt.eventually (lt_mem_nhds (by simp [h₁]))
  let P : ℝ → (E ≃ₗᵢ[ℂ] E) → Prop := fun t V =>
    (∀ ψ, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (V ψ) (V ψ)) ∧ 0 < phaseNorm (Φ t) e
  let U : ℝ → E →L[ℂ] E := fun t => if h : ∃ V, P t V then
    ((‖⟪h.choose e, e⟫_ℂ‖ : ℂ)⁻¹ * ⟪h.choose e, e⟫_ℂ) • (h.choose : E →L[ℂ] E) else 1
  -- Where `U t` comes from some `V`, it agrees with the explicit candidate.
  have hUapp : ∀ t (h : ∃ V, P t V) x, U t x = unitaryApply (Φ t) e x := fun t h x => by
    simp only [U, h, ↓reduceDIte]
    exact (unitaryApply_eq h.choose_spec.1 e x).symm
  have hP₀ : ∃ V, P t₀ V := ⟨LinearIsometryEquiv.refl ℂ E, h₀, by rw [h₁]; exact one_pos⟩
  have hev : ∀ᶠ t in 𝓝 t₀, ∃ V, P t V := by
    filter_upwards [hU, hpos] with t ⟨V, hV⟩ ht
    exact ⟨V, hV, ht⟩
  refine ⟨U, fun t => ?_, ?_, ?_, fun x => ?_⟩
  · by_cases h : ∃ V, P t V
    · simp only [U, h, ↓reduceDIte]
      exact (phase_smul_mem_unitary h.choose_spec.1 h.choose_spec.2).1
    · simp only [U, h, ↓reduceDIte]
      exact one_mem _
  · ext x
    rw [hUapp t₀ hP₀, unitaryApply_eq (V := LinearIsometryEquiv.refl ℂ E) h₀]
    simp [inner_self_eq_norm_sq_to_K, he]
  · filter_upwards [hev] with t h
    simp only [U, h, ↓reduceDIte]
    exact (phase_smul_mem_unitary h.choose_spec.1 h.choose_spec.2).2
  · refine (differentiableAt_unitaryApply hd e x (by rw [h₁]; exact one_pos))
      |>.congr_of_eventuallyEq ?_
    filter_upwards [hev] with t h
    exact hUapp t h x

end QuantumMechanics.Wigner
