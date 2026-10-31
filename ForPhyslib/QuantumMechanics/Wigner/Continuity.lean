/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Wigner.Projection

/-!
# Excluding the anti-unitary case by continuity

## i. Overview

Bargmann's triple product `Δ(a, b, c) = ⟪a, b⟫ ⟪b, c⟫ ⟪c, a⟫` depends only on the rays of `a`, `b`,
`c`. A unitary keeps it and an anti-unitary conjugates it. In operator form it is
`tr (|a⟩⟨a| |b⟩⟨b| |c⟩⟨c|)`. For orthonormal `e₁`, `e₂` the rays of `e₁`, `(e₁ - e₂)/√2` and
`(e₁ - I e₂)/√2` have `Δ = (1 + I)/4`, with imaginary part `1/4`; an anti-unitary turns this into
`-1/4`. So in dimension at least two no map is induced both by a unitary and by an anti-unitary.

For a family `Φ t` of maps on rank-one projections, each induced by a unitary or an anti-unitary,
with `Φ t₀` the identity and `t ↦ Φ t P` continuous at `t₀`, every `Φ t` near `t₀` is induced by a
unitary. This holds in any dimension. No trace is needed: for `P = |a⟩⟨a|` and a fixed `x`,
`⟪x, P Q R P x⟫ = |⟪a, x⟫|² Δ(a, b, c)`. Applied to the images of the test triple, its imaginary
part is continuous at `t₀` and starts at `1/4`, while for an anti-unitary it is `≤ 0`. In
dimension at most one every map on rays is induced by the identity, so there is nothing to
exclude.

## ii. Key results

- `QuantumMechanics.Wigner.triple_vecSub_vecSubI`: the test triple has `Δ = (1 + I)/4`.
- `QuantumMechanics.Wigner.PhaseEqOnSphere.false_of_unitary_of_antiunitary`: in dimension at least
  two, a map is not induced both by a unitary and by an anti-unitary.
- `QuantumMechanics.Wigner.eventually_exists_unitary_of_unitary_or_antiunitary`: in any
  dimension, near `t₀`, a family of maps induced by unitaries or anti-unitaries that is continuous
  at `t₀` and the identity there is induced by unitaries.
- `QuantumMechanics.Wigner.eventually_exists_unitary`: the same in finite dimension, for maps that
  preserve `tr (P Q)` on rank-one projections.

## iii. Table of contents

- A. The triple product
- B. Unitary versus anti-unitary
- C. Continuous families

## iv. References

- V. Bargmann, *Note on Wigner's theorem on symmetry operations*, J. Math. Phys. 5 (1964),
  862–868, §1.5.
- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), Lemma 4.3.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate Topology
open InnerProductSpace

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. The triple product
-/

/-- Bargmann's triple product `⟪a, b⟫ ⟪b, c⟫ ⟪c, a⟫`. -/
def triple (a b c : E) : ℂ :=
  ⟪a, b⟫_ℂ * ⟪b, c⟫_ℂ * ⟪c, a⟫_ℂ

lemma conj_mul_self_of_norm_eq_one {c : ℂ} (hc : ‖c‖ = 1) : conj c * c = 1 := by
  rw [Complex.conj_mul', hc]
  norm_num

/-- The triple product only depends on the rays. -/
lemma triple_congr {a a' b b' c c' : E} (ha : PhaseEq a a') (hb : PhaseEq b b')
    (hc : PhaseEq c c') : triple a b c = triple a' b' c' := by
  obtain ⟨α, hα, rfl⟩ := ha
  obtain ⟨β, hβ, rfl⟩ := hb
  obtain ⟨γ, hγ, rfl⟩ := hc
  simp only [triple, inner_smul_left, inner_smul_right]
  linear_combination
    (conj β * β * (conj γ * γ) * (⟪a', b'⟫_ℂ * ⟪b', c'⟫_ℂ * ⟪c', a'⟫_ℂ)) *
        conj_mul_self_of_norm_eq_one hα +
      (conj γ * γ * (⟪a', b'⟫_ℂ * ⟪b', c'⟫_ℂ * ⟪c', a'⟫_ℂ)) * conj_mul_self_of_norm_eq_one hβ +
      (⟪a', b'⟫_ℂ * ⟪b', c'⟫_ℂ * ⟪c', a'⟫_ℂ) * conj_mul_self_of_norm_eq_one hγ

lemma triple_linearIsometryEquiv (U : E ≃ₗᵢ[ℂ] E) (a b c : E) :
    triple (U a) (U b) (U c) = triple a b c := by
  simp only [triple, LinearIsometryEquiv.inner_map_map]

lemma triple_conjLinearIsometryEquiv (U : E ≃ₗᵢ⋆[ℂ] E) (a b c : E) :
    triple (U a) (U b) (U c) = conj (triple a b c) := by
  simp only [triple, LinearIsometryEquiv.inner_map_map_conj, map_mul]

/-- The triple product in operator form: `tr (|a⟩⟨a| |b⟩⟨b| |c⟩⟨c|) = Δ(a, b, c)`. -/
lemma trace_rankOne_mul_rankOne_mul_rankOne [FiniteDimensional ℂ E] (a b c : E) :
    LinearMap.trace ℂ E
        ((rankOne ℂ a a * rankOne ℂ b b * rankOne ℂ c c : E →L[ℂ] E) : E →ₗ[ℂ] E) =
      triple a b c := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, rankOne_comp_rankOne,
    ContinuousLinearMap.smul_comp, rankOne_comp_rankOne, smul_smul,
    ContinuousLinearMap.toLinearMap_smul, map_smul, trace_rankOne, smul_eq_mul, triple]

/-- The triple product without a trace:
`⟪x, |a⟩⟨a| |b⟩⟨b| |c⟩⟨c| |a⟩⟨a| x⟫ = |⟪a, x⟫|² Δ(a, b, c)`. -/
lemma inner_rankOne_mul_rankOne_mul_rankOne_mul_rankOne_apply (a b c x : E) :
    ⟪x, (rankOne ℂ a a * rankOne ℂ b b * rankOne ℂ c c * rankOne ℂ a a : E →L[ℂ] E) x⟫_ℂ =
      ((‖⟪a, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) * triple a b c := by
  change ⟪x, rankOne ℂ a a (rankOne ℂ b b (rankOne ℂ c c (rankOne ℂ a a x)))⟫_ℂ = _
  simp only [rankOne_apply, map_smul, inner_smul_right, triple]
  push_cast
  rw [← Complex.conj_mul', inner_conj_symm]
  ring

/-- The test triple: for `i ≠ k`, `Δ(b i, (b i - b k)/√2, (b i - I b k)/√2) = (1 + I)/4`. -/
lemma triple_vecSub_vecSubI {ι : Type*} (b : HilbertBasis ι ℂ E) {i k : ι}
    (hik : i ≠ k) : triple (b i) (vecSub b i k) (vecSubI b i k) = (1 + Complex.I) / 4 := by
  classical
  simp only [triple, inner_basis_vecSub, inner_vecSub_left, inner_basis_vecSubI,
    inner_vecSubI_left, inner_basis_basis, hik, hik.symm, ↓reduceIte]
  linear_combination (1 + Complex.I) * (((√2 : ℝ) : ℂ)⁻¹ * ((√2 : ℝ) : ℂ)⁻¹ + 2⁻¹) *
    sqrt_two_inv_mul_self

/-!
## B. Unitary versus anti-unitary
-/

lemma exists_ne_of_one_lt_finrank (h : 1 < Module.finrank ℂ E) :
    ∃ i k : Fin (Module.finrank ℂ E), i ≠ k :=
  ⟨⟨0, by omega⟩, ⟨1, h⟩, by simp [Fin.ext_iff]⟩

/-- In dimension at most one, any two unit vectors agree up to phase. -/
lemma phaseEq_of_finrank_le_one [FiniteDimensional ℂ E] (h : Module.finrank ℂ E ≤ 1) {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : PhaseEq x y := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp h
  obtain ⟨a, rfl⟩ := hv y
  obtain ⟨c, rfl⟩ := hv x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hy
  rw [norm_smul] at hx hy
  have hv0 : ‖v‖ ≠ 0 := by
    intro h0
    simp [h0] at hy
  refine ⟨c * a⁻¹, ?_, by rw [smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩
  rw [norm_mul, norm_inv, mul_right_cancel₀ hv0 (hx.trans hy.symm),
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha)]

/-- If a Hilbert basis has at most one vector, any two unit vectors agree up to phase. -/
lemma phaseEq_of_forall_eq {ι : Type*} (b : HilbertBasis ι ℂ E) (h : ∀ i k : ι, i = k) {x y : E}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : PhaseEq x y := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · have : x = 0 := b.ext_inner fun j => isEmptyElim j
    simp [this] at hx
  have key : ∀ z : E, ‖z‖ = 1 → PhaseEq z (b i) := fun z hz => by
    have hz' : z = ⟪b i, z⟫_ℂ • b i := b.ext_inner fun j => by
      rw [h j i, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
      simp
    refine ⟨_, ?_, hz'⟩
    have := congrArg norm hz'
    rwa [norm_smul, b.orthonormal.1 i, mul_one, hz, eq_comm] at this
  exact (key x hx).trans (key y hy).symm

/-- In dimension at least two, no map agrees up to phase both with a unitary and with an
anti-unitary. -/
lemma PhaseEqOnSphere.false_of_unitary_of_antiunitary [FiniteDimensional ℂ E]
    (h2 : 1 < Module.finrank ℂ E) {f : E → E} {U : E ≃ₗᵢ[ℂ] E} {U' : E ≃ₗᵢ⋆[ℂ] E}
    (h : PhaseEqOnSphere f U) (h' : PhaseEqOnSphere f U') : False := by
  obtain ⟨i, k, hik⟩ := exists_ne_of_one_lt_finrank h2
  have := FiniteDimensional.complete ℂ E
  set b := (stdOrthonormalBasis ℂ E).toHilbertBasis
  have h₁ : ‖b i‖ = 1 := b.orthonormal.1 i
  have h₂ := norm_vecSub (b := b) hik
  have h₃ := norm_vecSubI (b := b) hik
  have e := (triple_congr (h _ h₁) (h _ h₂) (h _ h₃)).symm.trans
    (triple_congr (h' _ h₁) (h' _ h₂) (h' _ h₃))
  rw [triple_linearIsometryEquiv, triple_conjLinearIsometryEquiv,
    triple_vecSub_vecSubI b hik] at e
  have := congrArg Complex.im e
  rw [Complex.conj_im] at this
  norm_num at this

/-!
## C. Continuous families
-/

/-- **Excluding the anti-unitary case**, in any dimension. Let every `Φ t` be induced on
rank-one projections by a unitary or an anti-unitary, let `Φ t₀` fix every rank-one projection,
and let `t ↦ Φ t P` be continuous at `t₀` for every rank-one projection `P`. Then for `t` near
`t₀`, `Φ t` is induced by a unitary. -/
theorem eventually_exists_unitary_of_unitary_or_antiunitary [CompleteSpace E]
    {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {t₀ : ℝ}
    (hW : ∀ t, (∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (U ψ) (U ψ)) ∨
      ∃ U : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (U ψ) (U ψ))
    (h₀ : ∀ ψ : E, ‖ψ‖ = 1 → Φ t₀ (rankOne ℂ ψ ψ) = rankOne ℂ ψ ψ)
    (hc : ∀ ψ : E, ‖ψ‖ = 1 → ContinuousAt (fun t => Φ t (rankOne ℂ ψ ψ)) t₀) :
    ∀ᶠ t in 𝓝 t₀, ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (U ψ) (U ψ) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  by_cases hne : ∃ i k : w, i ≠ k
  swap
  · simp only [ne_eq, not_exists, not_not] at hne
    refine Filter.Eventually.of_forall fun t => ?_
    rcases hW t with hU | ⟨U, hU⟩
    · exact hU
    refine ⟨LinearIsometryEquiv.refl ℂ E, fun ψ hψ => ?_⟩
    rw [hU ψ hψ, (phaseEq_of_forall_eq b hne (by rw [U.norm_map, hψ]) hψ).rankOne_self]
    rfl
  obtain ⟨i, k, hik⟩ := hne
  have h₁ : ‖b i‖ = 1 := b.orthonormal.1 i
  have h₂ := norm_vecSub (b := b) hik
  have h₃ := norm_vecSubI (b := b) hik
  let g : ℝ → ℂ := fun t => ⟪b i,
    (Φ t (rankOne ℂ (b i) (b i)) * Φ t (rankOne ℂ (vecSub b i k) (vecSub b i k)) *
      Φ t (rankOne ℂ (vecSubI b i k) (vecSubI b i k)) * Φ t (rankOne ℂ (b i) (b i))) (b i)⟫_ℂ
  have hT : Continuous fun A : E →L[ℂ] E => (⟪b i, A (b i)⟫_ℂ).im :=
    Complex.continuous_im.comp
      (continuous_const.inner (ContinuousLinearMap.apply ℂ E (b i)).continuous)
  have hg : ContinuousAt (fun t => (g t).im) t₀ :=
    hT.continuousAt.comp ((((hc _ h₁).mul (hc _ h₂)).mul (hc _ h₃)).mul (hc _ h₁))
  have hg₀ : 0 < (g t₀).im := by
    simp only [g, h₀ _ h₁, h₀ _ h₂, h₀ _ h₃,
      inner_rankOne_mul_rankOne_mul_rankOne_mul_rankOne_apply, triple_vecSub_vecSubI b hik,
      norm_inner_self_eq_one h₁, Complex.im_ofReal_mul]
    norm_num
  filter_upwards [hg.eventually (lt_mem_nhds hg₀)] with t ht
  rcases hW t with hU | ⟨U, hU⟩
  · exact hU
  simp only [g, hU _ h₁, hU _ h₂, hU _ h₃, inner_rankOne_mul_rankOne_mul_rankOne_mul_rankOne_apply,
    triple_conjLinearIsometryEquiv, triple_vecSub_vecSubI b hik, Complex.im_ofReal_mul,
    Complex.conj_im] at ht
  norm_num at ht
  nlinarith [sq_nonneg ‖⟪U (b i), b i⟫_ℂ‖]

/-- **Excluding the anti-unitary case**, in finite dimension. Let `Φ t` send rank-one projections
to rank-one projections and preserve `tr (P Q)` between them, let `Φ t₀` fix every rank-one
projection, and let `t ↦ Φ t P` be continuous at `t₀` for every rank-one projection `P`. Then for
`t` near `t₀`, `Φ t` is induced by a unitary. -/
theorem eventually_exists_unitary [FiniteDimensional ℂ E] {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    {t₀ : ℝ}
    (hP : ∀ t, ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ Φ t (rankOne ℂ ψ ψ) = rankOne ℂ ψ' ψ')
    (htr : ∀ t, ∀ ψ ϕ : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      LinearMap.trace ℂ E ((Φ t (rankOne ℂ ψ ψ) * Φ t (rankOne ℂ ϕ ϕ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((rankOne ℂ ψ ψ * rankOne ℂ ϕ ϕ : E →L[ℂ] E) : E →ₗ[ℂ] E))
    (h₀ : ∀ ψ : E, ‖ψ‖ = 1 → Φ t₀ (rankOne ℂ ψ ψ) = rankOne ℂ ψ ψ)
    (hc : ∀ ψ : E, ‖ψ‖ = 1 → ContinuousAt (fun t => Φ t (rankOne ℂ ψ ψ)) t₀) :
    ∀ᶠ t in 𝓝 t₀, ∃ U : E ≃ₗᵢ[ℂ] E, ∀ ψ, ‖ψ‖ = 1 → Φ t (rankOne ℂ ψ ψ) = rankOne ℂ (U ψ) (U ψ) :=
  have := FiniteDimensional.complete ℂ E
  eventually_exists_unitary_of_unitary_or_antiunitary
    (fun t => wigner_rankOne (Φ t) (hP t) (htr t)) h₀ hc

end QuantumMechanics.Wigner
