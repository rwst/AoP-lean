/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Schrödinger equation is equivalent to information conservation: the propagator of a
time-dependent Hamiltonian.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Theorem 2 (⇒) starts from "The Schrödinger equation gives rise to a differentiable unitary
propagator `U_{t₀→t₁}`". For a continuous family of bounded self-adjoint `H(t)` this is proved
here, in any dimension, from the global existence and uniqueness theorem for linear ODEs in a
Banach algebra (`exists_hasDerivAt_mul`, `ForMathlib/Analysis/ODE/Linear`):
* `exists_propagator_of_continuous`  `U' = (iħ)⁻¹ H(t) U` has a solution with `U t₀ = 1` on
  all of `ℝ`, and every `U t` is unitary (`U† U = 1` is conserved, and `U U† - 1` solves a
  linear equation with initial value `0`);
* `propagator_unique`  it is unique;
* `exists_propagator_conserves_vonNeumannEntropy`  DR-SCEQ ⇒ DR-INFO with this propagator, in
  any dimension;
* `TwoParameter.exists_propagator_isEvolution`  in finite dimension, the two-parameter evolution
  `Ψ t₀ t₁ ρ = U t₁ U t₀† ρ (U t₁ U t₀†)†` (`TwoParameter.conjEvolution`) satisfies QST:H + [B]EVMIX
  and DR-SCEQ, hence DR-INFO and EVDIFF.
-/

public import ForMathlib.Analysis.ODE.Linear
public import UnitaryEntropy.InfiniteDimensional
public import UnitaryEntropy.TwoParameter

@[expose] public noncomputable section

namespace UnitaryEntropy

open InnerProductSpace QuantumMechanics QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `(iħ)⁻¹ H` is skew-adjoint for self-adjoint `H`. -/
lemma star_inv_I_mul_smul {ħ : ℝ} {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) :
    star ((Complex.I * ħ)⁻¹ • H) = -((Complex.I * ħ)⁻¹ • H) := by
  rw [star_smul, hH.star_eq, star_inv_I_mul, neg_smul]

/-- **Theorem 2** (⇒), the propagator of a time-dependent Hamiltonian, in any dimension: for a
continuous family of self-adjoint `H(t)`, the Schrödinger equation `U' = (iħ)⁻¹ H(t) U` has a
solution on all of `ℝ` with `U t₀ = 1`, and every `U t` is unitary. -/
theorem exists_propagator_of_continuous {H : ℝ → E →L[ℂ] E} (hc : Continuous H)
    (hH : ∀ t, IsSelfAdjoint (H t)) (ħ t₀ : ℝ) :
    ∃ U : ℝ → E →L[ℂ] E, U t₀ = 1 ∧
      (∀ t, HasDerivAt U ((Complex.I * ħ)⁻¹ • (H t * U t)) t) ∧
      ∀ t, U t ∈ unitary (E →L[ℂ] E) := by
  obtain ⟨U, hU₀, hU, hu⟩ := exists_hasDerivAt_mul_mem_unitary
    (X := fun t => (Complex.I * ħ)⁻¹ • H t) (by fun_prop)
    (fun t => star_inv_I_mul_smul (hH t)) t₀
  exact ⟨U, hU₀, fun t => by simpa only [smul_mul_assoc] using hU t, hu⟩

/-- The propagator is unique. -/
theorem propagator_unique {H : ℝ → E →L[ℂ] E} (hc : Continuous H) {ħ t₀ : ℝ}
    {U V : ℝ → E →L[ℂ] E} (hU : ∀ t, HasDerivAt U ((Complex.I * ħ)⁻¹ • (H t * U t)) t)
    (hV : ∀ t, HasDerivAt V ((Complex.I * ħ)⁻¹ • (H t * V t)) t) (h : U t₀ = V t₀) : U = V :=
  eq_of_hasDerivAt_mul (A := fun t => (Complex.I * ħ)⁻¹ • H t) (by fun_prop)
    (fun t => by simpa only [smul_mul_assoc] using hU t)
    (fun t => by simpa only [smul_mul_assoc] using hV t) h

/-- **Theorem 2** (⇒), DR-SCEQ ⇒ DR-INFO, in any dimension, for a continuous time-dependent
Hamiltonian: the propagator exists, and for every density operator `ρ` and time `t`,
`ρF = U t ρ U t†` is a density operator, the reconstructed past `U t† ρF U t` is `ρ`, and
`S(ρF) = S(ρ)`. -/
theorem exists_propagator_conserves_vonNeumannEntropy {H : ℝ → E →L[ℂ] E} (hc : Continuous H)
    (hH : ∀ t, IsSelfAdjoint (H t)) (ħ t₀ : ℝ) :
    ∃ U : ℝ → E →L[ℂ] E, U t₀ = 1 ∧
      (∀ t, HasDerivAt U ((Complex.I * ħ)⁻¹ • (H t * U t)) t) ∧
      ∀ ρ, IsDensityOperator ρ → ∀ t, IsDensityOperator (U t * ρ * star (U t)) ∧
        star (U t) * (U t * ρ * star (U t)) * U t = ρ ∧
        vonNeumannEntropy (U t * ρ * star (U t)) = vonNeumannEntropy ρ := by
  obtain ⟨U, hU₀, hU, -⟩ := exists_propagator_of_continuous hc hH ħ t₀
  exact ⟨U, hU₀, hU, fun ρ hρ t => schrodinger_conserves_vonNeumannEntropy hH hU hU₀ hρ t⟩

namespace TwoParameter

open SchroedingerEvolution.TwoParameter (IsEvolution DrSceq)

/-- The two-parameter evolution of a propagator: `Ψ t₀ t₁ ρ = W ρ W†` with `W = U t₁ U t₀†`. -/
def conjEvolution (U : ℝ → E →L[ℂ] E) : ℝ → ℝ → (E →L[ℂ] E) → E →L[ℂ] E :=
  fun t₀ t₁ ρ => U t₁ * star (U t₀) * ρ * star (U t₁ * star (U t₀))

/-- A continuous family of unitaries gives a two-parameter evolution (QST:H + [B]EVMIX). -/
lemma isEvolution_conjEvolution {U : ℝ → E →L[ℂ] E} (hU : ∀ t, U t ∈ unitary (E →L[ℂ] E))
    (hc : Continuous U) : IsEvolution (conjEvolution U) where
  isDensity t₀ t₁ _ ρ hρ := hρ.unitary_conj (mul_mem (hU t₁) (Unitary.star_mem (hU t₀)))
  affine t₀ t₁ _ ρ σ _ _ s _ _ := by
    simp only [conjEvolution, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  map_self t ρ _ := by
    simp only [conjEvolution, Unitary.mul_star_self_of_mem (hU t), one_mul, star_one, mul_one]
  map_comp t₀ t₁ t₂ _ _ ρ _ := by
    have key : ∀ W V : E →L[ℂ] E, W * (V * ρ * star V) * star W = W * V * ρ * star (W * V) :=
      fun W V => by
        rw [star_mul]
        simp only [mul_assoc]
    have h : U t₂ * star (U t₁) * (U t₁ * star (U t₀)) = U t₂ * star (U t₀) := by
      rw [mul_assoc, ← mul_assoc (star (U t₁)), Unitary.star_mul_self_of_mem (hU t₁), one_mul]
    simp only [conjEvolution]
    rw [key, h]
  continuousOn := by
    refine Continuous.continuousOn ?_
    simp only [conjEvolution]
    fun_prop

variable [FiniteDimensional ℂ E]

/-- **Theorem 2** (⇒) with a time-dependent Hamiltonian, in finite dimension: a continuous family
of self-adjoint `H(t)` gives a differentiable unitary propagator `U` with `U 0 = 1`, and its
two-parameter evolution `Ψ t₀ t₁ ρ = U t₁ U t₀† ρ (U t₁ U t₀†)†` satisfies QST:H + [B]EVMIX and
DR-SCEQ, hence DR-INFO and EVDIFF. -/
theorem exists_propagator_isEvolution {H : ℝ → E →L[ℂ] E} (hc : Continuous H)
    (hH : ∀ t, IsSelfAdjoint (H t)) {ħ : ℝ} (hħ : ħ ≠ 0) :
    ∃ U : ℝ → E →L[ℂ] E, U 0 = 1 ∧
      (∀ t, HasDerivAt U ((Complex.I * ħ)⁻¹ • (H t * U t)) t) ∧
      IsEvolution (conjEvolution U) ∧ DrSceq ħ (conjEvolution U) ∧
      DrInfo (conjEvolution U) ∧ EvDiff (conjEvolution U) := by
  obtain ⟨U, hU₀, hU, hu⟩ := exists_propagator_of_continuous hc hH ħ 0
  have hΨ := isEvolution_conjEvolution hu
    (continuous_iff_continuousAt.mpr fun t => (hU t).continuousAt)
  have hD : DrSceq ħ (conjEvolution U) := ⟨H, U, hH, hU₀, hU, fun _ _ _ _ _ => rfl⟩
  exact ⟨U, hU₀, hU, hΨ, hD, (drSceq_iff_drInfo_and_evDiff hΨ hħ).mp hD⟩

end TwoParameter

end UnitaryEntropy
