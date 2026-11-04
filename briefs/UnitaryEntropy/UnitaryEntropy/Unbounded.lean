/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Schrödinger equation is equivalent to information conservation: unbounded Hamiltonians.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

EVDIFF on every density operator forces a bounded Hamiltonian
(`schrodinger_of_preserves_vonNeumannEntropy`). For an unbounded self-adjoint `H` the evolution
`t ↦ U t ψ` is differentiable only for `ψ` in the domain of `H`, so EVDIFF is weakened to a dense
subspace of states (`EvDiff`). For a time-independent evolution (EVTI), Theorem 2 then holds
with unbounded `H`:
* `drSceq_iff_drInfo_and_evDiff`  over QST:H + [B]EVMIX + EVTI, DR-SCEQ ⇔ DR-INFO + EVDIFF on a
  dense subspace. The direction ⇐ is DR-INFO ⇒ DR-SCEQ of `schrodinger_tfae` (Stone's theorem)
  and does not use EVDIFF; for ⇒, the domain of `H` is the dense subspace.
For a time-dependent `H(t)` the derivative at one time is only skew-symmetric on the subspace,
and the corresponding `H(t₀)` need not be self-adjoint; that case is not formalized.
-/

public import SchroedingerEvolution.InfiniteDimensional

@[expose] public noncomputable section

namespace UnitaryEntropy

open InnerProductSpace QuantumMechanics QuantumMechanics.Wigner
open SchroedingerEvolution.InfiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- `(x, y) ↦ |x⟩⟨y|` is a bounded real-bilinear map. -/
lemma isBoundedBilinearMap_rankOne :
    IsBoundedBilinearMap ℝ (fun p : E × E => rankOne ℂ p.1 p.2) where
  add_left x₁ x₂ y := by simp
  smul_left c x y := by
    dsimp only
    rw [← Complex.coe_smul, map_smul, smul_apply, Complex.coe_smul]
  add_right x y₁ y₂ := by simp
  smul_right c x y := by
    dsimp only
    rw [← Complex.coe_smul, map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul]
  bound := ⟨1, one_pos, fun x y => by simp⟩

omit [CompleteSpace E] in
/-- If `t ↦ u t` is differentiable, so is `t ↦ |u t⟩⟨u t|` in operator norm. -/
lemma differentiableAt_proj_of_hasDerivAt {u : ℝ → E} {u' : E} {t : ℝ}
    (hu : HasDerivAt u u' t) : DifferentiableAt ℝ (fun s => proj (u s)) t := by
  have h := ((isBoundedBilinearMap_rankOne (E := E)).differentiableAt (u t, u t)).comp t
    (hu.differentiableAt.prodMk hu.differentiableAt)
  exact h

/-- **EVDIFF on a dense set of states**: there is a dense subspace `D` such that
`t ↦ Φ t |ψ⟩⟨ψ|` is differentiable on `t ≥ 0`, in operator norm, for every unit vector `ψ ∈ D`. -/
def EvDiff (Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∃ D : Submodule ℂ E, Dense (D : Set E) ∧ ∀ ψ ∈ D, ‖ψ‖ = 1 → ∀ t ≥ 0,
    DifferentiableWithinAt ℝ (fun s => Φ s (proj ψ)) (Set.Ici 0) t

variable {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}

/-- DR-SCEQ ⇒ EVDIFF on a dense set: the states in the domain of `H` evolve differentiably. -/
theorem evDiff_of_drSceq {ħ : ℝ} (h : DrSceq ħ Φ) : EvDiff Φ := by
  obtain ⟨H, U, hH, -, hS, hΦ⟩ := h
  refine ⟨H.domain, hH.dense_domain, fun ψ hψ hψ1 t ht => ?_⟩
  obtain ⟨_, hd⟩ := hS ⟨ψ, hψ⟩ t
  refine (differentiableAt_proj_of_hasDerivAt hd).differentiableWithinAt.congr
    (fun s hs => ?_) ?_
  · rw [hΦ s hs _ (isDensityOperator_proj hψ1), mul_proj_mul_star]
  · rw [hΦ t ht _ (isDensityOperator_proj hψ1), mul_proj_mul_star]

/-- **Theorem 2** for a time-independent evolution, with an unbounded Hamiltonian: over
QST:H + [B]EVMIX + EVTI, DR-SCEQ, with a self-adjoint and in general unbounded `H`, is equivalent
to DR-INFO + EVDIFF on a dense set of states. EVDIFF is not needed for ⇐. -/
theorem drSceq_iff_drInfo_and_evDiff (hΦ : IsEvolution Φ) {ħ : ℝ} (hħ : ħ ≠ 0) :
    DrSceq ħ Φ ↔ DrInfo Φ ∧ EvDiff Φ := by
  have h := schrodinger_tfae hΦ hħ
  exact ⟨fun hS => ⟨(h.out 1 5).mp hS, evDiff_of_drSceq hS⟩, fun hI => (h.out 1 5).mpr hI.1⟩

end UnitaryEntropy
