/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Bargmann
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.EssentialSpectrum.Smul
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Existence.StoneReconstruction

/-!
# Stone's theorem in Schrödinger form

A strongly continuous unitary group `U` is the propagator of a Schrödinger equation
`d/dt U t ψ = (iħ)⁻¹ H U t ψ` for `ψ` in the domain of a self-adjoint, in general unbounded, `H`;
conversely, a family of bounded operators with `U 0 = 1` that solves such an equation is a
strongly continuous unitary group. Both directions are glue around PhyslibAlpha's Stone theorem.

## i. Overview

For the first direction, PhyslibAlpha reconstructs `U t = exp (i t T)` with `T` the closure of
the candidate generator, which is self-adjoint (`stoneCandidateGenerator_reconstruction`); the
orbits `exp (i t T) x` with `x` in the domain of `T` stay in the domain and solve `w' = i T w`.
Then `H = -ħ T` is self-adjoint and `(iħ)⁻¹ H = i T`.

For the second direction, let `T = -ħ⁻¹ H` and `V t = exp (i t T) = e^{-itH/ħ}` by the spectral
theorem (`schrodingerPropagator`). On the domain both `t ↦ U t ψ` and `t ↦ V t ψ` solve
`w' = i T w` with `w 0 = ψ`, so they agree (`hasDerivAt_generator_unique`, which needs only that
`T` is symmetric). The domain is dense and both are bounded, so `U t = V t`.

## ii. Key results

- `QuantumMechanics.SolvesSchrodinger`: `U` solves the Schrödinger equation for `H`.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.exists_solvesSchrodinger`: Stone's theorem,
  a strongly continuous unitary group has a self-adjoint Hamiltonian.
- `QuantumMechanics.schrodingerPropagator`: `e^{-itH/ħ}` for a self-adjoint `H`, by the spectral
  theorem.
- `QuantumMechanics.SolvesSchrodinger.eq_schrodingerPropagator`: a solution with `U 0 = 1` is
  `e^{-itH/ħ}`.
- `QuantumMechanics.exists_stronglyContinuousUnitaryGroup_of_solvesSchrodinger`: a solution with
  `U 0 = 1` is a strongly continuous unitary group.

## iii. References

- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer (2012), Prop 6.1
  and Thm 6.2.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `U` solves the Schrödinger equation `d/dt U t ψ = (iħ)⁻¹ H U t ψ` on the domain of `H`: for
`ψ` in the domain, every `U t ψ` is in the domain and `t ↦ U t ψ` has that derivative. -/
def SolvesSchrodinger (ħ : ℝ) (H : E →ₗ.[ℂ] E) (U : ℝ → E →L[ℂ] E) : Prop :=
  ∀ (ψ : H.domain) (t : ℝ), ∃ h : U t ψ ∈ H.domain,
    HasDerivAt (fun s => U s ψ) ((Complex.I * ħ)⁻¹ • H ⟨U t ψ, h⟩) t

open ProbabilisticTheory.QuantumMechanics ProbabilisticTheory.QuantumMechanics.Essential

/-- The orbits of `exp (i t T)` for a domain-aware spectral theorem solve `w' = i T w`. -/
lemma hasDerivAt_expUnitaryGroup_apply {T : E →ₗ.[ℂ] E} {μS : WOTSpectralMeasure ℝ E}
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : T.domain) (t : ℝ) :
    HasDerivAt (fun s => D.expUnitaryGroup s (x : E))
      (Complex.I • T ⟨D.expUnitaryGroup t (x : E), D.expUnitaryGroup_translate_mem x t⟩) t := by
  have h := D.expUnitaryGroup_hasDerivAt x t
  rwa [map_smul, ← D.expUnitaryGroup_translate x t] at h

/-- `(iħ)⁻¹ (-ħ) = i`. -/
lemma inv_I_mul_mul_neg {ħ : ℝ} (hħ : ħ ≠ 0) :
    (Complex.I * ħ)⁻¹ * ((-ħ : ℝ) : ℂ) = Complex.I := by
  have : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  rw [Complex.ofReal_neg, mul_inv, Complex.inv_I]
  field_simp

/-- **Stone's theorem.** A strongly continuous unitary group solves the Schrödinger equation for
a self-adjoint Hamiltonian, for every `ħ ≠ 0`. -/
theorem StronglyContinuousUnitaryGroup.exists_solvesSchrodinger
    (V : StronglyContinuousUnitaryGroup E) {ħ : ℝ} (hħ : ħ ≠ 0) :
    ∃ H : E →ₗ.[ℂ] E, IsSelfAdjoint H ∧ SolvesSchrodinger ħ H V.toFun := by
  have hU0 := V.map_zero
  have hUmul := V.map_add
  have hUunit := V.mem_unitary
  have hUcont := V.continuous_apply
  set T := (stoneCandidateGenerator (U := V.toFun) hUmul).closure
  set D := stoneReconstructionData hU0 hUmul hUunit hUcont
  have hV : ∀ s y, V.toFun s y = D.expUnitaryGroup s y := fun s y =>
    stoneCandidateGenerator_reconstruction hU0 hUmul hUunit hUcont y s
  refine ⟨(((-ħ : ℝ) : ℂ) • T : E →ₗ.[ℂ] E),
    isSelfAdjoint_smul_real D.isSelfAdjoint_of _ (neg_ne_zero.mpr hħ), fun ψ t => ?_⟩
  set x : T.domain := ⟨ψ, ψ.2⟩
  have hmem : V.toFun t ψ ∈ T.domain := by
    rw [hV]; exact D.expUnitaryGroup_translate_mem x t
  refine ⟨hmem, ?_⟩
  rw [LinearPMap.smul_apply, smul_smul, inv_I_mul_mul_neg hħ]
  have hsub : (⟨V.toFun t ψ, hmem⟩ : T.domain) =
      ⟨D.expUnitaryGroup t (x : E), D.expUnitaryGroup_translate_mem x t⟩ :=
    Subtype.ext (hV t ψ)
  have hfun : (fun s => V.toFun s ψ) = fun s => D.expUnitaryGroup s (x : E) :=
    funext fun s => hV s ψ
  rw [hsub, hfun]
  exact hasDerivAt_expUnitaryGroup_apply D x t

/-- `-ħ⁻¹ H` is self-adjoint if `H` is. -/
lemma isSelfAdjoint_neg_inv_smul {ħ : ℝ} (hħ : ħ ≠ 0) {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H) :
    IsSelfAdjoint ((((-ħ⁻¹ : ℝ) : ℂ) • H : E →ₗ.[ℂ] E)) :=
  isSelfAdjoint_smul_real hH _ (by simpa using hħ)

/-- The propagator `e^{-itH/ħ}` of a self-adjoint `H`, by the spectral theorem: `∫ e^{itλ} dP(λ)`
for the spectral measure `P` of `-H/ħ`. -/
def schrodingerPropagator {ħ : ℝ} (hħ : ħ ≠ 0) {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ) :
    E →L[ℂ] E :=
  (WOTSpectralMeasure.expIntegral (cayleyRealSpectralMeasure _ (isSelfAdjoint_neg_inv_smul hħ hH))
    t).toCLM

omit [CompleteSpace E] in
/-- `(iħ)⁻¹ H = i T` on the domain, for `T = -ħ⁻¹ H`. -/
lemma inv_I_mul_smul_apply {ħ : ℝ} (hħ : ħ ≠ 0) (H : E →ₗ.[ℂ] E) (y : E) (hy : y ∈ H.domain) :
    (Complex.I * ħ)⁻¹ • H ⟨y, hy⟩ =
      Complex.I • ((((-ħ⁻¹ : ℝ) : ℂ) • H : E →ₗ.[ℂ] E)) ⟨y, hy⟩ := by
  have : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  rw [LinearPMap.smul_apply, smul_smul]
  congr 1
  rw [Complex.ofReal_neg, Complex.ofReal_inv, mul_inv, Complex.inv_I]
  field_simp

/-- `e^{-itH/ħ}` solves the Schrödinger equation for `H`. -/
theorem solvesSchrodinger_schrodingerPropagator {ħ : ℝ} (hħ : ħ ≠ 0) {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) : SolvesSchrodinger ħ H (schrodingerPropagator hħ hH) := by
  set D := unboundedSpectralTheorem _ (isSelfAdjoint_neg_inv_smul hħ hH)
  intro ψ t
  have hmem := D.expUnitaryGroup_translate_mem ψ t
  refine ⟨hmem, ?_⟩
  have h := hasDerivAt_expUnitaryGroup_apply D ψ t
  rw [← inv_I_mul_smul_apply hħ H _ hmem] at h
  exact h

lemma schrodingerPropagator_zero {ħ : ℝ} (hħ : ħ ≠ 0) {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H) :
    schrodingerPropagator hħ hH 0 = 1 := by
  rw [schrodingerPropagator, WOTSpectralMeasure.expIntegral_zero]
  rfl

/-- **Uniqueness of the propagator.** A family of bounded operators with `U 0 = 1` that solves the
Schrödinger equation for a self-adjoint `H` is `e^{-itH/ħ}`. -/
theorem SolvesSchrodinger.eq_schrodingerPropagator {ħ : ℝ} {H : E →ₗ.[ℂ] E} {U : ℝ → E →L[ℂ] E}
    (hU : SolvesSchrodinger ħ H U) (hħ : ħ ≠ 0) (hH : IsSelfAdjoint H) (hU0 : U 0 = 1) (t : ℝ) :
    U t = schrodingerPropagator hħ hH t := by
  have hT := isSelfAdjoint_neg_inv_smul hħ hH
  set D := unboundedSpectralTheorem _ hT
  have hHT := inv_I_mul_smul_apply hħ H
  have hsym := LinearPMap.IsSelfAdjoint.isSymmetric hT
  have heq_dom : ∀ (x : H.domain) (t : ℝ), U t x = D.expUnitaryGroup t (x : E) := by
    intro x t
    choose hmem hder using hU x
    exact hasDerivAt_generator_unique hsym (y := fun s => U s x) hmem
      (fun s => D.expUnitaryGroup_translate_mem x s)
      (fun s => by rw [← hHT _ (hmem s)]; exact hder s)
      (fun s => hasDerivAt_expUnitaryGroup_apply D x s) (by simp [hU0]) t
  exact ContinuousLinearMap.ext fun x => congrFun (Continuous.ext_on hT.dense_domain
    (U t).continuous (schrodingerPropagator hħ hH t).continuous fun ξ hξ => heq_dom ⟨ξ, hξ⟩ t) x

/-- **Stone's theorem, converse.** A family of bounded operators with `U 0 = 1` that solves the
Schrödinger equation for a self-adjoint `H` is a strongly continuous unitary group. -/
theorem exists_stronglyContinuousUnitaryGroup_of_solvesSchrodinger {ħ : ℝ} (hħ : ħ ≠ 0)
    {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H) {U : ℝ → E →L[ℂ] E} (hU0 : U 0 = 1)
    (hU : SolvesSchrodinger ħ H U) :
    ∃ V : StronglyContinuousUnitaryGroup E, V.toFun = U := by
  set D := unboundedSpectralTheorem _ (isSelfAdjoint_neg_inv_smul hħ hH)
  have heq : ∀ t, U t = ContinuousLinearMapWOT.toCLM (D.expUnitaryGroup t) :=
    hU.eq_schrodingerPropagator hħ hH hU0
  refine ⟨⟨U, fun t => ?_, hU0, fun s t => ?_, fun x => ?_⟩, rfl⟩
  · have h := Unitary.mem_iff.mp (D.expUnitaryGroup.unitary t)
    rw [heq t, Unitary.mem_iff]
    exact ⟨congrArg ContinuousLinearMapWOT.toCLM h.1, congrArg ContinuousLinearMapWOT.toCLM h.2⟩
  · rw [heq, heq, heq, D.expUnitaryGroup.add]; rfl
  · simp_rw [heq]; exact D.expUnitaryGroup.continuous_apply x

/-- Every strongly continuous unitary group is `t ↦ ∫ e^{itx} dμS(x)` for a projection-valued
measure `μS` on `ℝ`, by Stone's theorem. -/
theorem StronglyContinuousUnitaryGroup.exists_expIntegral (V : StronglyContinuousUnitaryGroup E) :
    ∃ μS : WOTSpectralMeasure ℝ E, ∀ t, V.toFun t = (WOTSpectralMeasure.expIntegral μS t).toCLM :=
  ⟨_, fun t => ContinuousLinearMap.ext fun y => stoneCandidateGenerator_reconstruction V.map_zero
    V.map_add V.mem_unitary V.continuous_apply y t⟩

end QuantumMechanics
