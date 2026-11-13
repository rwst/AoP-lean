/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.CStarAlgebra.Commutator
public import ForMathlib.Analysis.Calculus.Deriv.Tendsto
public import ForPhyslib.QuantumMechanics.Dephasing
public import ForPhyslib.QuantumMechanics.PurePointSpectralMeasure
public import ForPhyslib.QuantumMechanics.TraceNorm
public import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint

/-!
# Compact operators commuting with an observable live on its point spectrum

## i. Overview

Let `X` be a bounded self-adjoint operator. Its *point-spectral subspace* `H_pp`
(`pointSubspace X`) is the closed span of its eigenvectors; `X` has pure point spectrum exactly
when `H_pp` is the whole space (`hasPurePointSpectrum_iff_pointSubspace_eq_top`).

**A compact operator commuting with `X` has range in `H_pp`**
(`apply_mem_pointSubspace_of_commute`). For a compact self-adjoint `ρ`, every eigenspace of `ρ`
for a nonzero eigenvalue is finite dimensional and invariant under `X`. On it `X` restricts to a
symmetric operator on a finite-dimensional space, which diagonalizes, so the eigenspace lies in
`H_pp`. The eigenspaces of `ρ` span a dense subspace, by the spectral theorem for compact
self-adjoint operators, so `ρ` maps everything into `H_pp`. A general compact `ρ` commuting with
`X` is a combination of two compact self-adjoint ones, `ρ + ρ†` and `i (ρ† - ρ)`.

Consequences:
* trace-class operators, in particular density operators, commuting with `X` live on `H_pp`
  (`apply_mem_pointSubspace_of_isTraceClass`);
* a compact operator commuting with `X` and supported on a spectral sector `S` without atoms,
  `μ_S(S ∩ {a}) = 0` for every `a`, vanishes (`eq_zero_of_spectralMeasureProj_mul_eq`); if the
  spectral measure has no atoms at all, `H_pp = 0`
  (`pointSubspace_eq_bot_of_spectralMeasureProj_singleton`);
* the equilibria of the dephasing equation `L(σ) = X σ X - ½ {X², σ} = 0` are exactly the
  operators commuting with `X`, for every bounded self-adjoint `X`
  (`dephasingGenerator_eq_zero_iff_commute`, from the C⋆-algebra fact that `[X, [X, σ]] = 0`
  forces `[X, σ] = 0`); so compact equilibria live on `H_pp`;
* a limit of a solution of the dephasing equation, in operator norm or in trace norm, is an
  equilibrium (`dephasingGenerator_eq_zero_of_tendsto`,
  `dephasingGenerator_eq_zero_of_tendsto_traceENorm`).

## ii. Table of contents

- A. Equilibria of the dephasing equation
- B. The point-spectral subspace
- C. Compact operators commuting with `X`
- D. Spectral sectors without atoms
- E. Limits of the dephasing flow
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal
open Filter Set Topology Module End ProbabilisticTheory

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {X : E →L[ℂ] E}

/-! ## A. Equilibria of the dephasing equation -/

omit [CompleteSpace E] in
/-- `L(σ) = -½ [X, [X, σ]]`. -/
lemma dephasingGenerator_eq_commutator (X σ : E →L[ℂ] E) :
    dephasingGenerator X σ = (-(2⁻¹ : ℝ)) • (X * (X * σ - σ * X) - (X * σ - σ * X) * X) := by
  rw [dephasingGenerator_apply]
  simp only [mul_sub, sub_mul, ← mul_assoc]
  module

/-- **Equilibria of the dephasing equation**: for a bounded self-adjoint `X`, `L(σ) = 0` iff `σ`
commutes with `X`. -/
theorem dephasingGenerator_eq_zero_iff_commute (hX : IsSelfAdjoint X) {σ : E →L[ℂ] E} :
    dephasingGenerator X σ = 0 ↔ Commute σ X := by
  rw [dephasingGenerator_eq_commutator, smul_eq_zero, sub_eq_zero]
  simp only [neg_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  constructor
  · exact fun h => (hX.commute_of_commute_commutator h).symm
  · intro h
    rw [h.eq, sub_self, mul_zero, zero_mul]

/-! ## B. The point-spectral subspace -/

/-- The point-spectral subspace `H_pp` of `X`: the closed span of its eigenvectors. -/
def pointSubspace (X : E →L[ℂ] E) : Submodule ℂ E :=
  (⨆ a : ℝ, (X - (a : ℂ) • (1 : E →L[ℂ] E)).ker).topologicalClosure

omit [CompleteSpace E] in
lemma hasPurePointSpectrum_iff_pointSubspace_eq_top :
    HasPurePointSpectrum X ↔ pointSubspace X = ⊤ :=
  top_le_iff

omit [CompleteSpace E] in
lemma isClosed_pointSubspace (X : E →L[ℂ] E) : IsClosed (pointSubspace X : Set E) :=
  Submodule.isClosed_topologicalClosure _

omit [CompleteSpace E] in
lemma mem_pointSubspace_of_apply_eq {a : ℝ} {v : E} (hv : X v = (a : ℂ) • v) :
    v ∈ pointSubspace X :=
  Submodule.le_topologicalClosure _ (Submodule.mem_iSup_of_mem a (mem_ker_sub_smul_one.mpr hv))

/-- A finite-dimensional subspace invariant under a self-adjoint `X` lies in `H_pp`. -/
theorem le_pointSubspace (hX : IsSelfAdjoint X) {V : Submodule ℂ E} [FiniteDimensional ℂ V]
    (hV : ∀ v ∈ V, X v ∈ V) : V ≤ pointSubspace X := by
  set T := (X : E →ₗ[ℂ] E).restrict hV
  have hT : T.IsSymmetric := hX.isSymmetric.restrict_invariant hV
  have htop : (⨆ μ, eigenspace T μ) = ⊤ :=
    Submodule.orthogonal_eq_bot_iff.mp hT.orthogonalComplement_iSup_eigenspaces_eq_bot
  intro w hw
  have hw' : (⟨w, hw⟩ : V) ∈ ⨆ μ, eigenspace T μ := htop ▸ Submodule.mem_top
  refine Submodule.iSup_induction (motive := fun u : V => (u : E) ∈ pointSubspace X) _ hw' ?_
    (by simp) fun u u' hu hu' => by
      rw [Submodule.coe_add]
      exact add_mem hu hu'
  intro μ u hu
  by_cases h0 : u = 0
  · simp [h0]
  have hXu : X u = μ • (u : E) := congrArg Subtype.val (mem_eigenspace_iff.mp hu)
  have hμ := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hu, h0⟩)
  have hre : ((μ.re : ℝ) : ℂ) = μ := Complex.conj_eq_iff_re.mp hμ
  exact mem_pointSubspace_of_apply_eq (a := μ.re) (by rw [hXu, hre])

/-! ## C. Compact operators commuting with `X` -/

variable {ρ : E →L[ℂ] E}

/-- An eigenspace of a compact `ρ` commuting with `X`, for a nonzero eigenvalue, lies in `H_pp`. -/
lemma eigenspace_le_pointSubspace (hX : IsSelfAdjoint X) (hρ : IsCompactOperator ρ)
    (hc : Commute ρ X) {μ : ℂ} (hμ : μ ≠ 0) :
    eigenspace (ρ : E →ₗ[ℂ] E) μ ≤ pointSubspace X := by
  have := ContinuousLinearMap.finite_dimensional_eigenspace hρ μ hμ
  refine le_pointSubspace hX fun v hv => ?_
  rw [mem_eigenspace_iff] at hv ⊢
  change ρ (X v) = μ • X v
  calc ρ (X v) = (ρ * X) v := rfl
    _ = X (ρ v) := by rw [hc.eq]; rfl
    _ = μ • X v := by rw [show ρ v = μ • v from hv, map_smul]

lemma apply_mem_pointSubspace_of_isSelfAdjoint (hX : IsSelfAdjoint X) (hρ : IsCompactOperator ρ)
    (hs : IsSelfAdjoint ρ) (hc : Commute ρ X) (v : E) : ρ v ∈ pointSubspace X := by
  set W := ⨆ μ, eigenspace (ρ : E →ₗ[ℂ] E) μ
  have hW : W.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hρ hs.isSymmetric)
  have hv : v ∈ closure (W : Set E) := by
    rw [← Submodule.topologicalClosure_coe, hW]
    trivial
  have hmaps : MapsTo ρ (W : Set E) (pointSubspace X) := by
    intro w hw
    refine Submodule.iSup_induction _ (motive := fun w => ρ w ∈ pointSubspace X) hw ?_
      (by rw [map_zero]; exact zero_mem _) fun x y hx hy => by
        rw [map_add]
        exact add_mem hx hy
    intro μ u hu
    rw [show ρ u = μ • u from mem_eigenspace_iff.mp hu]
    by_cases hμ : μ = 0
    · rw [hμ, zero_smul]
      exact zero_mem _
    · exact Submodule.smul_mem _ _ (eigenspace_le_pointSubspace hX hρ hc hμ hu)
  have h := map_mem_closure ρ.continuous hv hmaps
  rwa [(isClosed_pointSubspace X).closure_eq] at h

/-- **A compact operator commuting with `X` has range in the point-spectral subspace.** -/
theorem apply_mem_pointSubspace_of_commute (hX : IsSelfAdjoint X) (hρ : IsCompactOperator ρ)
    (hc : Commute ρ X) (v : E) : ρ v ∈ pointSubspace X := by
  have hc' : Commute (star ρ) X := by simpa [hX.star_eq] using hc.star_star
  set R := ρ + star ρ
  set S := Complex.I • (star ρ - ρ)
  have hR : IsSelfAdjoint R := by simp [R, IsSelfAdjoint, add_comm]
  have hS : IsSelfAdjoint S := by
    simp only [S, IsSelfAdjoint, star_smul, star_sub, star_star, Complex.star_def,
      Complex.conj_I]
    rw [neg_smul, ← smul_neg, neg_sub]
  have hRc : IsCompactOperator R := by
    rw [show ⇑R = ⇑ρ + ⇑(star ρ) from FunLike.coe_add _ _]
    exact hρ.add hρ.star
  have hSc : IsCompactOperator S := by
    rw [show ⇑S = Complex.I • (⇑(star ρ) - ⇑ρ) by
      rw [← FunLike.coe_sub, ← FunLike.coe_smul]]
    exact (hρ.star.sub hρ).smul _
  have hRv := apply_mem_pointSubspace_of_isSelfAdjoint hX hRc hR (hc.add_left hc') v
  have hSv := apply_mem_pointSubspace_of_isSelfAdjoint hX hSc hS
    ((hc'.sub_left hc).smul_left _) v
  have h2 : R v + Complex.I • S v = (2 : ℂ) • ρ v := by
    simp only [R, S, add_apply, smul_apply,
      sub_apply, smul_smul, Complex.I_mul_I]
    module
  have h : ρ v = (2 : ℂ)⁻¹ • (R v + Complex.I • S v) := by
    rw [h2, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (add_mem hRv (Submodule.smul_mem _ _ hSv))

/-- A trace-class operator commuting with `X`, in particular a density operator, has range in the
point-spectral subspace. -/
theorem apply_mem_pointSubspace_of_isTraceClass (hX : IsSelfAdjoint X) (hρ : IsTraceClass ρ)
    (hc : Commute ρ X) (v : E) : ρ v ∈ pointSubspace X :=
  apply_mem_pointSubspace_of_commute hX hρ.isCompactOperator hc v

/-- Without eigenvectors, no nonzero compact operator commutes with `X`. -/
theorem eq_zero_of_commute_of_pointSubspace_eq_bot (hX : IsSelfAdjoint X)
    (h : pointSubspace X = ⊥) (hρ : IsCompactOperator ρ) (hc : Commute ρ X) : ρ = 0 :=
  ContinuousLinearMap.ext fun v => by
    simpa [h] using apply_mem_pointSubspace_of_commute hX hρ hc v

/-! ## D. Spectral sectors without atoms -/

lemma spectralMeasureProj_mul (hX : IsSelfAdjoint X) {S T : Set ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) :
    spectralMeasureProj hX S * spectralMeasureProj hX T = spectralMeasureProj hX (S ∩ T) := by
  ext w
  exact congrArg (fun A : E →WOT[ℂ] E => A w)
    ((ProbabilisticTheory.QuantumMechanics.boundedSelfAdjointSpectralMeasure X hX).comp_eq_of_inter
      hS hT)

/-- A spectral projection `μ_S(S)` onto a sector without atoms vanishes on `H_pp`. -/
theorem spectralMeasureProj_apply_eq_zero (hX : IsSelfAdjoint X) {S : Set ℝ}
    (hS : MeasurableSet S) (hatom : ∀ a, spectralMeasureProj hX (S ∩ {a}) = 0) {v : E}
    (hv : v ∈ pointSubspace X) : spectralMeasureProj hX S v = 0 := by
  have hle : pointSubspace X ≤ (spectralMeasureProj hX S).ker := by
    refine Submodule.topologicalClosure_minimal _ (iSup_le fun a w hw => ?_)
      (ContinuousLinearMap.isClosed_ker _)
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ← spectralMeasureProj_singleton_apply_of_apply_eq hX (mem_ker_sub_smul_one.mp hw),
      ← mul_apply_eq_comp, spectralMeasureProj_mul hX hS (measurableSet_singleton a),
      hatom, zero_apply]
  exact hle hv

/-- If the spectral measure of `X` has no atoms, `X` has no eigenvectors: `H_pp = 0`. -/
theorem pointSubspace_eq_bot_of_spectralMeasureProj_singleton (hX : IsSelfAdjoint X)
    (hatom : ∀ a, spectralMeasureProj hX {a} = 0) : pointSubspace X = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h := spectralMeasureProj_apply_eq_zero hX MeasurableSet.univ (by simpa using hatom) hv
  have hu : spectralMeasureProj hX univ = 1 := by
    ext w
    exact congrArg (fun A : E →WOT[ℂ] E => A w)
      (ProbabilisticTheory.QuantumMechanics.boundedSelfAdjointSpectralMeasure X hX).univ
  rw [hu, one_apply_eq_self] at h
  simp [h]

/-- **No compact operator lives on a non-atomic spectral sector**: if `ρ` is compact, commutes
with `X`, and is supported on a sector `S` with `μ_S(S ∩ {a}) = 0` for every `a`, then `ρ = 0`. -/
theorem eq_zero_of_spectralMeasureProj_mul_eq (hX : IsSelfAdjoint X) {S : Set ℝ}
    (hS : MeasurableSet S) (hatom : ∀ a, spectralMeasureProj hX (S ∩ {a}) = 0)
    (hρ : IsCompactOperator ρ) (hc : Commute ρ X) (hρS : spectralMeasureProj hX S * ρ = ρ) :
    ρ = 0 := by
  ext v
  rw [← hρS, mul_apply_eq_comp, zero_apply]
  exact spectralMeasureProj_apply_eq_zero hX hS hatom
    (apply_mem_pointSubspace_of_commute hX hρ hc v)

/-! ## E. Limits of the dephasing flow -/

lemma continuous_dephasingGenerator (X : E →L[ℂ] E) : Continuous (dephasingGenerator X) := by
  simp only [funext (dephasingGenerator_apply X)]
  fun_prop

/-- **Limits of the dephasing flow are equilibria**: if a solution of `ρ' = L(ρ)` for `t > 0`
converges in operator norm, its limit `σ` has `L(σ) = 0`. -/
theorem dephasingGenerator_eq_zero_of_tendsto {r : ℝ → E →L[ℂ] E} {σ : E →L[ℂ] E}
    (hr : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hσ : Tendsto r atTop (𝓝 σ)) : dephasingGenerator X σ = 0 :=
  eq_zero_of_tendsto_of_hasDerivAt ((eventually_gt_atTop 0).mono hr) hσ
    (((continuous_dephasingGenerator X).tendsto σ).comp hσ)

/-- A trace-norm limit of a solution of the dephasing equation is an equilibrium. -/
theorem dephasingGenerator_eq_zero_of_tendsto_traceENorm {r : ℝ → E →L[ℂ] E} {σ : E →L[ℂ] E}
    (hr : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hσ : Tendsto (fun t => traceENorm (r t - σ)) atTop (𝓝 0)) : dephasingGenerator X σ = 0 :=
  dephasingGenerator_eq_zero_of_tendsto hr (tendsto_of_tendsto_traceENorm hσ)

end QuantumMechanics
