/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import HilbertUnphysicality.FurtherResults.FrameCutoffs

/-!
# Further results: the covariantly transported position is well defined in every frame

Not part of the brief. This file formalizes Sec. 3 of `further-results.tex` in the brief's
directory.

In Proposition 3 the position in the frame `y = e(x)` is `Y`, multiplication by the new
coordinate `y`. The module `FrameCutoffs` shows that no nonzero state keeps `Y` well defined in
every smooth frame under the free evolution. This module reads the position covariantly instead:
in the frame `y = e(x)` it is `U_e X U_e⁻¹`, the operator that the frame change `U_e` makes of
`X`. Then the obstruction disappears.

1. `U_e X U_e⁻¹` is multiplication by the old coordinate `e⁻¹(y)`, with domain `U_e D(X)`
   (`covariantPosition_eq`). It is self-adjoint, and `U_e` carries the expectation and the
   second moment of `X` in `ψ` to those of `U_e X U_e⁻¹` in `U_e ψ`.
2. So `U_e ψ` lies in the domain of the covariant position in every smooth frame if and only if
   `ψ ∈ D(X)` (`forall_mem_domain_covariantPosition_iff`), where `FrameCutoffs` demands a cutoff.
3. The free evolution maps Schwartz states to Schwartz states (`freeEvolution_toLp`). Every
   Schwartz state therefore keeps the covariant position well defined in every smooth frame at
   every time (`forall_frames_freeEvolution_toLp`), and nonzero ones exist
   (`exists_forall_frames_freeEvolution`), where `FrameCutoffs` leaves only `ψ = 0`.

The failure of [B]WDQ in Proposition 3 is thus a property of the coordinate observable `Y`, not
of the Hilbert space: every frame change is unitary, and the observable that transforms with the
frame stays well defined. For the change of frame `y = tan(π/2 · erf x)` of the brief, item 1 is
`conjLinearPMap_frameUnitary_positionOp` in the brief's main file.

The comparator lane, which certifies the main file of the brief, does not depend on this module.

## Main results

* `covariantPosition`, `covariantPosition_eq`, `isSelfAdjoint_covariantPosition`: the position
  `U_e X U_e⁻¹` of the frame `y = e(x)`;
* `covariantPosition_apply`, `inner_covariantPosition`, `norm_covariantPosition`: `U_e` carries
  `X ψ`, `⟪ψ, X ψ⟫` and `‖X ψ‖` to the frame `e`;
* `forall_mem_domain_covariantPosition_iff`: well defined in every smooth frame iff `ψ ∈ D(X)`;
* `freeEvolution_toLp`: the free evolution of a Schwartz state is a Schwartz state;
* `forall_frames_freeEvolution_toLp`, `exists_forall_frames_freeEvolution`: Schwartz states keep
  the covariant position well defined in every smooth frame at every time.
-/

open MeasureTheory SchwartzMap QuantumMechanics FourierTransform
open scoped ContDiff

@[expose] public noncomputable section

namespace HilbertUnphysicality.FurtherResults

/-! ### The covariant position -/

section Covariant

variable (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm)

/-- The position of the frame `y = e(x)`, transported covariantly: `U_e X U_e⁻¹`. -/
def covariantPosition : L2R →ₗ.[ℂ] L2R :=
  conjLinearPMap (smoothFrameChange e he he') positionOp

/-- `U_e X U_e⁻¹` is multiplication by the old coordinate `e⁻¹(y)`, on `U_e D(X)`. -/
theorem covariantPosition_eq :
    covariantPosition e he he' = L2.mulOp fun y => e.symm y := by
  have hg : Differentiable ℝ (e.symm.toEquiv : ℝ → ℝ) := he'.differentiable (by simp)
  have hg' : Differentiable ℝ (e.symm.toEquiv.symm : ℝ → ℝ) := by
    simpa using he.differentiable (by simp)
  have hmem (ψ : L2R) : smoothFrameChange e he he' ψ ∈ L2.mulDomain (fun y => e.symm y) ↔
      ψ ∈ positionOp.domain :=
    Lp.compDiffeo_mem_mulDomain_iff (a := fun x : ℝ => x) hg hg' measurable_id
  unfold covariantPosition
  refine LinearPMap.ext (Submodule.ext fun ψ => ?_) fun ψ _ _ => ?_
  · rw [mem_domain_conjLinearPMap, ← hmem, LinearIsometryEquiv.apply_symm_apply]
    rfl
  · rw [conjLinearPMap_apply]
    refine (Lp.compDiffeo_mulOp (a := fun x : ℝ => x) hg hg' measurable_id _).trans ?_
    congr 1
    exact Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)

/-- `U_e X U_e⁻¹` is self-adjoint. -/
theorem isSelfAdjoint_covariantPosition : IsSelfAdjoint (covariantPosition e he he') :=
  isSelfAdjoint_positionOp.conjLinearPMap

/-- `U_e ψ` is in the domain of the covariant position iff `ψ ∈ D(X)`. -/
theorem mem_domain_covariantPosition_iff (ψ : L2R) :
    smoothFrameChange e he he' ψ ∈ (covariantPosition e he he').domain ↔ ψ ∈ positionDomain := by
  rw [covariantPosition, mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- `U_e X U_e⁻¹ (U_e ψ) = U_e (X ψ)`. -/
theorem covariantPosition_apply (ψ : positionOp.domain) :
    covariantPosition e he he' ⟨smoothFrameChange e he he' ψ,
      (mem_domain_covariantPosition_iff e he he' ψ).2 ψ.2⟩ =
      smoothFrameChange e he he' (positionOp ψ) := by
  change conjLinearPMap (smoothFrameChange e he he') positionOp
    ⟨smoothFrameChange e he he' ψ, _⟩ = _
  rw [conjLinearPMap_apply]
  congr 2
  exact Subtype.ext (LinearIsometryEquiv.symm_apply_apply _ _)

/-- The expectation of the position is the same in every frame: `⟪U_e ψ, U_e X U_e⁻¹ U_e ψ⟫ =
⟪ψ, X ψ⟫`. -/
theorem inner_covariantPosition (ψ : positionOp.domain) :
    inner ℂ (smoothFrameChange e he he' ψ) (covariantPosition e he he'
      ⟨smoothFrameChange e he he' ψ, (mem_domain_covariantPosition_iff e he he' ψ).2 ψ.2⟩) =
      inner ℂ (ψ : L2R) (positionOp ψ) := by
  rw [covariantPosition_apply, LinearIsometryEquiv.inner_map_map]

/-- So is the second moment: `‖U_e X U_e⁻¹ U_e ψ‖ = ‖X ψ‖`. -/
theorem norm_covariantPosition (ψ : positionOp.domain) :
    ‖covariantPosition e he he'
      ⟨smoothFrameChange e he he' ψ, (mem_domain_covariantPosition_iff e he he' ψ).2 ψ.2⟩‖ =
      ‖positionOp ψ‖ := by
  rw [covariantPosition_apply, LinearIsometryEquiv.norm_map]

end Covariant

/-- **The covariant counterpart of Part 1.** A state lies in the domain of the covariant position
in every smooth frame if and only if it lies in `D(X)`. Read with `Y`, the same demand forces a
cutoff (`forall_smoothFrameChange_mem_positionDomain_iff`). -/
theorem forall_mem_domain_covariantPosition_iff (ψ : L2R) :
    (∀ (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm),
      smoothFrameChange e he he' ψ ∈ (covariantPosition e he he').domain) ↔
      ψ ∈ positionDomain :=
  ⟨fun h => (mem_domain_covariantPosition_iff (Homeomorph.refl ℝ) contDiff_id contDiff_id ψ).1
      (h _ contDiff_id contDiff_id),
    fun h e he he' => (mem_domain_covariantPosition_iff e he he' ψ).2 h⟩

/-! ### The free evolution of Schwartz states -/

section Schwartz

/-- The phase `e^{-2iπ²ξ²t}` of the free evolution in momentum space has temperate growth. -/
lemma hasTemperateGrowth_kineticPhase (t : ℝ) :
    (fun ξ : ℝ => lp.phase (2 * Real.pi ^ 2 * ξ ^ 2) t).HasTemperateGrowth := by
  have hφ : (fun ξ : ℝ => -(2 * Real.pi ^ 2 * ξ ^ 2 * t)).HasTemperateGrowth := by fun_prop
  exact Complex.hasTemperateGrowth_exp_mul_I.comp hφ

/-- The free evolution of a Schwartz state is the Schwartz state
`𝓕⁻¹ (e^{-2iπ²ξ²t} 𝓕 f)`. -/
theorem freeEvolution_toLp (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    freeEvolution t (f.toLp 2) = (fourierMultiplierCLM ℂ
      (fun ξ : ℝ => lp.phase (2 * Real.pi ^ 2 * ξ ^ 2) t) f).toLp 2 := by
  have h1 : fourierL2 (f.toLp 2) = (𝓕 f).toLp 2 := toLp_fourier_eq f
  have h2 : L2.mulEvolution measurable_kinetic t ((𝓕 f).toLp 2) =
      (smulLeftCLM ℂ (fun ξ : ℝ => lp.phase (2 * Real.pi ^ 2 * ξ ^ 2) t) (𝓕 f)).toLp 2 := by
    refine Lp.ext ?_
    filter_upwards [L2.coeFn_mulEvolution measurable_kinetic t ((𝓕 f).toLp 2),
      (𝓕 f).coeFn_toLp 2 volume,
      (smulLeftCLM ℂ (fun ξ : ℝ => lp.phase (2 * Real.pi ^ 2 * ξ ^ 2) t) (𝓕 f)).coeFn_toLp 2
        volume] with ξ e1 e2 e3
    rw [e1, e2, e3, smulLeftCLM_apply_apply (hasTemperateGrowth_kineticPhase t), smul_eq_mul]
  rw [freeEvolution_apply, h1, h2, fourierMultiplierCLM_apply]
  exact toLp_fourierInv_eq _

/-- The free evolution keeps Schwartz states in `D(X)`. -/
theorem freeEvolution_toLp_mem_positionDomain (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    freeEvolution t (f.toLp 2) ∈ positionDomain := by
  rw [freeEvolution_toLp]
  exact toLp_mem_positionDomain _

/-- **The covariant counterpart of Parts 1 and 2.** A Schwartz state lies in the domain of the
covariant position in every smooth frame at every time. -/
theorem forall_frames_freeEvolution_toLp (f : 𝓢(ℝ, ℂ)) (t : ℝ) (e : ℝ ≃ₜ ℝ)
    (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm) :
    smoothFrameChange e he he' (freeEvolution t (f.toLp 2)) ∈
      (covariantPosition e he he').domain :=
  (mem_domain_covariantPosition_iff e he he' _).2 (freeEvolution_toLp_mem_positionDomain f t)

/-- A nonzero Schwartz state: a smooth bump. -/
lemma exists_toLp_ne_zero : ∃ f : 𝓢(ℝ, ℂ), f.toLp 2 ≠ 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hs : HasCompactSupport fun x => ((b x : ℝ) : ℂ) :=
    b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hd : ContDiff ℝ ∞ fun x => ((b x : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨hs.toSchwartzMap hd, fun h0 => ?_⟩
  have hae : ((hs.toSchwartzMap hd : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =ᵐ[volume] 0 := by
    filter_upwards [(hs.toSchwartzMap hd).coeFn_toLp 2 volume,
      Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h1 h2
    rw [← h1, h0, h2]
  have hf0 := congrFun ((Continuous.ae_eq_iff_eq volume (hs.toSchwartzMap hd).continuous
    continuous_zero).1 hae) 0
  change ((b 0 : ℝ) : ℂ) = 0 at hf0
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), Complex.ofReal_one] at hf0
  exact one_ne_zero hf0

/-- **Contrast with `not_forall_frames_freeEvolution`.** Some nonzero Schwartz state keeps the
covariant position well defined in every smooth frame at every time. -/
theorem exists_forall_frames_freeEvolution :
    ∃ f : 𝓢(ℝ, ℂ), f.toLp 2 ≠ 0 ∧ ∀ (t : ℝ) (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e)
      (he' : ContDiff ℝ ∞ e.symm),
      smoothFrameChange e he he' (freeEvolution t (f.toLp 2)) ∈
        (covariantPosition e he he').domain := by
  obtain ⟨f, hf⟩ := exists_toLp_ne_zero
  exact ⟨f, hf, forall_frames_freeEvolution_toLp f⟩

end Schwartz

end HilbertUnphysicality.FurtherResults
