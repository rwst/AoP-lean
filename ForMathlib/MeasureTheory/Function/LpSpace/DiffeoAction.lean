/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.MeasureTheory.Function.JacobianDensity
public import ForMathlib.MeasureTheory.Function.L2Multiplication
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Diffeomorphisms act isometrically on `Lᵖ`

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let
`1 ≤ p < ∞`. Elements of `Lᵖ(E, μ)` transform as densities of weight `1/p`: for `e` in
`Equiv.Perm.diffeoGroup E`,

  `(U_e ψ)(x) = |det D(e⁻¹)(x)|^{1/p} • ψ(e⁻¹ x)`.

Then `e ↦ U_e` is a group homomorphism into the linear isometry equivalences of `Lᵖ(E, μ)`. For
`p = 2` this is the unitary representation by which changes of coordinates act on wave functions,
and `U_{e⁻¹} ψ = |det De|^{1/2} • (ψ ∘ e)` is the half-density pullback. The unitary carries
multiplication by `a` to multiplication by `a ∘ e⁻¹`: it transports multiplication operators
covariantly. On `ℝ`, `MeasureTheory.Lp.compDiffeo` is the same pullback `U_{e⁻¹}`, written with
`√|g'|`.

## Main definitions

* `MeasureTheory.Lp.diffeoRep hp`: the homomorphism `e ↦ U_e`.

## Main results

* `MeasureTheory.quasiMeasurePreserving_of_mem_diffeoGroup`: `e` and `e⁻¹` preserve null sets;
* `MeasureTheory.eLpNorm_pullback`: the pullback of weight `1/p` preserves the `Lᵖ` norm;
* `MeasureTheory.Lp.coeFn_diffeoRep`, `MeasureTheory.Lp.coeFn_diffeoRep_inv`: the formulas for
  `U_e` and `U_{e⁻¹}`;
* `MeasureTheory.Lp.diffeoRep_mem_mulDomain_iff`, `MeasureTheory.Lp.diffeoRep_mulOp`: on `L²`,
  `U_e` maps the domain of multiplication by `a` onto that of multiplication by `a ∘ e⁻¹`, and
  `U_e (a ψ) = (a ∘ e⁻¹) (U_e ψ)`.
-/

open Set Filter Equiv Equiv.Perm MeasureTheory
open scoped ENNReal

@[expose] public noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace MeasureTheory

/-- Elements of `diffeoGroup E` preserve null sets in both directions. -/
theorem quasiMeasurePreserving_of_mem_diffeoGroup (e : diffeoGroup E) :
    QuasiMeasurePreserving (e : Perm E) μ μ := by
  have hm := (differentiable_of_mem_diffeoGroup e).continuous.measurable
  refine ⟨hm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hm hs, ← (e : Perm E).image_symm_eq_preimage]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    (differentiable_symm_of_mem_diffeoGroup e).differentiableOn h0

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem measurable_abs_det_fderiv_rpow [FiniteDimensional ℝ E] [BorelSpace E] (a : E → E)
    (w : ℝ) : Measurable fun x => |(fderiv ℝ a x).det| ^ w :=
  (continuous_abs.measurable.comp
    (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ a))).pow_const w

end MeasureTheory

namespace Density

theorem pullback_congr_ae (w : ℝ) (e : diffeoGroup E) {f g : E → F} (h : f =ᵐ[μ] g) :
    pullback w (e : Perm E) f =ᵐ[μ] pullback w (e : Perm E) g := by
  filter_upwards [(quasiMeasurePreserving_of_mem_diffeoGroup e).ae_eq_comp h] with x hx
  simp only [pullback, Function.comp_apply] at hx ⊢
  rw [hx]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem pullback_add (w : ℝ) (a : E → E) (f g : E → F) :
    pullback w a (f + g) = pullback w a f + pullback w a g := by
  ext x
  simp [pullback, smul_add]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem pullback_smul {R : Type*} [SMul R F] [SMulCommClass ℝ R F] (w : ℝ) (a : E → E) (c : R)
    (f : E → F) : pullback w a (c • f) = c • pullback w a f := by
  ext x
  simp [pullback, smul_comm _ c]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pulling back by `e` undoes pulling back by `e⁻¹`. -/
theorem pullback_pullback_symm (w : ℝ) (e : diffeoGroup E) (f : E → F) :
    pullback w (e : Perm E) (pullback w (e : Perm E).symm f) = f := by
  rw [← pullback_comp w (differentiable_symm_of_mem_diffeoGroup e)
    (differentiable_of_mem_diffeoGroup e),
    show ((e : Perm E).symm ∘ (e : Perm E) : E → E) = id from
      funext (e : Perm E).symm_apply_apply, pullback_id]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pulling back by `e⁻¹` undoes pulling back by `e`. -/
theorem pullback_symm_pullback (w : ℝ) (e : diffeoGroup E) (f : E → F) :
    pullback w (e : Perm E).symm (pullback w (e : Perm E) f) = f :=
  pullback_pullback_symm w e⁻¹ f

variable (μ)

theorem aestronglyMeasurable_pullback (w : ℝ) (e : diffeoGroup E) {f : E → F}
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (pullback w (e : Perm E) f) μ :=
  (measurable_abs_det_fderiv_rpow _ w).aestronglyMeasurable.smul
    (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_of_mem_diffeoGroup e))

end Density

open Density

namespace MeasureTheory

variable (μ) {p : ℝ≥0∞}

/-- The pullback of weight `1/p` preserves the `Lᵖ` norm. -/
theorem eLpNorm_pullback (hp0 : p ≠ 0) (hp : p ≠ ∞) (e : diffeoGroup E) {f : E → F}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm (pullback p.toReal⁻¹ (e : Perm E) f) p μ = eLpNorm f p μ := by
  have hp' : p.toReal ≠ 0 := (ENNReal.toReal_pos hp0 hp).ne'
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf, eLpNorm_eq_eLpNorm' hp0 hp
      (aestronglyMeasurable_pullback μ _ e hf),
    eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm]
  congr 1
  refine Eq.trans ?_ (lintegral_pullback μ e fun x => ‖f x‖ₑ ^ p.toReal)
  congr 1 with x
  rw [pullback, enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
    Real.enorm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) ENNReal.toReal_nonneg,
    Real.rpow_inv_rpow (abs_nonneg _) hp']

theorem memLp_pullback (hp0 : p ≠ 0) (hp : p ≠ ∞) (e : diffeoGroup E) {f : E → F}
    (hf : MemLp f p μ) : MemLp (pullback p.toReal⁻¹ (e : Perm E) f) p μ := by
  rw [memLp_iff, eLpNorm_pullback μ hp0 hp e hf.aestronglyMeasurable]
  exact hf

theorem memLp_pullback_iff (hp0 : p ≠ 0) (hp : p ≠ ∞) (e : diffeoGroup E) {f : E → F} :
    MemLp (pullback p.toReal⁻¹ (e : Perm E) f) p μ ↔ MemLp f p μ := by
  refine ⟨fun h => ?_, memLp_pullback μ hp0 hp e⟩
  have := memLp_pullback μ hp0 hp e⁻¹ h
  rwa [coe_inv_diffeoGroup, pullback_symm_pullback] at this

namespace Lp

variable {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] [Fact (1 ≤ p)]
  (hp : p ≠ ∞)

variable {μ}

lemma ne_zero_of_fact : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'

variable (𝕜)

/-- `ψ ↦ |det D(e⁻¹)|^{1/p} • (ψ ∘ e⁻¹)`, as a linear isometry of `Lᵖ`. -/
def diffeoActₗᵢ (e : diffeoGroup E) : Lp F p μ →ₗᵢ[𝕜] Lp F p μ where
  toFun ψ := (memLp_pullback μ ne_zero_of_fact hp e⁻¹ (Lp.memLp ψ)).toLp _
  map_add' ψ φ := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    refine (pullback_congr_ae _ e⁻¹ (Lp.coeFn_add ψ φ)).trans ?_
    rw [pullback_add]
  map_smul' c ψ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    refine (pullback_congr_ae _ e⁻¹ (Lp.coeFn_smul c ψ)).trans ?_
    rw [pullback_smul]
  norm_map' ψ := by
    rw [LinearMap.coe_mk, AddHom.coe_mk, Lp.norm_toLp,
      eLpNorm_pullback μ ne_zero_of_fact hp _ (Lp.aestronglyMeasurable ψ), Lp.norm_def]

variable {𝕜}

theorem coeFn_diffeoActₗᵢ (e : diffeoGroup E) (ψ : Lp F p μ) :
    diffeoActₗᵢ 𝕜 hp e ψ =ᵐ[μ] pullback p.toReal⁻¹ ((e⁻¹ : diffeoGroup E) : Perm E) ψ :=
  MemLp.coeFn_toLp (memLp_pullback μ ne_zero_of_fact hp e⁻¹ (Lp.memLp ψ))

theorem diffeoActₗᵢ_one (ψ : Lp F p μ) : diffeoActₗᵢ 𝕜 hp 1 ψ = ψ := by
  refine Lp.ext ((coeFn_diffeoActₗᵢ hp 1 ψ).trans ?_)
  rw [inv_one]
  exact EventuallyEq.of_eq (pullback_id _ _)

theorem diffeoActₗᵢ_mul (a b : diffeoGroup E) (ψ : Lp F p μ) :
    diffeoActₗᵢ 𝕜 hp (a * b) ψ = diffeoActₗᵢ 𝕜 hp a (diffeoActₗᵢ 𝕜 hp b ψ) := by
  refine Lp.ext ((coeFn_diffeoActₗᵢ hp _ ψ).trans ?_)
  refine EventuallyEq.trans ?_ (coeFn_diffeoActₗᵢ hp a _).symm
  refine EventuallyEq.trans ?_ (pullback_congr_ae _ a⁻¹ (coeFn_diffeoActₗᵢ hp b ψ)).symm
  refine EventuallyEq.of_eq ?_
  rw [← pullback_comp _ (differentiable_of_mem_diffeoGroup _)
    (differentiable_of_mem_diffeoGroup _)]
  rfl

variable (𝕜) in
/-- Changes of coordinates act on `Lᵖ(E, μ)` by `(U_e ψ)(x) = |det D(e⁻¹)(x)|^{1/p} • ψ(e⁻¹ x)`,
a group homomorphism into the linear isometry equivalences. For `p = 2` it is a unitary
representation of `diffeoGroup E`. -/
def diffeoRep : diffeoGroup E →* (Lp F p μ ≃ₗᵢ[𝕜] Lp F p μ) where
  toFun e := LinearIsometryEquiv.ofSurjective (diffeoActₗᵢ 𝕜 hp e) fun ψ =>
    ⟨diffeoActₗᵢ 𝕜 hp e⁻¹ ψ, by rw [← diffeoActₗᵢ_mul, mul_inv_cancel, diffeoActₗᵢ_one]⟩
  map_one' := LinearIsometryEquiv.ext fun ψ => diffeoActₗᵢ_one hp ψ
  map_mul' a b := LinearIsometryEquiv.ext fun ψ => diffeoActₗᵢ_mul hp a b ψ

theorem diffeoRep_apply (e : diffeoGroup E) (ψ : Lp F p μ) :
    diffeoRep 𝕜 hp e ψ = diffeoActₗᵢ 𝕜 hp e ψ := rfl

/-- `(U_e ψ)(x) = |det D(e⁻¹)(x)|^{1/p} • ψ(e⁻¹ x)`. -/
theorem coeFn_diffeoRep (e : diffeoGroup E) (ψ : Lp F p μ) :
    diffeoRep 𝕜 hp e ψ =ᵐ[μ]
      fun x => |(fderiv ℝ (e : Perm E).symm x).det| ^ p.toReal⁻¹ • ψ ((e : Perm E).symm x) :=
  coeFn_diffeoActₗᵢ hp e ψ

/-- `(U_{e⁻¹} ψ)(x) = |det De(x)|^{1/p} • ψ(e x)`: the pullback. -/
theorem coeFn_diffeoRep_inv (e : diffeoGroup E) (ψ : Lp F p μ) :
    diffeoRep 𝕜 hp e⁻¹ ψ =ᵐ[μ]
      fun x => |(fderiv ℝ (e : Perm E) x).det| ^ p.toReal⁻¹ • ψ ((e : Perm E) x) :=
  coeFn_diffeoActₗᵢ hp e⁻¹ ψ

section Mul

variable {a : E → ℝ}

/-- `U_e` carries the domain of multiplication by `a` onto that of multiplication by
`a ∘ e⁻¹`. -/
theorem diffeoRep_mem_mulDomain_iff (e : diffeoGroup E) {ψ : Lp ℂ 2 μ} :
    diffeoRep ℂ ENNReal.ofNat_ne_top e ψ ∈ L2.mulDomain (a ∘ (e : Perm E).symm) ↔
      ψ ∈ L2.mulDomain a := by
  have he : (fun x => ((a ∘ (e : Perm E).symm) x : ℂ) * diffeoRep ℂ ENNReal.ofNat_ne_top e ψ x)
      =ᵐ[μ] pullback (2 : ℝ≥0∞).toReal⁻¹ ((e⁻¹ : diffeoGroup E) : Perm E)
        (fun x => (a x : ℂ) * ψ x) := by
    filter_upwards [coeFn_diffeoRep (𝕜 := ℂ) ENNReal.ofNat_ne_top e ψ] with x hx
    rw [hx, Function.comp_apply, pullback, Complex.real_smul, Complex.real_smul,
      coe_inv_diffeoGroup]
    ring
  rw [L2.mem_mulDomain, L2.mem_mulDomain, memLp_congr_ae he,
    memLp_pullback_iff μ two_ne_zero ENNReal.ofNat_ne_top]

/-- `U_e (a ψ) = (a ∘ e⁻¹) (U_e ψ)`: the unitary transports multiplication operators. -/
theorem diffeoRep_mulOp (e : diffeoGroup E)
    (ψ : (L2.mulOp a : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ).domain) :
    diffeoRep ℂ ENNReal.ofNat_ne_top e (L2.mulOp a ψ) =
      L2.mulOp (a ∘ (e : Perm E).symm)
        ⟨diffeoRep ℂ ENNReal.ofNat_ne_top e ψ, (diffeoRep_mem_mulDomain_iff e).2 ψ.2⟩ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_diffeoRep (𝕜 := ℂ) ENNReal.ofNat_ne_top e (L2.mulOp a ψ),
    (quasiMeasurePreserving_of_mem_diffeoGroup e⁻¹).ae_eq_comp (L2.coeFn_mulOp a ψ),
    L2.coeFn_mulOp (a ∘ (e : Perm E).symm)
      ⟨diffeoRep ℂ ENNReal.ofNat_ne_top e ψ, (diffeoRep_mem_mulDomain_iff e).2 ψ.2⟩,
    coeFn_diffeoRep (𝕜 := ℂ) ENNReal.ofNat_ne_top e (ψ : Lp ℂ 2 μ)] with x h1 h2 h3 h4
  simp only [Function.comp_apply] at h2 h3 ⊢
  rw [h1, h3, h4]
  erw [h2]
  rw [Complex.real_smul, Complex.real_smul, coe_inv_diffeoGroup]
  ring

end Mul

end Lp

end MeasureTheory
