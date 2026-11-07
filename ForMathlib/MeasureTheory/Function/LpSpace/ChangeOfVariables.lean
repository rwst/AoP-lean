/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Change of variables on `L²(ℝ)`

A bijection `g : ℝ ≃ ℝ` that is differentiable with a differentiable inverse acts on `L²(ℝ)` by
the unitary `ψ ↦ √|g'| · (ψ ∘ g)`. The weight `√|g'|` makes the change of variables
`∫ |ψ(g y)|² |g'(y)| dy = ∫ |ψ(x)|² dx` an isometry, and the operator for `g⁻¹` is its inverse.

## Main results

* `MeasureTheory.quasiMeasurePreserving_of_differentiable_symm`: `g` pulls null sets back to
  null sets when `g⁻¹` is differentiable;
* `MeasureTheory.lintegral_abs_deriv_mul_comp`: the change of variables for `g`;
* `MeasureTheory.eLpNorm_compDiffeo`: the weighted pullback preserves the `L²` norm;
* `MeasureTheory.Lp.compDiffeo`: the unitary, and `MeasureTheory.Lp.coeFn_compDiffeo`.
-/

open Set Filter
open scoped ENNReal

@[expose] public noncomputable section

namespace MeasureTheory

variable {𝕜 : Type*} [RCLike 𝕜] (g : ℝ ≃ ℝ)

/-- If `g⁻¹` is differentiable, then `g` pulls null sets back to null sets. -/
theorem quasiMeasurePreserving_of_differentiable_symm (hg : Continuous g)
    (hg' : Differentiable ℝ g.symm) : QuasiMeasurePreserving g volume volume := by
  refine ⟨hg.measurable, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply hg.measurable hs, ← g.image_symm_eq_preimage]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hg'.differentiableOn h0

/-- The chain rule for `g⁻¹ ∘ g = id`. -/
theorem deriv_symm_mul_deriv (hg : Differentiable ℝ g) (hg' : Differentiable ℝ g.symm)
    (y : ℝ) : deriv g.symm (g y) * deriv g y = 1 := by
  have h := HasDerivAt.comp y (hg' (g y)).hasDerivAt (hg y).hasDerivAt
  rw [g.symm_comp_self] at h
  exact h.unique (hasDerivAt_id y)

/-- The change of variables `∫ h(g y) |g'(y)| dy = ∫ h(x) dx`. -/
theorem lintegral_abs_deriv_mul_comp (hg : Differentiable ℝ g) (h : ℝ → ℝ≥0∞) :
    ∫⁻ y, ENNReal.ofReal |deriv g y| * h (g y) = ∫⁻ x, h x := by
  have := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun y _ => (hg y).hasDerivAt.hasDerivWithinAt) g.injective.injOn h
  rw [image_univ_of_surjective g.surjective, Measure.restrict_univ] at this
  exact this.symm

/-- The weight `√|g'|`, as a scalar. -/
def sqrtAbsDeriv (y : ℝ) : 𝕜 := (√|deriv g y| : ℝ)

theorem measurable_sqrtAbsDeriv : Measurable (sqrtAbsDeriv (𝕜 := 𝕜) g) :=
  RCLike.continuous_ofReal.measurable.comp
    (Real.continuous_sqrt.measurable.comp (continuous_abs.measurable.comp (measurable_deriv g)))

lemma enorm_sqrtAbsDeriv_rpow_two (y : ℝ) :
    ‖sqrtAbsDeriv (𝕜 := 𝕜) g y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal |deriv g y| := by
  rw [sqrtAbsDeriv, ← ofReal_norm, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _), ENNReal.rpow_two, ← ENNReal.ofReal_pow
    (Real.sqrt_nonneg _), Real.sq_sqrt (abs_nonneg _)]

variable {g} (hg : Differentiable ℝ g) (hg' : Differentiable ℝ g.symm)
include hg hg'

theorem aestronglyMeasurable_compDiffeo {ψ : ℝ → 𝕜} (hψ : AEStronglyMeasurable ψ volume) :
    AEStronglyMeasurable (fun y => sqrtAbsDeriv g y * ψ (g y)) volume :=
  (measurable_sqrtAbsDeriv g).aestronglyMeasurable.mul
    (hψ.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_of_differentiable_symm g hg.continuous hg'))

/-- The weighted pullback `ψ ↦ √|g'| · (ψ ∘ g)` preserves the `L²` norm. -/
theorem eLpNorm_compDiffeo {ψ : ℝ → 𝕜} (hψ : AEStronglyMeasurable ψ volume) :
    eLpNorm (fun y => sqrtAbsDeriv g y * ψ (g y)) 2 volume = eLpNorm ψ 2 volume := by
  rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hψ,
    eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top
      (aestronglyMeasurable_compDiffeo hg hg' hψ),
    eLpNorm'_eq_lintegral_enorm, eLpNorm'_eq_lintegral_enorm, ENNReal.toReal_ofNat]
  congr 1
  refine Eq.trans ?_ (lintegral_abs_deriv_mul_comp g hg fun x => ‖ψ x‖ₑ ^ (2 : ℝ))
  congr 1 with y
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), enorm_sqrtAbsDeriv_rpow_two]

theorem memLp_compDiffeo {ψ : ℝ → 𝕜} (hψ : MemLp ψ 2 volume) :
    MemLp (fun y => sqrtAbsDeriv g y * ψ (g y)) 2 volume := by
  rw [memLp_iff, eLpNorm_compDiffeo hg hg' hψ.aestronglyMeasurable]
  exact hψ

namespace Lp

/-- The pullback by `g`, as a linear isometry of `L²(ℝ)`. -/
def compDiffeoₗᵢ : Lp 𝕜 2 (volume : Measure ℝ) →ₗᵢ[𝕜] Lp 𝕜 2 (volume : Measure ℝ) where
  toFun ψ := (memLp_compDiffeo hg hg' (Lp.memLp ψ)).toLp _
  map_add' ψ φ := by
    have hq := quasiMeasurePreserving_of_differentiable_symm g hg.continuous hg'
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_compDiffeo hg hg' (Lp.memLp (ψ + φ))),
      Lp.coeFn_add ((memLp_compDiffeo hg hg' (Lp.memLp ψ)).toLp _)
        ((memLp_compDiffeo hg hg' (Lp.memLp φ)).toLp _),
      MemLp.coeFn_toLp (memLp_compDiffeo hg hg' (Lp.memLp ψ)),
      MemLp.coeFn_toLp (memLp_compDiffeo hg hg' (Lp.memLp φ)),
      hq.ae_eq_comp (Lp.coeFn_add ψ φ)] with y h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h1 h2 h5 ⊢
    rw [h1, h2, h3, h4, show (ψ + φ : Lp 𝕜 2 (volume : Measure ℝ)) (g y) = ψ (g y) + φ (g y)
      from h5, mul_add]
  map_smul' c ψ := by
    have hq := quasiMeasurePreserving_of_differentiable_symm g hg.continuous hg'
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_compDiffeo hg hg' (Lp.memLp (c • ψ))),
      Lp.coeFn_smul c ((memLp_compDiffeo hg hg' (Lp.memLp ψ)).toLp _),
      MemLp.coeFn_toLp (memLp_compDiffeo hg hg' (Lp.memLp ψ)),
      hq.ae_eq_comp (Lp.coeFn_smul c ψ)] with y h1 h2 h3 h5
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply] at h1 h2 h5 ⊢
    rw [h1, h2, h3, show (c • ψ : Lp 𝕜 2 (volume : Measure ℝ)) (g y) = c * ψ (g y) from h5,
      mul_left_comm]
  norm_map' ψ := by
    change ‖(memLp_compDiffeo hg hg' (Lp.memLp ψ)).toLp _‖ = ‖ψ‖
    rw [Lp.norm_toLp, eLpNorm_compDiffeo hg hg' (Lp.aestronglyMeasurable ψ), Lp.norm_def]

theorem coeFn_compDiffeoₗᵢ (ψ : Lp 𝕜 2 (volume : Measure ℝ)) :
    compDiffeoₗᵢ hg hg' ψ =ᵐ[volume] fun y => sqrtAbsDeriv g y * ψ (g y) :=
  MemLp.coeFn_toLp (memLp_compDiffeo hg hg' (Lp.memLp ψ))

/-- The pullback by `g` undoes the pullback by `g⁻¹`. -/
theorem compDiffeoₗᵢ_compDiffeoₗᵢ_symm (ψ : Lp 𝕜 2 (volume : Measure ℝ)) :
    compDiffeoₗᵢ hg hg' (compDiffeoₗᵢ (g := g.symm) hg' hg ψ) = ψ := by
  have hq := quasiMeasurePreserving_of_differentiable_symm g hg.continuous hg'
  refine Lp.ext ?_
  filter_upwards [coeFn_compDiffeoₗᵢ hg hg' (compDiffeoₗᵢ (g := g.symm) hg' hg ψ),
    hq.ae_eq_comp (coeFn_compDiffeoₗᵢ (g := g.symm) hg' hg ψ)] with y h1 h2
  simp only [Function.comp_apply, Equiv.symm_apply_apply] at h2
  rw [h1, h2, ← mul_assoc, sqrtAbsDeriv, sqrtAbsDeriv, ← RCLike.ofReal_mul,
    ← Real.sqrt_mul (abs_nonneg _), ← abs_mul, mul_comm (deriv g y), deriv_symm_mul_deriv g hg hg',
    abs_one, Real.sqrt_one, RCLike.ofReal_one, one_mul]

/-- The unitary `ψ ↦ √|g'| · (ψ ∘ g)` of `L²(ℝ)` induced by a diffeomorphism `g` of `ℝ`. -/
def compDiffeo : Lp 𝕜 2 (volume : Measure ℝ) ≃ₗᵢ[𝕜] Lp 𝕜 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective (compDiffeoₗᵢ hg hg') fun ψ =>
    ⟨_, compDiffeoₗᵢ_compDiffeoₗᵢ_symm hg hg' ψ⟩

theorem coeFn_compDiffeo (ψ : Lp 𝕜 2 (volume : Measure ℝ)) :
    compDiffeo hg hg' ψ =ᵐ[volume] fun y => sqrtAbsDeriv g y * ψ (g y) :=
  coeFn_compDiffeoₗᵢ hg hg' ψ

end Lp

end MeasureTheory
