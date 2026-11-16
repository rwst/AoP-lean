/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Densities of weight `w` on a finite-dimensional space

Let `E` be a finite-dimensional real normed space. The bijections `e` of `E` with `e` and `e⁻¹`
differentiable form a group `Equiv.Perm.diffeoGroup E`. A density of weight `w ∈ ℝ` is a
function `f : E → F` that transforms under this group by

  `(e • f)(x) = |det D(e⁻¹)(x)|^w • f(e⁻¹ x)`.

Weight `0` gives scalar functions, weight `1` gives densities in the usual sense (integrands), and
weight `1/2` gives half-densities, the wave functions of quantum mechanics. The type
`Density w E F` carries this action as a `MulAction`, so Mathlib's notions of covariance apply to
it without further work: invariant densities are `MulAction.fixedPoints`, and covariant
constructions are equivariant maps `→[diffeoGroup E]`.

## Main definitions

* `Equiv.Perm.diffeoGroup E`: the group of bijections of `E` that are differentiable with a
  differentiable inverse;
* `Density.pullback w e f`: the function `x ↦ |det De(x)|^w • f(e x)`;
* `Density w E F`: functions `E → F`, with the action of `diffeoGroup E` of weight `w`.

## Main results

* `Density.mulHom`: the pointwise product of densities of weights `w₁` and `w₂` is a density of
  weight `w₁ + w₂`;
* `Density.normRpowHom`: `x ↦ ‖f x‖ ^ p` is a density of weight `p * w`; for a half-density `ψ`,
  `|ψ|²` is a density;
* `Density.integral_smul`, `Density.integrable_smul_iff`: for every additive Haar measure,
  integration is an invariant linear functional on densities of weight `1`;
* `Density.lintegral_pullback`: the same for `ℝ≥0∞`-valued integrands;
* `Density.mem_fixedPoints_zero_iff`: the invariant scalars are the constants;
* `Density.eq_zero_of_mem_fixedPoints`: in positive dimension, no nonzero density of nonzero
  weight is invariant. An invariant volume needs a smaller group.
-/

open MeasureTheory Set
open scoped ENNReal

@[expose] public noncomputable section

namespace Equiv.Perm

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bijections `e` of `E` such that `e` and `e⁻¹` are differentiable. These are what the
change of variables in integrals needs; continuity of the derivative is not required. -/
def diffeoGroup : Subgroup (Perm E) where
  carrier := {e | Differentiable ℝ e ∧ Differentiable ℝ e.symm}
  mul_mem' {a b} ha hb := by
    refine ⟨?_, ?_⟩
    · rw [coe_mul]; exact Differentiable.comp ha.1 hb.1
    · change Differentiable ℝ (b.symm ∘ a.symm)
      exact Differentiable.comp hb.2 ha.2
  one_mem' := ⟨differentiable_id, differentiable_id⟩
  inv_mem' {e} he := ⟨he.2, he.1⟩

variable {E}

theorem differentiable_of_mem_diffeoGroup (e : diffeoGroup E) : Differentiable ℝ (e : Perm E) :=
  e.2.1

theorem differentiable_symm_of_mem_diffeoGroup (e : diffeoGroup E) :
    Differentiable ℝ (e : Perm E).symm :=
  e.2.2

theorem coe_inv_diffeoGroup (e : diffeoGroup E) :
    ((e⁻¹ : diffeoGroup E) : Perm E) = (e : Perm E).symm :=
  rfl

end Equiv.Perm

open Equiv Equiv.Perm

section Basic

variable {E F : Type*}

/-- Functions `E → F`, regarded as densities of weight `w`: the group `diffeoGroup E` acts by
`(e • f)(x) = |det D(e⁻¹)(x)|^w • f(e⁻¹ x)`. -/
structure Density (w : ℝ) (E F : Type*) where
  /-- A function, as a density of weight `w`. -/
  ofFun ::
  /-- The underlying function. -/
  toFun : E → F

namespace Density

variable {w : ℝ}

instance : CoeFun (Density w E F) fun _ => E → F := ⟨toFun⟩

@[simp] theorem ofFun_apply (f : E → F) (x : E) : (ofFun f : Density w E F) x = f x := rfl

theorem toFun_injective : Function.Injective (toFun : Density w E F → E → F) := by
  rintro ⟨f⟩ ⟨g⟩ h
  cases h
  rfl

@[ext] theorem ext {f g : Density w E F} (h : ∀ x, f x = g x) : f = g :=
  toFun_injective (funext h)

instance [Zero F] : Zero (Density w E F) := ⟨ofFun 0⟩
instance [Add F] : Add (Density w E F) := ⟨fun f g => ofFun (f.toFun + g.toFun)⟩
instance [Neg F] : Neg (Density w E F) := ⟨fun f => ofFun (-f.toFun)⟩
instance [Sub F] : Sub (Density w E F) := ⟨fun f g => ofFun (f.toFun - g.toFun)⟩
instance {R : Type*} [SMul R F] : SMul R (Density w E F) := ⟨fun c f => ofFun (c • f.toFun)⟩

instance [AddCommGroup F] : AddCommGroup (Density w E F) :=
  toFun_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- `toFun` as an additive map. -/
def toFunAddHom [AddCommGroup F] : Density w E F →+ (E → F) where
  toFun := toFun
  map_zero' := rfl
  map_add' _ _ := rfl

instance {R : Type*} [Semiring R] [AddCommGroup F] [Module R F] : Module R (Density w E F) :=
  toFun_injective.module R toFunAddHom fun _ _ => rfl

@[simp] theorem add_apply [AddCommGroup F] (f g : Density w E F) (x : E) :
    (f + g) x = f x + g x := rfl

@[simp] theorem zero_apply [AddCommGroup F] (x : E) : (0 : Density w E F) x = 0 := rfl

@[simp] theorem smul_apply' {R : Type*} [SMul R F] (c : R) (f : Density w E F) (x : E) :
    (c • f) x = c • f x := rfl

end Density

end Basic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Density

section pullback

variable [AddCommGroup F] [Module ℝ F]

/-- The pullback `x ↦ |det De(x)|^w • f(e x)` of a density of weight `w` by `e`. -/
def pullback (w : ℝ) (e : E → E) (f : E → F) (x : E) : F :=
  |(fderiv ℝ e x).det| ^ w • f (e x)

theorem pullback_id (w : ℝ) (f : E → F) : pullback w id f = f := by
  ext x
  simp [pullback, fderiv_id, ContinuousLinearMap.det, LinearMap.det_id]

/-- The chain rule for the Jacobian determinant. -/
theorem det_fderiv_comp {a b : E → E} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (x : E) : (fderiv ℝ (a ∘ b) x).det = (fderiv ℝ a (b x)).det * (fderiv ℝ b x).det := by
  rw [fderiv_comp x (ha (b x)) (hb x)]
  exact LinearMap.det_comp _ _

/-- Pulling back by `a ∘ b` is pulling back by `a`, then by `b`. -/
theorem pullback_comp (w : ℝ) {a b : E → E} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (f : E → F) : pullback w (a ∘ b) f = pullback w b (pullback w a f) := by
  ext x
  simp only [pullback, det_fderiv_comp ha hb, abs_mul, Function.comp_apply, smul_smul,
    Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_comm]

theorem det_fderiv_ne_zero (e : diffeoGroup E) (x : E) : (fderiv ℝ (e : Perm E) x).det ≠ 0 := by
  have h := det_fderiv_comp (differentiable_symm_of_mem_diffeoGroup e)
    (differentiable_of_mem_diffeoGroup e) x
  rw [show ((e : Perm E).symm ∘ (e : Perm E) : E → E) = id from
    funext (e : Perm E).symm_apply_apply, fderiv_id] at h
  refine right_ne_zero_of_mul_eq_one (h.symm.trans ?_)
  exact LinearMap.det_id

theorem abs_det_fderiv_pos (e : diffeoGroup E) (x : E) : 0 < |(fderiv ℝ (e : Perm E) x).det| :=
  abs_pos.2 (det_fderiv_ne_zero e x)

theorem abs_det_fderiv_symm_pos (e : diffeoGroup E) (x : E) :
    0 < |(fderiv ℝ (e : Perm E).symm x).det| :=
  abs_det_fderiv_pos e⁻¹ x

end pullback

variable {w : ℝ}

variable [AddCommGroup F] [Module ℝ F]

instance : SMul (diffeoGroup E) (Density w E F) where
  smul e f := ofFun (pullback w ((e : Perm E).symm) f)

/-- `(e • f)(x) = |det D(e⁻¹)(x)|^w • f(e⁻¹ x)`. -/
theorem smul_apply (e : diffeoGroup E) (f : Density w E F) (x : E) :
    (e • f) x = |(fderiv ℝ (e : Perm E).symm x).det| ^ w • f ((e : Perm E).symm x) := rfl

/-- The action of `e⁻¹` is the pullback by `e`: `(e⁻¹ • f)(x) = |det De(x)|^w • f(e x)`. -/
theorem inv_smul_apply (e : diffeoGroup E) (f : Density w E F) (x : E) :
    (e⁻¹ • f) x = |(fderiv ℝ (e : Perm E) x).det| ^ w • f ((e : Perm E) x) := rfl

instance : MulAction (diffeoGroup E) (Density w E F) where
  one_smul f := by
    change ofFun (pullback w id f) = f
    rw [pullback_id]
  mul_smul a b f := by
    change ofFun (pullback w ((b : Perm E).symm ∘ (a : Perm E).symm) f) =
      ofFun (pullback w (a : Perm E).symm (pullback w (b : Perm E).symm f))
    rw [pullback_comp w (differentiable_symm_of_mem_diffeoGroup b)
      (differentiable_symm_of_mem_diffeoGroup a)]

instance : DistribMulAction (diffeoGroup E) (Density w E F) where
  smul_zero e := by ext x; simp [smul_apply]
  smul_add e f g := by ext x; simp [smul_apply, smul_add]

instance {R : Type*} [Semiring R] [Module R F] [SMulCommClass ℝ R F] :
    SMulCommClass (diffeoGroup E) R (Density w E F) where
  smul_comm e c f := by
    ext x
    simp only [smul_apply, smul_apply']
    exact smul_comm _ _ _

/-- The weight-`0` action is composition: scalars do not transform. -/
theorem smul_apply_zero (e : diffeoGroup E) (f : Density 0 E F) (x : E) :
    (e • f) x = f ((e : Perm E).symm x) := by
  rw [smul_apply, Real.rpow_zero, one_smul]

section Equivariant

/-- The pointwise product of densities of weights `w₁` and `w₂` is a density of weight
`w₁ + w₂`. -/
def mulHom (w₁ w₂ : ℝ) (A : Type*) [Ring A] [Algebra ℝ A] :
    Density w₁ E A × Density w₂ E A →[diffeoGroup E] Density (w₁ + w₂) E A where
  toFun fg := ofFun fun x => fg.1 x * fg.2 x
  map_smul' e fg := by
    ext x
    simp only [Prod.smul_fst, Prod.smul_snd, smul_apply, id_eq,
      smul_mul_smul_comm, ← Real.rpow_add (abs_det_fderiv_symm_pos e x)]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `x ↦ ‖f x‖ ^ p` is a density of weight `p * w`. For a half-density `ψ` and `p = 2`, this
says that `|ψ|²` is a density. -/
def normRpowHom (w p : ℝ) : Density w E F →[diffeoGroup E] Density (p * w) E ℝ where
  toFun f := ofFun fun x => ‖f x‖ ^ p
  map_smul' e f := by
    ext x
    simp only [smul_apply, id_eq, smul_eq_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _) (norm_nonneg _), ← Real.rpow_mul
      (abs_nonneg _), mul_comm w]

end Equivariant

section Integral

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

/-- The change of variables `∫⁻ |det De| · (g ∘ e) ∂μ = ∫⁻ g ∂μ`. -/
theorem lintegral_pullback (e : diffeoGroup E) (g : E → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal |(fderiv ℝ (e : Perm E) x).det| * g ((e : Perm E) x) ∂μ =
      ∫⁻ x, g x ∂μ := by
  have := lintegral_image_eq_lintegral_abs_det_fderiv_mul μ MeasurableSet.univ
    (fun x _ => ((differentiable_of_mem_diffeoGroup e) x).hasFDerivAt.hasFDerivWithinAt)
    (e : Perm E).injective.injOn g
  rw [image_univ_of_surjective (e : Perm E).surjective, Measure.restrict_univ] at this
  exact this.symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integrability of densities of weight `1` is invariant. -/
theorem integrable_smul_iff (e : diffeoGroup E) (f : Density 1 E F) :
    Integrable (⇑(e • f)) μ ↔ Integrable (⇑f) μ := by
  have := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul μ MeasurableSet.univ
    (fun x _ => ((differentiable_symm_of_mem_diffeoGroup e) x).hasFDerivAt.hasFDerivWithinAt)
    (e : Perm E).symm.injective.injOn ⇑f
  rw [image_univ_of_surjective (e : Perm E).symm.surjective, integrableOn_univ,
    integrableOn_univ] at this
  rw [this]
  exact integrable_congr (Filter.Eventually.of_forall fun x => by rw [smul_apply, Real.rpow_one])

/-- Integration against any additive Haar measure is invariant on densities of weight `1`. -/
theorem integral_smul [CompleteSpace F] (e : diffeoGroup E) (f : Density 1 E F) :
    ∫ x, (e • f) x ∂μ = ∫ x, f x ∂μ := by
  have := integral_image_eq_integral_abs_det_fderiv_smul μ MeasurableSet.univ
    (fun x _ => ((differentiable_symm_of_mem_diffeoGroup e) x).hasFDerivAt.hasFDerivWithinAt)
    (e : Perm E).symm.injective.injOn ⇑f
  rw [image_univ_of_surjective (e : Perm E).symm.surjective, Measure.restrict_univ] at this
  rw [this]
  simp only [smul_apply, Real.rpow_one]

end Integral

section FixedPoints

/-- Translation by `v`, as an element of `diffeoGroup E`. -/
def translation (v : E) : diffeoGroup E :=
  ⟨{ toFun := fun x => x + v, invFun := fun x => x - v
     left_inv := fun x => add_sub_cancel_right x v
     right_inv := fun x => sub_add_cancel x v },
    show Differentiable ℝ (fun x : E => x + v) by fun_prop,
    show Differentiable ℝ (fun x : E => x - v) by fun_prop⟩

/-- Multiplication by `c ≠ 0`, as an element of `diffeoGroup E`. -/
def dilation {c : ℝ} (hc : c ≠ 0) : diffeoGroup E :=
  ⟨{ toFun := fun x => c • x, invFun := fun x => c⁻¹ • x
     left_inv := fun x => inv_smul_smul₀ hc x
     right_inv := fun x => smul_inv_smul₀ hc x },
    show Differentiable ℝ (fun x : E => c • x) by fun_prop,
    show Differentiable ℝ (fun x : E => c⁻¹ • x) by fun_prop⟩

theorem translation_smul_apply (v : E) (f : Density w E F) (x : E) :
    (translation v • f) x = f (x - v) := by
  have : ⇑((translation v : diffeoGroup E) : Perm E).symm = fun y => y - v := rfl
  rw [smul_apply, this, fderiv_sub_const, fderiv_fun_id,
    show (ContinuousLinearMap.id ℝ E).det = 1 from LinearMap.det_id, abs_one, Real.one_rpow,
    one_smul]

theorem dilation_smul_apply [FiniteDimensional ℝ E] {c : ℝ} (hc : c ≠ 0) (f : Density w E F)
    (x : E) : (dilation (E := E) hc • f) x = (|c⁻¹| ^ Module.finrank ℝ E) ^ w • f (c⁻¹ • x) := by
  have : ⇑((dilation hc : diffeoGroup E) : Perm E).symm = fun y => c⁻¹ • y := rfl
  rw [smul_apply, this, fderiv_fun_const_smul differentiableAt_fun_id, fderiv_fun_id, ← abs_pow,
    show (c⁻¹ • ContinuousLinearMap.id ℝ E).det = c⁻¹ ^ Module.finrank ℝ E by
      rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
        ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]]

/-- A function invariant under all translations is constant. -/
theorem eq_of_forall_translation {f : Density w E F}
    (hf : ∀ v : E, translation v • f = f) (x : E) : f x = f 0 := by
  have := congrArg (· x) (hf x)
  simp only [translation_smul_apply, sub_self] at this
  exact this.symm

/-- The scalars invariant under all of `diffeoGroup E` are the constants. -/
theorem mem_fixedPoints_zero_iff {f : Density 0 E F} :
    f ∈ MulAction.fixedPoints (diffeoGroup E) (Density 0 E F) ↔ ∀ x y, f x = f y := by
  refine ⟨fun hf x y => ?_, fun hf e => ?_⟩
  · rw [eq_of_forall_translation (fun v => hf _) x, eq_of_forall_translation (fun v => hf _) y]
  · ext x
    rw [smul_apply_zero, hf]

/-- In positive dimension, no nonzero density of nonzero weight is invariant under all of
`diffeoGroup E`: translations force it to be constant, and dilations then force it to vanish. -/
theorem eq_zero_of_mem_fixedPoints [FiniteDimensional ℝ E] [Nontrivial E] (hw : w ≠ 0)
    {f : Density w E F} (hf : f ∈ MulAction.fixedPoints (diffeoGroup E) (Density w E F)) :
    f = 0 := by
  have hc : ∀ x, f x = f 0 := eq_of_forall_translation fun v => hf _
  set b : ℝ := |(2 : ℝ)⁻¹| ^ Module.finrank ℝ E with hb
  have hb0 : 0 < b := pow_pos (by norm_num) _
  have hb1 : b < 1 := by
    rw [hb]
    refine pow_lt_one₀ (by norm_num) (by norm_num) (Module.finrank_pos (R := ℝ)).ne'
  have hbw : b ^ w ≠ 1 := by
    rcases hw.lt_or_gt with h | h
    · exact (Real.one_lt_rpow_of_pos_of_lt_one_of_neg hb0 hb1 h).ne'
    · exact (Real.rpow_lt_one hb0.le hb1 h).ne
  have h0 := congrArg (· 0) (hf (dilation (E := E) two_ne_zero))
  simp only [dilation_smul_apply, smul_zero] at h0
  have h1 : (b ^ w - 1) • f 0 = 0 := by rw [sub_smul, one_smul, hb, h0, sub_self]
  ext x
  rw [hc x, zero_apply]
  exact (smul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hbw)

end FixedPoints

end Density
