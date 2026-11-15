/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.FurtherResults.FrameGroups

/-!
# Further results: the linear changes of frame of `𝓢(ℝⁿ)`

Not part of the brief. This file extends Sec. 3 of `further-results.tex` in the brief's
directory from the translations of Example 3 to the linear changes of frame of `𝓢(ℝⁿ)`.

A frame group satisfies [B]WDQ exactly when it acts by unitary automorphisms of `V`
(`isFrameCompatible_iff_continuous`). So the unitary automorphisms of `V` form the largest frame
group with [B]WDQ, and every subgroup of it is again one (`isFrameCompatible_ofSubgroup_iff`). For
Example 3 in `n` dimensions the following unitaries of `L²(ℝⁿ)` are automorphisms of `𝓢(ℝⁿ)`:

* the translations `f ↦ f(· - a)`;
* the modulations `f ↦ e^{i⟨a, x⟩} f`;
* the linear changes of variable `f ↦ |det A|^{-1/2} f ∘ A⁻¹`;
* the Fourier transform;
* the chirps `f ↦ e^{i⟨x, B x⟩} f`.

Together they generate the metaplectic group up to phases (G. B. Folland, *Harmonic Analysis in
Phase Space*, Princeton 1989, Ch. 4), so all linear symplectic changes of frame satisfy [B]WDQ.
The generation theorem itself is not needed: the group they generate is a frame group with
[B]WDQ (`isFrameCompatible_linearFrames`), whatever it is.

## Main definitions

* `unitaryAut c t`: the linear bijections of `V` that preserve the inner product and are
  homeomorphisms for `t`;
* `FrameGroup.ofSubgroup`: a subgroup of inner-product-preserving linear bijections as a frame
  group;
* `translateN`, `modulate`, `dilate`, `fourierN`, `chirp`: the generators above, as continuous
  linear equivalences of `𝓢(ℝⁿ)`;
* `linearFrames n`: the group they generate.

## Main results

* `isFrameCompatible_ofSubgroup_iff`: a subgroup is a frame group with [B]WDQ if and only if it
  consists of unitary automorphisms of `V`;
* `isFrameCompatible_schwartzN`: for Example 3 in `n` dimensions, if and only if it consists of
  automorphisms of the Fréchet space `𝓢(ℝⁿ)` that preserve the inner product;
* `linearFrames_le_schwartzAut`, `isFrameCompatible_linearFrames`: the linear changes of frame
  satisfy [B]WDQ.
-/

open SchwartzMap MeasureTheory Complex ComplexConjugate FourierTransform

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

/-! ### The largest frame group with [B]WDQ -/

section UnitaryAut

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : PreInnerProductSpace.Core ℂ V)
  (t : TopologicalSpace V)

/-- The unitary automorphisms of `V` for the topology `t`: the linear bijections that preserve the
inner product and are homeomorphisms for `t`. -/
def unitaryAut : Subgroup (V ≃ₗ[ℂ] V) where
  carrier := {e | PreservesInner c c e ∧ @Continuous _ _ t t e ∧ @Continuous _ _ t t e.symm}
  one_mem' := ⟨fun _ _ => rfl, continuous_id, continuous_id⟩
  mul_mem' := by
    rintro e e' ⟨he, he1, he2⟩ ⟨he', he'1, he'2⟩
    refine ⟨fun v w => ?_, he1.comp he'1, he'2.comp he2⟩
    change c.inner (e (e' v)) (e (e' w)) = c.inner v w
    rw [he, he']
  inv_mem' := by
    rintro e ⟨he, he1, he2⟩
    exact ⟨he.symm, he2, he1⟩

variable {c}

/-- A subgroup of inner-product-preserving linear bijections of `V`, as a frame group. -/
def FrameGroup.ofSubgroup (H : Subgroup (V ≃ₗ[ℂ] V)) (hH : ∀ e ∈ H, PreservesInner c c e) :
    FrameGroup c H where
  act := H.subtype
  preservesInner g := hH g g.2

variable {ι : Type*} {X : ι → Module.End ℂ V}

/-- **The largest frame group with [B]WDQ.** A subgroup of inner-product-preserving linear
bijections is a frame group with [B]WDQ if and only if it consists of unitary automorphisms of the
quantum vector space. -/
theorem isFrameCompatible_ofSubgroup_iff (hX : ∀ i, IsSymmetric c (X i))
    (H : Subgroup (V ≃ₗ[ℂ] V)) (hH : ∀ e ∈ H, PreservesInner c c e) :
    IsFrameCompatible c X (FrameGroup.ofSubgroup H hH) ↔ H ≤ unitaryAut c (topology c X) := by
  rw [isFrameCompatible_iff_continuous _ hX]
  refine ⟨fun h e he => ⟨hH e he, h ⟨e, he⟩, ?_⟩, fun h g => (h g.2).2.1⟩
  rw [← LinearEquiv.coe_inv]
  exact h ⟨e, he⟩⁻¹

end UnitaryAut

/-! ### Example 3 in `n` dimensions -/

section SchwartzN

variable (n : ℕ)

set_option hygiene false in
/-- The Schwartz space `𝓢(ℝⁿ)` of complex functions. -/
local notation "𝓢ₙ" => 𝓢(EuclideanSpace ℝ (Fin n), ℂ)

set_option hygiene false in
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- The automorphisms of the Fréchet space `𝓢(ℝⁿ)` that preserve the `L²` inner product. -/
abbrev schwartzAut : Subgroup (𝓢ₙ ≃ₗ[ℂ] 𝓢ₙ) := unitaryAut (l2CoreN n) inferInstance

variable {n}

lemma mem_schwartzAut (e : 𝓢ₙ ≃L[ℂ] 𝓢ₙ)
    (he : ∀ f g, ∫ x, conj (e f x) * e g x = ∫ x, conj (f x) * g x) :
    e.toLinearEquiv ∈ schwartzAut n :=
  ⟨fun f g => by rw [l2CoreN_inner, l2CoreN_inner]; exact he f g, e.continuous, e.symm.continuous⟩

/-- **[B]WDQ for Example 3 in `n` dimensions.** A subgroup of inner-product-preserving linear
bijections of `𝓢(ℝⁿ)` is a frame group with [B]WDQ if and only if it acts by automorphisms of the
Fréchet space `𝓢(ℝⁿ)`. -/
theorem isFrameCompatible_schwartzN {ħ : ℝ} (hħ : ħ ≠ 0) (H : Subgroup (𝓢ₙ ≃ₗ[ℂ] 𝓢ₙ))
    (hH : ∀ e ∈ H, PreservesInner (l2CoreN n) (l2CoreN n) e) :
    IsFrameCompatible (l2CoreN n) (obsN n ħ) (FrameGroup.ofSubgroup H hH) ↔
      H ≤ schwartzAut n := by
  rw [isFrameCompatible_ofSubgroup_iff (isSymmetric_obsN n ħ), topology_schwartzN n hħ]

/-- Translation of the origin by `a`: `f ↦ f(· - a)`. -/
def translateN (a : Eₙ) : 𝓢ₙ ≃L[ℂ] 𝓢ₙ :=
  .equivOfInverse (compSubConstCLM ℂ a) (compSubConstCLM ℂ (-a))
    (fun f => by ext x; simp) (fun f => by ext x; simp)

lemma translateN_mem (a : Eₙ) : (translateN a).toLinearEquiv ∈ schwartzAut n :=
  mem_schwartzAut _ fun f g => integral_sub_right_eq_self (fun x => conj (f x) * g x) a

lemma hasTemperateGrowth_exp_mul_I {φ : Eₙ → ℝ} (hφ : φ.HasTemperateGrowth) :
    (fun x => exp (φ x * I)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_exp_mul_I.comp hφ

lemma hasTemperateGrowth_exp_neg_mul_I {φ : Eₙ → ℝ} (hφ : φ.HasTemperateGrowth) :
    (fun x => exp (-φ x * I)).HasTemperateGrowth := by
  have := hasTemperateGrowth_exp_mul_I hφ.neg
  simp only [Pi.neg_apply, ofReal_neg] at this
  exact this

/-- Multiplication by the phase `e^{iφ}`, for a real function `φ` of temperate growth. -/
def phase {φ : Eₙ → ℝ} (hφ : φ.HasTemperateGrowth) : 𝓢ₙ ≃L[ℂ] 𝓢ₙ :=
  .equivOfInverse (smulLeftCLM ℂ fun x => exp (φ x * I)) (smulLeftCLM ℂ fun x => exp (-φ x * I))
    (fun f => by
      ext x
      rw [smulLeftCLM_apply_apply (hasTemperateGrowth_exp_neg_mul_I hφ),
        smulLeftCLM_apply_apply (hasTemperateGrowth_exp_mul_I hφ), smul_eq_mul, smul_eq_mul,
        ← mul_assoc, ← exp_add]
      simp)
    (fun f => by
      ext x
      rw [smulLeftCLM_apply_apply (hasTemperateGrowth_exp_mul_I hφ),
        smulLeftCLM_apply_apply (hasTemperateGrowth_exp_neg_mul_I hφ), smul_eq_mul, smul_eq_mul,
        ← mul_assoc, ← exp_add]
      simp)

lemma phase_apply {φ : Eₙ → ℝ} (hφ : φ.HasTemperateGrowth) (f : 𝓢ₙ) (x : Eₙ) :
    phase hφ f x = exp (φ x * I) * f x := by
  change smulLeftCLM ℂ (fun x => exp (φ x * I)) f x = _
  rw [smulLeftCLM_apply_apply (hasTemperateGrowth_exp_mul_I hφ), smul_eq_mul]

lemma phase_mem {φ : Eₙ → ℝ} (hφ : φ.HasTemperateGrowth) :
    (phase hφ).toLinearEquiv ∈ schwartzAut n := by
  refine mem_schwartzAut _ fun f g => integral_congr_ae (.of_forall fun x => ?_)
  simp only [phase_apply, map_mul]
  calc conj (exp (φ x * I)) * conj (f x) * (exp (φ x * I) * g x)
      = (conj (exp (φ x * I)) * exp (φ x * I)) * (conj (f x) * g x) := by ring
    _ = conj (f x) * g x := by rw [conj_mul', norm_exp_ofReal_mul_I]; simp

/-- The modulation `f ↦ e^{i⟨a, x⟩} f`, a translation in momentum. -/
def modulate (a : Eₙ) : 𝓢ₙ ≃L[ℂ] 𝓢ₙ := phase (Function.hasTemperateGrowth_inner_right a)

/-- The chirp `f ↦ e^{i⟨x, B x⟩} f`. Only the symmetric part of `B` matters. -/
def chirp (B : Eₙ →L[ℝ] Eₙ) : 𝓢ₙ ≃L[ℂ] 𝓢ₙ :=
  phase (φ := fun x => inner ℝ x (B x))
    ((innerSL ℝ).bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' B.hasTemperateGrowth)

/-- The factor `|det A|^{-1/2}` that makes a linear change of variable unitary. -/
def detFactor (A : Eₙ ≃L[ℝ] Eₙ) : ℝ := |LinearMap.det (A : Eₙ →ₗ[ℝ] Eₙ)| ^ (-(1 / 2 : ℝ))

lemma det_ne_zero (A : Eₙ ≃L[ℝ] Eₙ) : LinearMap.det (A : Eₙ →ₗ[ℝ] Eₙ) ≠ 0 :=
  (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero

lemma detFactor_pos (A : Eₙ ≃L[ℝ] Eₙ) : 0 < detFactor A :=
  Real.rpow_pos_of_pos (abs_pos.2 (det_ne_zero A)) _

/-- Change of variables along a linear bijection: `∫ h(A⁻¹ x) dx = |det A| ∫ h`. -/
lemma integral_comp_symm (A : Eₙ ≃L[ℝ] Eₙ) (h : Eₙ → ℂ) :
    ∫ x, h (A.symm x) = |LinearMap.det (A : Eₙ →ₗ[ℝ] Eₙ)| • ∫ x, h x := by
  have hdet : (LinearMap.det (A.symm : Eₙ →ₗ[ℝ] Eₙ))⁻¹ = LinearMap.det (A : Eₙ →ₗ[ℝ] Eₙ) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← LinearMap.det_comp]
    convert LinearMap.det_id (A := ℝ) (M := Eₙ)
    ext x
    simp
  have hmap : Measure.map A.symm volume =
      ENNReal.ofReal |LinearMap.det (A : Eₙ →ₗ[ℝ] Eₙ)| • (volume : Measure Eₙ) := by
    rw [← hdet]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume (det_ne_zero A.symm)
  have := integral_map_equiv (μ := volume) A.symm.toHomeomorph.toMeasurableEquiv h
  change ∫ y, h y ∂Measure.map A.symm volume = ∫ x, h (A.symm x) at this
  rw [← this, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]

/-- The linear change of variable `f ↦ |det A|^{-1/2} f ∘ A⁻¹`. -/
def dilate (A : Eₙ ≃L[ℝ] Eₙ) : 𝓢ₙ ≃L[ℂ] 𝓢ₙ :=
  .equivOfInverse ((detFactor A : ℂ) • compCLMOfContinuousLinearEquiv ℂ A.symm)
    ((detFactor A : ℂ)⁻¹ • compCLMOfContinuousLinearEquiv ℂ A)
    (fun f => by
      have : (detFactor A : ℂ) ≠ 0 := ofReal_ne_zero.2 (detFactor_pos A).ne'
      ext x
      simp [this])
    (fun f => by
      have : (detFactor A : ℂ) ≠ 0 := ofReal_ne_zero.2 (detFactor_pos A).ne'
      ext x
      simp [this])

lemma dilate_apply (A : Eₙ ≃L[ℝ] Eₙ) (f : 𝓢ₙ) (x : Eₙ) :
    dilate A f x = detFactor A * f (A.symm x) :=
  rfl

lemma dilate_mem (A : Eₙ ≃L[ℝ] Eₙ) : (dilate A).toLinearEquiv ∈ schwartzAut n := by
  refine mem_schwartzAut _ fun f g => ?_
  have hsq : detFactor A * detFactor A * |LinearMap.det (A : Eₙ →ₗ[ℝ] Eₙ)| = 1 := by
    have hd := abs_pos.2 (det_ne_zero A)
    rw [detFactor, ← Real.rpow_add hd, ← Real.rpow_add_one hd.ne']
    norm_num
  simp only [dilate_apply, map_mul, conj_ofReal]
  calc ∫ x, ↑(detFactor A) * conj (f (A.symm x)) * (↑(detFactor A) * g (A.symm x))
      = ∫ x, ((detFactor A * detFactor A : ℝ) : ℂ) * (conj (f (A.symm x)) * g (A.symm x)) := by
        push_cast; ring_nf
    _ = ∫ x, conj (f x) * g x := by
        rw [integral_const_mul, integral_comp_symm A (fun x => conj (f x) * g x), real_smul,
          ← mul_assoc, ← ofReal_mul, hsq, ofReal_one, one_mul]

/-- The Fourier transform on `𝓢(ℝⁿ)`. -/
def fourierN : 𝓢ₙ ≃L[ℂ] 𝓢ₙ := fourierCLE ℂ 𝓢ₙ

lemma fourierN_mem : (fourierN (n := n)).toLinearEquiv ∈ schwartzAut n :=
  mem_schwartzAut _ fun f g => by
    simpa [fourierN, fourierCLE_apply, RCLike.inner_apply, mul_comm] using
      integral_inner_fourier_fourier f g

variable (n) in
/-- The linear changes of frame of `𝓢(ℝⁿ)`: the group generated by the translations, the
modulations, the linear changes of variable, the Fourier transform and the chirps. It contains the
metaplectic group up to phases. -/
def linearFrames : Subgroup (𝓢ₙ ≃ₗ[ℂ] 𝓢ₙ) :=
  Subgroup.closure <|
    Set.range (fun a => (translateN a).toLinearEquiv) ∪
    Set.range (fun a => (modulate a).toLinearEquiv) ∪
    Set.range (fun A => (dilate A).toLinearEquiv) ∪
    {fourierN.toLinearEquiv} ∪
    Set.range (fun B => (chirp B).toLinearEquiv)

theorem linearFrames_le_schwartzAut : linearFrames n ≤ schwartzAut n := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨A, rfl⟩) | rfl) | ⟨B, rfl⟩)
  · exact translateN_mem a
  · exact phase_mem (Function.hasTemperateGrowth_inner_right a)
  · exact dilate_mem A
  · exact fourierN_mem
  · exact phase_mem _

/-- **The linear changes of frame of Example 3 satisfy [B]WDQ.** -/
theorem isFrameCompatible_linearFrames {ħ : ℝ} (hħ : ħ ≠ 0) :
    IsFrameCompatible (l2CoreN n) (obsN n ħ)
      (FrameGroup.ofSubgroup (linearFrames n) fun _ he => (linearFrames_le_schwartzAut he).1) :=
  (isFrameCompatible_schwartzN hħ _ _).2 linearFrames_le_schwartzAut

end SchwartzN

end QuantumVectorSpaces.FurtherResults
