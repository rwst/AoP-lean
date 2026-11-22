/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Geometry.Symplectic.Manifold.FubiniStudy.Liouville
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import ForMathlib.Geometry.Manifold.DifferentialForm.Integration.Measure
import TauCeti.Analysis.InnerProductSpace.Euclidean.CrossProduct
import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman.Sphere

/-!
# The Fubini–Study form of the projective line

The projective line `ℂP¹ = ℙ ℂ (Fin 2 → ℂ)` carries the Fubini–Study form
`Projectivization.fubiniStudyForm 1`, the reduction of the standard form `Im ⟪u, w⟫` of `ℂ²` at the
unit sphere `S³`. The Riemann sphere `OnePoint ℂ` carries TauCeti's Fubini–Study form
`OnePoint.fubiniStudyForm`, of total area one, and Mathlib's bijection `t ↦ [t : 1]`,
`∞ ↦ [1 : 0]` (`OnePoint.equivProjectivization`) is a diffeomorphism between them. This file
compares the two forms and then the projective line with the round sphere `S² ⊂ ℝ³`.

**The two Fubini–Study forms.** Along `t ↦ [t : 1]` the form of `ℂP¹` pulls back to `π` times
that of the Riemann sphere (`Projectivization.mpullback_equivProjectivization_fubiniStudyForm`).
By uniqueness of the descended form it suffices that `π ω` on the Riemann sphere pulls back along
`S³ → ℂP¹ → OnePoint ℂ`, `(z₀, z₁) ↦ z₀ / z₁`, to the restricted standard form. Two smooth forms
that agree on the dense set `z₁ ≠ 0` are equal. There, with `ρ(t) = 1 / (π (1 + |t|²)²)` the
density of `ω` and `D_u = z₁ u₀ - z₀ u₁` for a tangent vector `u`, the pullback is
`π ρ(z₀ / z₁) Im (conj (D_u / z₁²) D_w / z₁²) = Im (conj D_u D_w)`, since `|z₀|² + |z₁|² = 1`.
By Lagrange's identity, `conj D_u D_w = ⟪u, w⟫ - ⟪u, z⟫ ⟪z, w⟫`, and the last product is real
because `u` and `w` are tangent, `Re ⟪z, u⟫ = Re ⟪z, w⟫ = 0`. So the pullback is `Im ⟪u, w⟫`.

**The round sphere.** Inverse stereographic projection from the north pole `e₂`, read on the
equatorial plane through `t ↦ (Re t, -Im t, 0)`, is TauCeti's diffeomorphism
`OnePoint.diffeomorphSphere` of the Riemann sphere onto `S²`; it pulls the area form
`x ⬝ (v × w)` of `S²` back to `4π ω`. Composed with the inverse of `t ↦ [t : 1]` it gives a
diffeomorphism `Projectivization.sphereDiffeomorph` of `ℂP¹` onto `S²`,
`[z₀ : z₁] ↦ (2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁), |z₀|² - |z₁|²) / (|z₀|² + |z₁|²)`, the Bloch
map of quantum mechanics. It pulls the area form back to `4` times the Fubini–Study form
(`Projectivization.mpullback_sphereDiffeomorph_sphereAreaForm`), so it carries the Liouville
measure of `ℂP¹` to a quarter of the area measure of `S²`
(`Projectivization.map_fubiniStudyMeasure_sphereDiffeomorph`), and `ℂP¹` has area `π`
(`Projectivization.fubiniStudyMeasure_univ`).

## Main definitions

* `OnePoint.realDiffeomorphProjectivization`: `t ↦ [t : 1]` as a diffeomorphism of real
  manifolds.
* `Projectivization.sphereDiffeomorph`: the diffeomorphism of `ℂP¹` onto the unit sphere of `ℝ³`.

## Main results

* `Projectivization.mpullback_equivProjectivization_fubiniStudyForm`: the Fubini–Study form of
  `ℂP¹` pulls back to `π` times that of the Riemann sphere.
* `Projectivization.mpullback_sphereDiffeomorph_sphereAreaForm`: the area form of `S²` pulls back
  to `4` times the Fubini–Study form of `ℂP¹`.
* `Projectivization.map_fubiniStudyMeasure_sphereDiffeomorph`: the Liouville measure of `ℂP¹` is
  carried to a quarter of the area measure of `S²`.
* `Projectivization.fubiniStudyMeasure_univ`: `ℂP¹` has Liouville measure `π`.
-/

open Metric MeasureTheory TauCeti ComplexConjugate
open scoped Manifold ContDiff LinearAlgebra.Projectivization TauCeti.ComplexManifold EuclideanSpace

public section

noncomputable section

set_option hygiene false in
/-- `ℂ²` with its Hermitian inner product. -/
local notation "E2" => EuclideanSpace ℂ (Fin (1 + 1))

set_option hygiene false in
/-- The unit sphere `S³` of `ℂ²`. -/
local notation "S³" => sphere (0 : E2) 1

set_option hygiene false in
/-- The inclusion of `S³` into `ℂ²`. -/
local notation "ιS" => ((↑) : S³ → E2)

set_option hygiene false in
/-- `ℝ³`. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option hygiene false in
/-- The unit sphere `S²` of `ℝ³`. -/
local notation "S²" => sphere (0 : ℝ³) 1

/-- A two-form scaled by `c` evaluates to `c` times the form. -/
theorem TauCeti.SmoothTwoForm.eval₂_smul {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    [IsManifold I ∞ M] (c : ℝ) (φ : SmoothTwoForm I M) (x : M) (v w : TangentSpace I x) :
    SmoothBundleForm.eval₂ (c • φ) x v w = c * SmoothBundleForm.eval₂ φ x v w := by
  simp only [SmoothBundleForm.eval₂_apply, Submodule.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- The map `t ↦ [t : 1]`, `∞ ↦ [1 : 0]` is smooth as a map of real manifolds. -/
theorem OnePoint.contMDiff_equivProjectivization_real :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin 1 → ℂ) ∞ (OnePoint.equivProjectivization ℂ) := by
  simpa using ((OnePoint.contMDiff_equivProjectivization (𝕜 := ℂ)).restrictScalars ℝ).of_le le_top

/-- The inverse of `t ↦ [t : 1]` is smooth as a map of real manifolds. -/
theorem OnePoint.contMDiff_equivProjectivization_symm_real :
    ContMDiff 𝓘(ℝ, Fin 1 → ℂ) 𝓘(ℝ, ℂ) ∞ (OnePoint.equivProjectivization ℂ).symm := by
  simpa using ((OnePoint.contMDiff_equivProjectivization_symm (𝕜 := ℂ)).restrictScalars ℝ).of_le
    le_top

/-- The Riemann sphere and the projective line `ℙ ℂ (Fin 2 → ℂ)` are diffeomorphic as real
manifolds, through `t ↦ [t : 1]` and `∞ ↦ [1 : 0]`. -/
@[expose] def OnePoint.realDiffeomorphProjectivization :
    OnePoint ℂ ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, Fin 1 → ℂ)⟯ ℙ ℂ (Fin 2 → ℂ) where
  toEquiv := OnePoint.equivProjectivization ℂ
  contMDiff_toFun := OnePoint.contMDiff_equivProjectivization_real
  contMDiff_invFun := OnePoint.contMDiff_equivProjectivization_symm_real

@[simp]
theorem OnePoint.coe_realDiffeomorphProjectivization :
    ⇑OnePoint.realDiffeomorphProjectivization = OnePoint.equivProjectivization ℂ :=
  rfl

@[simp]
theorem OnePoint.coe_realDiffeomorphProjectivization_symm :
    ⇑OnePoint.realDiffeomorphProjectivization.symm = (OnePoint.equivProjectivization ℂ).symm :=
  rfl

/-- The Fubini–Study form of the Riemann sphere, scaled by `c`, at a finite point `t`. -/
theorem OnePoint.eval₂_smul_fubiniStudyForm_coe (c : ℝ) (t a b : ℂ) :
    SmoothBundleForm.eval₂ (c • OnePoint.fubiniStudyForm) (t : OnePoint ℂ) a b =
      c * (OnePoint.fubiniStudyDensity t * (conj a * b).im) :=
  (SmoothTwoForm.eval₂_smul c _ _ _ _).trans
    (congrArg (c * ·) (OnePoint.eval₂_fubiniStudyForm_coe t a b))

namespace Projectivization

/-! ### The Fubini–Study forms of `ℂP¹` and of the Riemann sphere -/

/-- The affine coordinate `z₀ / z₁` of a vector of `ℂ²`. -/
private def ratio (w : E2) : ℂ := (w.ofLp 1)⁻¹ * w.ofLp 0

/-- The derivative of `w ↦ w₀ / w₁`. -/
private def ratioDeriv (w : E2) : E2 →L[ℂ] ℂ :=
  (w.ofLp 1)⁻¹ • EuclideanSpace.proj 0 - ((w.ofLp 1)⁻¹ ^ 2 * w.ofLp 0) • EuclideanSpace.proj 1

private theorem hasFDerivAt_ratio {w : E2} (hw : w.ofLp 1 ≠ 0) :
    HasFDerivAt ratio (ratioDeriv w) w := by
  have h1 : HasFDerivAt (fun v : E2 ↦ v.ofLp 1) (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)) w :=
    (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).hasFDerivAt
  have h0 : HasFDerivAt (fun v : E2 ↦ v.ofLp 0) (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)) w :=
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).hasFDerivAt
  refine (((hasFDerivAt_inv hw).comp w h1).mul h0).congr_fderiv ?_
  ext u
  simp [ratioDeriv]
  field_simp
  ring

/-- The map `S³ → ℂP¹ → OnePoint ℂ` is `z ↦ z₀ / z₁`, and `∞` where `z₁ = 0`. -/
private theorem equivProjectivization_symm_hopfMap (x : S³) :
    (OnePoint.equivProjectivization ℂ).symm (hopfMap 1 x) =
      if (x : E2).ofLp 1 = 0 then OnePoint.infty else ((ratio x : ℂ) : OnePoint ℂ) := by
  rw [hopfMap_apply, OnePoint.equivProjectivization_symm_apply_mk]
  rfl

/-- Where `z₁ ≠ 0`, the derivative of `S³ → OnePoint ℂ` is that of `z ↦ z₀ / z₁`. -/
private theorem hasMFDerivAt_equivProjectivization_symm_comp_hopfMap {x : S³}
    (hx : (x : E2).ofLp 1 ≠ 0) :
    HasMFDerivAt (𝓡 (2 * 1 + 1)) 𝓘(ℝ, ℂ)
      ((OnePoint.equivProjectivization ℂ).symm ∘ hopfMap 1) x
      ((ratioDeriv (x : E2)).restrictScalars ℝ ∘L mfderiv (𝓡 (2 * 1 + 1)) 𝓘(ℝ, E2) ιS x) := by
  have ho : IsOpen {q : S³ | (q : E2).ofLp 1 ≠ 0} :=
    isOpen_ne_fun ((EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).continuous.comp
      continuous_subtypeVal) continuous_const
  have heq : (OnePoint.equivProjectivization ℂ).symm ∘ hopfMap 1 =ᶠ[nhds x]
      fun q : S³ ↦ ((ratio q : ℂ) : OnePoint ℂ) := by
    filter_upwards [ho.mem_nhds hx] with q hq
    rw [Function.comp_apply, equivProjectivization_symm_hopfMap]
    simp [hq]
  have hι : HasMFDerivAt (𝓡 (2 * 1 + 1)) 𝓘(ℝ, E2) ιS x
      (mfderiv (𝓡 (2 * 1 + 1)) 𝓘(ℝ, E2) ιS x) :=
    ((contMDiff_coe_sphere (m := 1) x).mdifferentiableAt one_ne_zero).hasMFDerivAt
  have hr := ((hasFDerivAt_ratio hx).restrictScalars ℝ).hasMFDerivAt
  exact ((OnePoint.hasMFDerivAt_coe (ratio x)).comp x (hr.comp x hι)).congr_of_eventuallyEq heq

/-- Lagrange's identity on `S³`: for tangent vectors `u`, `w` at `z`, with `D_u = z₁ u₀ - z₀ u₁`,
`Im (conj D_u D_w) = Im ⟪u, w⟫`. -/
private theorem im_conj_mul_eq_of_tangent (a b u₀ u₁ w₀ w₁ : ℂ) (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1)
    (hu : (conj a * u₀ + conj b * u₁).re = 0) (hw : (conj a * w₀ + conj b * w₁).re = 0) :
    (conj (b * u₀ - a * u₁) * (b * w₀ - a * w₁)).im = (conj u₀ * w₀ + conj u₁ * w₁).im := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  obtain ⟨p₁, p₂⟩ := u₀
  obtain ⟨q₁, q₂⟩ := u₁
  obtain ⟨r₁, r₂⟩ := w₀
  obtain ⟨s₁, s₂⟩ := w₁
  simp only [Complex.sq_norm, Complex.normSq_mk] at hn
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im] at hu hw ⊢
  linear_combination (p₁ * r₂ - p₂ * r₁ + q₁ * s₂ - q₂ * s₁) * hn
    - (a₁ * r₂ - a₂ * r₁ + b₁ * s₂ - b₂ * s₁) * hu + (a₁ * p₂ - a₂ * p₁ + b₁ * q₂ - b₂ * q₁) * hw

/-- The pullback of `π ω` along `z ↦ z₀ / z₁` at a point of `S³` with `z₁ ≠ 0`, on tangent
vectors `u`, `w`, is `Im ⟪u, w⟫`. -/
private theorem pi_mul_fubiniStudyDensity_ratio (a b u₀ u₁ w₀ w₁ : ℂ) (hb : b ≠ 0)
    (hn : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1) (hu : (conj a * u₀ + conj b * u₁).re = 0)
    (hw : (conj a * w₀ + conj b * w₁).re = 0) :
    Real.pi * (OnePoint.fubiniStudyDensity (b⁻¹ * a) *
      (conj (b⁻¹ * u₀ - (b⁻¹) ^ 2 * a * u₁) * (b⁻¹ * w₀ - (b⁻¹) ^ 2 * a * w₁)).im) =
      (conj u₀ * w₀ + conj u₁ * w₁).im := by
  rw [← im_conj_mul_eq_of_tangent a b u₀ u₁ w₀ w₁ hn hu hw]
  have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  have h₁ : b⁻¹ * u₀ - (b⁻¹) ^ 2 * a * u₁ = (b⁻¹) ^ 2 * (b * u₀ - a * u₁) := by field_simp
  have h₂ : b⁻¹ * w₀ - (b⁻¹) ^ 2 * a * w₁ = (b⁻¹) ^ 2 * (b * w₀ - a * w₁) := by field_simp
  have h₃ : conj ((b⁻¹) ^ 2) * (b⁻¹) ^ 2 = ((‖b‖ ^ 2)⁻¹ ^ 2 : ℝ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast
    simp [inv_pow]
  rw [h₁, h₂, map_mul, mul_mul_mul_comm, h₃, Complex.im_ofReal_mul,
    OnePoint.fubiniStudyDensity_def, norm_mul, norm_inv]
  have hden : 1 + (‖b‖⁻¹ * ‖a‖) ^ 2 = (‖b‖ ^ 2)⁻¹ := by
    field_simp
    linarith
  rw [hden]
  field_simp

/-- The points of `S³` with `z₁ ≠ 0` are dense. -/
private theorem dense_setOf_ofLp_one_ne_zero : Dense {x : S³ | (x : E2).ofLp 1 ≠ 0} := by
  intro x
  by_cases hx : (x : E2).ofLp 1 = 0
  swap
  · exact subset_closure hx
  -- Approach `x` along the unit vectors in the direction of `x + ε e₁`.
  set v : E2 := EuclideanSpace.single 1 1
  have hx₀ : (x : E2).ofLp 0 ≠ 0 := by
    intro h₀
    have h := norm_eq_of_mem_sphere x
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two] at h
    simp [h₀, hx] at h
  have hne (ε : ℝ) : (x : E2) + (ε : ℂ) • v ≠ 0 := fun h ↦ hx₀ (by
    simpa [v] using congrArg (fun y : E2 ↦ y.ofLp 0) h)
  set c : ℝ → S³ := fun ε ↦ ⟨‖(x : E2) + (ε : ℂ) • v‖⁻¹ • ((x : E2) + (ε : ℂ) • v), by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hne ε))]⟩
  have hcont : Continuous c := by
    refine Continuous.subtype_mk ?_ _
    have h₁ : Continuous fun ε : ℝ ↦ (x : E2) + (ε : ℂ) • v :=
      continuous_const.add ((Complex.continuous_ofReal).smul continuous_const)
    exact (h₁.norm.inv₀ fun ε ↦ norm_ne_zero_iff.2 (hne ε)).smul h₁
  have hc₀ : c 0 = x := Subtype.ext (by simp [c, norm_eq_of_mem_sphere x])
  refine mem_closure_of_tendsto (hc₀ ▸ hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
    Filter.Tendsto c (nhdsWithin 0 {0}ᶜ) (nhds x)) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have h₁ : (x : E2) + ε • EuclideanSpace.single 1 1 ≠ 0 := by
    rw [← Complex.coe_smul]
    exact hne ε
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hε
  simp only [c, v, WithLp.ofLp_smul, WithLp.ofLp_add, Pi.smul_apply, Pi.add_apply, hx]
  simp [hε, h₁]

/-- `π ω` on the Riemann sphere pulls back along `S³ → ℂP¹ → OnePoint ℂ` to the restricted
standard form of `ℂ²`. -/
private theorem mpullback_comp_hopfMap :
    SmoothForm.mpullback ((OnePoint.equivProjectivization ℂ).symm ∘ hopfMap 1)
      (OnePoint.contMDiff_equivProjectivization_symm_real.comp (contMDiff_hopfMap ∞))
      (Real.pi • OnePoint.fubiniStudyForm) = sphereForm 1 := by
  refine SmoothBundleForm.eq_of_forall_mem_dense dense_setOf_ofLp_one_ne_zero fun x hx ↦ ?_
  ext m
  have hm : m = ![m 0, m 1] := by
    ext i
    fin_cases i <;> rfl
  rw [hm, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply,
    SmoothForm.eval₂_mpullback, (hasMFDerivAt_equivProjectivization_symm_comp_hopfMap hx).mfderiv,
    eval₂_sphereForm, Function.comp_apply, equivProjectivization_symm_hopfMap, ite_eq_right hx]
  refine (OnePoint.eval₂_smul_fubiniStudyForm_coe _ _ _ _).trans ?_
  set U := mvfderiv (𝓡 (2 * 1 + 1)) ιS x (m 0)
  set W := mvfderiv (𝓡 (2 * 1 + 1)) ιS x (m 1)
  change Real.pi * (OnePoint.fubiniStudyDensity (ratio x) *
    (conj (ratioDeriv (x : E2) U) * ratioDeriv (x : E2) W).im) = _
  -- `U` and `W` are tangent to `S³` at `x`.
  have hU : (inner ℂ (x : E2) U).re = 0 := by
    have h := mfderiv_coe_sphere_mem_orthogonal (n := 1) x (m 0)
    rwa [Submodule.mem_orthogonal_singleton_iff_inner_right,
      real_inner_eq_re_inner_euclideanSpace] at h
  have hW : (inner ℂ (x : E2) W).re = 0 := by
    have h := mfderiv_coe_sphere_mem_orthogonal (n := 1) x (m 1)
    rwa [Submodule.mem_orthogonal_singleton_iff_inner_right,
      real_inner_eq_re_inner_euclideanSpace] at h
  have hn := norm_eq_of_mem_sphere x
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_two, Real.sqrt_eq_one] at hn
  have hp (v : E2) (i : Fin 2) : EuclideanSpace.proj (𝕜 := ℂ) i v = v.ofLp i := rfl
  have hU' : (conj ((x : E2).ofLp 0) * U.ofLp 0 + conj ((x : E2).ofLp 1) * U.ofLp 1).re = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hU
  have hW' : (conj ((x : E2).ofLp 0) * W.ofLp 0 + conj ((x : E2).ofLp 1) * W.ofLp 1).re = 0 := by
    simpa [PiLp.inner_apply, Fin.sum_univ_two, mul_comm] using hW
  simp only [ratio, ratioDeriv, sub_apply, smul_apply, smul_eq_mul, hp]
  rw [pi_mul_fubiniStudyDensity_ratio _ _ _ _ _ _ hx hn hU' hW',
    real_inner_eq_re_inner_euclideanSpace]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- **The Fubini–Study form of `ℂP¹` is `π` times that of the Riemann sphere**, read through the
inverse of `t ↦ [t : 1]`. -/
theorem mpullback_equivProjectivization_symm_fubiniStudyForm :
    SmoothForm.mpullback (OnePoint.equivProjectivization ℂ).symm
      OnePoint.contMDiff_equivProjectivization_symm_real (Real.pi • OnePoint.fubiniStudyForm) =
      fubiniStudyForm 1 := by
  refine eq_fubiniStudyForm_of_mpullback_eq ?_
  rw [SmoothForm.mpullback_mpullback]
  exact mpullback_comp_hopfMap

/-- **The Fubini–Study form of `ℂP¹` pulls back along `t ↦ [t : 1]` to `π` times that of the
Riemann sphere**, which has total area one. -/
theorem mpullback_equivProjectivization_fubiniStudyForm :
    SmoothForm.mpullback (OnePoint.equivProjectivization ℂ)
      OnePoint.contMDiff_equivProjectivization_real (fubiniStudyForm 1) =
      Real.pi • OnePoint.fubiniStudyForm := by
  rw [← mpullback_equivProjectivization_symm_fubiniStudyForm]
  exact SmoothForm.mpullback_symm_mpullback OnePoint.realDiffeomorphProjectivization.symm _

/-! ### The projective line as the round sphere -/

/-- The north pole `e₂` of `S²`. -/
private def northPole : S² :=
  ⟨EuclideanSpace.single 2 1, by simp⟩

/-- The map `t ↦ (Re t, -Im t, 0)` onto the equatorial plane. -/
private def conjIsometry : ℂ →ₗᵢ[ℝ] (ℝ ∙ (northPole : ℝ³))ᗮ where
  toFun t := ⟨WithLp.toLp 2 ![t.re, -t.im, 0], by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp [northPole, PiLp.inner_apply]⟩
  map_add' s t := by
    ext i
    fin_cases i <;> simp
    ring
  map_smul' c t := by
    ext i
    fin_cases i <;> simp
  norm_map' t := by
    change ‖(WithLp.toLp 2 ![t.re, -t.im, 0] : ℝ³)‖ = ‖t‖
    rw [EuclideanSpace.norm_eq, Complex.norm_eq_sqrt_sq_add_sq]
    simp [Fin.sum_univ_three]

/-- The isometry `t ↦ (Re t, -Im t, 0)` of `ℂ` onto the equatorial plane. -/
private def conjIsometryEquiv : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (northPole : ℝ³))ᗮ :=
  conjIsometry.toLinearIsometryEquiv (by
    rw [Complex.finrank_real_complex, Submodule.finrank_orthogonal_span_singleton (n := 2)]
    simp [northPole])

private theorem coe_conjIsometryEquiv (t : ℂ) :
    (conjIsometryEquiv t : ℝ³) = WithLp.toLp 2 ![t.re, -t.im, 0] :=
  rfl

/-- The frame `(e₂, ι 1, ι i)` has volume `-1`, so the area form pulls back to `+4π ω`. -/
private theorem volumeForm_frame :
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.volumeForm
      ![(northPole : ℝ³), (conjIsometryEquiv 1 : ℝ³), (conjIsometryEquiv Complex.I : ℝ³)] = -1 := by
  rw [EuclideanSpace.volumeForm_basisFun_orientation_three, coe_conjIsometryEquiv,
    coe_conjIsometryEquiv]
  simp [northPole, cross_apply, dotProduct]

/-- Inverse stereographic projection from `e₂` pulls the area form of `S²` back to `4π` times
the Fubini–Study form of the Riemann sphere. -/
private theorem mpullback_diffeomorphSphere_sphereAreaForm :
    SmoothForm.mpullback (OnePoint.diffeomorphSphere northPole conjIsometryEquiv)
      ((OnePoint.diffeomorphSphere northPole conjIsometryEquiv).contMDiff.of_le le_top)
      sphereAreaForm = (4 * Real.pi) • OnePoint.fubiniStudyForm := by
  refine Subtype.ext ?_
  rw [SmoothForm.coe_mpullback, sphereAreaForm_eq_sphereVolumeForm,
    OnePoint.mpullback_diffeomorphSphere_sphereVolumeForm, volumeForm_frame]
  simp

/-- **The projective line is the round sphere**: the diffeomorphism of `ℂP¹` onto the unit sphere
of `ℝ³` through the Riemann sphere, `[z₀ : z₁] ↦ (2 Re (conj z₀ z₁), 2 Im (conj z₀ z₁),
|z₀|² - |z₁|²) / (|z₀|² + |z₁|²)`. -/
def sphereDiffeomorph : ℙ ℂ (Fin 2 → ℂ) ≃ₘ⟮𝓘(ℝ, Fin 1 → ℂ), 𝓡 2⟯ S² :=
  OnePoint.realDiffeomorphProjectivization.symm.trans
    { toEquiv := (OnePoint.diffeomorphSphere northPole conjIsometryEquiv).toEquiv
      contMDiff_toFun := (OnePoint.diffeomorphSphere northPole conjIsometryEquiv).contMDiff.of_le
        le_top
      contMDiff_invFun :=
        (OnePoint.diffeomorphSphere northPole conjIsometryEquiv).symm.contMDiff.of_le le_top }

/-- `[1 : 0]` goes to the north pole. -/
theorem sphereDiffeomorph_equivProjectivization_infty :
    (sphereDiffeomorph (OnePoint.equivProjectivization ℂ OnePoint.infty) : ℝ³) =
      WithLp.toLp 2 ![0, 0, 1] := by
  simp only [sphereDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    OnePoint.coe_realDiffeomorphProjectivization_symm, Equiv.symm_apply_apply]
  change ((OnePoint.diffeomorphSphere northPole conjIsometryEquiv OnePoint.infty : S²) : ℝ³) = _
  rw [OnePoint.diffeomorphSphere_infty]
  ext i
  fin_cases i <;> simp [northPole]

/-- `[t : 1]` goes to `(2 Re t, -2 Im t, |t|² - 1) / (1 + |t|²)`. -/
theorem sphereDiffeomorph_equivProjectivization_coe (t : ℂ) :
    (sphereDiffeomorph (OnePoint.equivProjectivization ℂ t) : ℝ³) =
      WithLp.toLp 2 ((1 + ‖t‖ ^ 2)⁻¹ • ![2 * t.re, -2 * t.im, ‖t‖ ^ 2 - 1]) := by
  simp only [sphereDiffeomorph, Diffeomorph.coe_trans, Function.comp_apply,
    OnePoint.coe_realDiffeomorphProjectivization_symm, Equiv.symm_apply_apply]
  change ((OnePoint.diffeomorphSphere northPole conjIsometryEquiv t : S²) : ℝ³) = _
  rw [OnePoint.coe_diffeomorphSphere_coe, coe_conjIsometryEquiv]
  ext i
  fin_cases i <;> simp [northPole]

/-- **The area form of the sphere is `4` times the Fubini–Study form of `ℂP¹`.** -/
theorem mpullback_sphereDiffeomorph_sphereAreaForm :
    SmoothForm.mpullback sphereDiffeomorph sphereDiffeomorph.contMDiff sphereAreaForm =
      (4 : ℝ) • fubiniStudyForm 1 := by
  have h : ⇑sphereDiffeomorph = OnePoint.diffeomorphSphere northPole conjIsometryEquiv ∘
      (OnePoint.equivProjectivization ℂ).symm :=
    rfl
  have hcongr (f g : ℙ ℂ (Fin 2 → ℂ) → S²) (hf : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞ f)
      (hg : ContMDiff 𝓘(ℝ, Fin 1 → ℂ) (𝓡 2) ∞ g) (hfg : f = g) :
      SmoothForm.mpullback f hf sphereAreaForm = SmoothForm.mpullback g hg sphereAreaForm := by
    subst hfg
    rfl
  have hD : ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ (OnePoint.diffeomorphSphere northPole conjIsometryEquiv) :=
    (OnePoint.diffeomorphSphere northPole conjIsometryEquiv).contMDiff.of_le le_top
  rw [hcongr _ _ _ (hD.comp OnePoint.contMDiff_equivProjectivization_symm_real) h,
    ← SmoothForm.mpullback_mpullback _ _ OnePoint.contMDiff_equivProjectivization_symm_real hD,
    mpullback_diffeomorphSphere_sphereAreaForm, mul_smul, map_smul,
    mpullback_equivProjectivization_symm_fubiniStudyForm]

/-- **The Liouville measure of `ℂP¹` is a quarter of the area of the sphere**, carried by
`Projectivization.sphereDiffeomorph`. -/
theorem map_fubiniStudyMeasure_sphereDiffeomorph :
    (fubiniStudyMeasure 1).map sphereDiffeomorph =
      (ENNReal.ofReal 4)⁻¹ • sphereAreaForm.liouvilleMeasure 1 := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 * 1) := ⟨by simp⟩
  have h := sphereDiffeomorph.toHomeomorph.measurePreserving_liouvilleMeasure_of_finrank_eq
    (σ := (4 : ℝ) • fubiniStudyForm 1) (τ := sphereAreaForm) (n := 1)
    (sphereDiffeomorph.contMDiff.mdifferentiable (by simp))
    (by rw [Diffeomorph.coe_toHomeomorph, ← SmoothForm.coe_mpullback _ sphereDiffeomorph.contMDiff,
      mpullback_sphereDiffeomorph_sphereAreaForm])
  rw [SmoothTwoForm.liouvilleMeasure_smul, Diffeomorph.coe_toHomeomorph] at h
  rw [← h.map_eq, fubiniStudyMeasure_def, Measure.map_smul, smul_smul,
    abs_of_pos (by norm_num : (0 : ℝ) < 4), pow_one,
    ENNReal.inv_mul_cancel (by simp) ENNReal.ofReal_ne_top, one_smul]
  exact sphereDiffeomorph.continuous.measurable.aemeasurable

/-- **`ℂP¹` has area `π`** for the Liouville measure of its Fubini–Study form. -/
theorem fubiniStudyMeasure_univ : fubiniStudyMeasure 1 Set.univ = ENNReal.ofReal Real.pi := by
  have h := congrArg (fun μ : Measure S² ↦ μ Set.univ) map_fubiniStudyMeasure_sphereDiffeomorph
  simp only [smul_apply, liouvilleMeasure_sphereAreaForm_univ, smul_eq_mul] at h
  rw [Measure.map_apply sphereDiffeomorph.continuous.measurable MeasurableSet.univ,
    Set.preimage_univ] at h
  rw [h, ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end Projectivization
