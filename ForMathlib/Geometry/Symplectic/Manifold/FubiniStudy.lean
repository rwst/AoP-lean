/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Geometry.Manifold.Instances.HopfMap
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Geometry.Symplectic.Manifold.Descent

/-!
# The Fubini–Study form on complex projective space

The standard symplectic form of `ℂⁿ⁺¹` is `ω(u, w) = Im ⟪u, w⟫_ℂ = ⟪i u, w⟫_ℝ`. Its restriction
`σ` to the unit sphere `S²ⁿ⁺¹` (`Projectivization.sphereForm`) is closed, and at a unit vector `x`
its kernel is the line spanned by the tangent vector `i x` of the circle orbit through `x`. This is
also the kernel of the derivative of the Hopf map `S²ⁿ⁺¹ → ℂPⁿ`: the derivative is surjective onto
a space of dimension `2 n`, so its kernel is a line, and it contains `i x` because the Hopf map is
constant along complex multiples. Unit complex scalars preserve `ω` and commute with the Hopf map,
so `σ` is basic for the Hopf map (`Projectivization.isBasic_sphereForm`).

By symplectic descent, `σ` is the pullback along the Hopf map of a unique symplectic form on
`ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`, the Fubini–Study form `Projectivization.fubiniStudyForm`. This is
the symplectic reduction of `ℂⁿ⁺¹` by the circle at the unit sphere.

## Main definitions

* `Projectivization.sphereForm`: the restriction of the standard form of `ℂⁿ⁺¹` to `S²ⁿ⁺¹`.
* `Projectivization.fubiniStudyForm`: its descent along the Hopf map.

## Main results

* `Projectivization.ker_bilinFormAt_sphereForm`: the kernel of `σ` is the kernel of the
  derivative of the Hopf map.
* `Projectivization.isBasic_sphereForm`: `σ` is basic for the Hopf map.
* `Projectivization.mpullback_fubiniStudyForm`: the Fubini–Study form pulls back to `σ`.
* `Projectivization.isSymplectic_fubiniStudyForm`: the Fubini–Study form is symplectic.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (`ℂPⁿ` as the reduced space of `ℂⁿ⁺¹` by the circle).
-/

public section

noncomputable section

open Function Manifold Metric Module Set TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization InnerProductSpace

namespace Projectivization

variable {n : ℕ}

set_option hygiene false in
/-- The inclusion of the unit sphere `S²ⁿ⁺¹` into `ℂⁿ⁺¹`. -/
local notation "ιS" =>
  ((↑) : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 → EuclideanSpace ℂ (Fin (n + 1)))

/-- The real inner product of `ℂⁿ⁺¹` is the real part of the complex one. -/
theorem real_inner_eq_re_inner_euclideanSpace (a b : EuclideanSpace ℂ (Fin (n + 1))) :
    ⟪a, b⟫_ℝ = (⟪a, b⟫_ℂ).re := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  rfl

/-- Multiplication by `i` is skew for the real inner product of `ℂⁿ⁺¹`. -/
theorem real_inner_I_smul_self_euclideanSpace (a : EuclideanSpace ℂ (Fin (n + 1))) :
    ⟪Complex.I • a, a⟫_ℝ = 0 := by
  simp [real_inner_eq_re_inner_euclideanSpace, inner_smul_left, ← Complex.ofReal_pow]

/-- Unit complex scalars preserve the real inner product of `ℂⁿ⁺¹`. -/
theorem real_inner_smul_smul_euclideanSpace {c : ℂ} (hc : ‖c‖ = 1)
    (a b : EuclideanSpace ℂ (Fin (n + 1))) : ⟪c • a, c • b⟫_ℝ = ⟪a, b⟫_ℝ := by
  rw [real_inner_eq_re_inner_euclideanSpace, real_inner_eq_re_inner_euclideanSpace,
    inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

variable (n) in
/-- The standard symplectic bilinear form `(u, w) ↦ ⟪i u, w⟫_ℝ = Im ⟪u, w⟫_ℂ` of `ℂⁿ⁺¹`. -/
@[expose] def stdSymplecticBilin :
    EuclideanSpace ℂ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℂ (Fin (n + 1)) →L[ℝ] ℝ :=
  (innerSL ℝ).comp (Complex.I • ContinuousLinearMap.id ℝ (EuclideanSpace ℂ (Fin (n + 1))))

theorem stdSymplecticBilin_apply (u w : EuclideanSpace ℂ (Fin (n + 1))) :
    stdSymplecticBilin n u w = ⟪Complex.I • u, w⟫_ℝ :=
  rfl

variable (n) in
/-- The restriction of the standard symplectic form of `ℂⁿ⁺¹` to the unit sphere `S²ⁿ⁺¹`. -/
def sphereForm : SmoothTwoForm (𝓡 (2 * n + 1)) (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :=
  SmoothForm.mpullback ιS contMDiff_coe_sphere (SmoothTwoForm.const (stdSymplecticBilin n))

/-- The restricted form evaluates as the standard form on the tangent vectors in `ℂⁿ⁺¹`. -/
theorem eval₂_sphereForm (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (v w : TangentSpace (𝓡 (2 * n + 1)) x) :
    SmoothBundleForm.eval₂ (sphereForm n) x v w =
      ⟪Complex.I • mvfderiv (𝓡 (2 * n + 1)) ιS x v,
        mvfderiv (𝓡 (2 * n + 1)) ιS x w⟫_ℝ := by
  rw [sphereForm, SmoothForm.eval₂_mpullback,
    SmoothTwoForm.const_apply _ real_inner_I_smul_self_euclideanSpace]
  rfl

/-- The restricted form is closed. -/
theorem isClosed_sphereForm : (sphereForm n).IsClosed :=
  (SmoothTwoForm.isClosed_const _).mpullback _ _

/-- The tangent vectors of the unit sphere at `x` are the vectors real-orthogonal to `x`. -/
theorem mfderiv_coe_sphere_mem_orthogonal (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (w : TangentSpace (𝓡 (2 * n + 1)) x) :
    mvfderiv (𝓡 (2 * n + 1)) ιS x w ∈
      (ℝ ∙ (x : EuclideanSpace ℂ (Fin (n + 1))))ᗮ := by
  rw [← range_mvfderiv_subtypeVal (n := 2 * n + 1) x]
  exact ⟨w, rfl⟩

/-- At a unit vector `x`, the vector `i x` is tangent to the sphere. -/
theorem exists_mfderiv_coe_eq_I_smul (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    ∃ u : TangentSpace (𝓡 (2 * n + 1)) x,
      mvfderiv (𝓡 (2 * n + 1)) ιS x u =
        Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1))) := by
  have h : Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1))) ∈
      (mvfderiv (𝓡 (2 * n + 1)) ιS x).range := by
    rw [range_mvfderiv_subtypeVal (n := 2 * n + 1),
      Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_comm]
    exact real_inner_I_smul_self_euclideanSpace _
  exact h

/-- The Hopf map is constant along complex multiples, so its derivative vanishes on `i x`. -/
theorem mfderiv_hopfMap_eq_zero (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    {u : TangentSpace (𝓡 (2 * n + 1)) x}
    (hu : mvfderiv (𝓡 (2 * n + 1)) ιS x u =
      Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1)))) :
    mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) x u = 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (ofLp_ne_zero_of_mem_sphere x)
  set G : EuclideanSpace ℂ (Fin (n + 1)) → Fin n → ℂ :=
    fun w j ↦ w.ofLp (i.succAbove j) / w.ofLp i
  have hG : ContDiffAt ℝ ∞ G x := contDiffAt_ratios i hi
  -- `G` is constant on the complex line through `x`, so its derivative vanishes on `i x`.
  have hGx : fderiv ℝ G x (Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1)))) = 0 := by
    have hconst : (fun t : ℝ ↦ G (x + t • Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1))))) =
        fun _ ↦ G x := by
      funext t
      ext j
      have ht : (1 + (t : ℂ) * Complex.I) ≠ 0 := fun h ↦ by
        simpa using congrArg Complex.re h
      simp only [G, WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Complex.real_smul]
      rw [show (x : EuclideanSpace ℂ (Fin (n + 1))).ofLp (i.succAbove j) +
          t * (Complex.I * (x : EuclideanSpace ℂ (Fin (n + 1))).ofLp (i.succAbove j)) =
          (1 + t * Complex.I) * (x : EuclideanSpace ℂ (Fin (n + 1))).ofLp (i.succAbove j) by
        ring, show (x : EuclideanSpace ℂ (Fin (n + 1))).ofLp i +
          t * (Complex.I * (x : EuclideanSpace ℂ (Fin (n + 1))).ofLp i) =
          (1 + t * Complex.I) * (x : EuclideanSpace ℂ (Fin (n + 1))).ofLp i by ring,
        mul_div_mul_left _ _ ht]
    have hline : HasDerivAt (fun t : ℝ ↦ (x : EuclideanSpace ℂ (Fin (n + 1))) +
        t • Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1))))
        (Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1)))) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1))))).const_add
        (x : EuclideanSpace ℂ (Fin (n + 1)))
    have h1 : HasDerivAt
        (fun t : ℝ ↦ G (x + t • Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1)))))
        (fderiv ℝ G x (Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1))))) 0 :=
      (hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
    rw [hconst] at h1
    exact h1.unique (hasDerivAt_const 0 (G x))
  have heq : hopfMap n =ᶠ[nhds x] ((affineChart i).symm ∘ G ∘ ιS) := hopfMap_eventuallyEq x hi
  have hcoe : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) ιS x :=
    (contMDiff_coe_sphere (m := 1) x).mdifferentiableAt one_ne_zero
  have hGd : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, Fin n → ℂ) G x :=
    (hG.differentiableAt (by simp)).mdifferentiableAt
  rw [heq.mfderiv_eq, ContinuousLinearMap.comp_apply, mfderiv_comp_apply x
    ((contMDiff_affineChart_symm_real i ∞ _).mdifferentiableAt (by simp)) (hGd.comp x hcoe),
    mfderiv_comp_apply x hGd hcoe]
  change tangentSpaceCast _ _ _ (mfderiv _ _ _ _
    (mfderiv _ _ G _ (mvfderiv (𝓡 (2 * n + 1)) ιS x u))) = 0
  have hG0 : mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) 𝓘(ℝ, Fin n → ℂ) G x
      (Complex.I • (x : EuclideanSpace ℂ (Fin (n + 1)))) = 0 := by
    rw [mfderiv_eq_fderiv]; exact hGx
  rw [hu, hG0, map_zero, map_zero]

/-- The derivative of the Hopf map has a one-dimensional kernel. -/
theorem finrank_ker_mfderiv_hopfMap (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    finrank ℝ (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) x).ker = 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) x).toLinearMap
  rw [LinearMap.range_eq_top.2 (surjective_mfderiv_hopfMap x), finrank_top] at h
  have hE : finrank ℝ (TangentSpace (𝓡 (2 * n + 1)) x) = 2 * n + 1 := finrank_euclideanSpace_fin
  have hF : finrank ℝ (TangentSpace 𝓘(ℝ, Fin n → ℂ) (hopfMap n x)) = 2 * n := by
    change finrank ℝ (Fin n → ℂ) = 2 * n
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  change finrank ℝ (LinearMap.ker _) = 1
  omega

/-- **The kernel of the restricted form is the kernel of the derivative of the Hopf map**: both
are the line spanned by the tangent vector `i x`. -/
theorem ker_bilinFormAt_sphereForm (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
    LinearMap.ker ((sphereForm n).bilinFormAt x) =
      (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) x).ker := by
  set D := mvfderiv (𝓡 (2 * n + 1)) ιS x
  have hD : Injective D := fun a b h ↦ injective_mvfderiv_subtypeVal_sphere (n := 2 * n + 1) x h
  obtain ⟨u₀, hu₀⟩ := exists_mfderiv_coe_eq_I_smul x
  have hu₀0 : u₀ ≠ 0 := by
    rintro rfl
    have hx := ne_zero_of_mem_unit_sphere x
    rw [map_zero] at hu₀
    exact hx ((smul_eq_zero.1 hu₀.symm).resolve_left Complex.I_ne_zero)
  have hmem (u) : u ∈ LinearMap.ker ((sphereForm n).bilinFormAt x) ↔
      ∀ w, ⟪Complex.I • D u, D w⟫_ℝ = 0 := by
    simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
      SmoothForm.bilinFormAt_apply, eval₂_sphereForm, D]
  -- The kernel of the form is the line through `u₀`.
  have hσ : LinearMap.ker ((sphereForm n).bilinFormAt x) = ℝ ∙ u₀ := by
    apply le_antisymm
    · intro u hu
      have h : Complex.I • D u ∈ (ℝ ∙ (x : EuclideanSpace ℂ (Fin (n + 1))))ᗮᗮ := by
        rw [Submodule.mem_orthogonal]
        intro a ha
        rw [← range_mvfderiv_subtypeVal (n := 2 * n + 1) x] at ha
        obtain ⟨w, rfl⟩ := ha
        rw [real_inner_comm]
        exact (hmem u).1 hu w
      rw [Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton] at h
      obtain ⟨t, ht⟩ := h
      rw [Submodule.mem_span_singleton]
      refine ⟨-t, hD ?_⟩
      rw [map_smul, hu₀]
      have hDu : D u = -(Complex.I • Complex.I • D u) := by simp [smul_smul]
      rw [hDu, ← ht, smul_comm Complex.I t, neg_smul]
    · rw [Submodule.span_singleton_le_iff_mem, hmem]
      intro w
      have h := mfderiv_coe_sphere_mem_orthogonal x w
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h
      change ⟪Complex.I • mvfderiv (𝓡 (2 * n + 1)) ιS x u₀,
        mvfderiv (𝓡 (2 * n + 1)) ιS x w⟫_ℝ = 0
      rw [hu₀, smul_smul, Complex.I_mul_I, neg_one_smul, inner_neg_left, h, neg_zero]
  -- So is the kernel of the derivative of the Hopf map, by dimension.
  have hh : ℝ ∙ u₀ = (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) x).ker := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact mfderiv_hopfMap_eq_zero x hu₀
    · rw [finrank_span_singleton hu₀0, finrank_ker_mfderiv_hopfMap]
  rw [hσ, hh]

/-- **The restricted form is basic for the Hopf map.** Two unit vectors with the same image differ
by a unit complex scalar `c`; multiplication by `c` commutes with the Hopf map and preserves the
standard form, and tangent vectors with the same image under the derivative of the Hopf map differ
by elements of its kernel, which is the kernel of the form. -/
theorem isBasic_sphereForm :
    RoughForm.IsBasic (V := ℝ) (k := 2) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) (sphereForm n).1 := by
  refine RoughForm.isBasic_iff.2 fun x y hxy v w hvw ↦ ?_
  -- `y = c • x` for a unit complex number `c`.
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • (x : EuclideanSpace ℂ (Fin (n + 1))) = y := by
    rw [eq_comm, hopfMap_apply, hopfMap_apply,
      mk_eq_mk_iff' ℂ _ _ _ (ofLp_ne_zero_of_mem_sphere x)] at hxy
    obtain ⟨c, hc⟩ := hxy
    exact ⟨c, by ext j; simpa using congrFun hc j⟩
  have hc1 : ‖c‖ = 1 := by
    have h := congrArg norm hc
    rwa [norm_smul, norm_eq_of_mem_sphere, norm_eq_of_mem_sphere, mul_one] at h
  have hmS (p : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :
      c • (p : EuclideanSpace ℂ (Fin (n + 1))) ∈ sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 := by
    simp [norm_smul, hc1]
  let L : EuclideanSpace ℂ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℂ (Fin (n + 1)) :=
    c • ContinuousLinearMap.id ℝ _
  let m : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 :=
    codRestrict (L ∘ ιS) _ hmS
  have hm : ContMDiff (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1)) ∞ m :=
    ContMDiff.codRestrict_sphere (L.contMDiff.comp contMDiff_coe_sphere) hmS
  have hmd : MDifferentiableAt (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1)) m x :=
    (hm x).mdifferentiableAt (by simp)
  have hmx : m x = y := Subtype.ext hc
  have hhm : hopfMap n ∘ m = hopfMap n := by
    funext p
    rw [comp_apply, hopfMap_apply, hopfMap_apply, mk_eq_mk_iff' ℂ _ _ _
      (ofLp_ne_zero_of_mem_sphere p)]
    exact ⟨c, rfl⟩
  -- The derivative of `m`, read in the tangent space at `y = m x`.
  let dm : TangentSpace (𝓡 (2 * n + 1)) x →L[ℝ] TangentSpace (𝓡 (2 * n + 1)) y :=
    mfderiv (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1)) m x
  -- It is multiplication by `c` on the tangent vectors in `ℂⁿ⁺¹`.
  have hDm (u : TangentSpace (𝓡 (2 * n + 1)) x) :
      mvfderiv (𝓡 (2 * n + 1)) ιS y (dm u) = c • mvfderiv (𝓡 (2 * n + 1)) ιS x u := by
    have h1 := mfderiv_comp_apply_of_eq x
      ((contMDiff_coe_sphere (m := 1) y).mdifferentiableAt one_ne_zero) hmd hmx u
    have h2 := mfderiv_comp_apply x L.mdifferentiableAt
      ((contMDiff_coe_sphere (m := 1) x).mdifferentiableAt one_ne_zero) u
    rw [show ιS ∘ m = L ∘ ιS from rfl, h2, L.mfderiv_eq] at h1
    exact h1.symm
  have hhd (u : TangentSpace (𝓡 (2 * n + 1)) x) :
      mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) y (dm u) =
        mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) x u := by
    have h := mfderiv_comp_apply_of_eq x ((contMDiff_hopfMap ∞ y).mdifferentiableAt (by simp))
      hmd hmx u
    rw [hhm] at h
    exact h.symm
  -- Tangent vectors with the same image differ by elements of the kernel of the form.
  set B := (sphereForm n).bilinFormAt y
  have hk (i : Fin 2) : B (w i - dm (v i)) = 0 := by
    rw [← LinearMap.mem_ker, ker_bilinFormAt_sphereForm, LinearMap.mem_ker]
    change mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) (hopfMap n) y (w i - dm (v i)) = 0
    rw [map_sub, hhd, hvw i]
    exact sub_self _
  have hB (a b k l : TangentSpace (𝓡 (2 * n + 1)) y) (hk : B k = 0) (hl : B l = 0) :
      B (a + k) (b + l) = B a b := by
    have hla : B l a = 0 := by rw [hl]; rfl
    have hl' : B a l = 0 := by
      rw [SmoothForm.bilinFormAt_apply] at hla ⊢
      rw [SmoothBundleForm.eval₂_swap, hla, neg_zero]
    simp [hk, hl']
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  have hw : w = ![w 0, w 1] := by ext i; fin_cases i <;> rfl
  rw [hv, hw, ← SmoothBundleForm.eval₂_apply, ← SmoothBundleForm.eval₂_apply]
  calc SmoothBundleForm.eval₂ (sphereForm n) x (v 0) (v 1)
      = B (dm (v 0)) (dm (v 1)) := by
        rw [SmoothForm.bilinFormAt_apply, eval₂_sphereForm, eval₂_sphereForm, hDm, hDm,
          smul_comm Complex.I c, real_inner_smul_smul_euclideanSpace hc1]
    _ = B (dm (v 0) + (w 0 - dm (v 0))) (dm (v 1) + (w 1 - dm (v 1))) :=
        (hB _ _ _ _ (hk 0) (hk 1)).symm
    _ = SmoothBundleForm.eval₂ (sphereForm n) y (w 0) (w 1) := by
        rw [add_sub_cancel, add_sub_cancel, SmoothForm.bilinFormAt_apply]

variable (n) in
/-- **The Fubini–Study form** on `ℂPⁿ = ℙ ℂ (Fin (n + 1) → ℂ)`: the descent of the restricted
standard form of `ℂⁿ⁺¹` along the Hopf map, the symplectic reduction of `ℂⁿ⁺¹` by the circle at
the unit sphere. In this normalization a projective line has area `π` (not proved here), unlike
`OnePoint.fubiniStudyForm`, which has total area `1`. -/
def fubiniStudyForm : SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)) :=
  SmoothForm.descendedForm (isSubmersion_hopfMap (by simp)) hopfMap_surjective (sphereForm n)
    isBasic_sphereForm

/-- The Fubini–Study form pulls back along the Hopf map to the restricted standard form. -/
theorem mpullback_fubiniStudyForm :
    SmoothForm.mpullback (hopfMap n) (contMDiff_hopfMap ∞) (fubiniStudyForm n) = sphereForm n :=
  SmoothForm.mpullback_descendedForm

/-- **The Fubini–Study form on `ℂPⁿ` is symplectic.** -/
theorem isSymplectic_fubiniStudyForm : (fubiniStudyForm n).IsSymplectic :=
  SmoothTwoForm.isSymplectic_descendedForm_iff.2
    ⟨isClosed_sphereForm, ker_bilinFormAt_sphereForm⟩

end Projectivization
