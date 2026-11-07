/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Geometry.Euclidean.Volume.Sphere

/-!
# Archimedes' hat-box theorem

The map `(z, θ) ↦ (√(1 - z²) cos θ, √(1 - z²) sin θ, z)` wraps the cylinder `(-1, 1) × (-π, π]`
onto the unit sphere of `ℝ³` minus its poles; it is the inverse of Lambert's cylindrical
equal-area projection. Its partial derivatives are orthogonal of lengths `1 / √(1 - z²)` and
`√(1 - z²)`, so its area Jacobian is `1`. By the area formula, the surface measure
`Measure.toSphere volume` is the pushforward of `dz dθ` on the cylinder. In particular the height
of a uniformly distributed point of the sphere is uniformly distributed on `(-1, 1)`.

## Main results

* `cylinderToSphere`: the map `(z, θ) ↦ (√(1 - z²) cos θ, √(1 - z²) sin θ, z)`.
* `injOn_cylinderToSphere`, `sphere_subset_image_cylinderToSphere`: it is injective on
  `(-1, 1) × (-π, π]`, with image the sphere minus its poles.
* `euclideanHausdorffMeasure_image_cylinderToSphere`: it preserves area.
* `MeasureTheory.Measure.map_toSphere_volume_eq_map_cylinderToSphere`: the surface measure is the
  pushforward of `dz dθ`.
* `MeasureTheory.Measure.map_toSphere_volume_height`: **Archimedes' hat-box theorem**, the height
  pushforward of the surface measure is `2π dz` on `(-1, 1)`.
-/

@[expose] public noncomputable section

open Real Set Metric Module MeasureTheory Function

/-- The map `(z, θ) ↦ (√(1 - z²) cos θ, √(1 - z²) sin θ, z)` from the cylinder to the unit sphere,
the inverse of Lambert's cylindrical equal-area projection. -/
def cylinderToSphere (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[√(1 - p.1 ^ 2) * cos p.2, √(1 - p.1 ^ 2) * sin p.2, p.1]

@[simp]
lemma cylinderToSphere_apply_two (p : ℝ × ℝ) : cylinderToSphere p 2 = p.1 :=
  rfl

lemma continuous_cylinderToSphere : Continuous cylinderToSphere :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)).symm.continuous.comp <|
    continuous_pi fun i ↦ by
      fin_cases i
      · exact (continuous_const.sub (continuous_fst.pow 2)).sqrt.mul
          (continuous_cos.comp continuous_snd)
      · exact (continuous_const.sub (continuous_fst.pow 2)).sqrt.mul
          (continuous_sin.comp continuous_snd)
      · exact continuous_fst

lemma norm_cylinderToSphere {p : ℝ × ℝ} (hp : p.1 ^ 2 ≤ 1) : ‖cylinderToSphere p‖ = 1 := by
  rw [EuclideanSpace.norm_eq, sqrt_eq_one]
  simp only [cylinderToSphere, Fin.sum_univ_three, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs,
    sq_abs, mul_pow, sq_sqrt (sub_nonneg.2 hp)]
  linear_combination (1 - p.1 ^ 2) * sin_sq_add_cos_sq p.2

lemma cylinderToSphere_mem_sphere {p : ℝ × ℝ} (hp : p.1 ^ 2 ≤ 1) :
    cylinderToSphere p ∈ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  mem_sphere_zero_iff_norm.2 (norm_cylinderToSphere hp)

private lemma sq_lt_one_of_mem {p : ℝ × ℝ} (hp : p ∈ Ioo (-1) 1 ×ˢ Ioc (-π) π) : p.1 ^ 2 < 1 := by
  nlinarith [hp.1.1, hp.1.2]

/-- `cylinderToSphere` is injective on `(-1, 1) × (-π, π]`. -/
theorem injOn_cylinderToSphere : InjOn cylinderToSphere (Ioo (-1) 1 ×ˢ Ioc (-π) π) := by
  rintro ⟨z, θ⟩ hp ⟨z', θ'⟩ hp' h
  have hz : z = z' := by simpa using congrArg (· 2) h
  subst hz
  have hr : √(1 - z ^ 2) ≠ 0 := (sqrt_pos.2 (by linarith [sq_lt_one_of_mem hp])).ne'
  have hc : cos θ = cos θ' :=
    mul_left_cancel₀ hr (by simpa [cylinderToSphere] using congrArg (· 0) h)
  have hs : sin θ = sin θ' :=
    mul_left_cancel₀ hr (by simpa [cylinderToSphere] using congrArg (· 1) h)
  have h1 := Complex.arg_cos_add_sin_mul_I hp.2
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.arg_cos_add_sin_mul_I hp'.2] at h1
  exact Prod.ext rfl h1.symm

/-- The image of `(-1, 1) × (-π, π]` under `cylinderToSphere` is the unit sphere minus its
poles. -/
theorem sphere_subset_image_cylinderToSphere :
    sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆
      cylinderToSphere '' (Ioo (-1) 1 ×ˢ Ioc (-π) π) ∪ {!₂[0, 0, 1], !₂[0, 0, -1]} := by
  intro x hx
  have hx' : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
    have h := mem_sphere_zero_iff_norm.1 hx
    rw [EuclideanSpace.norm_eq, sqrt_eq_one, Fin.sum_univ_three] at h
    simpa using h
  rcases (show x 2 ^ 2 ≤ 1 by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]).lt_or_eq with h | h
  · left
    set c : ℂ := ⟨x 0, x 1⟩
    have hc : ‖c‖ = √(1 - x 2 ^ 2) := by
      rw [Complex.norm_def, Complex.normSq_mk]
      congr 1
      linear_combination hx'
    have hc0 : c ≠ 0 := by
      rw [← norm_ne_zero_iff, hc]
      exact (sqrt_pos.2 (by linarith)).ne'
    refine ⟨(x 2, Complex.arg c), ⟨⟨?_, ?_⟩, Complex.arg_mem_Ioc c⟩, ?_⟩
    · nlinarith [abs_lt.1 ((sq_lt_one_iff_abs_lt_one _).1 h)]
    · exact (abs_lt.1 ((sq_lt_one_iff_abs_lt_one _).1 h)).2
    ext i
    fin_cases i
    · simp [c, cylinderToSphere, Complex.cos_arg hc0, ← hc,
        mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc0)]
    · simp [c, cylinderToSphere, Complex.sin_arg, ← hc, mul_div_cancel₀ _ (norm_ne_zero_iff.2 hc0)]
    · simp
  · right
    have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    rcases sq_eq_one_iff.1 h with h2 | h2
    · left
      ext i
      fin_cases i <;> simp [h0, h1, h2]
    · right
      ext i
      fin_cases i <;> simp [h0, h1, h2]

/-- The partial derivative of `cylinderToSphere` in `z`. -/
private def cylinderToSphereDz (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[-p.1 / √(1 - p.1 ^ 2) * cos p.2, -p.1 / √(1 - p.1 ^ 2) * sin p.2, 1]

/-- The partial derivative of `cylinderToSphere` in `θ`. -/
private def cylinderToSphereDθ (p : ℝ × ℝ) : EuclideanSpace ℝ (Fin 3) :=
  !₂[-(√(1 - p.1 ^ 2) * sin p.2), √(1 - p.1 ^ 2) * cos p.2, 0]

private lemma hasDerivAt_sqrt_one_sub_sq {z : ℝ} (hz : z ^ 2 < 1) :
    HasDerivAt (fun z ↦ √(1 - z ^ 2)) (-z / √(1 - z ^ 2)) z := by
  have h := ((hasDerivAt_pow 2 z).const_sub 1).sqrt (by linarith)
  convert h using 1
  have : √(1 - z ^ 2) ≠ 0 := (sqrt_pos.2 (by linarith)).ne'
  field_simp
  ring

private lemma hasFDerivAt_cylinderToSphere {p : ℝ × ℝ} (hp : p.1 ^ 2 < 1) :
    HasFDerivAt cylinderToSphere
      ((ContinuousLinearMap.toSpanSingleton ℝ (cylinderToSphereDz p)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (cylinderToSphereDθ p))) p := by
  set D := (ContinuousLinearMap.toSpanSingleton ℝ (cylinderToSphereDz p)).coprod
    (ContinuousLinearMap.toSpanSingleton ℝ (cylinderToSphereDθ p))
  have h1 : HasFDerivAt (Prod.fst : ℝ × ℝ → ℝ) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    hasFDerivAt_fst
  have h2 : HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    hasFDerivAt_snd
  have hr := (hasDerivAt_sqrt_one_sub_sq hp).comp_hasFDerivAt p h1
  have hc := (hasDerivAt_cos p.2).comp_hasFDerivAt p h2
  have hs := (hasDerivAt_sin p.2).comp_hasFDerivAt p h2
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 ↦ ℝ)
  have hg : HasFDerivAt (fun q : ℝ × ℝ ↦ (![√(1 - q.1 ^ 2) * cos q.2,
      √(1 - q.1 ^ 2) * sin q.2, q.1] : Fin 3 → ℝ)) ((e : _ →L[ℝ] _).comp D) p := by
    refine hasFDerivAt_pi'' fun i ↦ ?_
    fin_cases i
    · refine (hr.mul hc).congr_fderiv ?_
      ext <;> simp [D, e, cylinderToSphereDz, cylinderToSphereDθ]; ring
    · refine (hr.mul hs).congr_fderiv ?_
      ext <;> simp [D, e, cylinderToSphereDz, cylinderToSphereDθ]; ring
    · refine h1.congr_fderiv ?_
      ext <;> simp [D, e, cylinderToSphereDz, cylinderToSphereDθ]
  refine ((e.symm : (Fin 3 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)).hasFDerivAt.comp p hg).congr_fderiv
    ?_
  ext <;> simp

/-- The partial derivatives are orthogonal, of lengths `1 / √(1 - z²)` and `√(1 - z²)`, so the
area Jacobian is `1`. -/
private lemma normDet_cylinderToSphere {p : ℝ × ℝ} (hp : p.1 ^ 2 < 1) :
    ((LinearMap.toSpanSingleton ℝ _ (cylinderToSphereDz p)).coprod
        (LinearMap.toSpanSingleton ℝ _ (cylinderToSphereDθ p)) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).toLinearMap).normDet = 1 := by
  have hr : 0 < √(1 - p.1 ^ 2) := sqrt_pos.2 (by linarith)
  have hr2 : √(1 - p.1 ^ 2) ^ 2 = 1 - p.1 ^ 2 := sq_sqrt (by linarith)
  rw [LinearMap.normDet_coprod_of_orthogonal, LinearMap.normDet_eq_norm_apply_one,
    LinearMap.normDet_eq_norm_apply_one]
  · simp only [LinearMap.toSpanSingleton_apply, one_smul]
    rw [← pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero, mul_pow, EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq]
    simp only [cylinderToSphereDz, cylinderToSphereDθ, Fin.sum_univ_three, PiLp.toLp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
    field_simp
    rw [hr2]
    linear_combination (1 - p.1 ^ 2) * (1 + p.1 ^ 2 * (sin p.2 ^ 2 + cos p.2 ^ 2)) *
      sin_sq_add_cos_sq p.2
  · have hab : inner ℝ (cylinderToSphereDz p) (cylinderToSphereDθ p) = 0 := by
      simp [cylinderToSphereDz, cylinderToSphereDθ, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, Fin.sum_univ_three]
      ring
    intro u v
    simp [inner_smul_left, inner_smul_right, hab]

/-- **`cylinderToSphere` preserves area**: on a measurable subset `s` of `(-1, 1) × (-π, π]`, the
two-dimensional Hausdorff measure of its image is the area of `s`. -/
theorem euclideanHausdorffMeasure_image_cylinderToSphere {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hs' : s ⊆ Ioo (-1) 1 ×ˢ Ioc (-π) π) :
    μHE[2] (cylinderToSphere '' s) = volume s := by
  set f : WithLp 2 (ℝ × ℝ) → EuclideanSpace ℝ (Fin 3) := cylinderToSphere ∘ WithLp.ofLp
  set S : Set (WithLp 2 (ℝ × ℝ)) := WithLp.ofLp ⁻¹' s
  have hS : MeasurableSet S := hs.preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ).measurable
  have hf (x) (hx : x ∈ S) : HasFDerivAt f ((LinearMap.toSpanSingleton ℝ _
      (cylinderToSphereDz (WithLp.ofLp x))).coprod (LinearMap.toSpanSingleton ℝ _
        (cylinderToSphereDθ (WithLp.ofLp x))) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).toLinearMap).toContinuousLinearMap x := by
    refine ((hasFDerivAt_cylinderToSphere (sq_lt_one_of_mem (hs' hx))).comp x
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℝ).hasFDerivAt).congr_fderiv ?_
    ext y
    simp
  have hJ (x) (hx : x ∈ S) : (fderiv ℝ f x).normDet = 1 := by
    rw [(hf x hx).fderiv, LinearMap.coe_toContinuousLinearMap]
    exact normDet_cylinderToSphere (sq_lt_one_of_mem (hs' hx))
  have hinj (x) (hx : x ∈ S) : Injective (fderiv ℝ f x) := by
    have hne : (fderiv ℝ f x).normDet ≠ 0 := by rw [hJ x hx]; exact one_ne_zero
    exact LinearMap.ker_eq_bot.1 (not_not.1 (mt LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 hne))
  have hfS : InjOn f S :=
    (injOn_cylinderToSphere.mono hs').comp (WithLp.ofLp_injective 2).injOn (mapsTo_preimage _ _)
  have h := lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hS
    (fun x hx ↦ (hf x hx).differentiableAt) hinj hfS
  have hrank : finrank ℝ (WithLp 2 (ℝ × ℝ)) = 2 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq, finrank_prod, finrank_self]
  rw [setLIntegral_congr_fun hS (fun x hx ↦ by rw [hJ x hx]), ENNReal.ofReal_one, setLIntegral_one,
    (WithLp.volume_preserving_ofLp ℝ ℝ).measure_preimage hs.nullMeasurableSet, hrank, image_comp,
    image_preimage_eq _ (WithLp.ofLp_surjective 2)] at h
  exact h.symm

namespace MeasureTheory.Measure

private lemma toSphere_volume_apply_preimage (t : Set (EuclideanSpace ℝ (Fin 3))) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere ((↑) ⁻¹' t) =
      μHE[2] (t ∩ sphere 0 1) := by
  rw [TauCeti.toSphere_volume_eq_comap_euclideanHausdorffMeasure, finrank_euclideanSpace_fin,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).comap_apply,
    Subtype.image_preimage_coe, inter_comm]

/-- The surface measure of the image of a measurable subset `s` of `(-1, 1) × (-π, π]` under
`cylinderToSphere` is the area of `s`. -/
theorem toSphere_volume_preimage_image_cylinderToSphere {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hs' : s ⊆ Ioo (-1) 1 ×ˢ Ioc (-π) π) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere ((↑) ⁻¹' (cylinderToSphere '' s)) =
      volume s := by
  rw [toSphere_volume_apply_preimage, inter_eq_left.2,
    euclideanHausdorffMeasure_image_cylinderToSphere hs hs']
  rintro _ ⟨p, hp, rfl⟩
  exact cylinderToSphere_mem_sphere (sq_lt_one_of_mem (hs' hp)).le

/-- **The surface measure of the sphere is `dz dθ`**: it is the pushforward of the area measure of
the cylinder `(-1, 1) × (-π, π]` under `cylinderToSphere`. -/
theorem map_toSphere_volume_eq_map_cylinderToSphere :
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere).map (↑) =
      (volume.restrict (Ioo (-1) 1 ×ˢ Ioc (-π) π)).map cylinderToSphere := by
  set D : Set (ℝ × ℝ) := Ioo (-1) 1 ×ˢ Ioc (-π) π
  have hD : MeasurableSet D := measurableSet_Ioo.prod measurableSet_Ioc
  have hcyl := continuous_cylinderToSphere.measurable
  have hpoles : μHE[2] ({!₂[0, 0, 1], !₂[0, 0, -1]} : Set (EuclideanSpace ℝ (Fin 3))) = 0 := by
    have : NullSingletonClass (μH[(2 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 3))) :=
      nullSingletonClass_hausdorff _ (by norm_num)
    rw [Measure.euclideanHausdorffMeasure_def, smul_apply, (toFinite _).measure_zero, smul_zero]
  ext t ht
  rw [map_apply measurable_subtype_coe ht, map_apply hcyl ht, restrict_apply (hcyl ht),
    ← toSphere_volume_preimage_image_cylinderToSphere (hcyl ht |>.inter hD) inter_subset_right,
    image_preimage_inter]
  refine le_antisymm ?_ (measure_mono (preimage_mono inter_subset_left))
  rw [toSphere_volume_apply_preimage, toSphere_volume_apply_preimage]
  calc μHE[2] (t ∩ sphere 0 1)
      ≤ μHE[2] (t ∩ cylinderToSphere '' D ∩ sphere 0 1 ∪ {!₂[0, 0, 1], !₂[0, 0, -1]}) := by
        refine measure_mono fun x hx ↦ ?_
        rcases sphere_subset_image_cylinderToSphere hx.2 with h | h
        · exact Or.inl ⟨⟨hx.1, h⟩, hx.2⟩
        · exact Or.inr h
    _ ≤ μHE[2] (t ∩ cylinderToSphere '' D ∩ sphere 0 1) := by
        refine (measure_union_le _ _).trans ?_
        rw [hpoles, add_zero]

/-- **Archimedes' hat-box theorem**: the height `x₂` of a point of the unit sphere of `ℝ³`, under
the surface measure, is distributed as `2π dz` on `(-1, 1)`. -/
theorem map_toSphere_volume_height :
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere).map
      (fun x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (x : EuclideanSpace ℝ (Fin 3)) 2) =
        ENNReal.ofReal (2 * π) • volume.restrict (Ioo (-1) 1) := by
  have hproj : Measurable fun y : EuclideanSpace ℝ (Fin 3) ↦ y 2 :=
    (EuclideanSpace.proj (2 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).continuous.measurable
  rw [show (fun x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (x : EuclideanSpace ℝ (Fin 3)) 2) =
      (fun y : EuclideanSpace ℝ (Fin 3) ↦ y 2) ∘ (↑) from rfl,
    ← map_map hproj measurable_subtype_coe, map_toSphere_volume_eq_map_cylinderToSphere,
    map_map hproj continuous_cylinderToSphere.measurable]
  rw [show (fun y : EuclideanSpace ℝ (Fin 3) ↦ y 2) ∘ cylinderToSphere = Prod.fst from rfl,
    volume_eq_prod, ← prod_restrict, map_fst_prod, restrict_apply_univ, Real.volume_Ioc]
  ring_nf

end MeasureTheory.Measure
