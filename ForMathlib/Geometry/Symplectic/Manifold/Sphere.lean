/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import ForMathlib.MeasureTheory.Constructions.HaarToSphere
import TauCeti.Geometry.Symplectic.Manifold.DuistermaatHeckman.Sphere

/-!
# The Liouville measure of the two-sphere is its surface measure

The unit sphere `S² ⊂ ℝ³` carries the area form `σ_x(v, w) = x ⬝ (v × w)`
(`TauCeti.sphereAreaForm`), with Liouville measure `|σ|`, and Mathlib's surface measure
`volume.toSphere`, which gives a set `A` three times the volume of the cone over `A` in the unit
ball, the solid angle of `A`. They agree (`TauCeti.liouvilleMeasure_sphereAreaForm_eq_toSphere`).

Both are images of Lebesgue measure under `(z, θ) ↦ (√(1 - z²) cos θ, √(1 - z²) sin θ, z)`:
the Liouville measure on the strip `θ ∈ (0, 2π)` (`TauCeti.liouvilleMeasure_sphereAreaForm`), the
surface measure on `θ ∈ (-π, π]`
(`MeasureTheory.Measure.map_toSphere_volume_eq_map_cylinderToSphere`).
The map is `2π`-periodic in `θ`, and translating the part `(π, 2π)` of the first strip by `-2π`
gives the second up to the null segment `θ = 0`.

## Main results

* `TauCeti.liouvilleMeasure_sphereAreaForm_eq_toSphere`: the Liouville measure of the area form of
  `S²` is its surface measure.
-/

open Real Set Metric MeasureTheory
open scoped Manifold EuclideanSpace

public section

noncomputable section

namespace TauCeti

/-- Shifting the longitude interval `(π, 2π)` down by `2π` does not change the image measure. -/
private theorem map_restrict_cylinderToSphere_Ioo_zero_two_pi :
    (volume.restrict (Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 (2 * π))).map cylinderToSphere =
      (volume.restrict (Ioo (-1 : ℝ) 1 ×ˢ Ioc (-π) π)).map cylinderToSphere := by
  set I := Ioo (-1 : ℝ) 1
  have hcyl := continuous_cylinderToSphere.measurable
  have h₁ : I ×ˢ Ioo 0 (2 * π) = I ×ˢ Ioc 0 π ∪ I ×ˢ Ioo π (2 * π) := by
    rw [← prod_union, Ioc_union_Ioo_eq_Ioo pi_pos.le (by linarith [pi_pos])]
  have h₂ : I ×ˢ Ioc (-π) π = I ×ˢ Ioc (-π) 0 ∪ I ×ˢ Ioc 0 π := by
    rw [← prod_union, Ioc_union_Ioc_eq_Ioc (by linarith [pi_pos]) pi_pos.le]
  have hd₁ : Disjoint (I ×ˢ Ioc 0 π) (I ×ˢ Ioo π (2 * π)) :=
    disjoint_prod.2 (Or.inr (Set.disjoint_left.2 fun _ h h' ↦ (not_lt.2 h.2) h'.1))
  have hd₂ : Disjoint (I ×ˢ Ioc (-π) 0) (I ×ˢ Ioc 0 π) :=
    disjoint_prod.2 (Or.inr (Set.disjoint_left.2 fun _ h h' ↦ (not_lt.2 h.2) h'.1))
  rw [h₁, h₂, Measure.restrict_union hd₁ (measurableSet_Ioo.prod measurableSet_Ioo),
    Measure.restrict_union hd₂ (measurableSet_Ioo.prod measurableSet_Ioc), Measure.map_add _ _ hcyl,
    Measure.map_add _ _ hcyl, add_comm]
  congr 1
  -- The translation `θ ↦ θ - 2π` carries `(π, 2π)` onto `(-π, 0)` and commutes with the map.
  let τ : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (MeasurableEquiv.addRight (-(2 * π)))
  have hτ : MeasurePreserving τ volume volume :=
    (MeasurePreserving.id volume).prod (measurePreserving_add_right volume (-(2 * π)))
  have hτp (p : ℝ × ℝ) : τ p = (p.1, p.2 - 2 * π) := by
    rw [sub_eq_add_neg]
    rfl
  have hcτ : cylinderToSphere ∘ τ = cylinderToSphere := by
    funext p
    simp [hτp, cylinderToSphere]
  have hpre : τ ⁻¹' (I ×ˢ Ioo (-π) 0) = I ×ˢ Ioo π (2 * π) := by
    ext ⟨z, θ⟩
    simp only [mem_preimage, hτp, mem_prod, mem_Ioo]
    constructor <;> rintro ⟨h, h', h''⟩ <;> exact ⟨h, by linarith, by linarith⟩
  have hnull : I ×ˢ Ioo (-π) 0 =ᵐ[volume] I ×ˢ Ioc (-π) 0 := by
    refine ae_eq_set.2 ⟨by simp [sdiff_eq_empty.2 (prod_mono le_rfl Ioo_subset_Ioc_self)], ?_⟩
    refine measure_mono_null (t := univ ×ˢ {0}) ?_ ?_
    · rintro ⟨z, θ⟩ ⟨⟨hz, hθ⟩, hn⟩
      refine ⟨mem_univ _, ?_⟩
      by_contra h0
      exact hn ⟨hz, hθ.1, lt_of_le_of_ne hθ.2 h0⟩
    · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
  calc (volume.restrict (I ×ˢ Ioo π (2 * π))).map cylinderToSphere
      = ((volume.restrict (τ ⁻¹' (I ×ˢ Ioo (-π) 0))).map τ).map cylinderToSphere := by
        rw [Measure.map_map hcyl τ.measurable, hcτ, hpre]
    _ = (volume.restrict (I ×ˢ Ioc (-π) 0)).map cylinderToSphere := by
        rw [← τ.restrict_map, hτ.map_eq, Measure.restrict_congr_set hnull]

/-- **The Liouville measure of the area form of `S²` is the surface measure** `μ.toSphere` of
Lebesgue measure on `ℝ³`, the solid angle. -/
theorem liouvilleMeasure_sphereAreaForm_eq_toSphere :
    sphereAreaForm.liouvilleMeasure 1 = (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  have hemb : MeasurableEmbedding
      ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)) :=
    MeasurableEmbedding.subtypeVal isClosed_sphere.measurableSet
  rw [← hemb.comap_map (sphereAreaForm.liouvilleMeasure 1), ← hemb.comap_map (volume.toSphere),
    Measure.map_toSphere_volume_eq_map_cylinderToSphere,
    ← map_restrict_cylinderToSphere_Ioo_zero_two_pi]
  congr 1
  -- The longitude–height parametrization is `cylinderToSphere` after `(θ, h) ↦ (h, θ)`.
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
    ((MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow).trans
      MeasurableEquiv.prodComm
  have he : MeasurePreserving e volume volume :=
    (Measure.measurePreserving_swap (μ := volume) (ν := volume)).comp
      ((volume_preserving_finTwoArrow ℝ).comp
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)))
  have hep (y : EuclideanSpace ℝ (Fin 2)) : e y = (y 1, y 0) := rfl
  have hcyl := continuous_cylinderToSphere.measurable
  have hstrip : MeasurableSet (longitudeHeightStrip 0 : Set (EuclideanSpace ℝ (Fin 2))) :=
    (longitudeHeightStrip 0).isOpen.measurableSet
  have hcomp : ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)) ∘
      sphereLongitudeHeight 0 =
      (cylinderToSphere ∘ e) ∘ Subtype.val := by
    funext y
    simp [coe_sphereLongitudeHeight, cylinderToSphere, hep]
  have hpre : e ⁻¹' (Ioo (-1 : ℝ) 1 ×ˢ Ioo 0 (2 * π)) = longitudeHeightStrip 0 := by
    ext y
    simp [hep, and_comm]
  rw [liouvilleMeasure_sphereAreaForm, Measure.map_map measurable_subtypeVal
      (measurableEmbedding_sphereLongitudeHeight 0).measurable, hcomp,
    ← Measure.map_map (hcyl.comp e.measurable) measurable_subtypeVal]
  have hres : (volume.comap ((↑) : longitudeHeightStrip 0 → EuclideanSpace ℝ (Fin 2))).map (↑) =
      volume.restrict (longitudeHeightStrip 0 : Set (EuclideanSpace ℝ (Fin 2))) :=
    map_comap_subtypeVal hstrip _
  rw [hres, ← Measure.map_map hcyl e.measurable, ← hpre, ← e.restrict_map, he.map_eq]

end TauCeti
