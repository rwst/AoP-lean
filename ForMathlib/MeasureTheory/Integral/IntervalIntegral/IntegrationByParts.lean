/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration by parts against a primitive

For an integrable `G` with primitive `Φ u = ∫ₐᵘ G`, Fubini's theorem on the triangle
`a ≤ v ≤ u ≤ b` turns `∫ₐᵇ k Φ` into `∫ₐᵇ G(v) ∫ᵥᵇ k`. With `k = K'` this is integration by parts,
`∫ₐᵇ K' Φ = K(b) Φ(b) - ∫ₐᵇ K G`, without asking `Φ` to be differentiable everywhere.

## Main results

* `intervalIntegral.integral_mul_primitive`: `∫ₐᵇ k(u) ∫ₐᵘ G = ∫ₐᵇ G(v) ∫ᵥᵇ k`.
* `intervalIntegral.integral_deriv_mul_primitive`: `∫ₐᵇ K' Φ = K(b) Φ(b) - ∫ₐᵇ K G`.
-/

@[expose] public section

open MeasureTheory Set

namespace intervalIntegral

variable {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ}

/-- **Fubini on a triangle**: `∫ₐᵇ k(u) (∫ₐᵘ G) du = ∫ₐᵇ G(v) (∫ᵥᵇ k) dv`. -/
theorem integral_mul_primitive {k G : ℝ → 𝕜} (hab : a ≤ b) (hk : Continuous k)
    (hG : IntervalIntegrable G volume a b) :
    ∫ u in a..b, k u * ∫ v in a..u, G v = ∫ v in a..b, G v * ∫ u in v..b, k u := by
  set F : ℝ → ℝ → 𝕜 := fun u v => (if v ≤ u then k u else 0) * G v
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hk.continuousOn
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc a b))) := by
    have hG' : Integrable G (volume.restrict (Ioc a b)) := hG.1
    refine (hG'.comp_snd _).bdd_mul (c := C) ?_ ?_
    · exact (Measurable.ite (measurableSet_le measurable_snd measurable_fst)
        (hk.measurable.comp measurable_fst) measurable_const).aestronglyMeasurable
    · rw [Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
      split_ifs
      · exact hC _ (Ioc_subset_Icc_self hp.1)
      · simpa using (norm_nonneg _).trans (hC a (left_mem_Icc.mpr hab))
  have hL : ∀ u ∈ Ioc a b, k u * ∫ v in a..u, G v = ∫ v in Ioc a b, F u v := fun u hu => by
    have h : ∀ v, F u v = (Iic u).indicator (fun v => k u * G v) v := fun v => by
      by_cases hv : v ≤ u <;> simp [F, hv]
    simp_rw [h]
    rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, inf_of_le_right hu.2,
      ← integral_of_le hu.1.le, integral_const_mul]
  have hR : ∀ v ∈ Ioc a b, ∫ u in Ioc a b, F u v = G v * ∫ u in v..b, k u := fun v hv => by
    have h : ∀ u, F u v = (Ici v).indicator (fun u => k u * G v) u := fun u => by
      by_cases hu : v ≤ u <;> simp [F, hu]
    have hs : Ioc a b ∩ Ici v = Icc v b := by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨-, h₂⟩, h₃⟩
        exact ⟨h₃, h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨⟨hv.1.trans_le h₁, h₂⟩, h₁⟩
    simp_rw [h]
    rw [setIntegral_indicator measurableSet_Ici, hs, integral_Icc_eq_integral_Ioc,
      ← integral_of_le hv.2, integral_mul_const, mul_comm]
  rw [integral_of_le hab, integral_of_le hab, setIntegral_congr_fun measurableSet_Ioc hL,
    integral_integral_swap hint]
  exact setIntegral_congr_fun measurableSet_Ioc hR

/-- **Integration by parts against a primitive**: for `Φ u = ∫ₐᵘ G` and `K' = dK/du`
continuous, `∫ₐᵇ K' Φ = K(b) Φ(b) - ∫ₐᵇ K G`. -/
theorem integral_deriv_mul_primitive {K K' G : ℝ → 𝕜} (hab : a ≤ b)
    (hK : ∀ x, HasDerivAt K (K' x) x) (hK' : Continuous K')
    (hG : IntervalIntegrable G volume a b) :
    ∫ u in a..b, K' u * ∫ v in a..u, G v = K b * (∫ v in a..b, G v) - ∫ v in a..b, K v * G v := by
  have hKc : Continuous K := continuous_iff_continuousAt.mpr fun x => (hK x).continuousAt
  rw [integral_mul_primitive hab hK' hG, ← integral_const_mul,
    ← integral_sub (hG.const_mul (K b)) (hG.continuousOn_mul hKc.continuousOn)]
  refine integral_congr fun v _ => ?_
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hK x) (hK'.intervalIntegrable _ _)]
  ring

end intervalIntegral
