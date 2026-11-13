/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Topology.Algebra.Projectivization
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.LocalAtTarget

/-!
# Second countability of projective space

`ℙ K V` carries the quotient topology of the nonzero vectors (Mathlib's
`Projectivization.instTopologicalSpace`). This file shows that, for a topological vector space
with a separating dual over a second-countable field, `V` is second countable if and only if
`ℙ K V` is.

## Main results

* `Projectivization.secondCountableTopology`: if `V` is second countable, so is `ℙ K V`;
* `Projectivization.isInducing_chart`: on the open set where a continuous linear functional `φ`
  does not vanish, `v ↦ ([v], φ v)` is an embedding into `ℙ K V × K`;
* `Projectivization.secondCountableTopology_of`: conversely, if `ℙ K V` is second countable, so
  is `V`.
-/

open Set Filter Topology
open scoped LinearAlgebra.Projectivization

@[expose] public section

namespace Projectivization

section Basic

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [ContinuousConstSMul Kˣ V]

/-- If `V` is second countable, so is its projective space. -/
instance secondCountableTopology [SecondCountableTopology V] :
    SecondCountableTopology (ℙ K V) :=
  have : SecondCountableTopology {v : V // v ≠ 0} :=
    (IsInducing.subtypeVal (t := {v : V | v ≠ 0})).secondCountableTopology
  isOpenQuotientMap_mk'.secondCountableTopology

end Basic

section Chart

variable {K V : Type*} [NontriviallyNormedField K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V] [ContinuousSMul K V]

/-- The chart `v ↦ ([v], φ v)` on the open set where a continuous linear functional `φ` does not
vanish. -/
def chart (φ : V →L[K] K) (v : {v : V // φ v ≠ 0}) : ℙ K V × K :=
  (mk K v.1 fun h => v.2 (by rw [h, map_zero]), φ v.1)

omit [ContinuousSMul K V] in
theorem continuous_chart (φ : V →L[K] K) : Continuous (chart φ) :=
  (continuous_mk continuous_subtype_val _).prodMk (φ.continuous.comp continuous_subtype_val)

/-- The chart is an embedding: a vector `w` near `v` is recovered from its line `[w]`, through a
nearby `w'` with `[w'] = [w]`, and from `φ w`, which fixes the scalar `w = (φ w / φ w') w'`. -/
theorem isInducing_chart (φ : V →L[K] K) : IsInducing (chart φ) := by
  refine isInducing_iff_nhds.2 fun v => le_antisymm ((continuous_chart φ).tendsto v).le_comap ?_
  intro W hW
  have hW₂ : W ∈ comap Subtype.val (𝓝 v.1) := by rwa [← nhds_induced]
  obtain ⟨W', hW', hWW'⟩ := hW₂
  have hs : Tendsto (fun p : K × V => p.1 • p.2) (𝓝 (1, v.1)) (𝓝 v.1) := by
    simpa using continuous_smul.tendsto ((1 : K), v.1)
  obtain ⟨u, hu, t, ht, hut⟩ := mem_nhds_prod_iff.1 (hs hW')
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_nhds_iff.1 hu
  set z := φ v.1
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 v.2
  set η := min (‖z‖ / 2) (ε * ‖z‖ / 4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hφ : {w | ‖φ w - z‖ < η} ∈ 𝓝 v.1 :=
    (isOpen_lt (continuous_norm.comp (φ.continuous.sub continuous_const))
      continuous_const).mem_nhds (by simp [hη])
  set W₁ := interior (t ∩ {w | ‖φ w - z‖ < η})
  have hv₁ : v.1 ∈ W₁ := mem_interior_iff_mem_nhds.2 (inter_mem ht hφ)
  have hv₀ : v.1 ≠ 0 := fun h => v.2 (by rw [h, map_zero])
  have hO : mk' K '' (((↑) : {v : V // v ≠ 0} → V) ⁻¹' W₁) ∈ 𝓝 (chart φ v).1 :=
    (isOpenMap_mk' _ (isOpen_interior.preimage continuous_subtype_val)).mem_nhds
      ⟨⟨v.1, hv₀⟩, hv₁, rfl⟩
  refine ⟨_ ×ˢ Metric.ball z η, prod_mem_nhds hO (Metric.ball_mem_nhds _ hη), fun w hw => ?_⟩
  obtain ⟨⟨w', hw'W₁, hw'⟩, hwz⟩ := hw
  rw [mk'_eq_mk] at hw'
  obtain ⟨a, ha⟩ := (mk_eq_mk_iff K _ _ _ _).1 hw'
  obtain ⟨hw't, hw'z⟩ := interior_subset hw'W₁
  have hwz' : ‖φ w.1 - z‖ < η := by simpa [chart, dist_eq_norm] using hwz
  have hw'z' : ‖φ w'.1 - z‖ < η := hw'z
  set b : K := ((a⁻¹ : Kˣ) : K)
  have hwb : w.1 = b • w'.1 := by
    rw [← ha]
    change w.1 = ((a⁻¹ : Kˣ) : K) • (a • w.1)
    rw [← Units.smul_def, inv_smul_smul]
  have hz' : ‖z‖ / 2 < ‖φ w'.1‖ := by
    have h1 := norm_sub_norm_le z (φ w'.1)
    rw [norm_sub_rev] at h1
    linarith [min_le_left (‖z‖ / 2) (ε * ‖z‖ / 4)]
  have hz'0 : φ w'.1 ≠ 0 := norm_pos_iff.1 (by linarith)
  have hb : ‖b - 1‖ < ε := by
    have hbz : φ w.1 = b * φ w'.1 := by rw [hwb, map_smul, smul_eq_mul]
    have hb1 : b - 1 = (φ w.1 - φ w'.1) / φ w'.1 := by
      rw [hbz]
      field_simp
    have h2 : ‖φ w.1 - φ w'.1‖ < 2 * η := by
      calc ‖φ w.1 - φ w'.1‖ ≤ ‖φ w.1 - z‖ + ‖z - φ w'.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < η + η := by rw [norm_sub_rev z]; linarith
        _ = 2 * η := by ring
    have h3 : η ≤ ε * ‖z‖ / 4 := min_le_right _ _
    rw [hb1, norm_div, div_lt_iff₀ (by linarith)]
    nlinarith
  refine hWW' ?_
  change w.1 ∈ W'
  rw [hwb]
  exact hut (mk_mem_prod (hεu (by rwa [Metric.mem_ball, dist_eq_norm])) hw't)

/-- If the projective space of a topological vector space with a separating dual, over a
second-countable field, is second countable, then so is the space. Countably many charts cover
the nonzero vectors (`ℙ K V` is Lindelöf), and a translate of one chart covers `0`. -/
theorem secondCountableTopology_of [ContinuousAdd V] [SecondCountableTopology K]
    [SeparatingDual K V] [SecondCountableTopology (ℙ K V)] : SecondCountableTopology V := by
  classical
  rcases subsingleton_or_nontrivial V with hV | hV
  · infer_instance
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨φ₀, hφ₀⟩ := SeparatingDual.exists_ne_zero (R := K) hv₀
  let U (φ : V →L[K] K) : Set V := {v | φ v ≠ 0}
  have hUo (φ : V →L[K] K) : IsOpen (U φ) := isOpen_ne_fun φ.continuous continuous_const
  have hU2 (φ : V →L[K] K) : SecondCountableTopology (U φ) :=
    (isInducing_chart φ).secondCountableTopology
  have hsmul (φ : V →L[K] K) (v : V) (hv : v ≠ 0) : φ (mk K v hv).rep ≠ 0 ↔ φ v ≠ 0 := by
    obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
    rw [← ha, Units.smul_def, map_smul, smul_eq_mul]
    simp
  let O (φ : V →L[K] K) : Set (ℙ K V) := {p | φ p.rep ≠ 0}
  have hOo (φ : V →L[K] K) : IsOpen (O φ) := by
    rw [← isQuotientMap_mk'.isOpen_preimage]
    convert (hUo φ).preimage continuous_subtype_val using 1
    ext v
    exact hsmul φ v.1 v.2
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable O hOo
  have hcov (v : V) (hv : v ≠ 0) : ∃ φ ∈ T, v ∈ U φ := by
    have : mk K v hv ∈ ⋃ φ ∈ T, O φ := by
      rw [hTU, mem_iUnion]
      exact SeparatingDual.exists_ne_zero (R := K) (mk K v hv).rep_ne_zero
    obtain ⟨φ, hφT, hφ⟩ := mem_iUnion₂.1 this
    exact ⟨φ, hφT, (hsmul φ v hv).1 hφ⟩
  have := hT.to_subtype
  let S : Set V := (· + v₀) ⁻¹' U φ₀
  have hS : SecondCountableTopology S :=
    ((U φ₀).restrictPreimage_isInducing (Homeomorph.addRight v₀).isInducing).secondCountableTopology
  let W : Option T → Set V := fun o => o.elim S fun φ => U φ
  have hW2 : ∀ o, SecondCountableTopology (W o) := by
    rintro (_ | φ)
    · exact hS
    · exact hU2 φ
  refine TopologicalSpace.secondCountableTopology_of_countable_cover (U := W) ?_ ?_
  · rintro (_ | φ)
    · exact (hUo φ₀).preimage (continuous_id.add continuous_const)
    · exact hUo φ
  · refine eq_univ_of_forall fun v => ?_
    by_cases hv : v = 0
    · exact mem_iUnion.2 ⟨none, show φ₀ (v + v₀) ≠ 0 by simpa [hv] using hφ₀⟩
    · obtain ⟨φ, hφT, hφ⟩ := hcov v hv
      exact mem_iUnion.2 ⟨some ⟨φ, hφT⟩, hφ⟩

end Chart

end Projectivization
