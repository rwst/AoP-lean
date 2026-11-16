/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Wold decomposition of a semigroup of isometries

Let `V : M → E →L[𝕜] E` be a semigroup of isometries on a Hilbert space, indexed by an additive
commutative monoid `M` (`ℕ` for the powers of one isometry, `ℝ≥0` for continuous time):
`V (s + t) = V s * V t` and each `V t` is an isometry. No continuity in `t` is assumed.

The *unitary part* `woldUnitaryPart V` is the set of vectors in the range of every `V t`; the
*pure part* `woldPurePart V` is its orthogonal complement. Both are invariant under every `V t`.
On the unitary part every `V t` is onto, so `V` restricts to a semigroup of unitaries there; on the
pure part `V` has no unitary part left. A vector lies in the pure part iff its past is lost:
`‖V t† x‖ → 0`. On the unitary part `‖V t† x‖ = ‖x‖`.

For `M = ℕ` this is the first half of the Wold decomposition of an isometry. The second half, that
the pure part is a unilateral shift of multiplicity `dim (ker V†)`, and its continuous-time
analogue (Cooper's theorem: the pure part is the right shift on `L²((0, ∞); K)`) are not proved
here.

## Main definitions

* `ContinuousLinearMap.IsIsometrySemigroup`: a semigroup of isometries.
* `ContinuousLinearMap.woldUnitaryPart`, `ContinuousLinearMap.woldPurePart`: its unitary and pure
  parts.

## Main results

* `IsIsometrySemigroup.map_mem_woldUnitaryPart`, `IsIsometrySemigroup.exists_mem_woldUnitaryPart`:
  each `V t` maps the unitary part onto itself.
* `IsIsometrySemigroup.map_mem_woldPurePart`: each `V t` maps the pure part into itself.
* `IsIsometrySemigroup.iInf_map_woldPurePart`: the restriction to the pure part has no unitary
  part.
* `IsIsometrySemigroup.forall_surjective_iff`: every `V t` is onto iff the pure part is zero.
* `IsIsometrySemigroup.surjective_of_surjective`: for Archimedean `M`, if one `V t₀` with
  `t₀ > 0` is onto, then all are.
* `IsIsometrySemigroup.tendsto_norm_adjoint_apply`: `‖V t† x‖` tends to the norm of the projection
  of `x` onto the unitary part.
* `IsIsometrySemigroup.mem_woldPurePart_iff_tendsto`: `x` lies in the pure part iff
  `‖V t† x‖ → 0`.
* `IsIsometrySemigroup.norm_adjoint_apply_of_mem_woldUnitaryPart`: on the unitary part,
  `‖V t† x‖ = ‖x‖`.

## References

* H. Wold, *A study in the analysis of stationary time series*, Almqvist & Wiksell, 1938.
* J. L. B. Cooper, *One-parameter semigroups of isometric operators in Hilbert space*,
  Ann. of Math. 48 (1947), 827–842.
-/

@[expose] public section

open Filter Topology Submodule
open scoped InnerProductSpace

variable {𝕜 E M : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [AddCommMonoid M]

namespace ContinuousLinearMap

/-- A semigroup of isometries indexed by an additive monoid `M`: each `V t` is an isometry and
`V (s + t) = V s * V t`. -/
structure IsIsometrySemigroup (V : M → E →L[𝕜] E) : Prop where
  norm_map : ∀ t x, ‖V t x‖ = ‖x‖
  map_add : ∀ s t, V (s + t) = V s * V t

/-- The unitary part of `V`: the vectors in the range of every `V t`. -/
def woldUnitaryPart (V : M → E →L[𝕜] E) : Submodule 𝕜 E :=
  ⨅ t, LinearMap.range (V t : E →ₗ[𝕜] E)

/-- The pure part of `V`: the orthogonal complement of its unitary part. -/
def woldPurePart (V : M → E →L[𝕜] E) : Submodule 𝕜 E := (woldUnitaryPart V)ᗮ

instance [CompleteSpace E] (V : M → E →L[𝕜] E) : (woldPurePart V).HasOrthogonalProjection := by
  unfold woldPurePart; infer_instance

namespace IsIsometrySemigroup

variable {V : M → E →L[𝕜] E} (hV : IsIsometrySemigroup V)
include hV

/-! ### The decomposition -/

/-- `V t` as a linear isometry. -/
def toLinearIsometry (t : M) : E →ₗᵢ[𝕜] E := ⟨(V t : E →ₗ[𝕜] E), hV.norm_map t⟩

lemma inner_map_map (t : M) (x y : E) : ⟪V t x, V t y⟫_𝕜 = ⟪x, y⟫_𝕜 :=
  (hV.toLinearIsometry t).inner_map_map x y

lemma injective (t : M) : Function.Injective (V t) :=
  (hV.toLinearIsometry t).injective

lemma map_add_apply (s t : M) (x : E) : V (s + t) x = V s (V t x) := by
  rw [hV.map_add]; rfl

lemma apply_comm (s t : M) (x : E) : V s (V t x) = V t (V s x) := by
  rw [← hV.map_add_apply, add_comm, hV.map_add_apply]

lemma range_add_le (s t : M) :
    LinearMap.range (V (s + t) : E →ₗ[𝕜] E) ≤ LinearMap.range (V s : E →ₗ[𝕜] E) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨V t x, (hV.map_add_apply s t x).symm⟩

/-- `V t` maps the unitary part into itself. -/
theorem map_mem_woldUnitaryPart {x : E} (hx : x ∈ woldUnitaryPart V) (t : M) :
    V t x ∈ woldUnitaryPart V := by
  simp only [woldUnitaryPart, Submodule.mem_iInf] at hx ⊢
  intro s
  obtain ⟨y, rfl⟩ := hx s
  exact ⟨V t y, hV.apply_comm s t y⟩

/-- `V t` maps the unitary part onto itself. -/
theorem exists_mem_woldUnitaryPart {y : E} (hy : y ∈ woldUnitaryPart V) (t : M) :
    ∃ x ∈ woldUnitaryPart V, V t x = y := by
  simp only [woldUnitaryPart, Submodule.mem_iInf] at hy ⊢
  obtain ⟨x, rfl⟩ := hy t
  refine ⟨x, fun s => ?_, rfl⟩
  obtain ⟨z, hz⟩ := hy (t + s)
  simp only [ContinuousLinearMap.coe_coe, hV.map_add_apply] at hz
  exact ⟨z, hV.injective t hz⟩

/-- `V t` maps the pure part into itself. -/
theorem map_mem_woldPurePart {x : E} (hx : x ∈ woldPurePart V) (t : M) :
    V t x ∈ woldPurePart V := by
  intro u hu
  obtain ⟨w, hw, rfl⟩ := hV.exists_mem_woldUnitaryPart hu t
  rw [hV.inner_map_map]
  exact hx w hw

/-- On the pure part, `V` has no unitary part: no nonzero vector of it is in the image of the pure
part under every `V t`. -/
theorem iInf_map_woldPurePart :
    ⨅ t, (woldPurePart V).map (V t : E →ₗ[𝕜] E) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hx' : ∀ t, x ∈ (woldPurePart V).map (V t : E →ₗ[𝕜] E) := Submodule.mem_iInf _ |>.mp hx
  have hu : x ∈ woldUnitaryPart V := Submodule.mem_iInf _ |>.mpr fun t => by
    obtain ⟨y, -, hy⟩ := hx' t
    exact ⟨y, hy⟩
  obtain ⟨y, hy, rfl⟩ := hx' 0
  exact (mem_bot 𝕜).mpr (inner_self_eq_zero.mp (hV.map_mem_woldPurePart hy 0 _ hu))

/-- If one `V t₀` with `t₀ > 0` is onto, then every `V t` is. -/
theorem surjective_of_surjective [PartialOrder M] [ExistsAddOfLE M] [Archimedean M] {t₀ : M}
    (ht₀ : 0 < t₀) (h : Function.Surjective (V t₀)) (t : M) : Function.Surjective (V t) := by
  have h0 : Function.Surjective (V 0) := fun y =>
    ⟨y, hV.injective 0 (by rw [← hV.map_add_apply, add_zero])⟩
  have hn (n : ℕ) : Function.Surjective (V (n • t₀)) := by
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      rw [succ_nsmul]
      intro y
      obtain ⟨z, rfl⟩ := ih y
      obtain ⟨w, rfl⟩ := h z
      exact ⟨w, hV.map_add_apply _ _ _⟩
  obtain ⟨n, hle⟩ := Archimedean.arch t ht₀
  obtain ⟨c, hc⟩ := exists_add_of_le hle
  intro y
  obtain ⟨z, hz⟩ := hn n y
  rw [hc, hV.map_add_apply] at hz
  exact ⟨_, hz⟩

variable [CompleteSpace E]

lemma isClosed_range (t : M) : IsClosed (LinearMap.range (V t : E →ₗ[𝕜] E) : Set E) :=
  (hV.toLinearIsometry t).isometry.isClosedEmbedding.isClosed_range

lemma isClosed_woldUnitaryPart : IsClosed (woldUnitaryPart V : Set E) := by
  rw [woldUnitaryPart, Submodule.coe_iInf]
  exact isClosed_iInter hV.isClosed_range

lemma orthogonal_woldPurePart : (woldPurePart V)ᗮ = woldUnitaryPart V := by
  rw [woldPurePart, orthogonal_orthogonal_eq_closure,
    IsClosed.submodule_topologicalClosure_eq hV.isClosed_woldUnitaryPart]

/-- Every `V t` is onto iff the pure part is zero. -/
theorem forall_surjective_iff : (∀ t, Function.Surjective (V t)) ↔ woldPurePart V = ⊥ := by
  constructor
  · intro h
    have : woldUnitaryPart V = ⊤ := eq_top_iff.mpr fun y _ =>
      Submodule.mem_iInf _ |>.mpr fun t => h t y
    rw [woldPurePart, this, top_orthogonal_eq_bot]
  · intro h t y
    have : y ∈ woldUnitaryPart V := by
      rw [← hV.orthogonal_woldPurePart, h, bot_orthogonal_eq_top]; trivial
    exact (Submodule.mem_iInf _ |>.mp this) t

/-! ### The past: `V t† x` -/

lemma adjoint_apply_apply (t : M) (x : E) : adjoint (V t) (V t x) = x := by
  rw [← ContinuousLinearMap.comp_apply,
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (hV.norm_map t)]
  rfl

/-- On the unitary part, `V t†` is isometric: the past is recovered. -/
theorem norm_adjoint_apply_of_mem_woldUnitaryPart {x : E} (hx : x ∈ woldUnitaryPart V) (t : M) :
    ‖adjoint (V t) x‖ = ‖x‖ := by
  obtain ⟨w, rfl⟩ := (Submodule.mem_iInf _ |>.mp hx) t
  rw [ContinuousLinearMap.coe_coe, hV.adjoint_apply_apply, hV.norm_map]

/-- `x - V t V t† x` is the projection of `x` onto the orthogonal complement of the range of
`V t`. -/
lemma sub_apply_adjoint_apply (t : M) (x : E) :
    x - V t (adjoint (V t) x) = (LinearMap.range (V t : E →ₗ[𝕜] E))ᗮ.starProjection x := by
  symm
  refine eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · rintro _ ⟨y, rfl⟩
    rw [ContinuousLinearMap.coe_coe, inner_sub_right, hV.inner_map_map,
      ContinuousLinearMap.adjoint_inner_right, sub_self]
  · rw [sub_sub_cancel]
    exact inner_right_of_mem_orthogonal (LinearMap.mem_range_self (V t : E →ₗ[𝕜] E) _) hw

lemma norm_adjoint_apply (t : M) (x : E) :
    ‖adjoint (V t) x‖ = ‖x - (LinearMap.range (V t : E →ₗ[𝕜] E))ᗮ.starProjection x‖ := by
  rw [← hV.sub_apply_adjoint_apply, sub_sub_cancel, hV.norm_map]

lemma closure_iSup_orthogonal_range :
    (⨆ t, (LinearMap.range (V t : E →ₗ[𝕜] E))ᗮ).topologicalClosure = woldPurePart V := by
  rw [woldPurePart, woldUnitaryPart, ← orthogonal_orthogonal_eq_closure, ← iInf_orthogonal]
  congr 1
  refine iInf_congr fun t => ?_
  rw [orthogonal_orthogonal_eq_closure,
    IsClosed.submodule_topologicalClosure_eq (hV.isClosed_range t)]

section Order

variable [Preorder M] [ExistsAddOfLE M]

omit [CompleteSpace E] in
lemma range_antitone : Antitone fun t => LinearMap.range (V t : E →ₗ[𝕜] E) := by
  intro s t hst
  obtain ⟨c, rfl⟩ := exists_add_of_le hst
  exact hV.range_add_le s c

/-- `‖V t† x‖` tends to the norm of the projection of `x` onto the unitary part. -/
theorem tendsto_norm_adjoint_apply (x : E) :
    Tendsto (fun t => ‖adjoint (V t) x‖) atTop
      (𝓝 ‖x - (woldPurePart V).starProjection x‖) := by
  have hmono : Monotone fun t => (LinearMap.range (V t : E →ₗ[𝕜] E))ᗮ :=
    fun s t h => orthogonal_le (hV.range_antitone h)
  have h := starProjection_tendsto_closure_iSup _ hmono x
  simp_rw [hV.norm_adjoint_apply]
  convert ((tendsto_const_nhds (x := x)).sub h).norm using 4
  have key : ∀ (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection],
      K = L → K.starProjection x = L.starProjection x := by
    rintro K L _ _ rfl; rfl
  exact key _ _ hV.closure_iSup_orthogonal_range.symm

/-- The pure part consists of the vectors whose past is lost: `V t† x → 0`. -/
theorem mem_woldPurePart_iff_tendsto [Nonempty M] [IsDirected M (· ≤ ·)] {x : E} :
    x ∈ woldPurePart V ↔ Tendsto (fun t => ‖adjoint (V t) x‖) atTop (𝓝 0) := by
  constructor
  · intro hx
    simpa [starProjection_eq_self_iff.mpr hx] using hV.tendsto_norm_adjoint_apply x
  · intro h
    have h0 := tendsto_nhds_unique (hV.tendsto_norm_adjoint_apply x) h
    rw [norm_eq_zero, sub_eq_zero] at h0
    rw [h0]
    exact starProjection_apply_mem _ _

end Order

end IsIsometrySemigroup

end ContinuousLinearMap
