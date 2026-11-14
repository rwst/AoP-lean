/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.Isomorphisms
public import QuantumVectorSpaces.FurtherResults.SchwartzFrame

/-!
# Further results: [B]WDQ relative to a frame group

Not part of the brief. This file formalizes Sec. 3 of `further-results.tex` in the brief's
directory (R. Stephan, *Further results on the brief "Physical vector spaces for quantum
mechanics"*).

The brief states [B]WDQ for "all frames" and proves it under the premise that "the defining
observables of A must be observables in B and vice-versa" (proof of Theorem 5). That premise
fails for some frames (`QuantumVectorSpaces.Diagonal.not_continuous_mulOp`, and Sec. 1 for
Example 3), and no state space can serve all smooth frames at once (the Hilbert brief's
`HilbertUnphysicality.FurtherResults.not_forall_frames_freeEvolution`). So the frames have to
be part of the data. Here they are a group `F` acting on `V` by linear bijections that preserve
the inner product. The frame `g` has the defining observables `ρ(g)⁻¹ Xᵢ ρ(g)`: the observer
in frame `g` measures `Xᵢ` on their own description `ρ(g) v` of the state `v`.

[B]WDQ relative to `F` holds exactly when `F` acts by homeomorphisms of `V`. Then all frames give
the same topology and the same observables, and every frame change is a unitary equivalence, so
it carries pure states, Born probabilities and observables from one frame to another.

## Main definitions

* `FrameGroup c F`: a group `F` acting on `V` by linear bijections that preserve the inner
  product;
* `frameObs X ρ g`: the defining observables of the frame `g`, carried back to `V`;
* `IsFrameCompatible c X ρ`: the premise of the brief's proof, for every pair of frames in `F`.

## Main results

* `isFrameCompatible_iff_topology_eq`  the premise holds if and only if all frames give the same
  topology;
* `isFrameCompatible_iff_continuous`  if and only if every `ρ(g)` is continuous, that is, `F`
  acts by automorphisms of `V`;
* `IsFrameCompatible.isObservable_iff`  then all frames have the same observables;
* `IsFrameCompatible.unitaryEquiv`  and every frame change is a unitary equivalence;
* `isFrameCompatible_of_mem_algebra`  a sufficient condition: the transformed observables
  `ρ(g)⁻¹ Xᵢ ρ(g)` lie in the algebra of the `Xᵢ`;
* `isFrameCompatible_translate`  Example 3 with the translations `x ↦ x - a` as frame group;
* `not_exists_frameUnitary`  the change of frame `y = tan(π/2 · erf x)` of the Hilbert brief
  is not a linear map of `𝓢(ℝ)`, so it belongs to no frame group of Example 3.

## References

* J.-P. Antoine, Dirac formalism and symmetry problems in quantum mechanics. II. Symmetry
  problems, J. Math. Phys. 10 (1969) 2276–2290, Sec. II: a symmetry group is compatible with the
  space of states when the space is invariant under its representation; Proposition 4:
  observables transforming by a finite-dimensional representation stay continuous.
-/

open Topology

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

section FrameGroup

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : PreInnerProductSpace.Core ℂ V)
  {ι : Type*} (X : ι → Module.End ℂ V) (F : Type*) [Group F]

/-- A group of frame changes: a group `F` acting on `V` by linear bijections that preserve the
inner product. `act g` sends the description of a state in the frame `1` to its description in
the frame `g`. -/
structure FrameGroup where
  /-- The action of the frame changes on `V`. -/
  act : F →* (V ≃ₗ[ℂ] V)
  preservesInner (g : F) : PreservesInner c c (act g)

variable {c F}

/-- The defining observables of the frame `g`, carried back to `V`: `ρ(g)⁻¹ Xᵢ ρ(g)`. -/
def frameObs (ρ : FrameGroup c F) (g : F) : ι → Module.End ℂ V := pullback (ρ.act g) X

variable (ρ : FrameGroup c F)

@[simp]
lemma frameObs_one : frameObs X ρ 1 = X := by
  ext i v
  simp [frameObs, pullback, LinearEquiv.one_eq_refl]

/-- The topology of the frame `g` is the topology of `X` pulled back along `ρ(g)`. -/
lemma topology_frameObs (g : F) :
    topology c (frameObs X ρ g) = (topology c X).induced (ρ.act g) :=
  (induced_topology_eq_pullback c c X (ρ.preservesInner g)).symm

lemma isSymmetric_frameObs {X : ι → Module.End ℂ V} (hX : ∀ i, IsSymmetric c (X i)) (g : F)
    (i : ι) : IsSymmetric c (frameObs X ρ g i) :=
  ((ρ.preservesInner g).symm.isSymmetric_conj_iff (X i)).2 (hX i)

variable (c) in
/-- [B]WDQ relative to the frame group: in every pair of frames `g`, `h` of `F`, the defining
observables of `g` are observables of `h`. This is the premise of the brief's proof of
Theorem 5. -/
def IsFrameCompatible : Prop :=
  ∀ g h i, IsObservable c (topology c (frameObs X ρ h)) (frameObs X ρ g i)

variable {X}

/-- The premise of [B]WDQ holds for all frames in `F` if and only if they all give the topology
of the frame `1`. -/
theorem isFrameCompatible_iff_topology_eq (hX : ∀ i, IsSymmetric c (X i)) :
    IsFrameCompatible c X ρ ↔ ∀ g, topology c (frameObs X ρ g) = topology c X := by
  refine ⟨fun H g => ?_, fun H g h i => ⟨isSymmetric_frameObs ρ hX g i, ?_⟩⟩
  · refine (topology_eq_iff_continuous c _ X).2 ⟨fun i => ?_, fun j => ?_⟩
    · have := (H g 1 i).2
      rwa [frameObs_one] at this
    · have := (H 1 g j).2
      rwa [frameObs_one] at this
  · have := (isAdmissible_topology c (frameObs X ρ g)).continuous_obs i
    rwa [H g, ← H h] at this

/-- A family of linear bijections closed under inverses preserves a topology `t` if and only if
each of them is continuous for `t`. -/
lemma forall_induced_eq_iff (t : TopologicalSpace V) :
    (∀ g, t.induced (ρ.act g) = t) ↔ ∀ g, Continuous[t, t] (ρ.act g) := by
  refine ⟨fun H g => continuous_iff_le_induced.2 (H g).ge, fun H g => le_antisymm ?_ ?_⟩
  · have h1 := induced_mono (g := ρ.act g) (continuous_iff_le_induced.1 (H g⁻¹))
    rwa [induced_compose, map_inv, show ⇑(ρ.act g)⁻¹ ∘ ⇑(ρ.act g) = id from
      funext (ρ.act g).symm_apply_apply, induced_id] at h1
  · exact continuous_iff_le_induced.1 (H g)

/-- **[B]WDQ relative to a frame group.** The premise of the brief's proof holds for all frames
in `F` if and only if `F` acts on `V` by continuous maps, hence by automorphisms of the quantum
vector space. -/
theorem isFrameCompatible_iff_continuous (hX : ∀ i, IsSymmetric c (X i)) :
    IsFrameCompatible c X ρ ↔ ∀ g, Continuous[topology c X, topology c X] (ρ.act g) := by
  rw [isFrameCompatible_iff_topology_eq ρ hX, ← forall_induced_eq_iff ρ]
  simp_rw [topology_frameObs]

namespace IsFrameCompatible

variable {ρ}

theorem topology_eq (hX : ∀ i, IsSymmetric c (X i)) (H : IsFrameCompatible c X ρ) (g : F) :
    topology c (frameObs X ρ g) = topology c X :=
  (isFrameCompatible_iff_topology_eq ρ hX).1 H g

/-- All frames in a compatible frame group have the same observables. -/
theorem isObservable_iff (hX : ∀ i, IsSymmetric c (X i)) (H : IsFrameCompatible c X ρ) (g : F)
    (A : Module.End ℂ V) :
    IsObservable c (topology c (frameObs X ρ g)) A ↔ IsObservable c (topology c X) A := by
  rw [H.topology_eq hX g]

/-- In a compatible frame group, every frame change is a unitary equivalence of the quantum
vector space with itself. So it carries the pure states (`UnitaryEquiv.pureStates`), the Born
probabilities and the observables (`UnitaryEquiv.isObservable_conj_iff`) from one frame to
another. -/
def unitaryEquiv (hX : ∀ i, IsSymmetric c (X i)) (H : IsFrameCompatible c X ρ) (g : F) :
    UnitaryEquiv c X c X where
  toLinearEquiv := ρ.act g
  preservesInner := ρ.preservesInner g
  topology_eq := (topology_frameObs X ρ g).symm.trans (H.topology_eq hX g)

end IsFrameCompatible

/-- A sufficient condition, in the spirit of Antoine's Proposition 4: if every transformed
observable `ρ(g)⁻¹ Xᵢ ρ(g)` lies in the algebra of the `Xᵢ`, the frame group is compatible. -/
theorem isFrameCompatible_of_mem_algebra (hX : ∀ i, IsSymmetric c (X i))
    (h : ∀ g i, frameObs X ρ g i ∈ algebra X) : IsFrameCompatible c X ρ := by
  refine (isFrameCompatible_iff_topology_eq ρ hX).2 fun g =>
    topology_eq_of_mem_algebra c _ _ (h g) fun i => ?_
  rw [frameObs, algebra_pullback]
  refine ⟨(ρ.act g).conj (X i), ?_, ?_⟩
  · have := h g⁻¹ i
    rwa [frameObs, pullback, map_inv] at this
  · ext v
    simp

end FrameGroup

/-! ### Example 3: translations of the origin -/

section Translations

open SchwartzMap MeasureTheory ComplexConjugate

/-- Translation of the origin by `a`, as a linear bijection of `𝓢(ℝ)`: `f ↦ f(· - a)`. -/
def translateEquiv (a : ℝ) : 𝓢(ℝ, ℂ) ≃ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  LinearEquiv.ofLinearMap (compSubConstCLM ℂ a).toLinearMap (compSubConstCLM ℂ (-a)).toLinearMap
    (by ext f x; simp) (by ext f x; simp)

@[simp]
lemma translateEquiv_apply (a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : translateEquiv a f x = f (x - a) :=
  rfl

/-- The translations of the origin as a frame group of Example 3. -/
def translate : FrameGroup l2Core (Multiplicative ℝ) where
  act :=
    { toFun a := translateEquiv a.toAdd
      map_one' := by ext f x; simp
      map_mul' a b := by
        ext f x
        simp only [toAdd_mul, translateEquiv_apply, mul_apply_eq_comp]
        congr 1
        ring }
  preservesInner a f g := by
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, l2Core_inner, translateEquiv_apply]
    exact integral_sub_right_eq_self (fun x => conj (f x) * g x) a.toAdd

lemma translate_act_apply (a : Multiplicative ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    translate.act a f x = f (x - a.toAdd) :=
  rfl

lemma translate_act_symm_apply (a : Multiplicative ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (translate.act a).symm f x = f (x + a.toAdd) := by
  rw [← LinearEquiv.coe_inv, ← map_inv, translate_act_apply, toAdd_inv, sub_neg_eq_add]

/-- In the translated frame, position is shifted by `a` and momentum is unchanged. -/
lemma frameObs_translate (ħ : ℝ) (a : Multiplicative ℝ) :
    frameObs (obs ħ) translate a =
      ![posOp + (a.toAdd : ℂ) • 1, momOp ħ, 1] := by
  ext i f x
  fin_cases i
  · simp [frameObs, pullback, obs, translate_act_symm_apply, translate_act_apply, posOp_apply]
    ring
  · simp only [frameObs, pullback, obs, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm,
      translate_act_symm_apply, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
      momOp_apply]
    have h : ⇑(translate.act a f) = fun y => f (y - a.toAdd) := funext (translate_act_apply a f)
    rw [h, deriv_comp_sub_const, add_sub_cancel_right]
  · simp [frameObs, pullback, obs]

/-- **Example 3 satisfies [B]WDQ for translations of the origin.** -/
theorem isFrameCompatible_translate (ħ : ℝ) : IsFrameCompatible l2Core (obs ħ) translate := by
  refine isFrameCompatible_of_mem_algebra translate (isSymmetric_obs ħ) fun a i => ?_
  have h0 : posOp ∈ algebra (obs ħ) := Algebra.subset_adjoin ⟨0, rfl⟩
  have h1 : momOp ħ ∈ algebra (obs ħ) := Algebra.subset_adjoin ⟨1, rfl⟩
  rw [frameObs_translate]
  fin_cases i
  · exact Subalgebra.add_mem _ h0 (Subalgebra.smul_mem _ (Subalgebra.one_mem _) _)
  · exact h1
  · exact Subalgebra.one_mem _

/-- **The Hilbert brief's change of frame is in no frame group of Example 3.** No linear map
of `𝓢(ℝ)` agrees with the unitary `U` of `y = tan(π/2 · erf x)`. -/
theorem not_exists_frameUnitary :
    ¬ ∃ e : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ), ∀ f : 𝓢(ℝ, ℂ),
      (e f).toLp 2 volume = HilbertUnphysicality.frameUnitary (f.toLp 2 volume) := by
  rintro ⟨e, he⟩
  exact not_forall_frameUnitary_mem_range fun f => ⟨e f, (he f).symm⟩

end Translations

end QuantumVectorSpaces.FurtherResults
