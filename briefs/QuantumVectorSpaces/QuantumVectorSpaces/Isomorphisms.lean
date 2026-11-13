/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.Frames
public import ForMathlib.Topology.Algebra.Projectivization
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Isomorphisms of quantum vector spaces

The brief speaks of isomorphisms "in the category of quantum vector spaces" that "must preserve
the Lie algebraic structure" (Example 3; Theorem 5, [B]STDIST), but does not define them. This
file gives two definitions, both groupoids.

* A *unitary equivalence* `UnitaryEquiv c X c' Y` is a linear bijection `U : V ≃ W` that
  preserves the inner product and carries the topology of `Y` to the topology of `X`. It
  preserves everything QSTO:V uses: the pure states, the Born rule and the observables.
* A *Lie isomorphism* `LieIso c X c' Y` is a linear bijection that preserves the inner product
  and whose conjugation `A ↦ U A U⁻¹` maps the Lie algebra spanned by the `X i` onto the Lie
  algebra spanned by the `Y j`. This is the brief's "preserve the Lie algebraic structure".
  Every Lie isomorphism is a unitary equivalence: the topology need not be required.

## Main results

* `induced_topology_eq_pullback`  along a map `U` that preserves the inner product, the topology
  of `Y` pulls back to the topology on `V` with defining observables `U⁻¹ Y_j U`;
* `induced_topology_eq_iff`  so `U` is a unitary equivalence if and only if the `U⁻¹ Y_j U` are
  continuous on `V` and the `U X_i U⁻¹` are continuous on `W` (for `U = id` this is
  `topology_eq_iff_continuous`, the frame changes of [B]WDQ);
* `UnitaryEquiv.refl`, `UnitaryEquiv.symm`, `UnitaryEquiv.trans`, and the same for `LieIso`;
* `UnitaryEquiv.isObservable_conj_iff`  conjugation by `U` is a bijection of the observables;
* `UnitaryEquiv.pureStates`  `U` induces a homeomorphism of the pure states `ℙ ℂ V ≃ₜ ℙ ℂ W`;
* `LieIso.toUnitaryEquiv`  every Lie isomorphism is a unitary equivalence.
-/

open Topology
open scoped LinearAlgebra.Projectivization

attribute [local instance 100] LieRing.ofAssociativeRing

@[expose] public noncomputable section

namespace QuantumVectorSpaces

variable {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]
  {ι κ μ : Type*} (c : PreInnerProductSpace.Core ℂ V) (X : ι → Module.End ℂ V)
  (c' : PreInnerProductSpace.Core ℂ W) (Y : κ → Module.End ℂ W)
  (c'' : PreInnerProductSpace.Core ℂ U) (Z : μ → Module.End ℂ U)

/-! ### Transport along a map that preserves the inner product -/

section Transport

/-- The linear bijection `e` preserves the inner product. -/
def PreservesInner (e : V ≃ₗ[ℂ] W) : Prop := ∀ v w, c'.inner (e v) (e w) = c.inner v w

variable {c c'}

lemma PreservesInner.symm {e : V ≃ₗ[ℂ] W} (he : PreservesInner c c' e) :
    PreservesInner c' c e.symm := fun v w => by
  rw [← he, e.apply_symm_apply, e.apply_symm_apply]

/-- Conjugation by a map that preserves the inner product preserves symmetric operators. -/
lemma PreservesInner.isSymmetric_conj_iff {e : V ≃ₗ[ℂ] W} (he : PreservesInner c c' e)
    (A : Module.End ℂ V) : IsSymmetric c' (e.conj A) ↔ IsSymmetric c A := by
  refine ⟨fun h v w => ?_, fun h v w => ?_⟩
  · have h1 := h (e v) (e w)
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply] at h1
    rwa [he, he] at h1
  · obtain ⟨v, rfl⟩ := e.surjective v
    obtain ⟨w, rfl⟩ := e.surjective w
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    rw [he, he]
    exact h v w

variable (c c')

/-- The defining observables of `W` carried to `V` along `e`: the operators `e⁻¹ Y_j e`. -/
def pullback (e : V ≃ₗ[ℂ] W) (Y : κ → Module.End ℂ W) (j : κ) : Module.End ℂ V :=
  e.symm.conj (Y j)

lemma pullback_symm_pullback (e : V ≃ₗ[ℂ] W) : pullback e.symm (pullback e Y) = Y :=
  funext fun j => by simp [pullback]

variable {c c'} in
/-- An operator is continuous for the topology pulled back along `e` if and only if its
conjugate by `e` is continuous. -/
lemma continuous_induced_iff {t : TopologicalSpace W} (e : V ≃ₗ[ℂ] W) (A : Module.End ℂ V) :
    Continuous[t.induced e, t.induced e] A ↔ Continuous[t, t] (e.conj A) := by
  let := t
  let : TopologicalSpace V := t.induced e
  have hs : Continuous[t, t.induced e] e.symm :=
    continuous_induced_rng.2 (by
      rw [show ⇑e ∘ ⇑e.symm = id from funext e.apply_symm_apply]
      exact continuous_id)
  have h1 : ⇑(e.conj A) = e ∘ A ∘ e.symm := by ext; simp
  have h2 : e ∘ A = e.conj A ∘ e := by ext; simp
  refine ⟨fun h => ?_, fun h => continuous_induced_rng.2 ?_⟩
  · rw [h1]
    exact continuous_induced_dom.comp (h.comp hs)
  · rw [h2]
    exact h.comp continuous_induced_dom

/-- An admissible topology for `Y` pulls back along `e` to an admissible topology for the
operators `e⁻¹ Y_j e`. -/
theorem isAdmissible_induced {e : V ≃ₗ[ℂ] W} (he : PreservesInner c c' e)
    {t : TopologicalSpace W} (ht : IsAdmissible c' Y t) :
    IsAdmissible c (pullback e Y) (t.induced e) := by
  let := t
  have := ht.isTopologicalAddGroup
  have := ht.continuousSMul
  let : TopologicalSpace V := t.induced e
  refine ⟨isTopologicalAddGroup_induced e, continuousSMul_induced e, fun j => ?_, ?_⟩
  · rw [continuous_induced_iff, pullback, LinearEquiv.conj_conj_symm]
    exact ht.continuous_obs j
  · have he' : (fun p : V × V => c.inner p.1 p.2) = fun p => c'.inner (e p.1) (e p.2) := by
      ext; rw [he]
    rw [he']
    have hd : Continuous e := continuous_induced_dom
    exact ht.continuous_inner.comp ((hd.comp continuous_fst).prodMk (hd.comp continuous_snd))

/-- Along a map that preserves the inner product, the topology of `Y` pulls back to the topology
on `V` whose defining observables are the `e⁻¹ Y_j e`. -/
theorem induced_topology_eq_pullback {e : V ≃ₗ[ℂ] W} (he : PreservesInner c c' e) :
    (topology c' Y).induced e = topology c (pullback e Y) := by
  refine le_antisymm
    ((isGreatest_topology c _).2 (isAdmissible_induced c c' Y he (isAdmissible_topology c' Y)))
    ?_
  have h1 := isAdmissible_induced c' c (pullback e Y) he.symm
    (isAdmissible_topology c (pullback e Y))
  rw [pullback_symm_pullback] at h1
  have h2 := induced_mono (g := e) ((isGreatest_topology c' Y).2 h1)
  rwa [induced_compose, show ⇑e.symm ∘ ⇑e = id from funext e.symm_apply_apply,
    @induced_id _ (topology c (pullback e Y))] at h2

/-- Along a map `e` that preserves the inner product, the topology of `Y` pulls back to the
topology of `X` if and only if the `e⁻¹ Y_j e` are continuous on `V` and the `e X_i e⁻¹` are
continuous on `W`. For `e = id` these are the frame changes of [B]WDQ,
`topology_eq_iff_continuous`. -/
theorem induced_topology_eq_iff {e : V ≃ₗ[ℂ] W} (he : PreservesInner c c' e) :
    (topology c' Y).induced e = topology c X ↔
      (∀ j, Continuous[topology c X, topology c X] (pullback e Y j)) ∧
        ∀ i, Continuous[topology c' Y, topology c' Y] (e.conj (X i)) := by
  rw [induced_topology_eq_pullback c c' Y he, topology_eq_iff_continuous c (pullback e Y) X,
    ← induced_topology_eq_pullback c c' Y he]
  simp_rw [continuous_induced_iff]

end Transport

/-! ### Unitary equivalences -/

/-- A unitary equivalence of quantum vector spaces: a linear bijection `V ≃ W` that preserves
the inner product and carries the topology of `Y` to the topology of `X`, so that it is a
homeomorphism. -/
structure UnitaryEquiv extends V ≃ₗ[ℂ] W where
  preservesInner : PreservesInner c c' toLinearEquiv
  topology_eq : (topology c' Y).induced toLinearEquiv = topology c X

namespace UnitaryEquiv

variable {c X c' Y c'' Z}

/-- The identity is a unitary equivalence. -/
def refl : UnitaryEquiv c X c X where
  toLinearEquiv := LinearEquiv.refl ℂ V
  preservesInner _ _ := rfl
  topology_eq := @induced_id _ (topology c X)

/-- The inverse of a unitary equivalence. -/
def symm (e : UnitaryEquiv c X c' Y) : UnitaryEquiv c' Y c X where
  toLinearEquiv := e.toLinearEquiv.symm
  preservesInner := e.preservesInner.symm
  topology_eq := by
    rw [← e.topology_eq, induced_compose,
      show ⇑e.toLinearEquiv ∘ ⇑e.toLinearEquiv.symm = id from
        funext e.toLinearEquiv.apply_symm_apply,
      @induced_id _ (topology c' Y)]

/-- The composition of two unitary equivalences. -/
def trans (e : UnitaryEquiv c X c' Y) (f : UnitaryEquiv c' Y c'' Z) : UnitaryEquiv c X c'' Z where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  preservesInner v w := (f.preservesInner _ _).trans (e.preservesInner v w)
  topology_eq := by
    rw [← e.topology_eq, ← f.topology_eq, induced_compose]
    rfl

theorem continuous (e : UnitaryEquiv c X c' Y) :
    Continuous[topology c X, topology c' Y] e.toLinearEquiv := by
  rw [← e.topology_eq]
  exact continuous_induced_dom

theorem continuous_symm (e : UnitaryEquiv c X c' Y) :
    Continuous[topology c' Y, topology c X] e.toLinearEquiv.symm :=
  e.symm.continuous

/-- A unitary equivalence as a continuous linear equivalence. -/
def toContinuousLinearEquiv (e : UnitaryEquiv c X c' Y) :
    letI := topology c X; letI := topology c' Y; V ≃L[ℂ] W :=
  letI := topology c X; letI := topology c' Y
  { e.toLinearEquiv with
    continuous_toFun := e.continuous
    continuous_invFun := e.continuous_symm }

/-- Conjugation by a unitary equivalence is a bijection of the observables: a symmetric operator
is continuous on `V` if and only if its conjugate is continuous on `W`. -/
theorem isObservable_conj_iff (e : UnitaryEquiv c X c' Y) (A : Module.End ℂ V) :
    IsObservable c' (topology c' Y) (e.toLinearEquiv.conj A) ↔
      IsObservable c (topology c X) A := by
  rw [IsObservable, IsObservable, e.preservesInner.isSymmetric_conj_iff, ← e.topology_eq,
    continuous_induced_iff]

/-- A unitary equivalence induces a homeomorphism of the pure states, the projective spaces with
the quotient topologies, sending the ray of `v` to the ray of `U v`. -/
def pureStates (e : UnitaryEquiv c X c' Y) :
    letI := topology c X; letI := topology c' Y; ℙ ℂ V ≃ₜ ℙ ℂ W :=
  letI := topology c X; letI := topology c' Y
  Projectivization.mapHomeomorph e.toContinuousLinearEquiv

theorem pureStates_mk (e : UnitaryEquiv c X c' Y) (v : V) (hv : v ≠ 0) :
    letI := topology c X; letI := topology c' Y
    e.pureStates (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (e.toLinearEquiv v) (e.toLinearEquiv.map_ne_zero_iff.2 hv) :=
  letI := topology c X; letI := topology c' Y
  Projectivization.mapHomeomorph_mk _ _ _

end UnitaryEquiv

/-! ### Lie isomorphisms -/

/-- The Lie algebra of the defining observables: the complex Lie subalgebra of `Module.End ℂ V`,
with the commutator as bracket, that they span. -/
abbrev lieAlgebra : LieSubalgebra ℂ (Module.End ℂ V) := LieSubalgebra.lieSpan ℂ _ (Set.range X)

variable {X} in
lemma mem_algebra_of_mem_lieAlgebra {A : Module.End ℂ V} (hA : A ∈ lieAlgebra X) :
    A ∈ algebra X :=
  (LieSubalgebra.lieSpan_le (K := lieSubalgebraOfSubalgebra ℂ _ (algebra X))).2
    Algebra.subset_adjoin hA

/-- The algebra of the pulled-back observables `e⁻¹ Y_j e` is the conjugate of the algebra of
the `Y j`. -/
lemma algebra_pullback (e : V ≃ₗ[ℂ] W) :
    algebra (pullback e Y) = (algebra Y).map (e.symm.conjAlgEquiv ℂ).toAlgHom := by
  rw [AlgHom.map_adjoin, ← Set.range_comp]
  congr 2

/-- A Lie isomorphism of quantum vector spaces: a linear bijection `U : V ≃ W` that preserves
the inner product and whose conjugation `A ↦ U A U⁻¹` maps the Lie algebra of the `X i` onto the
Lie algebra of the `Y j`. -/
structure LieIso extends V ≃ₗ[ℂ] W where
  preservesInner : PreservesInner c c' toLinearEquiv
  conj_mem_iff (A : Module.End ℂ V) : toLinearEquiv.conj A ∈ lieAlgebra Y ↔ A ∈ lieAlgebra X

namespace LieIso

variable {c X c' Y c'' Z}

/-- The identity is a Lie isomorphism. -/
def refl : LieIso c X c X where
  toLinearEquiv := LinearEquiv.refl ℂ V
  preservesInner _ _ := rfl
  conj_mem_iff _ := Iff.rfl

/-- The inverse of a Lie isomorphism. -/
def symm (e : LieIso c X c' Y) : LieIso c' Y c X where
  toLinearEquiv := e.toLinearEquiv.symm
  preservesInner := e.preservesInner.symm
  conj_mem_iff B := by rw [← e.conj_mem_iff, LinearEquiv.conj_conj_symm]

/-- The composition of two Lie isomorphisms. -/
def trans (e : LieIso c X c' Y) (f : LieIso c' Y c'' Z) : LieIso c X c'' Z where
  toLinearEquiv := e.toLinearEquiv.trans f.toLinearEquiv
  preservesInner v w := (f.preservesInner _ _).trans (e.preservesInner v w)
  conj_mem_iff A := by
    rw [← LinearEquiv.conj_trans, LinearEquiv.trans_apply, f.conj_mem_iff, e.conj_mem_iff]

/-- Every Lie isomorphism is a unitary equivalence: the Lie algebras of the two frames generate
conjugate algebras, so the topologies agree. -/
def toUnitaryEquiv (e : LieIso c X c' Y) : UnitaryEquiv c X c' Y where
  toLinearEquiv := e.toLinearEquiv
  preservesInner := e.preservesInner
  topology_eq := by
    rw [induced_topology_eq_pullback c c' Y e.preservesInner]
    refine topology_eq_of_mem_algebra c _ _ (fun j => ?_) fun i => ?_
    · refine mem_algebra_of_mem_lieAlgebra ?_
      rw [← e.conj_mem_iff, pullback, LinearEquiv.conj_conj_symm]
      exact LieSubalgebra.subset_lieSpan ⟨j, rfl⟩
    · have h := mem_algebra_of_mem_lieAlgebra
        ((e.conj_mem_iff (X i)).2 (LieSubalgebra.subset_lieSpan ⟨i, rfl⟩))
      rw [algebra_pullback]
      exact ⟨_, h, by ext; simp⟩

end LieIso

end QuantumVectorSpaces
