/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.Countable

/-!
# Frame changes

In the proof of Theorem 5, [B]WDQ, two frames `A` and `B` of the same system come with their own
defining observables `X i` and `Y j` on the same space `V`, and the brief assumes that "the
defining observables of A must be observables in B and vice-versa". This file shows that this
premise holds exactly when the two frames give the same topology, and then they have the same
observables. The premise holds automatically in finite dimension, but not in general.

For Example 3 and the change of frame `y = tan(π/2 · erf x)` of the brief Unphysicality of
Hilbert spaces for quantum mechanics, where the premise fails, see Sec. 1 of
`further-results.tex` in this brief's directory and the module
`QuantumVectorSpaces.FurtherResults.SchwartzFrame`. For [B]WDQ relative to a group of frames,
see Sec. 3 there and the module `QuantumVectorSpaces.FurtherResults.FrameGroups`.

## Main results

* `IsObservable`  an observable for a topology: a continuous symmetric operator;
* `topology_eq_iff_continuous`  the frames give the same topology if and only if the defining
  observables of each are continuous for the other;
* `isObservable_iff_of_frames`  then the two frames have the same observables;
* `topology_eq_of_mem_algebra`  it suffices that the defining observables of each frame lie in
  the algebra of the other;
* `topology_eq_of_finiteDimensional`  in finite dimension all frames give the same topology;
* `Diagonal.not_continuous_mulOp`  but on the finitely supported sequences, the multiplication
  by `n` is not continuous for the frame whose only defining observable is the identity.

## References

* J.-P. Antoine, Dirac formalism and symmetry problems in quantum mechanics. II. Symmetry
  problems, J. Math. Phys. 10 (1969) 2276–2290, Sec. II: a symmetry group is compatible with the
  space of states when the space is invariant under its representation; Proposition 4:
  observables transforming by a finite-dimensional representation stay continuous.
-/

open Topology

@[expose] public noncomputable section

namespace QuantumVectorSpaces

section Frames

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : PreInnerProductSpace.Core ℂ V)
  {ι κ : Type*} (X : ι → Module.End ℂ V) (Y : κ → Module.End ℂ V)

/-- An observable for the topology `t`: a symmetric operator that is continuous for `t`. -/
def IsObservable (t : TopologicalSpace V) (A : Module.End ℂ V) : Prop :=
  IsSymmetric c A ∧ @Continuous V V t t A

/-- If the defining observables of `X` are continuous for the topology of `Y`, then that
topology is finer. (In Mathlib's order on topologies, finer is smaller.) -/
theorem topology_le_of_continuous (h : ∀ i, @Continuous V V (topology c Y) (topology c Y) (X i)) :
    topology c Y ≤ topology c X := by
  have ht := isAdmissible_topology c Y
  exact (isGreatest_topology c X).2
    ⟨ht.isTopologicalAddGroup, ht.continuousSMul, h, ht.continuous_inner⟩

/-- Two frames give the same topology if and only if the defining observables of each are
continuous for the topology of the other. -/
theorem topology_eq_iff_continuous :
    topology c X = topology c Y ↔
      (∀ i, @Continuous V V (topology c Y) (topology c Y) (X i)) ∧
        ∀ j, @Continuous V V (topology c X) (topology c X) (Y j) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · rw [← h]
      exact (isAdmissible_topology c X).continuous_obs i
    · rw [h]
      exact (isAdmissible_topology c Y).continuous_obs j
  · rintro ⟨hX, hY⟩
    exact le_antisymm (topology_le_of_continuous c Y X hY) (topology_le_of_continuous c X Y hX)

/-- [B]WDQ: if the defining observables of each frame are observables in the other, then the
two frames have the same observables. -/
theorem isObservable_iff_of_frames
    (hX : ∀ i, IsObservable c (topology c Y) (X i)) (hY : ∀ j, IsObservable c (topology c X) (Y j))
    (A : Module.End ℂ V) :
    IsObservable c (topology c X) A ↔ IsObservable c (topology c Y) A := by
  rw [(topology_eq_iff_continuous c X Y).2 ⟨fun i => (hX i).2, fun j => (hY j).2⟩]

/-- Frames whose defining observables lie in each other's algebra give the same topology. -/
theorem topology_eq_of_mem_algebra (hX : ∀ i, X i ∈ algebra Y) (hY : ∀ j, Y j ∈ algebra X) :
    topology c X = topology c Y :=
  (topology_eq_iff_continuous c X Y).2
    ⟨fun i => (isAdmissible_topology c Y).continuous_algebra c Y ⟨X i, hX i⟩,
      fun j => (isAdmissible_topology c X).continuous_algebra c X ⟨Y j, hY j⟩⟩

/-- In finite dimension, for a definite inner product, all frames give the same topology. -/
theorem topology_eq_of_finiteDimensional [FiniteDimensional ℂ V]
    (hc : ∀ v, c.inner v v = 0 → v = 0) : topology c X = topology c Y :=
  (topology_eq_moduleTopology c X hc).trans (topology_eq_moduleTopology c Y hc).symm

end Frames

/-! ### The premise is not automatic -/

namespace Diagonal

/-- The frame whose only defining observable is the identity; its topology is that of the `ℓ²`
norm. -/
abbrev idObs : Unit → Module.End ℂ (ℕ →₀ ℂ) := fun _ => 1

/-- In the frame with only the identity, every `p_A` is a multiple of the `ℓ²` norm, so it takes
the same value on all the unit vectors `eₙ`. -/
lemma seminormFamily_idObs_single (A : algebra idObs) (n : ℕ) :
    seminormFamily core idObs A (Finsupp.single n 1) =
      seminormFamily core idObs A (Finsupp.single 0 1) := by
  have hA : A.1 ∈ (⊥ : Subalgebra ℂ (Module.End ℂ (ℕ →₀ ℂ))) := by
    refine Algebra.adjoin_le ?_ A.2
    rintro _ ⟨_, rfl⟩
    exact Subalgebra.one_mem _
  obtain ⟨r, hr⟩ := Algebra.mem_bot.1 hA
  have h (m : ℕ) : seminormFamily core idObs A (Finsupp.single m 1) = ‖r‖ := by
    change core.toSeminorm (A.1 (Finsupp.single m 1)) = ‖r‖
    rw [← hr, Module.algebraMap_end_apply, Finsupp.smul_single, smul_eq_mul, mul_one,
      core_toSeminorm_single]
  rw [h, h]

/-- The premise of [B]WDQ is not automatic: the frame with every real multiplication operator
and the frame with only the identity share the space and the inner product, but the
multiplication by `n` is not continuous for the second frame. -/
theorem not_continuous_mulOp :
    ¬ @Continuous _ _ (topology core idObs) (topology core idObs) (mulOp fun n => n) := by
  intro hcont
  let := topology core idObs
  have hp := withSeminorms core idObs
  have hq : Continuous (core.toSeminorm.comp (mulOp fun n => (n : ℝ))) := by
    have h1 := hp.continuous_seminorm 1
    rw [seminormFamily_one] at h1
    exact h1.comp hcont
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp _ hq
  set K := (s.sup (seminormFamily core idObs)) (Finsupp.single 0 1)
  have hK (n : ℕ) : (n : ℝ) ≤ C * K := by
    have h1 := hC (Finsupp.single n 1)
    rw [Seminorm.comp_apply, mulOp_single, mul_one, core_toSeminorm_single, Complex.norm_real,
      Real.norm_natCast, smul_apply, NNReal.smul_def, smul_eq_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ C.2)
    refine Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun A hA => ?_
    rw [seminormFamily_idObs_single]
    exact Seminorm.le_finset_sup_apply hA
  obtain ⟨n, hn⟩ := exists_nat_gt ((C : ℝ) * K)
  exact (hK n).not_gt hn

end Diagonal

end QuantumVectorSpaces
