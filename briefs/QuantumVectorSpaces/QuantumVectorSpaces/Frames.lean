/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.Countable
public import HilbertUnphysicality
public import TauCeti.Analysis.SpecialFunctions.Gaussian.Schwartz

/-!
# Frame changes

In the proof of Theorem 5, [B]WDQ, two frames `A` and `B` of the same system come with their own
defining observables `X i` and `Y j` on the same space `V`, and the brief assumes that "the
defining observables of A must be observables in B and vice-versa". This file shows that this
premise holds exactly when the two frames give the same topology, and then they have the same
observables. The premise holds automatically in finite dimension, but not in general.

It fails for Example 3, `V = 𝓢(ℝ)`, with the change of frame `y = tan(π/2 · erf x)` that the
brief Unphysicality of Hilbert spaces for quantum mechanics uses against [B]WDQ (its
Proposition 3, in the module `HilbertUnphysicality`). Its unitary `U` sends the Gaussian packet `ψ`, a Schwartz function, to
`ϕ(y) = (π(1 + y²))^{-1/2}`, which is not one. So the second observer cannot express the first
observer's `ψ` in `𝓢(ℝ)`, and the second observer's position, carried back to the first frame,
is not defined at `ψ`. QSTO:V gives [B]WDQ only for changes of frame that map `V` onto itself.

## Main results

* `IsObservable`  an observable for a topology: a continuous symmetric operator;
* `topology_eq_iff_continuous`  the frames give the same topology if and only if the defining
  observables of each are continuous for the other;
* `isObservable_iff_of_frames`  then the two frames have the same observables;
* `topology_eq_of_mem_algebra`  it suffices that the defining observables of each frame lie in
  the algebra of the other;
* `topology_eq_of_finiteDimensional`  in finite dimension all frames give the same topology;
* `Diagonal.not_continuous_mulOp`  but on the finitely supported sequences, the multiplication
  by `n` is not continuous for the frame whose only defining observable is the identity;
* `SchwartzFrame.toLp_gaussSchwartz`  the Gaussian packet `ψ` of the Hilbert brief is a Schwartz
  function;
* `SchwartzFrame.toLp_mem_positionDomain`  every Schwartz function lies in the domain of the
  position operator on `L²(ℝ)`;
* `SchwartzFrame.frameUnitary_gaussState_not_mem_range`  `Uψ = ϕ` is not a Schwartz function;
* `SchwartzFrame.not_forall_frameUnitary_mem_range`  so `U` does not map `𝓢(ℝ)` into itself;
* `SchwartzFrame.toLp_gaussSchwartz_not_mem_domain`  and `U⁻¹YU`, the position `Y` of the
  second frame carried back to the first, is not defined at the Schwartz function `ψ`.

## References

* G. Carcassi, F. Calderón, C. A. Aidala, The unphysicality of Hilbert spaces,
  arXiv:2308.06669v3, Appendix, Sec. VIII: on the Schwartz space "the only unitary
  transformations we are interested in are those that map Schwartz functions to Schwartz
  functions", so the change of coordinate `y(x)` "is automatically ruled out".

* J.-P. Antoine, Dirac formalism and symmetry problems in quantum mechanics. II. Symmetry
  problems, J. Math. Phys. 10 (1969) 2276–2290, Sec. II: a symmetry group is compatible with the
  space of states when the space is invariant under its representation; Proposition 4:
  observables transforming by a finite-dimensional representation stay continuous.
* A. Galbis, E. Jordá, Composition operators on the Schwartz space, Rev. Mat. Iberoam. 34
  (2018) 397–412, Theorem 2.3: the changes of variable that map `𝓢(ℝ)` into itself.
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

/-! ### The change of frame of the Hilbert brief on `𝓢(ℝ)` -/

namespace SchwartzFrame

open HilbertUnphysicality MeasureTheory SchwartzMap QuantumMechanics

/-- The Gaussian packet `ψ(x) = (e^{-x²}/√π)^{1/2} = π^{-1/4} e^{-x²/2}` as a Schwartz
function. -/
def gaussSchwartz : 𝓢(ℝ, ℂ) :=
  ((√(√Real.pi) : ℝ) : ℂ)⁻¹ • TauCeti.gaussianSchwartzMap (b := (1 / 2 : ℂ)) (by norm_num)

lemma gaussSchwartz_apply (x : ℝ) : gaussSchwartz x = gaussFun x := by
  have h : √(Real.exp (-x ^ 2) / √Real.pi) = (√(√Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2) := by
    rw [Real.sqrt_div (Real.exp_pos _).le, div_eq_inv_mul, ← Real.exp_half]
    ring_nf
  simp only [gaussSchwartz, smul_apply, TauCeti.gaussianSchwartzMap_apply, smul_eq_mul, gaussFun,
    gaussDensity, h, Real.norm_eq_abs]
  rw [← Complex.ofReal_pow, sq_abs]
  push_cast
  ring_nf

/-- The Gaussian packet `ψ` of the Hilbert brief is a Schwartz function. -/
theorem toLp_gaussSchwartz : gaussSchwartz.toLp 2 volume = gaussState :=
  MemLp.toLp_congr _ _ (ae_of_all _ gaussSchwartz_apply)

/-- Every Schwartz function lies in the domain of the position operator on `L²(ℝ)`. -/
theorem toLp_mem_positionDomain (f : 𝓢(ℝ, ℂ)) : f.toLp 2 volume ∈ positionDomain := by
  refine (memLp (posOp f) 2).ae_eq ?_
  filter_upwards [coeFn_toLp f 2 volume] with x hx
  rw [posOp_apply, hx]

/-- The change of frame takes `ψ` out of `𝓢(ℝ)`: `Uψ = ϕ` is not a Schwartz function. -/
theorem frameUnitary_gaussState_not_mem_range :
    frameUnitary gaussState ∉ Set.range fun f : 𝓢(ℝ, ℂ) => f.toLp 2 volume := by
  rintro ⟨f, hf⟩
  exact frameUnitary_gaussState_not_mem (hf ▸ toLp_mem_positionDomain f)

/-- [B]WDQ on `𝓢(ℝ)` fails for this change of frame: `U` does not map `𝓢(ℝ)` into itself. -/
theorem not_forall_frameUnitary_mem_range :
    ¬ ∀ f : 𝓢(ℝ, ℂ), ∃ g : 𝓢(ℝ, ℂ), frameUnitary (f.toLp 2 volume) = g.toLp 2 volume := by
  intro h
  obtain ⟨g, hg⟩ := h gaussSchwartz
  rw [toLp_gaussSchwartz] at hg
  exact frameUnitary_gaussState_not_mem_range ⟨g, hg.symm⟩

/-- The premise of the proof of Theorem 5 fails for this change of frame: the position `Y` of
the second frame, carried back to the first as `U⁻¹YU`, is not defined at the Schwartz function
`ψ`, so it is not an operator on `𝓢(ℝ)`. -/
theorem toLp_gaussSchwartz_not_mem_domain :
    gaussSchwartz.toLp 2 volume ∉ (conjLinearPMap frameUnitary.symm positionOp).domain := by
  rw [mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_symm, toLp_gaussSchwartz]
  exact frameUnitary_gaussState_not_mem

end SchwartzFrame

end QuantumVectorSpaces
