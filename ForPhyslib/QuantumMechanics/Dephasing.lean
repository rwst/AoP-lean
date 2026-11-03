/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Calculus.MeanValue
public import ForPhyslib.QuantumMechanics.Pinching
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Dephasing by a Lindblad equation

## i. Overview

Let `X = ∑ₓ x Pₓ` be a self-adjoint operator on a finite-dimensional complex Hilbert space. The
Lindblad equation with vanishing Hamiltonian and the single jump operator `X` is
`ρ' = L(ρ)` with `L(ρ) = X ρ X - ½ (X² ρ + ρ X²)`. Since `Pₓ X = x Pₓ`, each block `Pₓ ρ P_y`
evolves on its own, by `(Pₓ ρ P_y)' = -½ (x - y)² Pₓ ρ P_y`. The diagonal blocks are constant and
the off-diagonal blocks decay exponentially, so every solution converges to the pinching
`P_X(ρ(0)) = ∑ₓ Pₓ ρ(0) Pₓ`.

The equation is assumed only for `t > 0`, together with continuity from the right at `t = 0`.
Under these assumptions the solution is unique and is given by the explicit dephasing flow
`∑ₓ ∑_y e^{-t (x - y)² / 2} Pₓ ρ(0) P_y`. In finite dimension convergence in operator norm is
convergence in any norm, in particular in trace norm.

## ii. Key results

- `QuantumMechanics.dephasingGenerator`: the generator `L`.
- `QuantumMechanics.spectralProj_mul_dephasingGenerator_mul`: `Pₓ L(ρ) P_y = -½ (x - y)² Pₓ ρ P_y`.
- `QuantumMechanics.dephasing`: the explicit solution.
- `QuantumMechanics.hasDerivAt_dephasing`, `QuantumMechanics.dephasing_zero`: it solves the
  equation with the right initial value.
- `QuantumMechanics.eq_dephasing`: every solution is the explicit one.
- `QuantumMechanics.tendsto_dephasing`: the explicit solution tends to the pinching.
- `QuantumMechanics.tendsto_pinching_of_hasDerivAt`: every solution tends to the pinching of its
  initial value.

## iii. Table of contents

- A. The generator
- B. The explicit solution
- C. Uniqueness and the limit

## iv. References

- H.-P. Breuer, F. Petruccione, *The Theory of Open Quantum Systems*, Oxford University Press
  (2002), Section 3.2.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace E] {X : E →L[ℂ] E}

/-!
## A. The generator
-/

/-- The dephasing Lindblad generator `L(ρ) = X ρ X - ½ (X² ρ + ρ X²)`: vanishing Hamiltonian and
the single jump operator `X`. -/
def dephasingGenerator (X : E →L[ℂ] E) : (E →L[ℂ] E) →ₗ[ℝ] E →L[ℂ] E where
  toFun ρ := X * ρ * X - (2⁻¹ : ℝ) • (X * X * ρ + ρ * (X * X))
  map_add' _ _ := by
    simp only [mul_add, add_mul, smul_add]
    rw [sub_add_sub_comm, add_add_add_comm]
  map_smul' _ _ := by
    simp only [mul_smul_comm, smul_mul_assoc, smul_add, smul_sub, RingHom.id_apply,
      smul_comm (2⁻¹ : ℝ)]

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
lemma dephasingGenerator_apply (X ρ : E →L[ℂ] E) :
    dephasingGenerator X ρ = X * ρ * X - (2⁻¹ : ℝ) • (X * X * ρ + ρ * (X * X)) := rfl

/-- The generator acts on the block `Pₓ A P_y` by the factor `-½ (x - y)²`. -/
lemma dephasingGenerator_block (hX : IsSelfAdjoint X) (x y : ℝ) (A : E →L[ℂ] E) :
    dephasingGenerator X (spectralProj X x * A * spectralProj X y) =
      (-((x - y) ^ 2 / 2)) • (spectralProj X x * A * spectralProj X y) := by
  set B := spectralProj X x * A * spectralProj X y
  have hl : X * B = x • B := by
    simp only [B, ← mul_assoc, mul_spectralProj hX, smul_mul_assoc]
  have hr : B * X = y • B := by
    simp only [B, mul_assoc, spectralProj_mul hX, mul_smul_comm]
  have h1 : X * B * X = (x * y) • B := by rw [hl, smul_mul_assoc, hr, smul_smul]
  have h2 : X * X * B = (x * x) • B := by rw [mul_assoc, hl, mul_smul_comm, hl, smul_smul]
  have h3 : B * (X * X) = (y * y) • B := by rw [← mul_assoc, hr, smul_mul_assoc, hr, smul_smul]
  rw [dephasingGenerator_apply, h1, h2, h3, ← add_smul, smul_smul, ← sub_smul]
  congr 1
  ring

/-- The generator acts blockwise: `Pₓ L(A) P_y = -½ (x - y)² Pₓ A P_y`. -/
lemma spectralProj_mul_dephasingGenerator_mul (hX : IsSelfAdjoint X) (x y : ℝ)
    (A : E →L[ℂ] E) :
    spectralProj X x * dephasingGenerator X A * spectralProj X y =
      (-((x - y) ^ 2 / 2)) • (spectralProj X x * A * spectralProj X y) := by
  have hl : spectralProj X x * X = x • spectralProj X x := spectralProj_mul hX x
  have hr : X * spectralProj X y = y • spectralProj X y := mul_spectralProj hX y
  set B := spectralProj X x * A * spectralProj X y
  have h1 : spectralProj X x * (X * A * X) * spectralProj X y = (x * y) • B := by
    calc _ = (spectralProj X x * X) * A * (X * spectralProj X y) := by simp only [mul_assoc]
      _ = _ := by rw [hl, hr, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  have h2 : spectralProj X x * (X * X * A) * spectralProj X y = (x * x) • B := by
    calc _ = (spectralProj X x * X) * X * A * spectralProj X y := by simp only [mul_assoc]
      _ = _ := by
        rw [hl, smul_mul_assoc, hl]
        simp only [smul_mul_assoc, smul_smul, B]
  have h3 : spectralProj X x * (A * (X * X)) * spectralProj X y = (y * y) • B := by
    calc _ = spectralProj X x * A * (X * (X * spectralProj X y)) := by simp only [mul_assoc]
      _ = _ := by rw [hr, mul_smul_comm, hr, mul_smul_comm, mul_smul_comm, smul_smul]
  rw [dephasingGenerator_apply, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    h1, h2, h3, ← add_smul, smul_smul, ← sub_smul]
  congr 1
  ring

/-!
## B. The explicit solution
-/

/-- The dephasing flow `∑ₓ ∑_y e^{-t (x - y)² / 2} Pₓ ρ P_y`. -/
def dephasing (X : E →L[ℂ] E) (t : ℝ) (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  ∑ x ∈ spectrumFinset X, ∑ y ∈ spectrumFinset X,
    Real.exp (-(t * ((x - y) ^ 2 / 2))) • (spectralProj X x * ρ * spectralProj X y)

lemma dephasing_zero (hX : IsSelfAdjoint X) (ρ : E →L[ℂ] E) : dephasing X 0 ρ = ρ := by
  simp [dephasing, sum_sum_spectralProj_mul hX]

/-- The dephasing flow solves the Lindblad equation. -/
theorem hasDerivAt_dephasing (hX : IsSelfAdjoint X) (ρ : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s => dephasing X s ρ) (dephasingGenerator X (dephasing X t ρ)) t := by
  simp only [dephasing, map_sum, map_smul, dephasingGenerator_block hX, smul_smul]
  refine HasDerivAt.fun_sum fun x _ => HasDerivAt.fun_sum fun y _ => ?_
  have h0 : HasDerivAt (fun s : ℝ => -(s * ((x - y) ^ 2 / 2))) (-((x - y) ^ 2 / 2)) t := by
    simpa using ((hasDerivAt_id' t).mul_const ((x - y) ^ 2 / 2)).fun_neg
  convert h0.exp.smul_const (spectralProj X x * ρ * spectralProj X y) using 1

/-- The dephasing flow tends to the pinching. -/
theorem tendsto_dephasing (ρ : E →L[ℂ] E) :
    Tendsto (fun t => dephasing X t ρ) atTop (𝓝 (pinching X ρ)) := by
  have hP : pinching X ρ = ∑ x ∈ spectrumFinset X, ∑ y ∈ spectrumFinset X,
      if x = y then spectralProj X x * ρ * spectralProj X y else 0 := by
    simp [pinching]
  rw [hP]
  refine tendsto_finsetSum _ fun x _ => tendsto_finsetSum _ fun y _ => ?_
  split_ifs with h
  · subst h
    simp
  · have hc : 0 < (x - y) ^ 2 / 2 := by have := sub_ne_zero.mpr h; positivity
    have he : Tendsto (fun t => Real.exp (-(t * ((x - y) ^ 2 / 2)))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hc)
    simpa using he.smul_const (spectralProj X x * ρ * spectralProj X y)

/-!
## C. Uniqueness and the limit
-/

/-- **Uniqueness.** A solution of the Lindblad equation for `t > 0` that is continuous from the
right at `0` is the dephasing flow of its initial value. -/
theorem eq_dephasing (hX : IsSelfAdjoint X) {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) :
    r t = dephasing X t (r 0) := by
  rw [← sum_sum_spectralProj_mul hX (r t), dephasing]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  let c := (x - y) ^ 2 / 2
  let f : ℝ → E →L[ℂ] E := fun s => spectralProj X x * r s * spectralProj X y
  let g : ℝ → E →L[ℂ] E := fun s => Real.exp (s * c) • f s
  have hg : ∀ s, 0 < s → HasDerivAt g 0 s := fun s hs => by
    have hf : HasDerivAt f (spectralProj X x * dephasingGenerator X (r s) * spectralProj X y) s :=
      ((hd s hs).const_mul _).mul_const _
    rw [spectralProj_mul_dephasingGenerator_mul hX] at hf
    refine ((((hasDerivAt_id' s).mul_const c).exp).fun_smul hf).congr_deriv ?_
    rw [smul_smul, ← add_smul]
    convert zero_smul ℝ (f s) using 2
    ring
  have hgc : ContinuousWithinAt g (Ici 0) 0 :=
    (Real.continuous_exp.comp (continuous_id.mul continuous_const)).continuousWithinAt.smul
      ((continuousWithinAt_const.mul hc).mul continuousWithinAt_const)
  have h := eq_of_hasDerivAt_eq_zero_of_continuousWithinAt hgc hg ht
  simp only [g, f, zero_mul, Real.exp_zero, one_smul] at h
  rw [← h, smul_smul, ← Real.exp_add]
  simp [c]

/-- **Equilibration.** Every solution of the Lindblad equation for `t > 0` that is continuous
from the right at `0` tends to the pinching of its initial value. -/
theorem tendsto_pinching_of_hasDerivAt (hX : IsSelfAdjoint X) {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) :
    Tendsto r atTop (𝓝 (pinching X (r 0))) :=
  (tendsto_dephasing (r 0)).congr'
    (eventuallyEq_of_mem (Ici_mem_atTop 0) fun _ ht => (eq_dephasing hX hd hc ht).symm)

end QuantumMechanics
