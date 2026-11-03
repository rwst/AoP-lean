/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Pinching
public import ForPhyslib.QuantumMechanics.Wigner.EqualMixtures
public import Physlib.Mathematics.ForMathlib.OneParameterSubgroups.Unitary

/-!
# The resolvent of the von Neumann equation

## i. Overview

Let `V t = exp (-i t K)` be a unitary one-parameter group on a finite-dimensional complex Hilbert
space, with self-adjoint generator `K`. On operators it acts by the unitary channel
`T t ρ = V t ρ V t†`, which solves the von Neumann equation `ρ' = L ρ` with
`L ρ = -i (K ρ - ρ K)`.

For every real `τ` the map `1 - τ L` is injective, so in finite dimension it is invertible. The
inverse `Ψ τ = (1 - τ L)⁻¹` is the resolvent. If `ρ` is self-adjoint, so is `σ = Ψ τ ρ`, and the
spectral projectors `Pₓ` of `σ` satisfy `Pₓ (L σ) Pₓ = 0`, because `σ Pₓ = Pₓ σ = x Pₓ`. Hence
`Pₓ ρ Pₓ = Pₓ σ Pₓ = x Pₓ`, and summing over `x` gives `Ψ τ ρ = ∑ₓ Pₓ ρ Pₓ`: the resolvent is a
projective measurement by the spectral decomposition of its own output. The same identity proves
injectivity, and shows that `Ψ τ` maps density operators to density operators.

The resolvent and the unitary step agree to first order: `Ψ τ = 1 + τ L + τ² L² Ψ τ` and
`T τ = 1 + τ L + O(τ²)`, with `‖L‖ ≤ 2 ‖K‖`. On density operators, which have operator norm at
most one, this gives `‖Ψ τ ρ - T τ ρ‖ ≤ 8 ‖K‖² τ²`. For a pure state `|ψ⟩⟨ψ|`, the spectral
projector of `Ψ τ |ψ⟩⟨ψ|` at its largest eigenvalue `q` is a pure state `|φ⟩⟨φ|`, with
`1 - q ≤ 8 ‖K‖² τ²` and `‖|φ⟩⟨φ| - T τ |ψ⟩⟨ψ|‖ ≤ 48 ‖K‖² τ²` once `8 ‖K‖² τ² ≤ ½`. The
last bound is a Davis–Kahan estimate: on the orthogonal complement of `φ` the operator is at most
`1 - q`, and `q ≥ ½`.

Since `T τ` is an isometry, errors of order `τ²` per step add up over `n` steps of duration `t / n`
to `O(t² / n)`. This gives the resolvent exponential formula `(Ψ (t / n))ⁿ ρ → T t ρ`.

We set `ħ = 1`; the general case is `K = H / ħ`.

## ii. Key results

- `QuantumMechanics.vonNeumannGenerator`: the generator `L ρ = -i (K ρ - ρ K)`.
- `QuantumMechanics.unitaryChannel`, `QuantumMechanics.hasDerivAt_unitaryChannel`: the unitary
  channel solves the von Neumann equation.
- `QuantumMechanics.vonNeumannResolvent`: the resolvent `(1 - τ L)⁻¹`.
- `QuantumMechanics.pinching_vonNeumannResolvent`: `Ψ τ ρ = ∑ₓ Pₓ ρ Pₓ` for the spectral
  projectors of `Ψ τ ρ`.
- `QuantumMechanics.isDensity_vonNeumannResolvent`: `Ψ τ` preserves density operators.
- `QuantumMechanics.norm_vonNeumannResolvent_sub_unitaryChannel_le`: the second-order estimate.
- `QuantumMechanics.exists_spectralProj_max_eq_proj`: the largest outcome on a pure state.
- `QuantumMechanics.tendsto_vonNeumannResolvent_iterate`: the resolvent exponential formula.
- `QuantumMechanics.tendsto_inv_smul_vonNeumannResolvent_sub`: `(Ψ τ ρ - ρ) / τ → L ρ`.
- `QuantumMechanics.timeReversal`: the reversed group `t ↦ V (-t)`.

## iii. Table of contents

- A. The von Neumann generator
- B. The unitary channel
- C. Spectral blocks of the generator
- D. The resolvent
- E. The resolvent is a projective measurement
- F. Second-order estimates
- G. The largest outcome on a pure state
- H. The exponential formula
- I. Time reversal

## iv. References

- K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Springer
  (2000), Section II.1.
- R. Bhatia, *Matrix Analysis*, Springer (1997), Section VII.3 (Davis–Kahan).
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace QuantumMechanics.Wigner Complex Set Filter
open scoped Topology

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-!
## A. The von Neumann generator
-/

/-- The von Neumann generator `L ρ = -i (K ρ - ρ K)`, with `ħ = 1`. -/
def vonNeumannGenerator (K : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
  (-I) • (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) K - (ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip K)

variable {K : E →L[ℂ] E}

lemma vonNeumannGenerator_apply (K ρ : E →L[ℂ] E) :
    vonNeumannGenerator K ρ = (-I) • (K * ρ - ρ * K) := rfl

lemma norm_vonNeumannGenerator_apply_le (K ρ : E →L[ℂ] E) :
    ‖vonNeumannGenerator K ρ‖ ≤ 2 * ‖K‖ * ‖ρ‖ := by
  rw [vonNeumannGenerator_apply, norm_smul, norm_neg, norm_I, one_mul]
  calc ‖K * ρ - ρ * K‖ ≤ ‖K * ρ‖ + ‖ρ * K‖ := norm_sub_le _ _
    _ ≤ ‖K‖ * ‖ρ‖ + ‖ρ‖ * ‖K‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖K‖ * ‖ρ‖ := by ring

section Complete

variable [CompleteSpace E]

lemma vonNeumannGenerator_star (hK : IsSelfAdjoint K) (ρ : E →L[ℂ] E) :
    vonNeumannGenerator K (star ρ) = star (vonNeumannGenerator K ρ) := by
  simp only [vonNeumannGenerator_apply, star_smul, star_sub, star_mul, hK.star_eq, star_neg,
    star_def, conj_I, neg_neg, smul_sub, neg_smul]
  abel

/-!
## B. The unitary channel
-/

/-- The unitary channel `ρ ↦ V t ρ V t†`. -/
def unitaryChannel (V : UnitaryOneParameterGroup E) (t : ℝ) (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  V t * ρ * star (V t)

variable (V : UnitaryOneParameterGroup E)

lemma unitaryChannel_zero (ρ : E →L[ℂ] E) : unitaryChannel V 0 ρ = ρ := by
  simp [unitaryChannel, V.toAddChar.map_zero_eq_one]

lemma unitaryChannel_add (s t : ℝ) (ρ : E →L[ℂ] E) :
    unitaryChannel V (s + t) ρ = unitaryChannel V s (unitaryChannel V t ρ) := by
  simp only [unitaryChannel, V.toAddChar.map_add_eq_mul, star_mul, mul_assoc]

lemma unitaryChannel_iterate (t : ℝ) (n : ℕ) (ρ : E →L[ℂ] E) :
    (unitaryChannel V t)^[n] ρ = unitaryChannel V (n * t) ρ := by
  induction n with
  | zero => simp [unitaryChannel_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, ← unitaryChannel_add]
    push_cast
    ring_nf

lemma unitaryChannel_sub (t : ℝ) (ρ σ : E →L[ℂ] E) :
    unitaryChannel V t (ρ - σ) = unitaryChannel V t ρ - unitaryChannel V t σ := by
  simp [unitaryChannel, mul_sub, sub_mul]

lemma norm_unitaryChannel (t : ℝ) (ρ : E →L[ℂ] E) : ‖unitaryChannel V t ρ‖ = ‖ρ‖ := by
  rw [unitaryChannel, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (V.mem_unitary t)),
    CStarRing.norm_mem_unitary_mul _ (V.mem_unitary t)]

lemma unitaryChannel_proj (t : ℝ) (ψ : E) : unitaryChannel V t (proj ψ) = proj (V t ψ) := by
  ext x
  simp only [unitaryChannel, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.star_eq_adjoint, proj_apply, ContinuousLinearMap.adjoint_inner_right,
    map_smul]

lemma isDensity_unitaryChannel (t : ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    IsDensity (unitaryChannel V t ρ) :=
  hρ.unitary_conj (V.mem_unitary t)

/-- The unitary channel solves the von Neumann equation `ρ' = L ρ`. -/
lemma hasDerivAt_unitaryChannel (ρ : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s => unitaryChannel V s ρ)
      (vonNeumannGenerator V.generator (unitaryChannel V t ρ)) t := by
  have h := ((V.hasDerivAt t).mul_const ρ).mul (V.hasDerivAt_star t)
  refine h.congr_deriv ?_
  have hc : V.generator * V t = V t * V.generator := (V.commute_generator t).eq
  rw [vonNeumannGenerator_apply, unitaryChannel,
    show V.generator * (V t * ρ * star (V t)) = V.generator * V t * ρ * star (V t) by
      simp only [mul_assoc], hc]
  simp only [mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, smul_sub, neg_smul, mul_assoc]
  abel

/-!
## C. Spectral blocks of the generator
-/

section Finite

variable [FiniteDimensional ℂ E]

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma trace_vonNeumannGenerator (K ρ : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(vonNeumannGenerator K ρ) = 0 := by
  rw [vonNeumannGenerator_apply, ContinuousLinearMap.toLinearMap_smul, map_smul,
    ContinuousLinearMap.toLinearMap_sub, map_sub, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm, sub_self, smul_zero]

/-- The diagonal blocks of `L σ` vanish in the spectral decomposition of `σ`. -/
lemma spectralProj_mul_vonNeumannGenerator_mul {σ : E →L[ℂ] E} (hσ : IsSelfAdjoint σ)
    (K : E →L[ℂ] E) (x : ℝ) : spectralProj σ x * vonNeumannGenerator K σ * spectralProj σ x = 0 := by
  rw [vonNeumannGenerator_apply, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul,
    show ∀ A B C D : E →L[ℂ] E, A * (B * C) * D = A * B * (C * D) by simp [mul_assoc],
    show ∀ A B C D : E →L[ℂ] E, A * (B * C) * D = A * B * C * D by simp [mul_assoc],
    mul_spectralProj hσ, spectralProj_mul hσ]
  simp [mul_assoc]

lemma pinching_vonNeumannGenerator {σ : E →L[ℂ] E} (hσ : IsSelfAdjoint σ) (K : E →L[ℂ] E) :
    pinching σ (vonNeumannGenerator K σ) = 0 :=
  Finset.sum_eq_zero fun x _ => spectralProj_mul_vonNeumannGenerator_mul hσ K x

/-- A self-adjoint `σ` is the pinching of `σ - τ L σ` by itself. -/
lemma pinching_sub_smul_vonNeumannGenerator {σ : E →L[ℂ] E} (hσ : IsSelfAdjoint σ)
    (K : E →L[ℂ] E) (τ : ℝ) : pinching σ (σ - τ • vonNeumannGenerator K σ) = σ := by
  have h : pinching σ (τ • vonNeumannGenerator K σ) = τ • pinching σ (vonNeumannGenerator K σ) := by
    simp [pinching, Finset.smul_sum]
  rw [pinching_sub, h, pinching_vonNeumannGenerator hσ, smul_zero, sub_zero,
    pinching_eq_self hσ (Commute.refl σ)]


omit [FiniteDimensional ℂ E] in
lemma Wigner.IsDensity.isSelfAdjoint {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) : IsSelfAdjoint ρ :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hρ.isPositive.isSymmetric

/-!
## D. The resolvent
-/

/-- The operator `1 - τ L` on operators. -/
def vonNeumannStep (K : E →L[ℂ] E) (τ : ℝ) : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E :=
  LinearMap.id - τ • (vonNeumannGenerator K).toLinearMap

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma vonNeumannStep_apply (K : E →L[ℂ] E) (τ : ℝ) (σ : E →L[ℂ] E) :
    vonNeumannStep K τ σ = σ - τ • vonNeumannGenerator K σ := rfl

omit [FiniteDimensional ℂ E] in
lemma vonNeumannStep_star (hK : IsSelfAdjoint K) (τ : ℝ) (σ : E →L[ℂ] E) :
    vonNeumannStep K τ (star σ) = star (vonNeumannStep K τ σ) := by
  simp [vonNeumannStep_apply, vonNeumannGenerator_star hK, star_sub]

/-- `1 - τ L` is injective: a self-adjoint `σ` is the pinching of `(1 - τ L) σ` by itself, and a
general `σ` splits into self-adjoint parts. -/
lemma injective_vonNeumannStep (hK : IsSelfAdjoint K) (τ : ℝ) :
    Function.Injective (vonNeumannStep K τ) := by
  refine (injective_iff_map_eq_zero _).mpr fun σ h => ?_
  have hsa : ∀ a : E →L[ℂ] E, IsSelfAdjoint a → vonNeumannStep K τ a = 0 → a = 0 := fun a ha h => by
    rw [← pinching_sub_smul_vonNeumannGenerator ha K τ, ← vonNeumannStep_apply, h]
    simp [pinching]
  have hstar : vonNeumannStep K τ (star σ) = 0 := by rw [vonNeumannStep_star hK, h, star_zero]
  have ha := hsa (σ + star σ) (IsSelfAdjoint.add_star_self σ) (by rw [map_add, h, hstar, add_zero])
  have hb := hsa (I • (σ - star σ)) (by
      simp only [IsSelfAdjoint, star_smul, star_sub, star_star, star_def, conj_I, neg_smul,
        ← smul_neg, neg_sub])
    (by rw [map_smul, map_sub, h, hstar, sub_zero, smul_zero])
  have h2 : (2 : ℂ) • σ = (σ + star σ) - I • (I • (σ - star σ)) := by
    rw [smul_smul, I_mul_I]
    module
  rw [ha, hb, smul_zero, sub_zero] at h2
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The resolvent `Ψ τ = (1 - τ L)⁻¹` of the von Neumann generator of `V`. -/
def vonNeumannResolvent (V : UnitaryOneParameterGroup E) (τ : ℝ) :
    (E →L[ℂ] E) ≃ₗ[ℂ] E →L[ℂ] E :=
  (LinearEquiv.ofInjectiveEndo _ (injective_vonNeumannStep V.generator_isSelfAdjoint τ)).symm

/-- `(1 - τ L) (Ψ τ ρ) = ρ`. -/
lemma vonNeumannResolvent_sub (τ : ℝ) (ρ : E →L[ℂ] E) :
    vonNeumannResolvent V τ ρ - τ • vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ)
      = ρ :=
  (LinearEquiv.ofInjectiveEndo _ (injective_vonNeumannStep V.generator_isSelfAdjoint τ)
    ).apply_symm_apply ρ

/-- `Ψ τ ((1 - τ L) σ) = σ`. -/
lemma vonNeumannResolvent_vonNeumannStep (τ : ℝ) (σ : E →L[ℂ] E) :
    vonNeumannResolvent V τ (vonNeumannStep V.generator τ σ) = σ :=
  (LinearEquiv.ofInjectiveEndo _ (injective_vonNeumannStep V.generator_isSelfAdjoint τ)
    ).symm_apply_apply σ

/-- The resolvent identity `Ψ τ ρ - ρ = τ L (Ψ τ ρ)`. -/
lemma vonNeumannResolvent_sub_self (τ : ℝ) (ρ : E →L[ℂ] E) :
    vonNeumannResolvent V τ ρ - ρ =
      τ • vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ) := by
  nth_rw 2 [← vonNeumannResolvent_sub V τ ρ]
  abel

lemma vonNeumannResolvent_star (τ : ℝ) (ρ : E →L[ℂ] E) :
    vonNeumannResolvent V τ (star ρ) = star (vonNeumannResolvent V τ ρ) := by
  nth_rw 1 [← vonNeumannResolvent_sub V τ ρ]
  rw [← vonNeumannStep_apply, ← vonNeumannStep_star V.generator_isSelfAdjoint,
    vonNeumannResolvent_vonNeumannStep]

lemma isSelfAdjoint_vonNeumannResolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) :
    IsSelfAdjoint (vonNeumannResolvent V τ ρ) := by
  rw [IsSelfAdjoint, ← vonNeumannResolvent_star, hρ.star_eq]

lemma trace_vonNeumannResolvent (τ : ℝ) (ρ : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(vonNeumannResolvent V τ ρ) = LinearMap.trace ℂ E ↑ρ := by
  nth_rw 2 [← vonNeumannResolvent_sub V τ ρ]
  rw [← Complex.coe_smul, ContinuousLinearMap.toLinearMap_sub, map_sub,
    ContinuousLinearMap.toLinearMap_smul, map_smul,
    trace_vonNeumannGenerator, smul_zero, sub_zero]

/-!
## E. The resolvent is a projective measurement
-/

/-- **The resolvent is a projective measurement**: for self-adjoint `ρ`, `Ψ τ ρ = ∑ₓ Pₓ ρ Pₓ`, where `Pₓ` are the spectral
projectors of `Ψ τ ρ` itself. -/
theorem pinching_vonNeumannResolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) :
    pinching (vonNeumannResolvent V τ ρ) ρ = vonNeumannResolvent V τ ρ := by
  nth_rw 2 [← vonNeumannResolvent_sub V τ ρ]
  exact pinching_sub_smul_vonNeumannGenerator (isSelfAdjoint_vonNeumannResolvent V τ hρ) _ τ

/-- `Pₓ ρ Pₓ = x Pₓ` for the spectral projectors `Pₓ` of `Ψ τ ρ`. -/
theorem spectralProj_mul_mul_vonNeumannResolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ)
    (x : ℝ) :
    spectralProj (vonNeumannResolvent V τ ρ) x * ρ * spectralProj (vonNeumannResolvent V τ ρ) x =
      x • spectralProj (vonNeumannResolvent V τ ρ) x := by
  have h := vonNeumannResolvent_sub V τ ρ
  have hσ := isSelfAdjoint_vonNeumannResolvent V τ hρ
  set σ := vonNeumannResolvent V τ ρ
  set P := spectralProj σ x
  have h0 := spectralProj_mul_vonNeumannGenerator_mul hσ V.generator x
  calc P * ρ * P = P * σ * P - τ • (P * vonNeumannGenerator V.generator σ * P) := by
        rw [← h]
        simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc]
    _ = x • P := by
        rw [h0, smul_zero, sub_zero, mul_assoc, mul_spectralProj hσ, mul_smul_comm,
          spectralProj_mul_self]

/-- The resolvent maps density operators to density operators. -/
theorem isDensity_vonNeumannResolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    IsDensity (vonNeumannResolvent V τ ρ) := by
  rw [← pinching_vonNeumannResolvent V τ hρ.isSelfAdjoint]
  exact isDensity_pinching (isSelfAdjoint_vonNeumannResolvent V τ hρ.isSelfAdjoint) hρ

/-!
## F. Second-order estimates
-/

omit [FiniteDimensional ℂ E] in
/-- First order: `‖T t ρ - ρ‖ ≤ 2 ‖K‖ ‖ρ‖ t`. -/
lemma norm_unitaryChannel_sub_le (ρ : E →L[ℂ] E) {t : ℝ} (ht : 0 ≤ t) :
    ‖unitaryChannel V t ρ - ρ‖ ≤ 2 * ‖V.generator‖ * ‖ρ‖ * t := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => unitaryChannel V s ρ)
    (fun s _ => (hasDerivAt_unitaryChannel V ρ s).hasDerivWithinAt)
    (fun s _ => (norm_vonNeumannGenerator_apply_le _ _).trans_eq (by rw [norm_unitaryChannel]))
    t ⟨ht, le_rfl⟩
  simpa [unitaryChannel_zero] using h

omit [FiniteDimensional ℂ E] in
/-- Second order: `‖T t ρ - ρ - t L ρ‖ ≤ 4 ‖K‖² ‖ρ‖ t²`. -/
lemma norm_unitaryChannel_sub_sub_le (ρ : E →L[ℂ] E) {t : ℝ} (ht : 0 ≤ t) :
    ‖unitaryChannel V t ρ - ρ - t • vonNeumannGenerator V.generator ρ‖ ≤
      4 * ‖V.generator‖ ^ 2 * ‖ρ‖ * t ^ 2 := by
  set L := vonNeumannGenerator V.generator
  have hd : ∀ s, HasDerivAt (fun s : ℝ => unitaryChannel V s ρ - ρ - s • L ρ)
      (L (unitaryChannel V s ρ - ρ)) s := fun s => by
    have h := ((hasDerivAt_unitaryChannel V ρ s).sub_const ρ).fun_sub
      ((hasDerivAt_id s).smul_const (L ρ))
    rw [map_sub]
    simpa using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s : ℝ => unitaryChannel V s ρ - ρ - s • L ρ) (C := 4 * ‖V.generator‖ ^ 2 * ‖ρ‖ * t)
    (fun s _ => (hd s).hasDerivWithinAt) (fun s hs => by
      calc ‖L (unitaryChannel V s ρ - ρ)‖ ≤ 2 * ‖V.generator‖ * ‖unitaryChannel V s ρ - ρ‖ :=
            norm_vonNeumannGenerator_apply_le _ _
        _ ≤ 2 * ‖V.generator‖ * (2 * ‖V.generator‖ * ‖ρ‖ * t) := by
            gcongr
            exact (norm_unitaryChannel_sub_le V ρ hs.1).trans (by gcongr; exact hs.2.le)
        _ = 4 * ‖V.generator‖ ^ 2 * ‖ρ‖ * t := by ring) t ⟨ht, le_rfl⟩
  simpa [unitaryChannel_zero, sq, mul_assoc] using h

/-- Second order for the resolvent: `Ψ τ ρ - ρ - τ L ρ = τ² L² Ψ τ ρ`. -/
lemma norm_vonNeumannResolvent_sub_sub_le (τ : ℝ) (ρ : E →L[ℂ] E) :
    ‖vonNeumannResolvent V τ ρ - ρ - τ • vonNeumannGenerator V.generator ρ‖ ≤
      4 * ‖V.generator‖ ^ 2 * ‖vonNeumannResolvent V τ ρ‖ * τ ^ 2 := by
  set L := vonNeumannGenerator V.generator
  set σ := vonNeumannResolvent V τ ρ
  have h : σ - ρ - τ • L ρ = τ • L (τ • L σ) := by
    rw [← vonNeumannResolvent_sub_self, map_sub, smul_sub, ← vonNeumannResolvent_sub_self]
  rw [h, norm_smul, Real.norm_eq_abs]
  calc |τ| * ‖L (τ • L σ)‖ ≤ |τ| * (2 * ‖V.generator‖ * ‖τ • L σ‖) := by
        gcongr
        exact norm_vonNeumannGenerator_apply_le _ _
    _ = |τ| * (2 * ‖V.generator‖ * (|τ| * ‖L σ‖)) := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |τ| * (2 * ‖V.generator‖ * (|τ| * (2 * ‖V.generator‖ * ‖σ‖))) := by
        gcongr
        exact norm_vonNeumannGenerator_apply_le _ _
    _ = 4 * ‖V.generator‖ ^ 2 * ‖σ‖ * τ ^ 2 := by rw [← sq_abs τ]; ring

/-- The resolvent tends to the identity: `‖Ψ τ ρ - ρ‖ ≤ 2 ‖K‖ |τ|` on density operators. -/
lemma norm_vonNeumannResolvent_sub_le (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    ‖vonNeumannResolvent V τ ρ - ρ‖ ≤ 2 * ‖V.generator‖ * |τ| := by
  rw [vonNeumannResolvent_sub_self, norm_smul, Real.norm_eq_abs]
  calc |τ| * ‖vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ)‖
      ≤ |τ| * (2 * ‖V.generator‖ * ‖vonNeumannResolvent V τ ρ‖) := by
        gcongr
        exact norm_vonNeumannGenerator_apply_le _ _
    _ ≤ |τ| * (2 * ‖V.generator‖ * 1) := by
        gcongr
        exact (isDensity_vonNeumannResolvent V τ hρ).norm_le_one
    _ = 2 * ‖V.generator‖ * |τ| := by ring

/-- **Second-order estimate**: on density operators, `‖Ψ τ ρ - T τ ρ‖ ≤ 8 ‖K‖² τ²`. -/
theorem norm_vonNeumannResolvent_sub_unitaryChannel_le {τ : ℝ} (hτ : 0 ≤ τ) {ρ : E →L[ℂ] E}
    (hρ : IsDensity ρ) :
    ‖vonNeumannResolvent V τ ρ - unitaryChannel V τ ρ‖ ≤ 8 * ‖V.generator‖ ^ 2 * τ ^ 2 := by
  have h1 := norm_vonNeumannResolvent_sub_sub_le V τ ρ
  have h2 := norm_unitaryChannel_sub_sub_le V ρ hτ
  have hΨ := (isDensity_vonNeumannResolvent V τ hρ).norm_le_one
  have hρ1 := hρ.norm_le_one
  calc ‖vonNeumannResolvent V τ ρ - unitaryChannel V τ ρ‖
      = ‖(vonNeumannResolvent V τ ρ - ρ - τ • vonNeumannGenerator V.generator ρ) -
          (unitaryChannel V τ ρ - ρ - τ • vonNeumannGenerator V.generator ρ)‖ := by
        congr 1
        abel
    _ ≤ 4 * ‖V.generator‖ ^ 2 * ‖vonNeumannResolvent V τ ρ‖ * τ ^ 2 +
          4 * ‖V.generator‖ ^ 2 * ‖ρ‖ * τ ^ 2 := (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ ≤ 4 * ‖V.generator‖ ^ 2 * 1 * τ ^ 2 + 4 * ‖V.generator‖ ^ 2 * 1 * τ ^ 2 := by gcongr
    _ = 8 * ‖V.generator‖ ^ 2 * τ ^ 2 := by ring

/-!
## G. The largest outcome on a pure state
-/

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
lemma re_inner_self_apply_sub_ge {A : E →L[ℂ] E} {u : E} (hu : ‖u‖ = 1) :
    -‖A‖ ≤ (⟪u, A u⟫_ℂ).re := by
  have h1 := Complex.abs_re_le_norm ⟪u, A u⟫_ℂ
  have h2 := norm_inner_le_norm (𝕜 := ℂ) u (A u)
  have h3 := A.le_opNorm u
  rw [hu] at h2 h3
  linarith [neg_abs_le (⟪u, A u⟫_ℂ).re]

lemma re_inner_spectralProj (X : E →L[ℂ] E) (x : ℝ) (u : E) :
    (⟪u, spectralProj X x u⟫_ℂ).re = ‖spectralProj X x u‖ ^ 2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_spectralProj X x)
  have h : ⟪u, spectralProj X x u⟫_ℂ = ⟪spectralProj X x u, spectralProj X x u⟫_ℂ := by
    nth_rw 1 [← spectralProj_mul_self X x]
    exact (hs u _).symm
  rw [h, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- If `σ` is a density operator within `δ` of the pure state `|u⟩⟨u|`, its largest eigenvalue is
at least `1 - δ`. -/
lemma one_sub_norm_sub_proj_le {σ : E →L[ℂ] E} (hσ : IsDensity σ) {u : E} (hu : ‖u‖ = 1) {x : ℝ}
    (hx : ∀ y ∈ spectrumFinset σ, y ≤ x) : 1 - ‖σ - proj u‖ ≤ x := by
  have hs := hσ.isSelfAdjoint
  have hsum : ∑ y ∈ spectrumFinset σ, ‖spectralProj σ y u‖ ^ 2 = 1 := by
    have h := congrArg (fun A : E →L[ℂ] E => (⟪u, A u⟫_ℂ).re) (sum_spectralProj hs)
    simp only [sum_apply, inner_sum, Complex.re_sum, re_inner_spectralProj] at h
    rw [h]
    simp [inner_self_eq_norm_sq_to_K, hu]
  have hle : (⟪u, σ u⟫_ℂ).re ≤ x := by
    have h := congrArg (fun A : E →L[ℂ] E => (⟪u, A u⟫_ℂ).re) (sum_smul_spectralProj hs)
    simp only [sum_apply, smul_apply, inner_sum, Complex.re_sum,
      ← Complex.coe_smul, inner_smul_right, Complex.re_ofReal_mul,
      re_inner_spectralProj] at h
    rw [← h]
    calc ∑ y ∈ spectrumFinset σ, y * ‖spectralProj σ y u‖ ^ 2
        ≤ ∑ y ∈ spectrumFinset σ, x * ‖spectralProj σ y u‖ ^ 2 :=
          Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_right (hx y hy) (sq_nonneg _)
      _ = x := by rw [← Finset.mul_sum, hsum, mul_one]
  have hge : 1 - ‖σ - proj u‖ ≤ (⟪u, σ u⟫_ℂ).re := by
    have h := re_inner_self_apply_sub_ge (A := σ - proj u) hu
    have h1 : (⟪u, proj u u⟫_ℂ).re = 1 := by rw [inner_proj_apply]; simp [hu]
    rw [sub_apply, inner_sub_right, Complex.sub_re, h1] at h
    linarith
  linarith

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
/-- Two pure states are close if the component of `u` orthogonal to `φ` is small. -/
lemma norm_proj_sub_proj_le {u φ : E} (hu : ‖u‖ = 1) (hφ : ‖φ‖ = 1) :
    ‖proj φ - proj u‖ ≤ 3 * ‖u - ⟪φ, u⟫_ℂ • φ‖ := by
  set c := ⟪φ, u⟫_ℂ
  set w := u - c • φ
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hφw : ⟪φ, w⟫_ℂ = 0 := by simp only [w, inner_sub_right, inner_smul_right, hφφ, mul_one, c,
    sub_self]
  have hpy : ‖u‖ * ‖u‖ = ‖w‖ * ‖w‖ + ‖c‖ * ‖c‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) w (c • φ)
      (by rw [inner_smul_right, inner_eq_zero_symm.mp hφw, mul_zero])
    rwa [sub_add_cancel, norm_smul, hφ, mul_one] at h
  rw [hu, one_mul] at hpy
  have h1 : proj u - proj (c • φ) = rankOne ℂ u w + rankOne ℂ w (c • φ) := by
    ext y
    simp only [proj, sub_apply, add_apply, rankOne_apply, w, inner_sub_left, sub_smul, smul_sub]
    abel
  have hA : ‖proj φ - proj (c • φ)‖ = ‖w‖ ^ 2 := by
    rw [proj_smul, show proj φ - ((‖c‖ ^ 2 : ℝ) : ℂ) • proj φ = ((1 - ‖c‖ ^ 2 : ℝ) : ℂ) • proj φ by
      rw [ofReal_sub, ofReal_one, sub_smul, one_smul], norm_smul, norm_real, Real.norm_eq_abs, proj,
      norm_rankOne, hφ, abs_of_nonneg (by nlinarith [norm_nonneg w])]
    nlinarith
  have hB : ‖proj u - proj (c • φ)‖ ≤ 2 * ‖w‖ := by
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_rankOne, norm_rankOne, hu, norm_smul, hφ]
    nlinarith [norm_nonneg w, norm_nonneg c]
  calc ‖proj φ - proj u‖ = ‖(proj φ - proj (c • φ)) - (proj u - proj (c • φ))‖ := by
        congr 1
        abel
    _ ≤ ‖w‖ ^ 2 + 2 * ‖w‖ := (norm_sub_le _ _).trans (by rw [hA]; linarith)
    _ ≤ 3 * ‖w‖ := by nlinarith [norm_nonneg w]

/-- A Davis–Kahan bound. Let `σ` be a density operator whose spectral projector at `x ≥ ½` is the
pure state `|φ⟩⟨φ|`. If `‖σ - |u⟩⟨u|‖ ≤ δ` for a unit `u`, then the component of `u`
orthogonal to `φ` has norm at most `2 δ`. -/
lemma norm_sub_inner_smul_le {σ : E →L[ℂ] E} (hσ : IsDensity σ) {x : ℝ} (hx : 2⁻¹ ≤ x) {u φ : E}
    (hu : ‖u‖ = 1) (hφ : ‖φ‖ = 1) (hP : spectralProj σ x = proj φ) :
    ‖u - ⟪φ, u⟫_ℂ • φ‖ ≤ 2 * ‖σ - proj u‖ := by
  have hs := hσ.isSelfAdjoint
  set c := ⟪φ, u⟫_ℂ
  set w := u - c • φ
  set P := spectralProj σ x
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hPφ : P φ = φ := by rw [hP, proj_apply, hφφ, one_smul]
  have hσφ : σ φ = (x : ℂ) • φ := by
    have h := congrArg (fun A : E →L[ℂ] E => A φ) (mul_spectralProj hs x)
    simp only [smul_apply] at h
    rw [Complex.coe_smul, ← hPφ]
    exact h
  have hwφ : ⟪w, φ⟫_ℂ = 0 := by
    rw [inner_eq_zero_symm]
    simp only [w, inner_sub_right, inner_smul_right, hφφ, mul_one, c, sub_self]
  have hPw : proj φ w = 0 := by
    rw [proj_apply, inner_eq_zero_symm.mp hwφ, zero_smul]
  -- `σ - x |φ⟩⟨φ|` is positive with trace `1 - x`
  set σ' := σ - x • proj φ
  have hσ' : σ' = (1 - P) * σ * (1 - P) := by
    have h1 : P * σ = x • P := spectralProj_mul hs x
    have h2 : σ * P = x • P := mul_spectralProj hs x
    have h3 : P * P = P := spectralProj_mul_self σ x
    have h4 : (1 - P) * σ * (1 - P) = σ - P * σ - σ * P + P * (σ * P) := by noncomm_ring
    rw [h4, h1, h2, mul_smul_comm, h3, show σ' = σ - x • P by rw [hP]]
    abel
  have hpos : (σ' : E →ₗ[ℂ] E).IsPositive := by
    have h := ((ContinuousLinearMap.isPositive_toLinearMap_iff σ).mp hσ.isPositive).conj_adjoint
      (1 - P)
    rw [← ContinuousLinearMap.star_eq_adjoint, star_sub, star_one,
      (isSelfAdjoint_spectralProj σ x).star_eq] at h
    rw [hσ']
    exact h.toLinearMap
  have htr : (LinearMap.trace ℂ E (σ' : E →ₗ[ℂ] E)).re = 1 - x := by
    rw [ContinuousLinearMap.toLinearMap_sub, map_sub, ← Complex.coe_smul,
      ContinuousLinearMap.toLinearMap_smul, map_smul, hσ.trace_eq_one, proj,
      trace_rankOne, hφφ]
    simp
  have hnorm : ‖σ'‖ ≤ 1 - x := htr ▸ ContinuousLinearMap.norm_le_re_trace hpos
  -- the main estimate
  have hwσw : (⟪w, σ w⟫_ℂ).re ≤ (1 - x) * ‖w‖ ^ 2 := by
    have h : ⟪w, σ w⟫_ℂ = ⟪w, σ' w⟫_ℂ := by
      simp [σ', sub_apply, smul_apply, hPw]
    rw [h]
    calc (⟪w, σ' w⟫_ℂ).re ≤ ‖⟪w, σ' w⟫_ℂ‖ := Complex.re_le_norm _
      _ ≤ ‖w‖ * (‖σ'‖ * ‖w‖) := (norm_inner_le_norm _ _).trans (by gcongr; exact σ'.le_opNorm w)
      _ ≤ ‖w‖ * ((1 - x) * ‖w‖) := by gcongr
      _ = (1 - x) * ‖w‖ ^ 2 := by ring
  have hwσu : ⟪w, σ u⟫_ℂ = ⟪w, σ w⟫_ℂ := by
    have : u = w + c • φ := by simp [w]
    rw [this, map_add, map_smul, hσφ, inner_add_right, inner_smul_right, inner_smul_right, hwφ]
    simp
  have hwσu' : ⟪w, σ u⟫_ℂ = (‖w‖ ^ 2 : ℂ) + ⟪w, (σ - proj u) u⟫_ℂ := by
    have hpu : proj u u = u := by
      rw [proj_apply, inner_self_eq_norm_sq_to_K, hu]
      simp
    have hwu : ⟪w, u⟫_ℂ = (‖w‖ ^ 2 : ℂ) := by
      have : u = w + c • φ := by simp [w]
      nth_rw 1 [this]
      rw [inner_add_right, inner_smul_right, hwφ, mul_zero, add_zero, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [sub_apply, inner_sub_right, hpu, hwu]
    ring
  have hΔ : -(‖w‖ * ‖σ - proj u‖) ≤ (⟪w, (σ - proj u) u⟫_ℂ).re := by
    have h1 := Complex.abs_re_le_norm ⟪w, (σ - proj u) u⟫_ℂ
    have h2 := norm_inner_le_norm (𝕜 := ℂ) w ((σ - proj u) u)
    have h3 := (σ - proj u).le_opNorm u
    rw [hu, mul_one] at h3
    have := neg_abs_le (⟪w, (σ - proj u) u⟫_ℂ).re
    nlinarith [norm_nonneg w]
  have key : x * ‖w‖ ^ 2 ≤ ‖w‖ * ‖σ - proj u‖ := by
    have h := congrArg Complex.re hwσu'
    rw [hwσu] at h
    simp only [Complex.add_re] at h
    norm_cast at h
    nlinarith
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · nlinarith [norm_nonneg (σ - proj u)]

omit [FiniteDimensional ℂ E] in
lemma mul_proj_mul_of_isSelfAdjoint {P : E →L[ℂ] E} (hP : IsSelfAdjoint P) (ψ : E) :
    P * proj ψ * P = proj (P ψ) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP
  ext y
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, proj_apply, map_smul]
  exact congrArg (· • P ψ) (hs ψ y).symm

/-- **The largest outcome on a pure state.** Let `|ψ⟩⟨ψ|` be a pure state and `8 ‖K‖² τ² ≤ ½`. The spectral
projector of `Ψ τ |ψ⟩⟨ψ|` at its largest eigenvalue `x` is a pure state `|φ⟩⟨φ|`, with
`1 - x ≤ 8 ‖K‖² τ²` and `‖|φ⟩⟨φ| - T τ |ψ⟩⟨ψ|‖ ≤ 48 ‖K‖² τ²`. -/
theorem exists_spectralProj_max_eq_proj {ψ : E} (hψ : ‖ψ‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hδ : 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ 2⁻¹) :
    ∃ x ∈ spectrumFinset (vonNeumannResolvent V τ (proj ψ)),
      (∀ y ∈ spectrumFinset (vonNeumannResolvent V τ (proj ψ)), y ≤ x) ∧
      1 - 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ x ∧
      ∃ φ : E, ‖φ‖ = 1 ∧ spectralProj (vonNeumannResolvent V τ (proj ψ)) x = proj φ ∧
        ‖proj φ - unitaryChannel V τ (proj ψ)‖ ≤ 48 * ‖V.generator‖ ^ 2 * τ ^ 2 := by
  have hψd := isDensity_proj hψ
  have h12 := spectralProj_mul_mul_vonNeumannResolvent V τ hψd.isSelfAdjoint
  set σ := vonNeumannResolvent V τ (proj ψ)
  have hσ : IsDensity σ := isDensity_vonNeumannResolvent V τ hψd
  have hs := hσ.isSelfAdjoint
  have hne : (spectrumFinset σ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have h1 := congrArg (fun A : E →L[ℂ] E => A ψ) (sum_spectralProj hs)
    simp only [h, Finset.sum_empty, zero_apply, one_apply_eq_self] at h1
    rw [← h1, norm_zero] at hψ
    exact zero_ne_one hψ
  obtain ⟨x, hx, hmax⟩ := (spectrumFinset σ).exists_max_image id hne
  set u := V τ ψ
  have hu : ‖u‖ = 1 := by rw [ContinuousLinearMap.norm_map_of_mem_unitary (V.mem_unitary τ), hψ]
  have hΔ : ‖σ - proj u‖ ≤ 8 * ‖V.generator‖ ^ 2 * τ ^ 2 := by
    rw [← unitaryChannel_proj]
    exact norm_vonNeumannResolvent_sub_unitaryChannel_le V hτ hψd
  have hx1 : 1 - 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ x :=
    (sub_le_sub_left hΔ 1).trans (one_sub_norm_sub_proj_le hσ hu hmax)
  have hx0 : x ≠ 0 := by linarith
  -- the spectral projector at `x` is pure
  set P := spectralProj σ x
  have h12 := h12 x
  rw [mul_proj_mul_of_isSelfAdjoint (isSelfAdjoint_spectralProj σ x)] at h12
  set v := P ψ
  have hv : v ≠ 0 := by
    intro hv
    rw [hv, proj, map_zero] at h12
    exact spectralProj_ne_zero hs hx ((smul_eq_zero.mp h12.symm).resolve_left hx0)
  have hPv : P v = v := by
    show P (P ψ) = P ψ
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, spectralProj_mul_self]
  have hvx : ‖v‖ ^ 2 = x := by
    have h := congrArg (fun A : E →L[ℂ] E => A v) h12
    simp only [proj_apply, smul_apply, inner_self_eq_norm_sq_to_K, ← Complex.coe_smul] at h
    rw [show spectralProj σ x v = v from hPv] at h
    have h' := congrArg Complex.re (smul_left_injective ℂ hv h)
    norm_cast at h'
  set φ := ((‖v‖ : ℂ)⁻¹) • v
  have hφ : ‖φ‖ = 1 := by
    rw [norm_smul, norm_inv, norm_real, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hPφ : P = proj φ := by
    have h1 : ‖(‖v‖ : ℂ)⁻¹‖ ^ 2 * x = 1 := by
      rw [norm_inv, norm_real, norm_norm, inv_pow, hvx, inv_mul_cancel₀ hx0]
    rw [proj_smul, h12, Complex.coe_smul, smul_smul, h1, one_smul]
  refine ⟨x, hx, hmax, hx1, φ, hφ, hPφ, ?_⟩
  rw [unitaryChannel_proj]
  calc ‖proj φ - proj u‖ ≤ 3 * ‖u - ⟪φ, u⟫_ℂ • φ‖ := norm_proj_sub_proj_le hu hφ
    _ ≤ 3 * (2 * ‖σ - proj u‖) := by gcongr; exact norm_sub_inner_smul_le hσ (by linarith) hu hφ hPφ
    _ ≤ 48 * ‖V.generator‖ ^ 2 * τ ^ 2 := by linarith

/-!
## H. The exponential formula
-/

omit [FiniteDimensional ℂ E] in
/-- Errors of at most `ε` per step against the unitary step accumulate to at most `n ε`, because
the unitary channel is an isometry. -/
lemma norm_sub_unitaryChannel_le_of_step {x : ℕ → E →L[ℂ] E} {τ ε : ℝ} (n : ℕ)
    (h : ∀ k < n, ‖x (k + 1) - unitaryChannel V τ (x k)‖ ≤ ε) :
    ‖x n - unitaryChannel V (n * τ) (x 0)‖ ≤ n * ε := by
  induction n with
  | zero => simp [unitaryChannel_zero]
  | succ n ih =>
    have h1 : x (n + 1) - unitaryChannel V ((n + 1 : ℕ) * τ) (x 0) =
        (x (n + 1) - unitaryChannel V τ (x n)) +
          unitaryChannel V τ (x n - unitaryChannel V (n * τ) (x 0)) := by
      rw [unitaryChannel_sub, ← unitaryChannel_add, show τ + n * τ = (n + 1 : ℕ) * τ by
        push_cast; ring]
      abel
    rw [h1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_unitaryChannel]
    have := ih fun k hk => h k (by omega)
    have := h n (by omega)
    push_cast
    linarith

/-- The resolvent preserves density operators under iteration. -/
lemma isDensity_vonNeumannResolvent_iterate (τ : ℝ) (n : ℕ) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    IsDensity ((vonNeumannResolvent V τ)^[n] ρ) := by
  induction n with
  | zero => exact hρ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact isDensity_vonNeumannResolvent V τ ih

/-- **The resolvent exponential formula**: `(Ψ (t / n))ⁿ ρ → T t ρ` on density operators,
with error at most `8 ‖K‖² t² / n`. -/
theorem tendsto_vonNeumannResolvent_iterate {t : ℝ} (ht : 0 ≤ t) {ρ : E →L[ℂ] E}
    (hρ : IsDensity ρ) :
    Tendsto (fun n : ℕ => (vonNeumannResolvent V (t / n))^[n] ρ) atTop
      (𝓝 (unitaryChannel V t ρ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (8 * ‖V.generator‖ ^ 2 * t ^ 2))
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h := norm_sub_unitaryChannel_le_of_step V
    (x := fun k => (vonNeumannResolvent V (t / n))^[k] ρ) (τ := t / n)
    (ε := 8 * ‖V.generator‖ ^ 2 * (t / n) ^ 2) n fun k _ => by
      simp only [Function.iterate_succ_apply']
      exact norm_vonNeumannResolvent_sub_unitaryChannel_le V (by positivity)
        (isDensity_vonNeumannResolvent_iterate V _ k hρ)
  rw [mul_div_cancel₀ t hn'] at h
  refine h.trans_eq ?_
  field_simp

/-- The resolvent is infinitesimal with generator `L`: `(Ψ τ ρ - ρ) / τ → L ρ` as `τ → 0⁺`. -/
theorem tendsto_inv_smul_vonNeumannResolvent_sub {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    Tendsto (fun τ : ℝ => τ⁻¹ • (vonNeumannResolvent V τ ρ - ρ)) (𝓝[>] 0)
      (𝓝 (vonNeumannGenerator V.generator ρ)) := by
  have hΨ : Tendsto (fun τ : ℝ => vonNeumannResolvent V τ ρ) (𝓝 0) (𝓝 ρ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun τ : ℝ => 2 * ‖V.generator‖ * |τ|) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto' 0 0 abs_zero).const_mul (2 * ‖V.generator‖)
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun τ => norm_vonNeumannResolvent_sub_le V τ hρ) h0
  have hL := ((vonNeumannGenerator V.generator).continuous.tendsto ρ).comp
    (hΨ.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
  refine hL.congr' (eventually_nhdsWithin_of_forall fun τ (hτ : 0 < τ) => ?_)
  simp only [Function.comp_apply]
  rw [vonNeumannResolvent_sub_self, inv_smul_smul₀ hτ.ne']

/-!
## I. Time reversal
-/

/-- The reversed group `t ↦ V (-t)`, generated by `-K`. -/
def timeReversal (V : UnitaryOneParameterGroup E) : UnitaryOneParameterGroup E :=
  UnitaryOneParameterGroup.ofSelfAdjoint V.generator_isSelfAdjoint.neg

omit [FiniteDimensional ℂ E] in
lemma timeReversal_apply (t : ℝ) : timeReversal V t = V (-t) := by
  rw [timeReversal, UnitaryOneParameterGroup.ofSelfAdjoint_apply, V.apply_eq_exp_generator,
    smul_neg, ← neg_smul]
  push_cast
  ring_nf

omit [FiniteDimensional ℂ E] in
lemma unitaryChannel_timeReversal (t : ℝ) (ρ : E →L[ℂ] E) :
    unitaryChannel (timeReversal V) t ρ = unitaryChannel V (-t) ρ := by
  simp [unitaryChannel, timeReversal_apply]

end Finite

end Complete

end QuantumMechanics
