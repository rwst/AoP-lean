/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.Positive
public import ForPhyslib.QuantumMechanics.Wigner.Density
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic
public import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# Pinching by an observable

## i. Overview

Let `X` be a self-adjoint operator on a finite-dimensional complex Hilbert space `E`, with spectral
decomposition `X = ∑ₓ x Pₓ`. The spectral projector `Pₓ` is the functional calculus of the
indicator of `{x}`, and the sum runs over the (finite) real spectrum of `X`. The *pinching* by `X`
is the map `P_X(ρ) = ∑ₓ Pₓ ρ Pₓ`: it keeps the diagonal blocks of `ρ` with respect to the
eigenspaces of `X` and deletes the off-diagonal ones. It is the output of a nonselective projective
measurement of `X`.

An operator commutes with `X` exactly when it is block diagonal, that is, fixed by the pinching.
The pinching preserves density operators and is self-dual for the trace pairing. Consequently
`ρ - P_X(ρ)` is Hilbert–Schmidt orthogonal to every operator commuting with `X`, which gives the
Pythagoras identity `‖ρ - σ‖²_HS = ‖ρ - P_X(ρ)‖²_HS + ‖P_X(ρ) - σ‖²_HS`. Hence `P_X(ρ)` is the
unique operator commuting with `X` closest to `ρ` in Hilbert–Schmidt norm. The Hilbert–Schmidt norm
is TauCeti's `ContinuousLinearMap.hilbertSchmidtNorm`.

## ii. Key results

- `QuantumMechanics.spectralProj`, `QuantumMechanics.pinching`: the spectral projector `Pₓ` and
  the pinching `P_X`.
- `QuantumMechanics.spectralProj_mul_spectralProj`, `QuantumMechanics.sum_spectralProj`,
  `QuantumMechanics.mul_spectralProj`: `Pₓ P_y = δₓ_y Pₓ`, `∑ₓ Pₓ = 1`, `X Pₓ = x Pₓ`.
- `QuantumMechanics.sum_smul_spectralProj`: the spectral decomposition `X = ∑ₓ x Pₓ`.
- `QuantumMechanics.commute_iff_pinching_eq`: `[σ, X] = 0` iff `P_X(σ) = σ`.
- `QuantumMechanics.trace_pinching_mul`: `tr(P_X(A) B) = tr(A P_X(B))`.
- `QuantumMechanics.isDensity_pinching`: the pinching of a density operator is a density
  operator.
- `QuantumMechanics.ker_pinching_le`, `QuantumMechanics.ker_le_ker_pinching`: supports under
  pinching.
- `QuantumMechanics.sq_hilbertSchmidtNorm_sub`: the Pythagoras identity.
- `QuantumMechanics.hilbertSchmidtNorm_sub_pinching_lt`: `P_X(ρ)` is the unique closest operator
  commuting with `X`.

## iii. Table of contents

- A. Spectral projectors
- B. The pinching map
- C. Density operators and supports
- D. Hilbert–Schmidt distance

## iv. References

- M. Hayashi, *A Group Theoretic Approach to Quantum Information*, Springer (2017), Section 2.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace QuantumMechanics.Wigner

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-!
## A. Spectral projectors
-/

/-- The real spectrum of an operator on a finite-dimensional space, as a finite set. -/
def spectrumFinset (X : E →L[ℂ] E) : Finset ℝ := (X.finite_spectrum ℝ).toFinset

lemma mem_spectrumFinset {X : E →L[ℂ] E} {x : ℝ} : x ∈ spectrumFinset X ↔ x ∈ spectrum ℝ X :=
  Set.Finite.mem_toFinset _

private lemma continuousOn_spectrum (X : E →L[ℂ] E) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ X) :=
  (X.finite_spectrum ℝ).continuousOn f

variable [CompleteSpace E]

/-- The spectral projector `Pₓ` of `X` at `x`: the functional calculus of the indicator of `{x}`.
For self-adjoint `X` it is the orthogonal projection onto the `x`-eigenspace. -/
def spectralProj (X : E →L[ℂ] E) (x : ℝ) : E →L[ℂ] E := cfc (({x} : Set ℝ).indicator 1) X

variable {X : E →L[ℂ] E}

omit [FiniteDimensional ℂ E] in
lemma isSelfAdjoint_spectralProj (X : E →L[ℂ] E) (x : ℝ) : IsSelfAdjoint (spectralProj X x) :=
  cfc_predicate _ _

lemma spectralProj_mul_spectralProj (X : E →L[ℂ] E) (x y : ℝ) :
    spectralProj X x * spectralProj X y = if x = y then spectralProj X x else 0 := by
  rw [spectralProj, spectralProj, ← cfc_mul _ _ X (continuousOn_spectrum X _)
    (continuousOn_spectrum X _)]
  split_ifs with h
  · subst h
    refine cfc_congr fun t _ => ?_
    by_cases ht : t = x <;> simp [ht]
  · rw [← cfc_zero ℝ X]
    refine cfc_congr fun t _ => ?_
    by_cases ht : t = x
    · subst ht
      simp [h]
    · simp [ht]

lemma spectralProj_mul_self (X : E →L[ℂ] E) (x : ℝ) :
    spectralProj X x * spectralProj X x = spectralProj X x := by
  simp [spectralProj_mul_spectralProj]

lemma sum_spectralProj (hX : IsSelfAdjoint X) :
    ∑ x ∈ spectrumFinset X, spectralProj X x = 1 := by
  simp only [spectralProj]
  rw [← cfc_sum _ X _ fun _ _ => continuousOn_spectrum X _, ← cfc_one ℝ X]
  refine cfc_congr fun t ht => ?_
  simp [Finset.sum_apply, mem_spectrumFinset.mpr ht]

lemma mul_spectralProj (hX : IsSelfAdjoint X) (x : ℝ) :
    X * spectralProj X x = x • spectralProj X x := by
  nth_rw 1 [← cfc_id' ℝ X]
  rw [spectralProj, ← cfc_mul _ _ X (continuousOn_spectrum X _) (continuousOn_spectrum X _),
    ← cfc_smul _ _ X (continuousOn_spectrum X _)]
  refine cfc_congr fun t _ => ?_
  by_cases ht : t = x <;> simp [ht]

lemma spectralProj_mul (hX : IsSelfAdjoint X) (x : ℝ) :
    spectralProj X x * X = x • spectralProj X x := by
  rw [← mul_spectralProj hX, spectralProj, ((Commute.refl X).cfc_real _).eq]

/-- The spectral decomposition `X = ∑ₓ x Pₓ`. -/
lemma sum_smul_spectralProj (hX : IsSelfAdjoint X) :
    ∑ x ∈ spectrumFinset X, x • spectralProj X x = X := by
  simp_rw [← mul_spectralProj hX, ← Finset.mul_sum, sum_spectralProj hX, mul_one]

/-- The spectral projector at a point of the spectrum is nonzero. -/
lemma spectralProj_ne_zero (hX : IsSelfAdjoint X) {x : ℝ} (hx : x ∈ spectrumFinset X) :
    spectralProj X x ≠ 0 := by
  intro h
  have h1 : (1 : ℝ) ∈ spectrum ℝ (spectralProj X x) := by
    rw [spectralProj, cfc_map_spectrum _ X hX (continuousOn_spectrum X _)]
    exact ⟨x, mem_spectrumFinset.mp hx, by simp⟩
  rcases subsingleton_or_nontrivial (E →L[ℂ] E) with hs | hs
  · exact spectrum.mem_iff.mp h1 (isUnit_of_subsingleton _)
  · rw [h, spectrum.zero_eq] at h1
    norm_num at h1

omit [FiniteDimensional ℂ E] in
lemma commute_spectralProj {σ : E →L[ℂ] E} (h : Commute σ X) (x : ℝ) :
    Commute σ (spectralProj X x) :=
  (h.symm.cfc_real _).symm

/-!
## B. The pinching map
-/

/-- The pinching `P_X(ρ) = ∑ₓ Pₓ ρ Pₓ` by `X`, the sum running over the real spectrum of `X`. -/
def pinching (X ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  ∑ x ∈ spectrumFinset X, spectralProj X x * ρ * spectralProj X x

lemma pinching_add (X ρ σ : E →L[ℂ] E) : pinching X (ρ + σ) = pinching X ρ + pinching X σ := by
  simp [pinching, mul_add, add_mul, Finset.sum_add_distrib]

lemma pinching_sub (X ρ σ : E →L[ℂ] E) : pinching X (ρ - σ) = pinching X ρ - pinching X σ := by
  simp [pinching, mul_sub, sub_mul, Finset.sum_sub_distrib]

lemma pinching_star (X ρ : E →L[ℂ] E) : pinching X (star ρ) = star (pinching X ρ) := by
  simp [pinching, star_sum, star_mul, (isSelfAdjoint_spectralProj X _).star_eq, mul_assoc]

/-- Block decomposition: `A = ∑ₓ ∑_y Pₓ A P_y`. -/
lemma sum_sum_spectralProj_mul (hX : IsSelfAdjoint X) (A : E →L[ℂ] E) :
    ∑ x ∈ spectrumFinset X, ∑ y ∈ spectrumFinset X,
      spectralProj X x * A * spectralProj X y = A := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_spectralProj hX, one_mul, mul_one]

/-- An operator commuting with `X` is fixed by the pinching. -/
lemma pinching_eq_self (hX : IsSelfAdjoint X) {σ : E →L[ℂ] E} (h : Commute σ X) :
    pinching X σ = σ := by
  simp_rw [pinching, ← (commute_spectralProj h _).eq, mul_assoc, spectralProj_mul_self,
    ← Finset.mul_sum, sum_spectralProj hX, mul_one]

/-- The pinching of any operator commutes with `X`. -/
lemma commute_pinching (hX : IsSelfAdjoint X) (ρ : E →L[ℂ] E) : Commute (pinching X ρ) X := by
  simp only [Commute, SemiconjBy, pinching, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_assoc, spectralProj_mul hX, ← mul_assoc, ← mul_assoc, mul_spectralProj hX,
    mul_smul_comm, smul_mul_assoc, smul_mul_assoc]

/-- **Commutant.** An operator commutes with `X` iff it is block diagonal. -/
theorem commute_iff_pinching_eq (hX : IsSelfAdjoint X) {σ : E →L[ℂ] E} :
    Commute σ X ↔ pinching X σ = σ :=
  ⟨pinching_eq_self hX, fun h => h ▸ commute_pinching hX σ⟩

lemma pinching_pinching (hX : IsSelfAdjoint X) (ρ : E →L[ℂ] E) :
    pinching X (pinching X ρ) = pinching X ρ :=
  pinching_eq_self hX (commute_pinching hX ρ)

lemma pinching_one (hX : IsSelfAdjoint X) : pinching X 1 = 1 :=
  pinching_eq_self hX (Commute.one_left X)

/-- The pinching is self-dual for the trace pairing. -/
theorem trace_pinching_mul (A B : E →L[ℂ] E) :
    LinearMap.trace ℂ E ↑(pinching X A * B) = LinearMap.trace ℂ E ↑(A * pinching X B) := by
  simp only [pinching, Finset.sum_mul, Finset.mul_sum, ContinuousLinearMap.toLinearMap_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  set P := spectralProj X x
  rw [show P * A * P * B = P * (A * P * B) by simp only [mul_assoc],
    ContinuousLinearMap.toLinearMap_mul, LinearMap.trace_mul_comm,
    ← ContinuousLinearMap.toLinearMap_mul]
  simp only [mul_assoc]

/-- The trace against an operator commuting with `X` sees only the pinching. -/
lemma trace_pinching_mul_of_commute (hX : IsSelfAdjoint X) (A : E →L[ℂ] E) {B : E →L[ℂ] E}
    (hB : Commute B X) :
    LinearMap.trace ℂ E ↑(pinching X A * B) = LinearMap.trace ℂ E ↑(A * B) := by
  rw [trace_pinching_mul, pinching_eq_self hX hB]

/-!
## C. Density operators and supports
-/

lemma isDensity_pinching (hX : IsSelfAdjoint X) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    IsDensity (pinching X ρ) where
  isPositive := by
    simp only [pinching, ContinuousLinearMap.toLinearMap_sum]
    refine Finset.sum_induction _ LinearMap.IsPositive (fun _ _ ha hb => ha.add hb)
      LinearMap.isPositive_zero fun x _ => ?_
    have h := ((ContinuousLinearMap.isPositive_toLinearMap_iff ρ).mp hρ.isPositive).conj_adjoint
      (spectralProj X x)
    rw [← ContinuousLinearMap.star_eq_adjoint, (isSelfAdjoint_spectralProj X x).star_eq] at h
    exact h.toLinearMap
  trace_eq_one := by
    have h := trace_pinching_mul (X := X) ρ 1
    rwa [mul_one, pinching_one hX, mul_one, hρ.trace_eq_one] at h

/-- The pinching of a positive operator has no larger support. -/
theorem ker_pinching_le (hX : IsSelfAdjoint X) {ρ : E →L[ℂ] E}
    (hρ : (ρ : E →ₗ[ℂ] E).IsPositive) :
    LinearMap.ker (pinching X ρ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E) := by
  intro v hv
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
  have h0 : ∑ y ∈ spectrumFinset X,
      RCLike.re ⟪ρ (spectralProj X y v), spectralProj X y v⟫_ℂ = 0 := by
    have := congrArg (fun w => RCLike.re ⟪w, v⟫_ℂ) hv
    simp only [pinching, sum_apply, mul_apply_eq_comp, sum_inner, map_sum, inner_zero_left,
      map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hPa : ContinuousLinearMap.adjoint (spectralProj X y) = spectralProj X y := by
      rw [← ContinuousLinearMap.star_eq_adjoint, (isSelfAdjoint_spectralProj X y).star_eq]
    rw [← ContinuousLinearMap.adjoint_inner_left (spectralProj X y), hPa]
  have hP : ∀ x ∈ spectrumFinset X, ρ (spectralProj X x v) = 0 := fun x hx =>
    hρ.apply_eq_zero_of_re_inner_eq_zero
      ((Finset.sum_eq_zero_iff_of_nonneg fun y _ => hρ.re_inner_nonneg_left _).mp h0 x hx)
  have hv' : v = (∑ x ∈ spectrumFinset X, spectralProj X x) v := by simp [sum_spectralProj hX]
  rw [hv', sum_apply, map_sum]
  exact Finset.sum_eq_zero hP

/-- If the support of `σ` commuting with `X` contains that of `ρ`, it contains that of `P_X(ρ)`. -/
theorem ker_le_ker_pinching {ρ σ : E →L[ℂ] E} (h : Commute σ X)
    (hk : LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (ρ : E →ₗ[ℂ] E)) :
    LinearMap.ker (σ : E →ₗ[ℂ] E) ≤ LinearMap.ker (pinching X ρ : E →ₗ[ℂ] E) := by
  intro v hv
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv ⊢
  have hP : ∀ x, ρ (spectralProj X x v) = 0 := fun x => by
    have : spectralProj X x v ∈ LinearMap.ker (σ : E →ₗ[ℂ] E) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← mul_apply_eq_comp,
        (commute_spectralProj h x).eq, mul_apply_eq_comp, hv, map_zero]
    simpa using hk this
  simp [pinching, hP]

/-!
## D. Hilbert–Schmidt distance
-/

omit [FiniteDimensional ℂ E] in
/-- In finite dimension the squared Hilbert–Schmidt norm is the sum of the squared norms of the
columns in any orthonormal basis. -/
lemma sq_hilbertSchmidtNorm_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E)
    (T : E →L[ℂ] E) : T.hilbertSchmidtNorm ^ 2 = ∑ i, ‖T (b i)‖ ^ 2 := by
  rw [T.sq_hilbertSchmidtNorm b.toHilbertBasis, T.hilbertSchmidtEnergy_def, tsum_fintype,
    ENNReal.toReal_sum fun _ _ => by finiteness]
  simp [b.coe_toHilbertBasis, ← ofReal_norm, ← ENNReal.ofReal_pow]

lemma sq_hilbertSchmidtNorm_add (A B : E →L[ℂ] E) :
    (A + B).hilbertSchmidtNorm ^ 2 = A.hilbertSchmidtNorm ^ 2 + B.hilbertSchmidtNorm ^ 2 +
      2 * RCLike.re (LinearMap.trace ℂ E ↑(star A * B)) := by
  let b := stdOrthonormalBasis ℂ E
  rw [sq_hilbertSchmidtNorm_eq_sum b, sq_hilbertSchmidtNorm_eq_sum b,
    sq_hilbertSchmidtNorm_eq_sum b, LinearMap.trace_eq_sum_inner _ b, map_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_apply, @norm_add_sq ℂ, ContinuousLinearMap.star_eq_adjoint]
  simp only [ContinuousLinearMap.coe_coe, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right]
  ring

lemma hilbertSchmidtNorm_eq_zero_iff (T : E →L[ℂ] E) : T.hilbertSchmidtNorm = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ ContinuousLinearMap.hilbertSchmidtNorm_zero⟩
  let b := stdOrthonormalBasis ℂ E
  have h2 := sq_hilbertSchmidtNorm_eq_sum b T
  rw [h, zero_pow two_ne_zero, eq_comm,
    Finset.sum_eq_zero_iff_of_nonneg fun _ _ => by positivity] at h2
  refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun i => ?_)
  simpa using h2 i (Finset.mem_univ i)

/-- **Pythagoras.** For `σ` commuting with `X`,
`‖ρ - σ‖²_HS = ‖ρ - P_X(ρ)‖²_HS + ‖P_X(ρ) - σ‖²_HS`. -/
theorem sq_hilbertSchmidtNorm_sub (hX : IsSelfAdjoint X) (ρ : E →L[ℂ] E) {σ : E →L[ℂ] E}
    (hσ : Commute σ X) :
    (ρ - σ).hilbertSchmidtNorm ^ 2 =
      (ρ - pinching X ρ).hilbertSchmidtNorm ^ 2 + (pinching X ρ - σ).hilbertSchmidtNorm ^ 2 := by
  have hD : Commute (pinching X ρ - σ) X := (commute_pinching hX ρ).sub_left hσ
  have hA : pinching X (star (ρ - pinching X ρ)) = 0 := by
    rw [pinching_star, pinching_sub, pinching_pinching hX, sub_self, star_zero]
  have hcross : LinearMap.trace ℂ E ↑(star (ρ - pinching X ρ) * (pinching X ρ - σ)) = 0 := by
    rw [← trace_pinching_mul_of_commute hX _ hD, hA, zero_mul, ContinuousLinearMap.toLinearMap_zero,
      map_zero]
  have h := sq_hilbertSchmidtNorm_add (ρ - pinching X ρ) (pinching X ρ - σ)
  rwa [sub_add_sub_cancel, hcross, map_zero, mul_zero, add_zero] at h

/-- **Closest commuting operator.** Every `σ ≠ P_X(ρ)` commuting with `X` is strictly farther
from `ρ` in Hilbert–Schmidt norm than `P_X(ρ)`. -/
theorem hilbertSchmidtNorm_sub_pinching_lt (hX : IsSelfAdjoint X) (ρ : E →L[ℂ] E)
    {σ : E →L[ℂ] E} (hσ : Commute σ X) (hne : σ ≠ pinching X ρ) :
    (ρ - pinching X ρ).hilbertSchmidtNorm < (ρ - σ).hilbertSchmidtNorm := by
  have h := sq_hilbertSchmidtNorm_sub hX ρ hσ
  have hpos : 0 < (pinching X ρ - σ).hilbertSchmidtNorm :=
    lt_of_le_of_ne (ContinuousLinearMap.hilbertSchmidtNorm_nonneg _) fun h0 =>
      hne (sub_eq_zero.mp ((hilbertSchmidtNorm_eq_zero_iff _).mp h0.symm)).symm
  refine (pow_lt_pow_iff_left₀ (ContinuousLinearMap.hilbertSchmidtNorm_nonneg _)
    (ContinuousLinearMap.hilbertSchmidtNorm_nonneg _) two_ne_zero).mp ?_
  rw [h]
  linarith [pow_pos hpos 2]

end QuantumMechanics
