/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DensityOperator
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Pythagoras

/-!
# Observables with pure point spectrum and the pinching

## i. Overview

A *resolution of the identity* on a Hilbert space `E` of any dimension is a family `{Pᵢ}` of
pairwise orthogonal orthogonal projections with `∑ᵢ Pᵢ = 1` strongly; the index type is arbitrary.
A bounded observable with pure point spectrum is `X = ∑ᵢ xᵢ Pᵢ` with distinct real `xᵢ`
(`IsEigenDecomposition`), so that `Pᵢ` is the eigenprojection of `X` for `xᵢ`.

The *pinching* `P(ρ) = ∑ᵢ Pᵢ ρ Pᵢ`, the output of a nonselective projective measurement, is defined
for every bounded `ρ` as a strong sum: the terms are pairwise orthogonal and
`∑ᵢ ‖Pᵢ ρ Pᵢ v‖² ≤ ‖ρ‖² ‖v‖²`. It keeps the diagonal blocks `Pᵢ ρ Pᵢ` and deletes the others.
An operator commutes with `X` iff it commutes with every `Pᵢ` iff it is fixed by the pinching.
The pinching preserves positivity and the trace in `[0, ∞]`, hence density operators.

The Hilbert–Schmidt energy splits over the blocks `Pᵢ T Pⱼ` (TauCeti), which gives the
Pythagoras identity `‖ρ - σ‖²_HS = ‖ρ - P(ρ)‖²_HS + ‖P(ρ) - σ‖²_HS` for `σ` commuting with
every `Pᵢ`. Hence `P(ρ)` is the unique density operator commuting with `X` closest to `ρ`.

## ii. Key results

- `QuantumMechanics.IsResolutionOfIdentity`, `QuantumMechanics.IsEigenDecomposition`.
- `QuantumMechanics.IsResolutionOfIdentity.ext_block`: an operator is determined by its blocks.
- `QuantumMechanics.IsResolutionOfIdentity.pinching`: the pinching, with
  `mul_pinching_mul` (its blocks) and `isDensityOperator_pinching`.
- `QuantumMechanics.IsResolutionOfIdentity.pinching_eq_self_iff`,
  `QuantumMechanics.IsEigenDecomposition.commute_iff`: commuting means block diagonal.
- `QuantumMechanics.IsResolutionOfIdentity.hilbertSchmidtEnergy_sub`: the Pythagoras identity.
- `QuantumMechanics.IsResolutionOfIdentity.hilbertSchmidtNorm_sub_pinching_lt`: the pinching is
  the unique closest commuting density operator.

## iii. Table of contents

- A. Resolutions of the identity
- B. The pinching
- C. Density operators
- D. Hilbert–Schmidt distance
- E. Observables with pure point spectrum

## iv. References

- B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS (2005), §1–2.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open Filter Topology ContinuousLinearMap
open ContinuousLinearMap (posTrace re_inner_apply_nonneg)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

/-! ## A. Resolutions of the identity -/

/-- A resolution of the identity: pairwise orthogonal orthogonal projections `Pᵢ` with
`∑ᵢ Pᵢ = 1` strongly. -/
structure IsResolutionOfIdentity (P : ι → E →L[ℂ] E) : Prop where
  isStarProjection : ∀ i, IsStarProjection (P i)
  mul_eq_zero : ∀ i j, i ≠ j → P i * P j = 0
  hasSum : ∀ v, HasSum (fun i => P i v) v

namespace IsResolutionOfIdentity

variable {P : ι → E →L[ℂ] E} (hP : IsResolutionOfIdentity P)
include hP

lemma mul_self (i : ι) : P i * P i = P i := (hP.isStarProjection i).isIdempotentElem.eq

lemma star_eq (i : ι) : star (P i) = P i := (hP.isStarProjection i).isSelfAdjoint.star_eq

lemma apply_apply (i : ι) (v : E) : P i (P i v) = P i v :=
  congrArg (fun T => T v) (hP.mul_self i)

lemma apply_apply_of_ne {i j : ι} (h : i ≠ j) (v : E) : P i (P j v) = 0 :=
  congrArg (fun T => T v) (hP.mul_eq_zero i j h)

lemma inner_apply_left (i : ι) (u v : E) : ⟪P i u, v⟫_ℂ = ⟪u, P i v⟫_ℂ :=
  (hP.isStarProjection i).isSelfAdjoint.isSymmetric u v

/-- `∑ᵢ ‖Pᵢ v‖² = ‖v‖²`. -/
lemma hasSum_norm_sq (v : E) : HasSum (fun i => ‖P i v‖ ^ 2) (‖v‖ ^ 2) := by
  have h := Complex.hasSum_re ((innerSL ℂ v).hasSum (hP.hasSum v))
  have h1 : ∀ i, (⟪v, P i v⟫_ℂ).re = ‖P i v‖ ^ 2 := fun i => by
    have : ⟪v, P i v⟫_ℂ = ⟪P i v, P i v⟫_ℂ := by
      conv_lhs => rw [← hP.apply_apply i v]
      exact (hP.inner_apply_left i v (P i v)).symm
    rw [this]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  simp only [innerSL_apply_apply, h1] at h
  convert h using 1
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) v).symm

lemma norm_apply_le (i : ι) (v : E) : ‖P i v‖ ≤ ‖v‖ := by
  have h := le_hasSum (hP.hasSum_norm_sq v) i fun _ _ => sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- In a strong sum `∑ⱼ wⱼ = s` with `wⱼ` in the range of `Pⱼ`, `Pᵢ s = wᵢ`. -/
lemma apply_of_hasSum {w : ι → E} (hw : ∀ i, P i (w i) = w i) {s : E} (hs : HasSum w s)
    (i : ι) : P i s = w i := by
  classical
  have h := (P i).hasSum hs
  have h' : (fun j => P i (w j)) = fun j => if j = i then w i else 0 := by
    ext j
    split_ifs with hj
    · rw [hj, hw]
    · rw [← hw j, hP.apply_apply_of_ne (Ne.symm hj)]
  rw [h'] at h
  exact h.unique (hasSum_ite_eq i (w i))

/-- A family `wᵢ` in the ranges of the `Pᵢ` is summable iff `∑ ‖wᵢ‖² < ∞`. -/
lemma summable_of_summable_norm_sq {w : ι → E} (hw : ∀ i, P i (w i) = w i)
    (hs : Summable fun i => ‖w i‖ ^ 2) : Summable w := by
  set V : ι → Submodule ℂ E := fun i => LinearMap.range (P i : E →ₗ[ℂ] E)
  have hV : OrthogonalFamily ℂ (fun i => V i) fun i => (V i).subtypeₗᵢ := by
    rw [orthogonalFamily_iff_pairwise]
    intro i j hij
    rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    change ⟪P i a, P j b⟫_ℂ = 0
    rw [hP.inner_apply_left, hP.apply_apply_of_ne hij, inner_zero_right]
  have := (hV.summable_iff_norm_sq_summable (fun i => ⟨w i, w i, hw i⟩)).mpr hs
  exact this

/-- In a strong sum `∑ⱼ wⱼ = s` with `wⱼ` in the range of `Pⱼ`, `‖s‖² = ∑ ‖wⱼ‖²`. -/
lemma hasSum_norm_sq_of_hasSum {w : ι → E} (hw : ∀ i, P i (w i) = w i) {s : E}
    (hs : HasSum w s) : HasSum (fun i => ‖w i‖ ^ 2) (‖s‖ ^ 2) := by
  simpa only [hP.apply_of_hasSum hw hs] using hP.hasSum_norm_sq s

/-- An operator is determined by its blocks `Pᵢ A Pⱼ`. -/
theorem ext_block {A B : E →L[ℂ] E} (h : ∀ i j, P i * A * P j = P i * B * P j) : A = B := by
  ext v
  have hblock : ∀ i, P i (A v) = P i (B v) := fun i => by
    have hA := ((P i).comp A).hasSum (hP.hasSum v)
    have hB := ((P i).comp B).hasSum (hP.hasSum v)
    simp only [comp_apply] at hA hB
    have hAB : (fun j => P i (A (P j v))) = fun j => P i (B (P j v)) := by
      ext j
      exact congrArg (fun T => T v) (h i j)
    rw [hAB] at hA
    exact hA.unique hB
  exact (hP.hasSum (A v)).unique (by simpa only [hblock] using hP.hasSum (B v))

open Classical in
lemma mul_eq_ite (i j : ι) : P i * P j = if i = j then P i else 0 := by
  split_ifs with h
  · rw [h, hP.mul_self]
  · exact hP.mul_eq_zero i j h

/-- The partial sum `Q_F = ∑_{i ∈ F} Pᵢ` over a finite set of indices. -/
def _root_.QuantumMechanics.partialSum (P : ι → E →L[ℂ] E) (F : Finset ι) : E →L[ℂ] E :=
  ∑ i ∈ F, P i

omit [CompleteSpace E] hP in
lemma partialSum_apply (F : Finset ι) (v : E) : partialSum P F v = ∑ i ∈ F, P i v := by
  rw [partialSum, sum_apply]

open Classical in
lemma mul_partialSum (F : Finset ι) (i : ι) :
    P i * partialSum P F = if i ∈ F then P i else 0 := by
  rw [partialSum, Finset.mul_sum]
  simp_rw [hP.mul_eq_ite]
  rw [Finset.sum_ite_eq]

open Classical in
lemma partialSum_mul (F : Finset ι) (i : ι) :
    partialSum P F * P i = if i ∈ F then P i else 0 := by
  rw [partialSum, Finset.sum_mul]
  simp_rw [hP.mul_eq_ite]
  rw [Finset.sum_ite_eq']

lemma star_partialSum (F : Finset ι) : star (partialSum P F) = partialSum P F := by
  rw [partialSum, star_sum]
  simp_rw [hP.star_eq]

lemma norm_partialSum_le (F : Finset ι) : ‖partialSum P F‖ ≤ 1 := by
  classical
  refine opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul]
  have hs : HasSum (fun i => if i ∈ F then P i v else 0) (partialSum P F v) := by
    have h0 : HasSum (fun i => if i ∈ F then P i v else 0)
        (∑ i ∈ F, if i ∈ F then P i v else 0) :=
      hasSum_sum_of_ne_finset_zero fun i hi => by simp [hi]
    have e : ∑ i ∈ F, (if i ∈ F then P i v else 0) = partialSum P F v := by
      rw [partialSum_apply]
      exact Finset.sum_congr rfl fun i hi => by simp [hi]
    rwa [e] at h0
  have h := hP.hasSum_norm_sq_of_hasSum (fun i => by split_ifs <;> simp [hP.apply_apply]) hs
  have hle : ‖partialSum P F v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    refine hasSum_le (fun i => ?_) h (hP.hasSum_norm_sq v)
    split_ifs <;> simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hle

lemma tendsto_partialSum_apply (v : E) :
    Tendsto (fun F => partialSum P F v) atTop (𝓝 v) := by
  have h := hP.hasSum v
  rw [HasSum, SummationFilter.unconditional_filter] at h
  simpa only [partialSum_apply] using h

/-! ## B. The pinching -/

lemma summable_pinching (ρ : E →L[ℂ] E) (v : E) : Summable fun i => P i (ρ (P i v)) := by
  refine hP.summable_of_summable_norm_sq (fun i => hP.apply_apply i _) ?_
  refine ((hP.hasSum_norm_sq v).summable.mul_left (‖ρ‖ ^ 2)).of_nonneg_of_le
    (fun _ => sq_nonneg _) fun i => ?_
  rw [← mul_pow]
  gcongr
  exact (hP.norm_apply_le i _).trans (ρ.le_opNorm _)

/-- The **pinching** `P(ρ) = ∑ᵢ Pᵢ ρ Pᵢ`, a strong sum. -/
def pinching (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun v => ∑' i, P i (ρ (P i v))
      map_add' := fun u v => by
        simp only [map_add]
        exact (hP.summable_pinching ρ u).tsum_add (hP.summable_pinching ρ v)
      map_smul' := fun c v => by
        simp only [map_smul, RingHom.id_apply]
        exact (hP.summable_pinching ρ v).tsum_const_smul c }
    ‖ρ‖ fun v => by
      change ‖∑' i, P i (ρ (P i v))‖ ≤ ‖ρ‖ * ‖v‖
      have h := hP.hasSum_norm_sq_of_hasSum (fun i => hP.apply_apply i _)
        (hP.summable_pinching ρ v).hasSum
      have hle : ‖∑' i, P i (ρ (P i v))‖ ^ 2 ≤ (‖ρ‖ * ‖v‖) ^ 2 := by
        rw [mul_pow]
        refine hasSum_le (fun i => ?_) h ((hP.hasSum_norm_sq v).mul_left _)
        rw [← mul_pow]
        gcongr
        exact (hP.norm_apply_le i _).trans (ρ.le_opNorm _)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hle

lemma hasSum_pinching_apply (ρ : E →L[ℂ] E) (v : E) :
    HasSum (fun i => P i (ρ (P i v))) (hP.pinching ρ v) :=
  (hP.summable_pinching ρ v).hasSum

lemma mul_pinching (ρ : E →L[ℂ] E) (i : ι) : P i * hP.pinching ρ = P i * ρ * P i := by
  ext v
  exact hP.apply_of_hasSum (fun j => hP.apply_apply j _) (hP.hasSum_pinching_apply ρ v) i

lemma pinching_mul (ρ : E →L[ℂ] E) (i : ι) : hP.pinching ρ * P i = P i * ρ * P i := by
  classical
  ext v
  have h := hP.hasSum_pinching_apply ρ (P i v)
  have h' : (fun j => P j (ρ (P j (P i v)))) = fun j => if j = i then P i (ρ (P i v)) else 0 := by
    ext j
    split_ifs with hj
    · rw [hj, hP.apply_apply]
    · rw [hP.apply_apply_of_ne hj, map_zero, map_zero]
  rw [h'] at h
  exact h.unique (hasSum_ite_eq i _)

open Classical in
/-- The blocks of the pinching: `Pᵢ P(ρ) Pⱼ` is `Pᵢ ρ Pᵢ` for `i = j` and `0` otherwise. -/
lemma mul_pinching_mul (ρ : E →L[ℂ] E) (i j : ι) :
    P i * hP.pinching ρ * P j = if i = j then P i * ρ * P i else 0 := by
  rw [hP.mul_pinching, mul_assoc]
  split_ifs with h
  · rw [h, hP.mul_self]
  · rw [hP.mul_eq_zero i j h, mul_zero]

lemma pinching_add (ρ σ : E →L[ℂ] E) :
    hP.pinching (ρ + σ) = hP.pinching ρ + hP.pinching σ :=
  hP.ext_block fun i j => by
    simp only [mul_add, add_mul, hP.mul_pinching_mul]
    split_ifs <;> simp

lemma pinching_sub (ρ σ : E →L[ℂ] E) :
    hP.pinching (ρ - σ) = hP.pinching ρ - hP.pinching σ :=
  hP.ext_block fun i j => by
    simp only [mul_sub, sub_mul, hP.mul_pinching_mul]
    split_ifs <;> simp

lemma pinching_smul (c : ℂ) (ρ : E →L[ℂ] E) : hP.pinching (c • ρ) = c • hP.pinching ρ :=
  hP.ext_block fun i j => by
    simp only [mul_smul_comm, smul_mul_assoc, hP.mul_pinching_mul]
    split_ifs <;> simp

lemma star_pinching (ρ : E →L[ℂ] E) : star (hP.pinching ρ) = hP.pinching (star ρ) :=
  hP.ext_block fun i j => by
    have h := congrArg star (hP.mul_pinching_mul ρ j i)
    simp only [star_mul, hP.star_eq, mul_assoc] at h
    rw [mul_assoc, h, hP.mul_pinching_mul (star ρ) i j]
    by_cases hij : i = j
    · subst hij
      simp [star_mul, hP.star_eq, mul_assoc]
    · simp [hij, Ne.symm hij]

/-- The pinching is idempotent. -/
lemma pinching_pinching (ρ : E →L[ℂ] E) : hP.pinching (hP.pinching ρ) = hP.pinching ρ :=
  hP.ext_block fun i j => by
    rw [hP.mul_pinching_mul, hP.mul_pinching_mul, hP.mul_pinching_mul]
    simp

/-- `σ` is fixed by the pinching iff it commutes with every `Pᵢ`. -/
theorem pinching_eq_self_iff {σ : E →L[ℂ] E} :
    hP.pinching σ = σ ↔ ∀ i, Commute σ (P i) := by
  refine ⟨fun h i => ?_, fun h => hP.ext_block fun i j => ?_⟩
  · change σ * P i = P i * σ
    rw [← h, hP.pinching_mul, hP.mul_pinching]
  · rw [hP.mul_pinching_mul]
    split_ifs with hij
    · rw [hij]
    · rw [mul_assoc, (h j).eq, ← mul_assoc, hP.mul_eq_zero i j hij, zero_mul]

/-! ## C. Density operators -/

lemma tsum_enorm_sq (v : E) : ∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2 := by
  have h := hP.hasSum_norm_sq v
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma tsum_enorm_adjoint_sq (v : E) : ∑' i, ‖adjoint (P i) v‖ₑ ^ 2 = ‖v‖ₑ ^ 2 := by
  simp_rw [← star_eq_adjoint, hP.star_eq]
  exact hP.tsum_enorm_sq v

/-- The pinching of a positive operator is positive. -/
theorem pinching_nonneg {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) : 0 ≤ hP.pinching ρ := by
  rw [nonneg_iff_isPositive, isPositive_def']
  refine ⟨?_, fun v => ?_⟩
  · change star (hP.pinching ρ) = hP.pinching ρ
    rw [hP.star_pinching, hρ.isSelfAdjoint.star_eq]
  · rw [reApplyInnerSelf_apply, inner_re_symm]
    have h := Complex.hasSum_re ((innerSL ℂ v).hasSum (hP.hasSum_pinching_apply ρ v))
    refine h.nonneg fun i => ?_
    change 0 ≤ (⟪v, P i (ρ (P i v))⟫_ℂ).re
    rw [← hP.inner_apply_left]
    exact re_inner_apply_nonneg hρ (P i v)

/-- The pinching preserves the trace of a positive operator. -/
theorem posTrace_pinching {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) :
    posTrace (hP.pinching ρ) = posTrace ρ := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis ℂ E
  rw [posTrace_eq_tsum (hP.pinching_nonneg hρ) b, posTrace_eq_tsum_norm_sqrt_sq hρ b]
  have hterm : ∀ k, ENNReal.ofReal (⟪b k, hP.pinching ρ (b k)⟫_ℂ).re =
      ∑' i, ‖CFC.sqrt ρ (P i (b k))‖ₑ ^ 2 := fun k => by
    have h : HasSum (fun i => (⟪b k, P i (ρ (P i (b k)))⟫_ℂ).re)
        (⟪b k, hP.pinching ρ (b k)⟫_ℂ).re :=
      Complex.hasSum_re ((innerSL ℂ (b k)).hasSum (hP.hasSum_pinching_apply ρ (b k)))
    have e : ∀ i, (⟪b k, P i (ρ (P i (b k)))⟫_ℂ).re = ‖CFC.sqrt ρ (P i (b k))‖ ^ 2 := fun i => by
      rw [← hP.inner_apply_left]
      exact re_inner_apply_eq_norm_sqrt_sq hρ _
    simp only [e] at h
    rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable]
    simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  simp_rw [hterm]
  rw [ENNReal.tsum_comm]
  have h := tsum_hilbertSchmidtEnergy_comp_right (CFC.sqrt ρ) b b P hP.tsum_enorm_adjoint_sq
  simp only [hilbertSchmidtEnergy_def, comp_apply] at h
  rw [h]
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- The pinching of a density operator is a density operator. -/
theorem isDensityOperator_pinching {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (hP.pinching ρ) :=
  isDensityOperator_iff.mpr ⟨hP.pinching_nonneg hρ.nonneg,
    by rw [hP.posTrace_pinching hρ.nonneg, hρ.posTrace_eq_one]⟩

/-! ## D. Hilbert–Schmidt distance -/

omit hP in
/-- A density operator has Hilbert–Schmidt energy at most one. -/
theorem hilbertSchmidtEnergy_le_one {κ : Type*} {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (b : HilbertBasis κ ℂ E) : ρ.hilbertSchmidtEnergy b ≤ 1 := by
  have hs := CFC.sqrt_nonneg ρ
  have hss : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hn : ‖CFC.sqrt ρ‖ ≤ 1 := by
    have h := CStarRing.norm_star_mul_self (x := CFC.sqrt ρ)
    rw [hs.isSelfAdjoint.star_eq, hss] at h
    nlinarith [hρ.norm_le_one, norm_nonneg (CFC.sqrt ρ)]
  rw [← hρ.posTrace_eq_one, posTrace_eq_tsum_norm_sqrt_sq hρ.nonneg b, hilbertSchmidtEnergy_def]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
  calc ‖ρ (b k)‖ = ‖CFC.sqrt ρ (CFC.sqrt ρ (b k))‖ := by
        conv_lhs => rw [← hss]
        rfl
    _ ≤ ‖CFC.sqrt ρ‖ * ‖CFC.sqrt ρ (b k)‖ := (CFC.sqrt ρ).le_opNorm _
    _ ≤ ‖CFC.sqrt ρ (b k)‖ := mul_le_of_le_one_left (norm_nonneg _) hn

omit hP in
/-- The difference of two density operators has finite Hilbert–Schmidt energy. -/
theorem hilbertSchmidtEnergy_sub_ne_top {κ : Type*} {ρ σ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (b : HilbertBasis κ ℂ E) : (ρ - σ).hilbertSchmidtEnergy b ≠ ⊤ := by
  have h := rpow_hilbertSchmidtEnergy_add_le ρ ((-1 : ℂ) • σ) b
  have e : ρ + (-1 : ℂ) • σ = ρ - σ := by rw [neg_one_smul, ← sub_eq_add_neg]
  rw [hilbertSchmidtEnergy_smul, e] at h
  have hρ1 := hilbertSchmidtEnergy_le_one hρ b
  have hσ1 := hilbertSchmidtEnergy_le_one hσ b
  have hlt : (ρ - σ).hilbertSchmidtEnergy b ^ (1 / 2 : ℝ) < ⊤ := by
    refine h.trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_top_of_le_ne_top ENNReal.one_ne_top hρ1)
    · simp only [enorm_neg, enorm_one, one_pow, one_mul]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_top_of_le_ne_top ENNReal.one_ne_top hσ1)
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).mp hlt |>.ne

/-- **The Pythagoras identity** for the Hilbert–Schmidt energy: for `σ` commuting with every
`Pᵢ`, `‖ρ - σ‖²_HS = ‖ρ - P(ρ)‖²_HS + ‖P(ρ) - σ‖²_HS`, in `[0, ∞]`. -/
theorem hilbertSchmidtEnergy_sub {κ : Type*} (ρ : E →L[ℂ] E) {σ : E →L[ℂ] E}
    (hσ : ∀ i, Commute σ (P i)) (b : HilbertBasis κ ℂ E) :
    (ρ - σ).hilbertSchmidtEnergy b = (ρ - hP.pinching ρ).hilbertSchmidtEnergy b +
      (hP.pinching ρ - σ).hilbertSchmidtEnergy b := by
  have hsplit := fun T : E →L[ℂ] E => tsum_tsum_hilbertSchmidtEnergy_comp T b b P P
    hP.tsum_enorm_sq hP.tsum_enorm_adjoint_sq
  rw [← hsplit (ρ - σ), ← hsplit (ρ - hP.pinching ρ), ← hsplit (hP.pinching ρ - σ),
    ← ENNReal.tsum_add]
  refine tsum_congr fun j => ?_
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun i => ?_
  have hσb := hP.mul_pinching_mul σ i j
  rw [hP.pinching_eq_self_iff.mpr hσ] at hσb
  simp only [← mul_def, ← mul_assoc, mul_sub, sub_mul, hP.mul_pinching_mul, hσb]
  by_cases hij : i = j
  · subst hij
    simp [hilbertSchmidtEnergy_zero]
  · simp [hij, hilbertSchmidtEnergy_zero]

/-- **The pinching is the unique closest commuting operator**: for a density operator `σ ≠ P(ρ)`
commuting with every `Pᵢ`, `‖ρ - P(ρ)‖_HS < ‖ρ - σ‖_HS`. -/
theorem hilbertSchmidtNorm_sub_pinching_lt {ρ σ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (hc : ∀ i, Commute σ (P i)) (hne : σ ≠ hP.pinching ρ) :
    (ρ - hP.pinching ρ).hilbertSchmidtNorm < (ρ - σ).hilbertSchmidtNorm := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis ℂ E
  have hPρ := hP.isDensityOperator_pinching hρ
  have h := hP.hilbertSchmidtEnergy_sub ρ hc b
  have h1 := hilbertSchmidtEnergy_sub_ne_top hρ hPρ b
  have h2 := hilbertSchmidtEnergy_sub_ne_top hPρ hσ b
  have hpos : (hP.pinching ρ - σ).hilbertSchmidtEnergy b ≠ 0 := by
    intro h0
    rw [hilbertSchmidtEnergy_def, ENNReal.tsum_eq_zero] at h0
    refine hne (sub_eq_zero.mp ?_).symm
    ext v
    have hk : ∀ k, (hP.pinching ρ - σ) (b k) = 0 := fun k => by simpa using h0 k
    have h3 := (hP.pinching ρ - σ).hasSum (b.hasSum_repr v)
    simp only [map_smul, hk, smul_zero] at h3
    exact h3.unique hasSum_zero
  rw [hilbertSchmidtNorm_eq_sqrt _ b, hilbertSchmidtNorm_eq_sqrt _ b, h]
  refine Real.sqrt_lt_sqrt ENNReal.toReal_nonneg ?_
  rw [ENNReal.toReal_add h1 h2]
  have : 0 < ((hP.pinching ρ - σ).hilbertSchmidtEnergy b).toReal :=
    ENNReal.toReal_pos hpos h2
  linarith

end IsResolutionOfIdentity

/-! ## E. Observables with pure point spectrum -/

/-- `X = ∑ᵢ xᵢ Pᵢ`: a bounded observable with pure point spectrum, with distinct real eigenvalues
`xᵢ` and eigenprojections `Pᵢ` forming a resolution of the identity. -/
structure IsEigenDecomposition (X : E →L[ℂ] E) (P : ι → E →L[ℂ] E) (x : ι → ℝ) : Prop where
  isResolutionOfIdentity : IsResolutionOfIdentity P
  injective : Function.Injective x
  mul_eq : ∀ i, X * P i = (x i : ℂ) • P i

namespace IsEigenDecomposition

variable {X : E →L[ℂ] E} {P : ι → E →L[ℂ] E} {x : ι → ℝ} (hX : IsEigenDecomposition X P x)
include hX

/-- `X v = ∑ᵢ xᵢ Pᵢ v`. -/
lemma hasSum_apply (v : E) : HasSum (fun i => (x i : ℂ) • P i v) (X v) := by
  have h := X.hasSum (hX.isResolutionOfIdentity.hasSum v)
  have e : ∀ i, X (P i v) = (x i : ℂ) • P i v := fun i => congrArg (fun T => T v) (hX.mul_eq i)
  simpa only [e] using h

lemma mul_eq' (i : ι) : P i * X = (x i : ℂ) • P i := by
  ext v
  have hP := hX.isResolutionOfIdentity
  exact hP.apply_of_hasSum (fun j => by rw [map_smul, hP.apply_apply]) (hX.hasSum_apply v) i

lemma isSelfAdjoint : IsSelfAdjoint X := by
  have hP := hX.isResolutionOfIdentity
  refine hP.ext_block fun i j => ?_
  have h0 : P j * X * P i = (x i : ℂ) • (P j * P i) := by
    rw [mul_assoc, hX.mul_eq, mul_smul_comm]
  have h1 : P i * star X * P j = (x i : ℂ) • (P i * P j) := by
    have h := congrArg star h0
    rwa [star_mul, star_mul, hP.star_eq, hP.star_eq, star_smul, star_mul, hP.star_eq, hP.star_eq,
      Complex.star_def, Complex.conj_ofReal, ← mul_assoc] at h
  rw [h1, mul_assoc, hX.mul_eq, mul_smul_comm]
  by_cases hij : i = j
  · rw [hij]
  · rw [hP.mul_eq_zero i j hij, smul_zero, smul_zero]

/-- An operator commutes with `X` iff it commutes with every eigenprojection. -/
theorem commute_iff {σ : E →L[ℂ] E} : Commute σ X ↔ ∀ i, Commute σ (P i) := by
  have hP := hX.isResolutionOfIdentity
  refine ⟨fun h => hP.pinching_eq_self_iff.mp (hP.ext_block fun i j => ?_), fun h => ?_⟩
  · rw [hP.mul_pinching_mul]
    split_ifs with hij
    · rw [hij]
    · have h1 : (x i : ℂ) • (P i * σ * P j) = (x j : ℂ) • (P i * σ * P j) := by
        calc (x i : ℂ) • (P i * σ * P j) = P i * X * σ * P j := by
              rw [hX.mul_eq', smul_mul_assoc, smul_mul_assoc]
          _ = P i * σ * X * P j := by rw [mul_assoc (P i) X, ← h.eq, ← mul_assoc]
          _ = (x j : ℂ) • (P i * σ * P j) := by rw [mul_assoc _ X, hX.mul_eq, mul_smul_comm]
      have hne : (x i : ℂ) - x j ≠ 0 :=
        sub_ne_zero.mpr (by exact_mod_cast hX.injective.ne hij)
      have h2 : ((x i : ℂ) - x j) • (P i * σ * P j) = 0 := by rw [sub_smul, h1, sub_self]
      exact ((smul_eq_zero.mp h2).resolve_left hne).symm
  · change σ * X = X * σ
    ext v
    have h1 := σ.hasSum (hX.hasSum_apply v)
    have h2 := hX.hasSum_apply (σ v)
    simp only [map_smul] at h1
    have e : ∀ i, P i (σ v) = σ (P i v) := fun i => (congrArg (fun T => T v) (h i).eq).symm
    simp only [e] at h2
    exact h1.unique h2

end IsEigenDecomposition

end QuantumMechanics
