/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DiscreteObservable

/-!
# Outcome probabilities and the Lüders rule

## i. Overview

Let `{Pᵢ}` be a resolution of the identity on a Hilbert space `E` of any dimension: the
eigenprojections of an observable with pure point spectrum. For a density operator `ρ` the
probability of the outcome `i` is `pᵢ = tr(Pᵢ ρ Pᵢ)` (the Born rule, here in `[0, ∞]`), and the
state after the outcome `i` is the Lüders state `ρᵢ = Pᵢ ρ Pᵢ / pᵢ`.

The probabilities sum to `tr ρ = 1`, and the pinching `P(ρ) = ∑ᵢ Pᵢ ρ Pᵢ` does not change them.
The Lüders state `ρᵢ` is a density operator fixed by the pinching, and gives the outcome `i` with
certainty: the measurement is *repeatable*. The pinching is the classical mixture
`P(ρ) = ∑ᵢ pᵢ ρᵢ`, and updating it on the outcome `i` gives `ρᵢ`, the same state as updating `ρ`.

More generally, let `σ = ∑ᵢ wᵢ σᵢ` be a mixture of density operators `σᵢ` that give the outcome
`i` with certainty. Then the outcome `i` has probability `wᵢ`, and the Lüders state of `σ` for
the outcome `i` is `σᵢ`. This is classical conditioning: learning which component of a mixture
occurred selects that component.

## ii. Key results

- `QuantumMechanics.outcomeProb`, `QuantumMechanics.luders`.
- `QuantumMechanics.IsResolutionOfIdentity.tsum_outcomeProb`: the probabilities sum to `tr ρ`.
- `QuantumMechanics.IsResolutionOfIdentity.outcomeProb_pinching`: the pinching keeps them.
- `QuantumMechanics.IsResolutionOfIdentity.isDensityOperator_luders`,
  `QuantumMechanics.IsResolutionOfIdentity.pinching_luders`: the Lüders state is a density
  operator fixed by the pinching.
- `QuantumMechanics.IsResolutionOfIdentity.outcomeProb_luders`: repeatability.
- `QuantumMechanics.IsResolutionOfIdentity.luders_pinching`: updating `P(ρ)` is updating `ρ`.
- `QuantumMechanics.IsResolutionOfIdentity.hasSum_pinching_apply_luders`: `P(ρ) = ∑ᵢ pᵢ ρᵢ`.
- `QuantumMechanics.IsResolutionOfIdentity.outcomeProb_of_hasSum`,
  `QuantumMechanics.IsResolutionOfIdentity.luders_of_hasSum`: updating a mixture selects the
  component.

## iii. Table of contents

- A. Outcome probabilities
- B. The Lüders rule
- C. Mixtures

## iv. References

- G. Lüders, *Über die Zustandsänderung durch den Meßprozeß*, Ann. Phys. **8** (1951) 322–328.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open ContinuousLinearMap (posTrace posTrace_eq_tsum posTrace_smul posTrace_eq_zero_iff
  re_inner_apply_nonneg)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

/-- The probability `tr(Pᵢ ρ Pᵢ) ∈ [0, ∞]` of the outcome `i` (the Born rule). -/
def outcomeProb (P : ι → E →L[ℂ] E) (ρ : E →L[ℂ] E) (i : ι) : ℝ≥0∞ :=
  posTrace (P i * ρ * P i)

/-- The Lüders state `Pᵢ ρ Pᵢ / tr(Pᵢ ρ Pᵢ)` after the outcome `i`. -/
def luders (P : ι → E →L[ℂ] E) (ρ : E →L[ℂ] E) (i : ι) : E →L[ℂ] E :=
  (((outcomeProb P ρ i).toReal⁻¹ : ℝ) : ℂ) • (P i * ρ * P i)

namespace IsResolutionOfIdentity

variable {P : ι → E →L[ℂ] E} (hP : IsResolutionOfIdentity P)
include hP

/-! ## A. Outcome probabilities -/

lemma mul_mul_nonneg {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) (i : ι) : 0 ≤ P i * ρ * P i := by
  simpa [hP.star_eq] using star_left_conjugate_nonneg hρ (P i)

/-- The outcome probabilities of a positive `ρ` sum to `tr ρ`. -/
theorem tsum_outcomeProb {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) : ∑' i, outcomeProb P ρ i = posTrace ρ := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis ℂ E
  rw [← hP.posTrace_pinching hρ, posTrace_eq_tsum (hP.pinching_nonneg hρ) b]
  simp_rw [outcomeProb, posTrace_eq_tsum (hP.mul_mul_nonneg hρ _) b]
  rw [tsum_comm]
  refine tsum_congr fun k => ?_
  have h : HasSum (fun i => (⟪b k, P i (ρ (P i (b k)))⟫_ℂ).re)
      (⟪b k, hP.pinching ρ (b k)⟫_ℂ).re :=
    Complex.hasSum_re ((innerSL ℂ (b k)).hasSum (hP.hasSum_pinching_apply ρ (b k)))
  rw [← h.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => ?_) h.summable]
  · rfl
  · rw [← hP.inner_apply_left]
    exact re_inner_apply_nonneg hρ _

/-- The outcome probabilities of a density operator sum to one. -/
theorem tsum_outcomeProb_eq_one {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    ∑' i, outcomeProb P ρ i = 1 := by
  rw [hP.tsum_outcomeProb hρ.nonneg, hρ.posTrace_eq_one]

lemma outcomeProb_ne_top {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (i : ι) :
    outcomeProb P ρ i ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    ((le_tsum _ i).trans (hP.tsum_outcomeProb_eq_one hρ).le)

lemma outcomeProb_eq_zero_iff {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) (i : ι) :
    outcomeProb P ρ i = 0 ↔ P i * ρ * P i = 0 :=
  posTrace_eq_zero_iff (hP.mul_mul_nonneg hρ i)

/-- The pinching does not change the outcome probabilities. -/
theorem outcomeProb_pinching (ρ : E →L[ℂ] E) (i : ι) :
    outcomeProb P (hP.pinching ρ) i = outcomeProb P ρ i := by
  classical
  simp only [outcomeProb, hP.mul_pinching_mul, ↓reduceIte]

/-! ## B. The Lüders rule -/

/-- `pᵢ ρᵢ = Pᵢ ρ Pᵢ`. -/
lemma smul_luders {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (i : ι) :
    (((outcomeProb P ρ i).toReal : ℝ) : ℂ) • luders P ρ i = P i * ρ * P i := by
  by_cases h : outcomeProb P ρ i = 0
  · rw [luders, h, (hP.outcomeProb_eq_zero_iff hρ.nonneg i).mp h]
    simp
  · have h' : (outcomeProb P ρ i).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨h, hP.outcomeProb_ne_top hρ i⟩
    rw [luders, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ h', Complex.ofReal_one,
      one_smul]

/-- The Lüders state is a density operator. -/
theorem isDensityOperator_luders {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) {i : ι}
    (hi : outcomeProb P ρ i ≠ 0) : IsDensityOperator (luders P ρ i) := by
  have hpos : 0 < (outcomeProb P ρ i).toReal :=
    ENNReal.toReal_pos hi (hP.outcomeProb_ne_top hρ i)
  refine isDensityOperator_iff.mpr ⟨?_, ?_⟩
  · rw [luders, ContinuousLinearMap.nonneg_iff_isPositive]
    exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (hP.mul_mul_nonneg hρ.nonneg i))
      |>.smul_of_nonneg (by exact_mod_cast (inv_pos.mpr hpos).le)
  · rw [luders, posTrace_smul (inv_pos.mpr hpos).le, ← outcomeProb,
      ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_toReal (hP.outcomeProb_ne_top hρ i),
      ENNReal.inv_mul_cancel hi (hP.outcomeProb_ne_top hρ i)]

open Classical in
lemma mul_luders (ρ : E →L[ℂ] E) (i j : ι) :
    P j * luders P ρ i = if j = i then luders P ρ i else 0 := by
  rw [luders, mul_smul_comm, ← mul_assoc, ← mul_assoc, hP.mul_eq_ite]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

open Classical in
lemma luders_mul (ρ : E →L[ℂ] E) (i j : ι) :
    luders P ρ i * P j = if j = i then luders P ρ i else 0 := by
  rw [luders, smul_mul_assoc, mul_assoc, hP.mul_eq_ite]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- The Lüders state lies in the block of its outcome. -/
lemma mul_luders_mul (ρ : E →L[ℂ] E) (i : ι) : P i * luders P ρ i * P i = luders P ρ i := by
  classical
  simp only [hP.mul_luders, hP.luders_mul, ↓reduceIte]

/-- The Lüders state commutes with every `Pⱼ`. -/
lemma commute_luders (ρ : E →L[ℂ] E) (i j : ι) : Commute (luders P ρ i) (P j) := by
  change _ * _ = _ * _
  rw [hP.mul_luders, hP.luders_mul]

/-- The Lüders state is fixed by the pinching: it is an equilibrium. -/
theorem pinching_luders (ρ : E →L[ℂ] E) (i : ι) : hP.pinching (luders P ρ i) = luders P ρ i :=
  hP.pinching_eq_self_iff.mpr (hP.commute_luders ρ i)

open Classical in
/-- **Repeatability**: after the outcome `i`, a second measurement gives `i` with certainty. -/
theorem outcomeProb_luders {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) {i : ι}
    (hi : outcomeProb P ρ i ≠ 0) (j : ι) :
    outcomeProb P (luders P ρ i) j = if j = i then 1 else 0 := by
  classical
  rw [outcomeProb, hP.mul_luders, ite_mul, zero_mul, hP.luders_mul]
  split_ifs
  · exact (hP.isDensityOperator_luders hρ hi).posTrace_eq_one
  · exact ContinuousLinearMap.posTrace_zero

/-- Updating the pinched state is updating the state. -/
theorem luders_pinching (ρ : E →L[ℂ] E) (i : ι) :
    luders P (hP.pinching ρ) i = luders P ρ i := by
  classical
  simp only [luders, hP.outcomeProb_pinching, hP.mul_pinching_mul, ↓reduceIte]

/-! ## C. Mixtures -/

/-- The pinching is the classical mixture `P(ρ) = ∑ᵢ pᵢ ρᵢ` of the Lüders states. -/
theorem hasSum_pinching_apply_luders {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (v : E) :
    HasSum (fun i => (((outcomeProb P ρ i).toReal : ℝ) : ℂ) • luders P ρ i v)
      (hP.pinching ρ v) := by
  convert hP.hasSum_pinching_apply ρ v using 2 with i
  rw [← smul_apply, hP.smul_luders hρ]
  rfl

/-- If `σ` gives the outcome `i` with certainty, then `Pⱼ σ = 0` for `j ≠ i`. -/
lemma mul_eq_zero_of_mul_mul_eq {σ : E →L[ℂ] E} {i j : ι} (hσ : P i * σ * P i = σ)
    (hij : j ≠ i) : P j * σ = 0 := by
  rw [← hσ, ← mul_assoc, ← mul_assoc, hP.mul_eq_zero j i hij, zero_mul, zero_mul]

/-- The block `Pᵢ σ Pᵢ` of a mixture `σ = ∑ⱼ wⱼ σⱼ` of operators `σⱼ = Pⱼ σⱼ Pⱼ` is `wᵢ σᵢ`. -/
lemma mul_mul_eq_of_hasSum {w : ι → ℝ} {σ' : ι → E →L[ℂ] E}
    (hσ' : ∀ j, P j * σ' j * P j = σ' j) {σ : E →L[ℂ] E}
    (hσ : ∀ v, HasSum (fun j => ((w j : ℝ) : ℂ) • σ' j v) (σ v)) (i : ι) :
    P i * σ * P i = ((w i : ℝ) : ℂ) • σ' i := by
  classical
  ext v
  have h := (P i).hasSum (hσ (P i v))
  have h' : (fun j => P i (((w j : ℝ) : ℂ) • σ' j (P i v))) =
      fun j => if j = i then ((w i : ℝ) : ℂ) • σ' i v else 0 := by
    ext j
    split_ifs with hj
    · subst hj
      rw [map_smul]
      congr 1
      exact congrArg (· v) (hσ' j)
    · rw [map_smul, ← mul_apply_eq_comp,
        hP.mul_eq_zero_of_mul_mul_eq (hσ' j) (Ne.symm hj)]
      simp
  rw [h'] at h
  exact h.unique (hasSum_ite_eq i _)

/-- In a mixture `σ = ∑ⱼ wⱼ σⱼ` of operators `σⱼ` that give the outcome `j` with certainty, the
outcome `i` has probability `wᵢ` if `σᵢ` is a density operator. -/
theorem outcomeProb_of_hasSum {w : ι → ℝ} {σ' : ι → E →L[ℂ] E}
    (hσ' : ∀ j, P j * σ' j * P j = σ' j) {σ : E →L[ℂ] E}
    (hσ : ∀ v, HasSum (fun j => ((w j : ℝ) : ℂ) • σ' j v) (σ v)) {i : ι} (hw : 0 ≤ w i)
    (hd : IsDensityOperator (σ' i)) : outcomeProb P σ i = ENNReal.ofReal (w i) := by
  rw [outcomeProb, hP.mul_mul_eq_of_hasSum hσ' hσ i, posTrace_smul hw, hd.posTrace_eq_one,
    mul_one]

/-- **Classical conditioning**: in a mixture `σ = ∑ⱼ wⱼ σⱼ` of operators `σⱼ` that give the
outcome `j` with certainty, the Lüders state for an outcome `i` with `wᵢ > 0` and `σᵢ` a density
operator is `σᵢ`. -/
theorem luders_of_hasSum {w : ι → ℝ} {σ' : ι → E →L[ℂ] E}
    (hσ' : ∀ j, P j * σ' j * P j = σ' j) {σ : E →L[ℂ] E}
    (hσ : ∀ v, HasSum (fun j => ((w j : ℝ) : ℂ) • σ' j v) (σ v)) {i : ι} (hw : 0 ≤ w i)
    (hd : IsDensityOperator (σ' i)) (hi : w i ≠ 0) : luders P σ i = σ' i := by
  rw [luders, hP.outcomeProb_of_hasSum hσ' hσ hw hd, ENNReal.toReal_ofReal hw,
    hP.mul_mul_eq_of_hasSum hσ' hσ i, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hi,
    Complex.ofReal_one, one_smul]

end IsResolutionOfIdentity

end QuantumMechanics
