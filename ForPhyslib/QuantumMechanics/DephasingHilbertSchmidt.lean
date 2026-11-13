/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DephasingFlow
public import ForPhyslib.QuantumMechanics.NoncommutativeScheffe
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Equilibration of the dephasing equation through the Hilbert–Schmidt norm

## i. Overview

Let `X = ∑ᵢ xᵢ Pᵢ` have pure point spectrum, and let `r` solve the dephasing equation
`ρ' = X ρ X - ½ {X², ρ}` for `t > 0`, continuous from the right at `0`, with `r(0)` a density
operator. `DephasingFlow` proves `r(t) → P(r(0))` in trace norm through the Gaussian average and
its trace-norm contraction. This file gives a second proof, the one of the brief.

The blocks of `r(t) - P(r(0))` are `0` on the diagonal and `e^{-t(xᵢ - xⱼ)²/2} Pᵢ r(0) Pⱼ` off it,
so its Hilbert–Schmidt energy is `∑_{i ≠ j} e^{-t(xᵢ - xⱼ)²} ‖Pᵢ r(0) Pⱼ‖²_HS`. Each term tends to
zero and is dominated by `‖Pᵢ r(0) Pⱼ‖²_HS`, whose sum `‖r(0)‖²_HS ≤ 1` is finite; by dominated
convergence (Tannery's theorem) `‖r(t) - P(r(0))‖_HS → 0`. Every `r(t)` is a density operator:
the Gaussian average of a positive operator is positive, and the pinching, which preserves the
trace, does not see the off-diagonal blocks. The non-commutative Scheffé lemma then gives
convergence in trace norm.

## ii. Key results

- `QuantumMechanics.IsEigenDecomposition.isDensityOperator_gaussianDephasing`,
  `QuantumMechanics.IsEigenDecomposition.isDensityOperator_of_hasDerivAt`: solutions stay density
  operators.
- `QuantumMechanics.IsEigenDecomposition.hilbertSchmidtEnergy_sub_pinching_of_hasDerivAt`: the
  energy of `r(t) - P(r(0))`, eqs. (6)–(8) of the brief.
- `QuantumMechanics.IsEigenDecomposition.tendsto_hilbertSchmidtNorm_of_hasDerivAt`: convergence
  in Hilbert–Schmidt norm, eq. (9).
- `QuantumMechanics.IsEigenDecomposition.tendsto_traceENorm_of_hasDerivAt'`: convergence in trace
  norm through the non-commutative Scheffé lemma, eq. (10).

## iii. Table of contents

- A. Solutions stay density operators
- B. Convergence in Hilbert–Schmidt norm
- C. Convergence in trace norm
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder NNReal
open Filter Topology Set ContinuousLinearMap MeasureTheory ProbabilityTheory

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*} {X : E →L[ℂ] E} {P : ι → E →L[ℂ] E} {x : ι → ℝ}

namespace IsEigenDecomposition

variable (hX : IsEigenDecomposition X P x)
include hX

/-! ## A. Solutions stay density operators -/

/-- The Gaussian average of a positive operator is positive. -/
theorem gaussianDephasing_nonneg (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) :
    0 ≤ gaussianDephasing X v ρ := by
  have hρp := (isPositive_iff_complex ρ).mp (nonneg_iff_isPositive.mp hρ)
  rw [nonneg_iff_isPositive, isPositive_iff_complex]
  intro y
  set z : ℝ → E := fun s => star (phaseGroup X s) y
  set g : ℝ → ℝ := fun s => RCLike.re ⟪ρ (z s), z s⟫_ℂ
  have hpt : ∀ s, ⟪y, (phaseGroup X s * ρ * star (phaseGroup X s)) y⟫_ℂ = (g s : ℂ) := fun s => by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← adjoint_inner_left, ← star_eq_adjoint,
      ← inner_conj_symm, ← (hρp (z s)).1]
    simp [g, z]
  set L : (E →L[ℂ] E) →L[ℂ] ℂ := (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ E y)
  have hint : ⟪y, gaussianDephasing X v ρ y⟫_ℂ = ((∫ s, g s ∂(gaussianReal 0 v) : ℝ) : ℂ) := by
    have h := L.integral_comp_comm (hX.integrable_conj_phaseGroup v ρ)
    change L (gaussianDephasing X v ρ) = _
    rw [gaussianDephasing, ← h]
    simp only [L, comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply, hpt]
    exact integral_ofReal
  have hg0 : 0 ≤ ∫ s, g s ∂(gaussianReal 0 v) := integral_nonneg fun s => (hρp (z s)).2
  have h' : ⟪gaussianDephasing X v ρ y, y⟫_ℂ = ((∫ s, g s ∂(gaussianReal 0 v) : ℝ) : ℂ) := by
    rw [← inner_conj_symm, hint, Complex.conj_ofReal]
  rw [h']
  simp [hg0]

/-- The Gaussian average of a density operator is a density operator. -/
theorem isDensityOperator_gaussianDephasing (v : ℝ≥0) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) : IsDensityOperator (gaussianDephasing X v ρ) := by
  have hP := hX.isResolutionOfIdentity
  have h0 := hX.gaussianDephasing_nonneg v hρ.nonneg
  have hpin : hP.pinching (gaussianDephasing X v ρ) = hP.pinching ρ := hP.ext_block fun i j => by
    rw [hP.mul_pinching_mul, hP.mul_pinching_mul]
    split_ifs with h
    · subst h
      rw [hX.mul_gaussianDephasing_mul]
      simp
    · rfl
  refine isDensityOperator_iff.mpr ⟨h0, ?_⟩
  rw [← hP.posTrace_pinching h0, hpin, hP.posTrace_pinching hρ.nonneg, hρ.posTrace_eq_one]

/-- A solution of the dephasing equation starting at a density operator stays one. -/
theorem isDensityOperator_of_hasDerivAt {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) (hρ : IsDensityOperator (r 0)) {t : ℝ} (ht : 0 ≤ t) :
    IsDensityOperator (r t) := by
  rw [hX.eq_gaussianDephasing hd hc ht]
  exact hX.isDensityOperator_gaussianDephasing _ hρ

/-! ## B. Convergence in Hilbert–Schmidt norm -/

open Classical in
/-- The blocks of `r(t) - P(r(0))`: zero on the diagonal, `e^{-t(xᵢ - xⱼ)²/2} Pᵢ r(0) Pⱼ` off
it. -/
lemma mul_sub_pinching_mul_of_hasDerivAt {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) (i j : ι) :
    P i * (r t - hX.isResolutionOfIdentity.pinching (r 0)) * P j =
      ((if i = j then 0 else Real.exp (-(t * ((x i - x j) ^ 2 / 2))) : ℝ) : ℂ) •
        (P i * r 0 * P j) := by
  rw [mul_sub, sub_mul, hX.mul_eq_of_hasDerivAt hd hc i j ht,
    hX.isResolutionOfIdentity.mul_pinching_mul]
  split_ifs with h
  · subst h
    simp
  · rw [sub_zero]
    exact (Complex.coe_smul _ _).symm

/-- The Hilbert–Schmidt energy splits over the blocks `Pᵢ T Pⱼ`, indexed by `(j, i)`. -/
lemma tsum_hilbertSchmidtEnergy_mul_mul {κ : Type*} (b : HilbertBasis κ ℂ E) (T : E →L[ℂ] E) :
    ∑' p : ι × ι, (P p.2 * T * P p.1).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  have hP := hX.isResolutionOfIdentity
  have h := tsum_tsum_hilbertSchmidtEnergy_comp T b b P P hP.tsum_enorm_sq
    hP.tsum_enorm_adjoint_sq
  simp only [← mul_def, ← mul_assoc] at h
  exact (tsum_prod (f := fun j i : ι => (P i * T * P j).hilbertSchmidtEnergy b)).trans h

open Classical in
/-- **Eqs. (6)–(8)**: `‖r(t) - P(r(0))‖²_HS = ∑_{i ≠ j} e^{-t(xᵢ - xⱼ)²} ‖Pᵢ r(0) Pⱼ‖²_HS`, with
`e^{-t(xᵢ - xⱼ)²}` written as the square of `e^{-t(xᵢ - xⱼ)²/2}`. -/
theorem hilbertSchmidtEnergy_sub_pinching_of_hasDerivAt {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) {κ : Type*}
    (b : HilbertBasis κ ℂ E) :
    (r t - hX.isResolutionOfIdentity.pinching (r 0)).hilbertSchmidtEnergy b =
      ∑' p : ι × ι, ENNReal.ofReal
        ((if p.2 = p.1 then 0 else Real.exp (-(t * ((x p.2 - x p.1) ^ 2 / 2)))) ^ 2) *
        (P p.2 * r 0 * P p.1).hilbertSchmidtEnergy b := by
  rw [← hX.tsum_hilbertSchmidtEnergy_mul_mul b]
  refine tsum_congr fun p => ?_
  rw [hX.mul_sub_pinching_mul_of_hasDerivAt hd hc ht, hilbertSchmidtEnergy_smul, ← ofReal_norm,
    Complex.norm_real, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

open Classical in
/-- **Eq. (9)**: `‖r(t) - P(r(0))‖_HS → 0`, by dominated convergence over the blocks. -/
theorem tendsto_hilbertSchmidtNorm_of_hasDerivAt {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) (hρ : IsDensityOperator (r 0)) :
    Tendsto (fun t => (r t - hX.isResolutionOfIdentity.pinching (r 0)).hilbertSchmidtNorm)
      atTop (𝓝 0) := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis ℂ E
  set e : ι × ι → ℝ≥0∞ := fun p => (P p.2 * r 0 * P p.1).hilbertSchmidtEnergy b
  set w : ℝ → ι × ι → ℝ := fun t p =>
    if p.2 = p.1 then 0 else Real.exp (-(t * ((x p.2 - x p.1) ^ 2 / 2)))
  have hetop : ∑' p, e p ≠ ⊤ := by
    rw [hX.tsum_hilbertSchmidtEnergy_mul_mul b]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (IsResolutionOfIdentity.hilbertSchmidtEnergy_le_one hρ b)
  have hep : ∀ p, e p ≠ ⊤ := fun p => ne_top_of_le_ne_top hetop (le_tsum _ p)
  set a : ι × ι → ℝ := fun p => (e p).toReal
  have ha : Summable a := ENNReal.summable_toReal hetop
  have hw0 : ∀ t p, 0 ≤ w t p := fun t p => by
    simp only [w]
    split_ifs <;> positivity
  have hw1 : ∀ t, 0 ≤ t → ∀ p, w t p ≤ 1 := fun t ht p => by
    simp only [w]
    split_ifs
    · exact zero_le_one
    · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (by positivity)))
  have hle : ∀ t, 0 ≤ t → ∀ p, w t p ^ 2 * a p ≤ a p := fun t ht p =>
    mul_le_of_le_one_left ENNReal.toReal_nonneg (pow_le_one₀ (hw0 t p) (hw1 t ht p))
  have hsum : ∀ t, 0 ≤ t → Summable fun p => w t p ^ 2 * a p := fun t ht =>
    ha.of_nonneg_of_le (fun p => by positivity) (hle t ht)
  have henergy : ∀ t, 0 ≤ t → (r t - hX.isResolutionOfIdentity.pinching (r 0)).hilbertSchmidtNorm =
      √(∑' p, w t p ^ 2 * a p) := fun t ht => by
    rw [hilbertSchmidtNorm_eq_sqrt _ b, hX.hilbertSchmidtEnergy_sub_pinching_of_hasDerivAt hd hc ht,
      ← ENNReal.toReal_ofReal (tsum_nonneg fun p => by positivity),
      ENNReal.ofReal_tsum_of_nonneg (fun p => by positivity) (hsum t ht)]
    congr 2
    refine tsum_congr fun p => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (hep p)]
  have hS : Tendsto (fun t => ∑' p, w t p ^ 2 * a p) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := fun t p => w t p ^ 2 * a p)
      (g := fun _ => 0) ha (fun p => ?_) ?_
    · simpa using h
    · by_cases h : p.2 = p.1
      · simp [w, h]
      · have hc0 : 0 < (x p.2 - x p.1) ^ 2 / 2 := by
          have : x p.2 - x p.1 ≠ 0 := sub_ne_zero.mpr (hX.injective.ne h)
          positivity
        have hlim : Tendsto (fun t => Real.exp (-(t * ((x p.2 - x p.1) ^ 2 / 2)))) atTop (𝓝 0) :=
          Real.tendsto_exp_atBot.comp
            (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hc0))
        simpa [w, h] using (hlim.pow 2).mul_const (a p)
    · filter_upwards [eventually_ge_atTop 0] with t ht p
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle t ht p
  have h0 := (Real.continuous_sqrt.tendsto 0).comp hS
  rw [Real.sqrt_zero] at h0
  exact h0.congr' ((eventually_ge_atTop 0).mono fun t ht => (henergy t ht).symm)

/-! ## C. Convergence in trace norm -/

/-- **Eq. (10)**: `r(t) → P(r(0))` in trace norm, from the Hilbert–Schmidt convergence and the
non-commutative Scheffé lemma. A second proof of `tendsto_traceENorm_of_hasDerivAt`. -/
theorem tendsto_traceENorm_of_hasDerivAt' {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) (hρ : IsDensityOperator (r 0)) :
    Tendsto (fun t => traceENorm (r t - hX.isResolutionOfIdentity.pinching (r 0))) atTop
      (𝓝 0) := by
  have hP := hX.isResolutionOfIdentity
  set ρ' : ℝ → E →L[ℂ] E := fun t => if 0 ≤ t then r t else hP.pinching (r 0)
  have hρ' : ∀ t, IsDensityOperator (ρ' t) := fun t => by
    simp only [ρ']
    split_ifs with ht
    · exact hX.isDensityOperator_of_hasDerivAt hd hc hρ ht
    · exact hP.isDensityOperator_pinching hρ
  have hev : ∀ᶠ t in atTop, ρ' t = r t :=
    (eventually_ge_atTop 0).mono fun t ht => by simp only [ρ', ht, ↓reduceIte]
  have hHS : Tendsto (fun t => (ρ' t - hP.pinching (r 0)).hilbertSchmidtNorm) atTop (𝓝 0) :=
    (hX.tendsto_hilbertSchmidtNorm_of_hasDerivAt hd hc hρ).congr'
      (hev.mono fun t ht => by beta_reduce; rw [ht])
  exact (tendsto_traceENorm_of_tendsto_hilbertSchmidtNorm hρ' (hP.isDensityOperator_pinching hρ)
    hHS).congr' (hev.mono fun t ht => by beta_reduce; rw [ht])

end IsEigenDecomposition

end QuantumMechanics
