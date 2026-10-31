/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DiscreteObservable
public import ForPhyslib.QuantumMechanics.Dephasing
public import ForPhyslib.QuantumMechanics.TraceNorm
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The dephasing flow in any dimension

## i. Overview

Let `X = ∑ᵢ xᵢ Pᵢ` be a bounded observable with pure point spectrum on a Hilbert space of any
dimension (`IsEigenDecomposition`). The dephasing Lindblad equation
`ρ' = L(ρ) = X ρ X - ½ (X² ρ + ρ X²)` has a bounded generator on `E →L[ℂ] E`, and acts on the
blocks `Pᵢ ρ Pⱼ` by the factor `-½ (xᵢ - xⱼ)²`. So every solution `r` for `t > 0`, continuous
from the right at `0` in operator norm, has the blocks
`Pᵢ r(t) Pⱼ = e^{-t (xᵢ - xⱼ)² / 2} Pᵢ r(0) Pⱼ`, and `e^{tL} ρ` is one.

The same blocks belong to the Gaussian average `G_t(ρ) = ∫ e^{isX} ρ e^{-isX} dN(0, t)(s)`, by the
characteristic function of the Gaussian. Hence `r(t) = G_t(r(0))`. As an average of unitary
conjugations, `G_t` contracts the trace norm. With a finite truncation `Q ρ Q`, `Q = ∑_{i ∈ F} Pᵢ`,
this gives **equilibration in trace norm**: `‖r(t) - P(r(0))‖₁ → 0` for every density operator
`r(0)`, where `P` is the pinching. The off-diagonal blocks of the truncation decay exponentially,
and the truncation error is uniform in `t`.

## ii. Key results

- `QuantumMechanics.dephasingCLM`, `QuantumMechanics.dephasingFlow`: the bounded generator and
  `e^{tL}`, with `hasDerivAt_dephasingFlow`.
- `QuantumMechanics.IsEigenDecomposition.mul_eq_of_hasDerivAt`: the blocks of a solution.
- `QuantumMechanics.gaussianDephasing`: the Gaussian average, with its blocks
  (`IsEigenDecomposition.mul_gaussianDephasing_mul`) and the trace-norm contraction
  (`IsEigenDecomposition.traceENorm_gaussianDephasing_sub_le`).
- `QuantumMechanics.IsEigenDecomposition.eq_gaussianDephasing`: every solution is the Gaussian
  average of its initial value.
- `QuantumMechanics.IsEigenDecomposition.tendsto_traceENorm_of_hasDerivAt`: equilibration in trace
  norm.

## iii. Table of contents

- A. The generator and the flow
- B. The unitary group `e^{isX}`
- C. The Gaussian average
- D. Equilibration in trace norm

## iv. References

- G. Lindblad, *On the generators of quantum dynamical semigroups*, Commun. Math. Phys. **48**
  (1976), 119–130.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder NNReal Nat
open Filter Topology Set ContinuousLinearMap MeasureTheory ProbabilityTheory
  ProbabilisticTheory ProbabilisticTheory.TraceClass Complex

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

/-! ## A. The generator and the flow -/

/-- The dephasing generator `L(ρ) = X ρ X - ½ (X² ρ + ρ X²)` as a bounded operator on
`E →L[ℂ] E`. -/
def dephasingCLM (X : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
  (mul ℂ (E →L[ℂ] E) X).comp ((mul ℂ (E →L[ℂ] E)).flip X) -
    ((2⁻¹ : ℝ) : ℂ) • (mul ℂ (E →L[ℂ] E) (X * X) + (mul ℂ (E →L[ℂ] E)).flip (X * X))

lemma dephasingCLM_apply (X ρ : E →L[ℂ] E) : dephasingCLM X ρ = dephasingGenerator X ρ := by
  rw [dephasingGenerator_apply, dephasingCLM, sub_apply, smul_apply, add_apply, comp_apply,
    mul_apply', mul_apply', flip_apply, flip_apply, mul_apply', mul_apply', Complex.coe_smul]
  simp only [mul_assoc]

/-- The flow `e^{tL} ρ` of the dephasing equation. -/
def dephasingFlow (X : E →L[ℂ] E) (t : ℝ) (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  NormedSpace.exp ((t : ℂ) • dephasingCLM X) ρ

lemma dephasingFlow_zero (X ρ : E →L[ℂ] E) : dephasingFlow X 0 ρ = ρ := by
  have h : ((0 : ℝ) : ℂ) • dephasingCLM X = 0 := by
    ext A : 1
    simp
  rw [dephasingFlow, h, NormedSpace.exp_zero]
  rfl

/-- The flow solves the dephasing equation. -/
theorem hasDerivAt_dephasingFlow (X ρ : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s => dephasingFlow X s ρ) (dephasingGenerator X (dephasingFlow X t ρ)) t := by
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℂ) (dephasingCLM X) (t : ℂ)
  have h : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • dephasingCLM X))
      (dephasingCLM X * NormedSpace.exp ((t : ℂ) • dephasingCLM X)) t := by
    have := h1.scomp t ofRealCLM.hasDerivAt
    simpa only [ofRealCLM_apply, ofReal_one, one_smul, Function.comp_def] using this
  have h2 :=
    ((ContinuousLinearMap.apply ℂ (E →L[ℂ] E) ρ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h
  rw [← dephasingCLM_apply]
  exact h2

variable {X : E →L[ℂ] E} {P : ι → E →L[ℂ] E} {x : ι → ℝ}

namespace IsEigenDecomposition

variable (hX : IsEigenDecomposition X P x)
include hX

/-- The generator acts blockwise: `Pᵢ L(A) Pⱼ = -½ (xᵢ - xⱼ)² Pᵢ A Pⱼ`. -/
lemma mul_dephasingGenerator_mul (i j : ι) (A : E →L[ℂ] E) :
    P i * dephasingGenerator X A * P j = (-((x i - x j) ^ 2 / 2)) • (P i * A * P j) := by
  have hl : ∀ B : E →L[ℂ] E, P i * (X * B) = x i • (P i * B) := fun B => by
    rw [← mul_assoc, hX.mul_eq', Complex.coe_smul, smul_mul_assoc]
  have hr : X * P j = x j • P j := by rw [hX.mul_eq, Complex.coe_smul]
  rw [dephasingGenerator_apply]
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, hl, hr,
    smul_smul]
  module

/-- **The blocks of a solution.** A solution of the dephasing equation for `t > 0`, continuous
from the right at `0`, has `Pᵢ r(t) Pⱼ = e^{-t (xᵢ - xⱼ)² / 2} Pᵢ r(0) Pⱼ` for `t ≥ 0`. -/
theorem mul_eq_of_hasDerivAt {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) (i j : ι) {t : ℝ} (ht : 0 ≤ t) :
    P i * r t * P j = Real.exp (-(t * ((x i - x j) ^ 2 / 2))) • (P i * r 0 * P j) := by
  set c := (x i - x j) ^ 2 / 2
  let f : ℝ → E →L[ℂ] E := fun s => P i * r s * P j
  let g : ℝ → E →L[ℂ] E := fun s => Real.exp (s * c) • f s
  have hg : ∀ s, 0 < s → HasDerivAt g 0 s := fun s hs => by
    have hf : HasDerivAt f (P i * dephasingGenerator X (r s) * P j) s :=
      ((hd s hs).const_mul _).mul_const _
    rw [hX.mul_dephasingGenerator_mul] at hf
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
  simp

end IsEigenDecomposition

/-! ## B. The unitary group `e^{isX}` -/

section Exp

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- If `A B = a B`, then `e^A B = e^a B`. -/
lemma exp_mul_of_mul_eq {A B : 𝔸} {a : ℂ} (h : A * B = a • B) :
    NormedSpace.exp A * B = Complex.exp a • B := by
  have hpow : ∀ n : ℕ, A ^ n * B = a ^ n • B := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, h, mul_smul_comm, ih, smul_smul, pow_succ, mul_comm]
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) A,
    ← (NormedSpace.expSeries_summable' (𝕂 := ℂ) A).tsum_mul_right B]
  simp_rw [smul_mul_assoc, hpow, smul_smul]
  have hs : Summable fun n : ℕ => ((n ! : ℂ)⁻¹ * a ^ n) := by
    simpa only [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℂ) a
  rw [hs.tsum_smul_const, Complex.exp_eq_exp_ℂ, congrFun (NormedSpace.exp_eq_tsum ℂ) a]
  simp only [smul_eq_mul]

/-- If `B A = a B`, then `B e^A = e^a B`. -/
lemma mul_exp_of_mul_eq {A B : 𝔸} {a : ℂ} (h : B * A = a • B) :
    B * NormedSpace.exp A = Complex.exp a • B := by
  have hpow : ∀ n : ℕ, B * A ^ n = a ^ n • B := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, smul_mul_assoc, h, smul_smul, pow_succ]
  rw [congrFun (NormedSpace.exp_eq_tsum ℂ) A,
    ← (NormedSpace.expSeries_summable' (𝕂 := ℂ) A).tsum_mul_left B]
  simp_rw [mul_smul_comm, hpow, smul_smul]
  have hs : Summable fun n : ℕ => ((n ! : ℂ)⁻¹ * a ^ n) := by
    simpa only [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℂ) a
  rw [hs.tsum_smul_const, Complex.exp_eq_exp_ℂ, congrFun (NormedSpace.exp_eq_tsum ℂ) a]
  simp only [smul_eq_mul]

end Exp

/-- The unitary group `e^{isX}`. -/
def phaseGroup (X : E →L[ℂ] E) (s : ℝ) : E →L[ℂ] E := NormedSpace.exp (((s : ℂ) * I) • X)

lemma continuous_phaseGroup (X : E →L[ℂ] E) : Continuous (phaseGroup X) :=
  (continuous_iff_continuousAt.mpr fun A => (NormedSpace.exp_analytic (𝕂 := ℂ) A).continuousAt).comp
    (((continuous_ofReal.mul continuous_const)).smul continuous_const)

namespace IsEigenDecomposition

variable (hX : IsEigenDecomposition X P x)
include hX

lemma phaseGroup_mul (s : ℝ) (i : ι) :
    phaseGroup X s * P i = Complex.exp (s * I * x i) • P i :=
  exp_mul_of_mul_eq (by rw [smul_mul_assoc, hX.mul_eq, smul_smul])

lemma mul_phaseGroup (s : ℝ) (i : ι) :
    P i * phaseGroup X s = Complex.exp (s * I * x i) • P i :=
  mul_exp_of_mul_eq (by rw [mul_smul_comm, hX.mul_eq', smul_smul])

lemma phaseGroup_mem_unitary (s : ℝ) : phaseGroup X s ∈ unitary (E →L[ℂ] E) := by
  let _ : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.mem_iff.mpr ?_)
  rw [star_smul, hX.isSelfAdjoint.star_eq, ← neg_smul]
  congr 1
  simp

lemma norm_phaseGroup_le (s : ℝ) : ‖phaseGroup X s‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v => by
    rw [norm_map_of_mem_unitary (hX.phaseGroup_mem_unitary s), one_mul]

lemma star_phaseGroup_mul (s : ℝ) (j : ι) :
    star (phaseGroup X s) * P j = Complex.exp (-(s * I * x j)) • P j := by
  have h := congrArg star (hX.mul_phaseGroup s j)
  rw [star_mul, hX.isResolutionOfIdentity.star_eq, star_smul,
    hX.isResolutionOfIdentity.star_eq] at h
  rw [h, Complex.star_def, ← Complex.exp_conj]
  congr 2
  simp

/-- The blocks of a conjugation by `e^{isX}`. -/
lemma mul_conj_phaseGroup_mul (s : ℝ) (i j : ι) (A : E →L[ℂ] E) :
    P i * (phaseGroup X s * A * star (phaseGroup X s)) * P j =
      Complex.exp ((x i - x j : ℝ) * s * I) • (P i * A * P j) := by
  rw [show P i * (phaseGroup X s * A * star (phaseGroup X s)) * P j =
      (P i * phaseGroup X s) * A * (star (phaseGroup X s) * P j) by simp only [mul_assoc],
    hX.mul_phaseGroup, hX.star_phaseGroup_mul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

end IsEigenDecomposition

/-! ## C. The Gaussian average -/

/-- The Gaussian average `G_v(ρ) = ∫ e^{isX} ρ e^{-isX} dN(0, v)(s)`. -/
def gaussianDephasing (X : E →L[ℂ] E) (v : ℝ≥0) (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  ∫ s, phaseGroup X s * ρ * star (phaseGroup X s) ∂(gaussianReal 0 v)

namespace IsEigenDecomposition

variable (hX : IsEigenDecomposition X P x)
include hX

omit hX in
lemma continuous_conj_phaseGroup (A : E →L[ℂ] E) :
    Continuous fun s => phaseGroup X s * A * star (phaseGroup X s) :=
  ((continuous_phaseGroup X).mul continuous_const).mul (continuous_phaseGroup X).star

lemma norm_conj_phaseGroup_le (s : ℝ) (A : E →L[ℂ] E) :
    ‖phaseGroup X s * A * star (phaseGroup X s)‖ ≤ ‖A‖ := by
  have h1 := hX.norm_phaseGroup_le s
  have h2 : ‖star (phaseGroup X s)‖ ≤ 1 := by rw [norm_star]; exact h1
  calc ‖phaseGroup X s * A * star (phaseGroup X s)‖
      ≤ ‖phaseGroup X s‖ * ‖A‖ * ‖star (phaseGroup X s)‖ := norm_mul₃_le
    _ ≤ 1 * ‖A‖ * 1 := by gcongr
    _ = ‖A‖ := by ring

lemma integrable_conj_phaseGroup (v : ℝ≥0) (A : E →L[ℂ] E) :
    Integrable (fun s => phaseGroup X s * A * star (phaseGroup X s)) (gaussianReal 0 v) :=
  (integrable_const ‖A‖).mono' (continuous_conj_phaseGroup A).aestronglyMeasurable
    (ae_of_all _ fun s => hX.norm_conj_phaseGroup_le s A)

/-- **The blocks of the Gaussian average**: `Pᵢ G_v(ρ) Pⱼ = e^{-v (xᵢ - xⱼ)² / 2} Pᵢ ρ Pⱼ`, the
characteristic function of `N(0, v)` at `xᵢ - xⱼ`. -/
theorem mul_gaussianDephasing_mul (v : ℝ≥0) (ρ : E →L[ℂ] E) (i j : ι) :
    P i * gaussianDephasing X v ρ * P j =
      Real.exp (-(v * ((x i - x j) ^ 2 / 2))) • (P i * ρ * P j) := by
  set M : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
    (mul ℂ (E →L[ℂ] E) (P i)).comp ((mul ℂ (E →L[ℂ] E)).flip (P j))
  have hM : ∀ A, M A = P i * A * P j := fun A => by
    simp only [M, comp_apply, flip_apply, mul_apply', mul_assoc]
  rw [← hM, gaussianDephasing, ← M.integral_comp_comm (hX.integrable_conj_phaseGroup v ρ)]
  simp_rw [hM, hX.mul_conj_phaseGroup_mul]
  rw [integral_smul_const, ← charFun_apply_real, charFun_gaussianReal]
  have h : Complex.exp ((x i - x j : ℝ) * (0 : ℝ) * I - (v : ℝ) * ((x i - x j : ℝ) : ℂ) ^ 2 / 2) =
      ((Real.exp (-(v * ((x i - x j) ^ 2 / 2))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h, Complex.coe_smul]

/-- **The Gaussian average contracts the trace norm** on differences of positive trace-class
operators: it is an average of unitary conjugations, computed in `𝒮₁`. -/
theorem traceENorm_gaussianDephasing_sub_le (v : ℝ≥0) {ρ σ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ)
    (hρ : IsTraceClass ρ) (hσ0 : 0 ≤ σ) (hσ : IsTraceClass σ) :
    traceENorm (gaussianDephasing X v ρ - gaussianDephasing X v σ) ≤ traceENorm (ρ - σ) := by
  have hU1 := hX.norm_phaseGroup_le
  have hUc : ∀ y, Continuous fun s => phaseGroup X s y := fun y =>
    (continuous_phaseGroup X).clm_apply continuous_const
  have hρσ : IsTraceClass (ρ - σ) := by
    rw [sub_eq_add_neg]
    exact isTraceClass_add hρ (isTraceClass_neg hσ)
  have hbound : ∀ (T : E →L[ℂ] E) (hT : IsTraceClass T) (s : ℝ),
      ‖ofOperator (phaseGroup X s * T * star (phaseGroup X s)) (isTraceClass_mul_mul hT)‖ ≤
        traceNorm T hT := fun T hT s => by
    rw [norm_eq_traceNorm]
    have h2 : ‖star (phaseGroup X s)‖ ≤ 1 := by rw [norm_star]; exact hU1 s
    calc _ ≤ ‖phaseGroup X s‖ * traceNorm T hT * ‖star (phaseGroup X s)‖ :=
          traceNorm_mul_mul_le hT _
      _ ≤ 1 * traceNorm T hT * 1 := by
          have h0 := traceNorm_nonneg T hT
          exact mul_le_mul (mul_le_mul_of_nonneg_right (hU1 s) h0) h2 (norm_nonneg _)
            (by positivity)
      _ = traceNorm T hT := by ring
  set f : ℝ → TraceClass E := fun s =>
    ofOperator (phaseGroup X s * ρ * star (phaseGroup X s)) (isTraceClass_mul_mul hρ)
  set g : ℝ → TraceClass E := fun s =>
    ofOperator (phaseGroup X s * σ * star (phaseGroup X s)) (isTraceClass_mul_mul hσ)
  have hfi : Integrable f (gaussianReal 0 v) :=
    (integrable_const (traceNorm ρ hρ)).mono' (continuous_conj hU1 hUc hρ0 hρ).aestronglyMeasurable
      (ae_of_all _ (hbound ρ hρ))
  have hgi : Integrable g (gaussianReal 0 v) :=
    (integrable_const (traceNorm σ hσ)).mono' (continuous_conj hU1 hUc hσ0 hσ).aestronglyMeasurable
      (ae_of_all _ (hbound σ hσ))
  have hF : (∫ s, f s ∂(gaussianReal 0 v)).1 = gaussianDephasing X v ρ := by
    rw [← toOperator_apply, ← toOperator.integral_comp_comm hfi]
    rfl
  have hG : (∫ s, g s ∂(gaussianReal 0 v)).1 = gaussianDephasing X v σ := by
    rw [← toOperator_apply, ← toOperator.integral_comp_comm hgi]
    rfl
  have hfg : ∀ s, f s - g s =
      ofOperator (phaseGroup X s * (ρ - σ) * star (phaseGroup X s)) (isTraceClass_mul_mul hρσ) :=
    fun s => Subtype.ext (by
      change (f s).1 - (g s).1 = _
      simp [f, g, mul_sub, sub_mul])
  rw [← hF, ← hG]
  change traceENorm ((∫ s, f s ∂(gaussianReal 0 v)) - ∫ s, g s ∂(gaussianReal 0 v)).1 ≤ _
  rw [← integral_sub hfi hgi, traceENorm_eq_ofReal (isTraceClass_coe _), ← norm_eq_traceNorm,
    traceENorm_eq_ofReal hρσ]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v)
    (f := fun s => f s - g s) (C := traceNorm (ρ - σ) hρσ)
    (ae_of_all _ fun s => by rw [hfg]; exact hbound _ hρσ s)
  simpa using h

/-- **Every solution is the Gaussian average of its initial value**:
`r(t) = ∫ e^{isX} r(0) e^{-isX} dN(0, t)(s)` for `t ≥ 0`. -/
theorem eq_gaussianDephasing {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) :
    r t = gaussianDephasing X t.toNNReal (r 0) :=
  hX.isResolutionOfIdentity.ext_block fun i j => by
    rw [hX.mul_eq_of_hasDerivAt hd hc i j ht, hX.mul_gaussianDephasing_mul, Real.coe_toNNReal _ ht]

end IsEigenDecomposition

/-! ## D. Equilibration in trace norm -/

lemma traceENorm_sum_le {κ : Type*} (s : Finset κ) (f : κ → E →L[ℂ] E) :
    traceENorm (∑ p ∈ s, f p) ≤ ∑ p ∈ s, traceENorm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (traceENorm_add_le _ _).trans (by gcongr)

namespace IsResolutionOfIdentity

variable (hP : IsResolutionOfIdentity P)
include hP

lemma norm_le_one (i : ι) : ‖P i‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v => by rw [one_mul]; exact hP.norm_apply_le i v

open Classical in
/-- The blocks of the truncation `Q A Q`, `Q = ∑_{i ∈ F} Pᵢ`. -/
lemma mul_partialSum_mul_mul (F : Finset ι) (A : E →L[ℂ] E) (k l : ι) :
    P k * (partialSum P F * A * partialSum P F) * P l =
      if k ∈ F ∧ l ∈ F then P k * A * P l else 0 := by
  rw [show P k * (partialSum P F * A * partialSum P F) * P l =
      (P k * partialSum P F) * A * (partialSum P F * P l) by simp only [mul_assoc],
    hP.mul_partialSum, hP.partialSum_mul]
  by_cases hk : k ∈ F <;> by_cases hl : l ∈ F <;> simp [hk, hl]

open Classical in
/-- The blocks of a finite combination of blocks. -/
lemma mul_sum_smul_mul (F : Finset ι) (a : ι × ι → ℝ) (A : E →L[ℂ] E) (k l : ι) :
    P k * (∑ p ∈ F ×ˢ F, a p • (P p.1 * A * P p.2)) * P l =
      if k ∈ F ∧ l ∈ F then a (k, l) • (P k * A * P l) else 0 := by
  rw [Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ p : ι × ι, P k * (a p • (P p.1 * A * P p.2)) * P l =
      if (k, l) = p then a (k, l) • (P k * A * P l) else 0 := fun p => by
    rw [mul_smul_comm, smul_mul_assoc, show P k * (P p.1 * A * P p.2) * P l =
      (P k * P p.1) * A * (P p.2 * P l) by simp only [mul_assoc], hP.mul_eq_ite, hP.mul_eq_ite]
    obtain ⟨p1, p2⟩ := p
    rcases eq_or_ne k p1 with rfl | h1 <;> rcases eq_or_ne l p2 with rfl | h2
    · simp
    · simp [h2, h2.symm]
    · simp [h1]
    · simp [h1, h2, h2.symm]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_product]

end IsResolutionOfIdentity

namespace IsEigenDecomposition

variable (hX : IsEigenDecomposition X P x)
include hX

/-- **Equilibration in trace norm.** Every solution of the dephasing equation for `t > 0`,
continuous from the right at `0`, whose initial value `ρ` is a density operator tends to the
pinching `∑ᵢ Pᵢ ρ Pᵢ` in trace norm. -/
theorem tendsto_traceENorm_of_hasDerivAt {r : ℝ → E →L[ℂ] E}
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) (hρ : IsDensityOperator (r 0)) :
    Tendsto (fun t => traceENorm (r t - hX.isResolutionOfIdentity.pinching (r 0))) atTop
      (𝓝 0) := by
  classical
  have hP := hX.isResolutionOfIdentity
  set ρ := r 0
  have hPρ := hP.isDensityOperator_pinching hρ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal (3 * η) ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · refine ⟨ε.toReal / 3, by have := ENNReal.toReal_pos hε.ne' hne; positivity, ?_⟩
      rw [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), ENNReal.ofReal_toReal hne]
  have hη := ENNReal.ofReal_pos.mpr hη0
  -- a finite truncation `Q ρ Q` close to `ρ`, with `Q P(ρ) Q` close to `P(ρ)`
  have h1 := tendsto_traceENorm_conj (U := partialSum P) (U₀ := 1) hP.norm_partialSum_le
    norm_id_le hP.tendsto_partialSum_apply hρ
  have h2 := tendsto_traceENorm_conj (U := partialSum P) (U₀ := 1) hP.norm_partialSum_le
    norm_id_le hP.tendsto_partialSum_apply hPρ
  simp only [hP.star_partialSum, star_one, one_mul, mul_one] at h1 h2
  obtain ⟨F, hF1, hF2⟩ :=
    ((h1.eventually (gt_mem_nhds hη)).and (h2.eventually (gt_mem_nhds hη))).exists
  set Q := partialSum P F
  set σ := Q * ρ * Q
  have hσ0 : 0 ≤ σ := by
    have h := star_right_conjugate_nonneg hρ.nonneg Q
    rwa [hP.star_partialSum] at h
  have hσtc : IsTraceClass σ := isTraceClass_mul_mul hρ.isTraceClass
  -- the off-diagonal blocks of the truncation decay
  set a : ℝ → ι × ι → ℝ := fun t p =>
    Real.exp (-(t * ((x p.1 - x p.2) ^ 2 / 2))) - if p.1 = p.2 then 1 else 0
  have ha : ∀ p : ι × ι, Tendsto (fun t => ENNReal.ofReal |a t p|) atTop (𝓝 0) := fun p => by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    by_cases h : p.1 = p.2
    · simp [a, h]
    · have hc0 : 0 < (x p.1 - x p.2) ^ 2 / 2 := by
        have : x p.1 - x p.2 ≠ 0 := sub_ne_zero.mpr (hX.injective.ne h)
        positivity
      have hlim : Tendsto (fun t => Real.exp (-(t * ((x p.1 - x p.2) ^ 2 / 2)))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hc0))
      simpa [a, h] using hlim.abs
  have hsum := tendsto_finsetSum (F ×ˢ F) fun p _ => ha p
  simp only [Finset.sum_const_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds hη), eventually_ge_atTop 0] with t ht ht0
  have hrt : r t = gaussianDephasing X t.toNNReal ρ := hX.eq_gaussianDephasing hd hc ht0
  have hfin : gaussianDephasing X t.toNNReal σ - hP.pinching σ =
      ∑ p ∈ F ×ˢ F, a t p • (P p.1 * ρ * P p.2) :=
    hP.ext_block fun k l => by
      rw [mul_sub, sub_mul, hX.mul_gaussianDephasing_mul, hP.mul_pinching_mul,
        hP.mul_sum_smul_mul, Real.coe_toNNReal _ ht0]
      simp only [σ, Q, hP.mul_partialSum_mul_mul]
      by_cases hkl : k = l
      · subst hkl
        by_cases hk : k ∈ F <;> simp [hk, a]
      · by_cases hk : k ∈ F <;> by_cases hl : l ∈ F <;> simp [hk, hl, hkl, a]
  have hpin : hP.pinching σ = Q * hP.pinching ρ * Q :=
    hP.ext_block fun k l => by
      rw [hP.mul_pinching_mul]
      simp only [σ, Q, hP.mul_partialSum_mul_mul, hP.mul_pinching_mul]
      by_cases hkl : k = l
      · subst hkl
        by_cases hk : k ∈ F <;> simp [hk]
      · simp [hkl]
  have hsplit : r t - hP.pinching ρ =
      (gaussianDephasing X t.toNNReal ρ - gaussianDephasing X t.toNNReal σ) +
        (gaussianDephasing X t.toNNReal σ - hP.pinching σ) +
        (Q * hP.pinching ρ * Q - hP.pinching ρ) := by
    rw [hrt, hpin]
    abel
  have hterm : ∀ p ∈ F ×ˢ F, traceENorm (a t p • (P p.1 * ρ * P p.2)) ≤
      ENNReal.ofReal |a t p| := fun p _ => by
    rw [← Complex.coe_smul, traceENorm_smul _ (isTraceClass_mul_mul hρ.isTraceClass),
      ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_of_le_one_right zero_le ?_
    refine (traceENorm_mul_mul_le _ _ hρ.isTraceClass).trans ?_
    rw [hρ.traceENorm_eq_one, mul_one]
    have hn : ∀ i, ‖P i‖ₑ ≤ 1 := fun i => by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (hP.norm_le_one i)
    exact mul_le_one' (hn _) (hn _)
  calc traceENorm (r t - hP.pinching ρ)
      ≤ traceENorm (gaussianDephasing X t.toNNReal ρ - gaussianDephasing X t.toNNReal σ) +
          traceENorm (gaussianDephasing X t.toNNReal σ - hP.pinching σ) +
          traceENorm (Q * hP.pinching ρ * Q - hP.pinching ρ) := by
        rw [hsplit]
        exact (traceENorm_add_le _ _).trans (by gcongr; exact traceENorm_add_le _ _)
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η := by
        gcongr
        · refine (hX.traceENorm_gaussianDephasing_sub_le _ hρ.nonneg hρ.isTraceClass hσ0
            hσtc).trans ?_
          rw [traceENorm_sub_comm]
          exact hF1.le
        · rw [hfin]
          exact ((traceENorm_sum_le _ _).trans (Finset.sum_le_sum hterm)).trans ht.le
    _ = ENNReal.ofReal (3 * η) := by
        rw [← ENNReal.ofReal_add hη0.le hη0.le, ← ENNReal.ofReal_add (by positivity) hη0.le]
        ring_nf
    _ ≤ ε := hηε

end IsEigenDecomposition

end QuantumMechanics
