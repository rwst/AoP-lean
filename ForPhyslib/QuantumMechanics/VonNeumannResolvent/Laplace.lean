/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import ForPhyslib.QuantumMechanics.TraceNorm
public import ForPhyslib.QuantumMechanics.VonNeumannResolvent
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Pairing
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The resolvent of the von Neumann equation in any dimension

## i. Overview

Let `V t = exp (-i t K)` be a norm-continuous unitary group on a complex Hilbert space of any
dimension, with bounded self-adjoint generator `K`, unitary channel `T t ρ = V t ρ V t†` and von
Neumann generator `L ρ = -i (K ρ - ρ K)`. For every real `τ` the Laplace integral

  `Ψ τ = ∫₀^∞ e^{-s} T (τ s) ds`

converges in operator norm on `E →L[ℂ] E`, and it is the two-sided inverse of `1 - τ L`: the
integrand of `(1 - τ L) Ψ τ ρ` is `-(d/ds) (e^{-s} T (τ s) ρ)`, and `L` commutes with `T`. So
`Ψ τ` is the resolvent of the finite-dimensional file `VonNeumannResolvent`, now without any
dimension hypothesis. As a mixture of unitary channels, `Ψ τ` is completely positive, and it
maps density operators to density operators: the integral also converges in the trace class, where
the trace is continuous.

The resolvent is a projective measurement adapted to its output. Let `σ = Ψ τ ρ` for a density
operator `ρ`; it is a positive trace-class operator, so it has a Hilbert basis `(bᵢ)` of
eigenvectors, `σ bᵢ = μᵢ bᵢ`. Since `ρ = σ - τ L σ` and `⟪bᵢ, L σ bᵢ⟫ = 0`, the rank-one
projectors `Pᵢ = |bᵢ⟩⟨bᵢ|` satisfy `Pᵢ ρ Pᵢ = ⟪bᵢ, ρ bᵢ⟫ Pᵢ = μᵢ Pᵢ`, and summing gives
`Ψ τ ρ = ∑ᵢ Pᵢ ρ Pᵢ`. The finite-dimensional file groups equal eigenvalues into spectral
projectors; rank-one projectors onto an eigenbasis serve equally well and need no spectral theory
beyond the eigenbasis of a compact operator.

The second-order estimates are as in finite dimension, now in the trace norm. For a pure state
`|ψ⟩⟨ψ|` the largest eigenvalue `x` of `σ = Ψ τ |ψ⟩⟨ψ|` has `1 - x ≤ 8 ‖K‖² τ²`, its eigenvector
`φ` has `‖|φ⟩⟨φ| - T τ |ψ⟩⟨ψ|‖₁ ≤ 64 ‖K‖² τ²` (a Davis–Kahan bound), and `σ - x |φ⟩⟨φ|` is
positive with trace `1 - x`. Together `‖Ψ τ |ψ⟩⟨ψ| - T τ |ψ⟩⟨ψ|‖₁ ≤ 80 ‖K‖² τ²`, and the canonical
expansion extends this to every density operator. Telescoping, with `T` a trace-norm isometry,
gives the resolvent exponential formula `(Ψ (t / n))ⁿ ρ → T t ρ` in the trace norm.

We set `ħ = 1`; the general case is `K = H / ħ`.

## ii. Key results

- `QuantumMechanics.laplaceResolvent`: `Ψ τ = ∫₀^∞ e^{-s} T (τ s) ds`.
- `QuantumMechanics.laplaceResolvent_sub`, `laplaceResolvent_vonNeumannStep`: `Ψ τ` inverts
  `1 - τ L` on both sides.
- `QuantumMechanics.isDensityOperator_laplaceResolvent`: `Ψ τ` preserves density operators.
- `QuantumMechanics.laplaceResolventCP`: `Ψ τ` is completely positive.
- `QuantumMechanics.vonNeumannResolvent_eq_laplaceResolvent`: in finite dimension `(1 - τ L)⁻¹` is
  the Laplace integral.
- `QuantumMechanics.exists_hilbertBasis_laplaceResolvent`: `Ψ τ ρ = ∑ᵢ Pᵢ ρ Pᵢ` for the
  projectors onto an eigenbasis of `Ψ τ ρ`, with `Pᵢ ρ Pᵢ = μᵢ Pᵢ`.
- `QuantumMechanics.exists_max_laplaceResolvent_proj`: the largest outcome on a pure state.
- `QuantumMechanics.traceENorm_laplaceResolvent_sub_unitaryChannel_le`: the second-order estimate
  `‖Ψ τ ρ - T τ ρ‖₁ ≤ 80 ‖K‖² τ²` on density operators.
- `QuantumMechanics.traceENorm_laplaceResolvent_iterate_sub_le`: the exponential formula with
  error `80 ‖K‖² t² / n`.
- `QuantumMechanics.traceENorm_inv_smul_laplaceResolvent_sub_le`: `(Ψ τ ρ - ρ) / τ → L ρ`.

## iii. Table of contents

- A. The unitary channel on operators
- B. The Laplace resolvent
- C. Density operators and complete positivity
- D. The resolvent is a projective measurement
- E. Second-order estimates in operator norm
- F. The largest outcome on a pure state
- G. Second-order estimate in trace norm
- H. The exponential formula and the generator

## iv. References

- K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Springer
  (2000), Thm II.1.10 (the Laplace representation of the resolvent).
- R. Bhatia, *Matrix Analysis*, Springer (1997), Section VII.3 (Davis–Kahan).
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder Topology ENNReal CStarAlgebra
open InnerProductSpace QuantumMechanics.Wigner Complex Set Filter MeasureTheory
  ProbabilisticTheory ProbabilisticTheory.TraceClass
open ContinuousLinearMap (re_inner_apply_nonneg posTrace)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (V : UnitaryOneParameterGroup E)

/-! ## A. The unitary channel on operators -/

/-- The unitary channel `T t` as a bounded operator on `E →L[ℂ] E`. -/
def unitaryChannelL (t : ℝ) : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
  ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) (V t) (star (V t))

lemma unitaryChannelL_apply (t : ℝ) (ρ : E →L[ℂ] E) :
    unitaryChannelL V t ρ = unitaryChannel V t ρ := rfl

lemma continuous_unitaryChannelL : Continuous (unitaryChannelL V) := by
  have h1 : Continuous fun t => V t := V.continuous
  show Continuous fun t => ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) (V t) (star (V t))
  exact ((ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E)).continuous.comp h1).clm_apply
    (continuous_star.comp h1)

lemma norm_unitaryOneParameterGroup_le (t : ℝ) : ‖V t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [ContinuousLinearMap.norm_map_of_mem_unitary (V.mem_unitary t), one_mul]

lemma norm_unitaryChannelL_le (t : ℝ) : ‖unitaryChannelL V t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ρ => by
    rw [unitaryChannelL_apply, norm_unitaryChannel, one_mul]

/-- The unitary channel commutes with the von Neumann generator. -/
lemma unitaryChannel_vonNeumannGenerator (t : ℝ) (ρ : E →L[ℂ] E) :
    unitaryChannel V t (vonNeumannGenerator V.generator ρ) =
      vonNeumannGenerator V.generator (unitaryChannel V t ρ) := by
  have hc : V.generator * V t = V t * V.generator := (V.commute_generator t).eq
  have hc' : V.generator * star (V t) = star (V t) * V.generator := by
    have h := congrArg star hc
    rw [star_mul, star_mul, V.generator_isSelfAdjoint.star_eq] at h
    exact h.symm
  simp only [unitaryChannel, vonNeumannGenerator_apply, mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, sub_mul, show V.generator * (V t * ρ * star (V t)) =
      V.generator * V t * ρ * star (V t) by simp only [mul_assoc], hc,
    show V t * ρ * star (V t) * V.generator = V t * ρ * (star (V t) * V.generator) by
      simp only [mul_assoc], ← hc']
  simp only [mul_assoc]

lemma isDensityOperator_unitaryChannel (t : ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (unitaryChannel V t ρ) :=
  hρ.conj (Unitary.mem_iff.mp (V.mem_unitary t)).1

/-- The unitary channel does not increase the trace norm. -/
lemma traceENorm_unitaryChannel_le (t : ℝ) (X : E →L[ℂ] E) :
    traceENorm (unitaryChannel V t X) ≤ traceENorm X := by
  by_cases h : IsTraceClass X
  · refine (traceENorm_mul_mul_le _ _ h).trans ?_
    have h1 : ‖V t‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (norm_unitaryOneParameterGroup_le V t)
    have h2 : ‖star (V t)‖ₑ ≤ 1 := by rwa [← ofReal_norm, norm_star, ofReal_norm]
    calc ‖V t‖ₑ * traceENorm X * ‖star (V t)‖ₑ ≤ 1 * traceENorm X * 1 := by gcongr
      _ = traceENorm X := by rw [one_mul, mul_one]
  · simp [traceENorm_eq_top h]

/-! ## B. The Laplace resolvent -/

/-- The integrand `s ↦ e^{-s} T (τ s)` of the Laplace resolvent. -/
def laplaceKernel (τ s : ℝ) : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
  Real.exp (-s) • unitaryChannelL V (τ * s)

lemma continuous_laplaceKernel (τ : ℝ) : Continuous (laplaceKernel V τ) :=
  (Real.continuous_exp.comp continuous_neg).smul
    ((continuous_unitaryChannelL V).comp (continuous_const.mul continuous_id))

lemma norm_laplaceKernel_le (τ s : ℝ) : ‖laplaceKernel V τ s‖ ≤ Real.exp (-s) := by
  rw [laplaceKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (norm_unitaryChannelL_le V _)

lemma integrableOn_laplaceKernel (τ : ℝ) : IntegrableOn (laplaceKernel V τ) (Ioi 0) :=
  (integrableOn_exp_neg_Ioi 0).mono' (continuous_laplaceKernel V τ).aestronglyMeasurable
    (Eventually.of_forall fun s => norm_laplaceKernel_le V τ s)

/-- **The resolvent** `Ψ τ = ∫₀^∞ e^{-s} T (τ s) ds` of the von Neumann generator. -/
def laplaceResolvent (τ : ℝ) : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
  ∫ s in Ioi (0 : ℝ), laplaceKernel V τ s

lemma integrableOn_laplaceKernel_apply (τ : ℝ) (ρ : E →L[ℂ] E) :
    IntegrableOn (fun s => Real.exp (-s) • unitaryChannel V (τ * s) ρ) (Ioi 0) :=
  (ContinuousLinearMap.apply ℂ (E →L[ℂ] E) ρ).integrable_comp (integrableOn_laplaceKernel V τ)

lemma laplaceResolvent_apply (τ : ℝ) (ρ : E →L[ℂ] E) :
    laplaceResolvent V τ ρ = ∫ s in Ioi (0 : ℝ), Real.exp (-s) • unitaryChannel V (τ * s) ρ := by
  rw [laplaceResolvent, ContinuousLinearMap.integral_apply (integrableOn_laplaceKernel V τ)]
  rfl

lemma hasDerivAt_laplace (τ : ℝ) (ρ : E →L[ℂ] E) (s : ℝ) :
    HasDerivAt (fun s => Real.exp (-s) • unitaryChannel V (τ * s) ρ)
      (-(Real.exp (-s) • (unitaryChannel V (τ * s) ρ -
        τ • vonNeumannGenerator V.generator (unitaryChannel V (τ * s) ρ)))) s := by
  have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
    convert (hasDerivAt_neg s).exp using 1
    ring
  have h2 : HasDerivAt (fun s => unitaryChannel V (τ * s) ρ)
      (τ • vonNeumannGenerator V.generator (unitaryChannel V (τ * s) ρ)) s := by
    have h := (hasDerivAt_unitaryChannel V ρ (τ * s)).scomp s ((hasDerivAt_id s).const_mul τ)
    rw [mul_one] at h
    exact h
  convert h1.smul h2 using 1
  rw [smul_sub, neg_sub, neg_smul]
  abel

/-- `∫₀^∞ e^{-s} (1 - τ L) T (τ s) ρ ds = ρ`: the integrand is a derivative. -/
lemma integral_laplace_vonNeumannStep (τ : ℝ) (ρ : E →L[ℂ] E) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-s) • (unitaryChannel V (τ * s) ρ -
      τ • vonNeumannGenerator V.generator (unitaryChannel V (τ * s) ρ)) = ρ := by
  set L := vonNeumannGenerator V.generator
  set g := fun s : ℝ => Real.exp (-s) • unitaryChannel V (τ * s) ρ
  have hg := integrableOn_laplaceKernel_apply V τ ρ
  have hint : IntegrableOn (fun s : ℝ => -(Real.exp (-s) • (unitaryChannel V (τ * s) ρ -
      τ • L (unitaryChannel V (τ * s) ρ)))) (Ioi 0) := by
    refine (hg.sub ((L.integrable_comp hg).smul τ)).neg.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, ContinuousLinearMap.map_smul_of_tower,
      smul_sub, smul_comm τ (Real.exp (-s))]
  have hlim : Tendsto g atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun s => ?_)
      (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const ‖ρ‖)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_unitaryChannel]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => hasDerivAt_laplace V τ ρ s) hint hlim
  rw [integral_neg] at h
  simpa [g, unitaryChannel_zero] using h

/-- `(1 - τ L) (Ψ τ ρ) = ρ`. -/
theorem laplaceResolvent_sub (τ : ℝ) (ρ : E →L[ℂ] E) :
    laplaceResolvent V τ ρ - τ • vonNeumannGenerator V.generator (laplaceResolvent V τ ρ) = ρ := by
  set L := vonNeumannGenerator V.generator
  have hg := integrableOn_laplaceKernel_apply V τ ρ
  have hg2 : IntegrableOn (fun s => τ • L (Real.exp (-s) • unitaryChannel V (τ * s) ρ)) (Ioi 0) :=
    (L.integrable_comp hg).smul τ
  rw [laplaceResolvent_apply, ← L.integral_comp_comm hg, ← integral_smul, ← integral_sub hg hg2]
  refine (integral_congr_ae (Eventually.of_forall fun s => ?_)).trans
    (integral_laplace_vonNeumannStep V τ ρ)
  simp only [ContinuousLinearMap.map_smul_of_tower, smul_sub, smul_comm τ (Real.exp (-s))]
  rfl

/-- `Ψ τ` commutes with `L`. -/
lemma laplaceResolvent_vonNeumannGenerator (τ : ℝ) (ρ : E →L[ℂ] E) :
    laplaceResolvent V τ (vonNeumannGenerator V.generator ρ) =
      vonNeumannGenerator V.generator (laplaceResolvent V τ ρ) := by
  rw [laplaceResolvent_apply, laplaceResolvent_apply,
    ← (vonNeumannGenerator V.generator).integral_comp_comm (integrableOn_laplaceKernel_apply V τ ρ)]
  simp only [ContinuousLinearMap.map_smul_of_tower, unitaryChannel_vonNeumannGenerator]

/-- `Ψ τ ((1 - τ L) σ) = σ`. -/
theorem laplaceResolvent_vonNeumannStep (τ : ℝ) (σ : E →L[ℂ] E) :
    laplaceResolvent V τ (vonNeumannStep V.generator τ σ) = σ := by
  rw [vonNeumannStep_apply, map_sub, ContinuousLinearMap.map_smul_of_tower,
    laplaceResolvent_vonNeumannGenerator,
    laplaceResolvent_sub]

/-- The resolvent identity `Ψ τ ρ - ρ = τ L (Ψ τ ρ)`. -/
lemma laplaceResolvent_sub_self (τ : ℝ) (ρ : E →L[ℂ] E) :
    laplaceResolvent V τ ρ - ρ =
      τ • vonNeumannGenerator V.generator (laplaceResolvent V τ ρ) := by
  nth_rw 2 [← laplaceResolvent_sub V τ ρ]
  abel

lemma laplaceResolvent_star (τ : ℝ) (ρ : E →L[ℂ] E) :
    laplaceResolvent V τ (star ρ) = star (laplaceResolvent V τ ρ) := by
  nth_rw 1 [← laplaceResolvent_sub V τ ρ]
  rw [← vonNeumannStep_apply, ← vonNeumannStep_star V.generator_isSelfAdjoint,
    laplaceResolvent_vonNeumannStep]

lemma isSelfAdjoint_laplaceResolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) :
    IsSelfAdjoint (laplaceResolvent V τ ρ) := by
  rw [IsSelfAdjoint, ← laplaceResolvent_star, hρ.star_eq]

/-! ## C. Density operators and complete positivity -/

/-- `re ⟪x, A x⟫`, as a real-linear functional of `A`. -/
def expectationL (x : E) : (E →L[ℂ] E) →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ E x)).restrictScalars ℝ)

omit [CompleteSpace E] in
lemma expectationL_apply (x : E) (A : E →L[ℂ] E) : expectationL x A = (⟪x, A x⟫_ℂ).re := rfl

/-- The resolvent preserves positivity. -/
theorem laplaceResolvent_nonneg (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) :
    0 ≤ laplaceResolvent V τ ρ := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  refine ⟨isSelfAdjoint_laplaceResolvent V τ hρ.isSelfAdjoint, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  change 0 ≤ expectationL x (laplaceResolvent V τ ρ)
  rw [laplaceResolvent_apply,
    ← (expectationL x).integral_comp_comm (integrableOn_laplaceKernel_apply V τ ρ)]
  refine setIntegral_nonneg measurableSet_Ioi fun s _ => ?_
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg (Real.exp_pos _).le
    (re_inner_apply_nonneg (star_right_conjugate_nonneg hρ (V (τ * s))) x)

/-- **The resolvent maps density operators to density operators.** The Laplace integral also
converges in the trace class, where the trace is a continuous functional. -/
theorem isDensityOperator_laplaceResolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (laplaceResolvent V τ ρ) := by
  set f : ℝ → TraceClass E := fun s => (Real.exp (-s) : ℂ) •
    ofOperator (V (τ * s) * ρ * star (V (τ * s))) (isTraceClass_mul_mul hρ.isTraceClass)
  have hfc : Continuous f := by
    refine (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul ?_
    exact continuous_conj (U := fun s => V (τ * s))
      (fun s => norm_unitaryOneParameterGroup_le V _)
      (fun x => (V.continuous.comp (continuous_const.mul continuous_id)).clm_apply continuous_const)
      hρ.nonneg hρ.isTraceClass
  have hnorm : ∀ s, ‖ofOperator (V (τ * s) * ρ * star (V (τ * s)))
      (isTraceClass_mul_mul hρ.isTraceClass)‖ = 1 := fun s =>
    (isDensityOperator_unitaryChannel V (τ * s) hρ).norm_ofOperator
  have hf : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_exp_neg_Ioi 0).mono' hfc.aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [norm_smul, hnorm, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  set S := ∫ s in Ioi (0 : ℝ), f s
  have hS : S.1 = laplaceResolvent V τ ρ := by
    rw [← toOperator_apply, ← toOperator.integral_comp_comm hf, laplaceResolvent_apply]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    change ((Real.exp (-s) : ℂ) • (V (τ * s) * ρ * star (V (τ * s))) : E →L[ℂ] E) = _
    rw [Complex.coe_smul]
    rfl
  have htc : IsTraceClass (laplaceResolvent V τ ρ) := hS ▸ S.2
  refine ⟨laplaceResolvent_nonneg V τ hρ.nonneg, htc, ?_⟩
  have htr : ∀ s, tracePairing 1 (f s) = (Real.exp (-s) : ℂ) := fun s => by
    rw [map_smul, tracePairing_apply, smul_eq_mul]
    have h := (isDensityOperator_unitaryChannel V (τ * s) hρ).trace_eq_one
    rw [trace_transport (one_mul _).symm] at h
    have h' := congrArg (fun z => (Real.exp (-s) : ℂ) * z) h
    simp only [mul_one] at h'
    exact h'
  have h1 : tracePairing 1 S = 1 := by
    rw [← (tracePairing 1).integral_comp_comm hf]
    simp_rw [htr]
    rw [integral_complex_ofReal, integral_exp_neg_Ioi_zero, ofReal_one]
  rw [tracePairing_apply, trace_transport (one_mul S.1)] at h1
  rw [← h1]
  exact trace_transport hS.symm htc

/-- The unitary channel is completely positive: it is conjugation by a unitary, a
⋆-automorphism. -/
lemma unitaryChannelL_cstarMatrix_nonneg (t : ℝ) {k : ℕ}
    {M : CStarMatrix (Fin k) (Fin k) (E →L[ℂ] E)} (hM : 0 ≤ M) :
    0 ≤ M.map (unitaryChannelL V t) := by
  have h : 0 ≤ M.map (Unitary.conjStarAlgAut ℂ (E →L[ℂ] E) ⟨V t, V.mem_unitary t⟩) :=
    CompletelyPositiveMapClass.map_cstarMatrix_nonneg' _ k M hM
  convert h using 3
  funext ρ
  rw [Unitary.conjStarAlgAut_apply]
  rfl

lemma laplaceKernel_cstarMatrix_nonneg (τ s : ℝ) {k : ℕ}
    {M : CStarMatrix (Fin k) (Fin k) (E →L[ℂ] E)} (hM : 0 ≤ M) :
    0 ≤ M.map (laplaceKernel V τ s) := by
  have h : M.map (laplaceKernel V τ s) = Real.exp (-s) • M.map (unitaryChannelL V (τ * s)) := by
    ext i j
    simp [laplaceKernel]
  rw [h]
  exact smul_nonneg (Real.exp_pos _).le (unitaryChannelL_cstarMatrix_nonneg V _ hM)

/-- **The resolvent is completely positive**, as a mixture of unitary channels: `Ψ τ` as a
completely positive map. -/
def laplaceResolventCP (τ : ℝ) : (E →L[ℂ] E) →CP (E →L[ℂ] E) :=
  CompletelyPositiveMap.integral (laplaceKernel V τ) (volume.restrict (Ioi 0))
    (Eventually.of_forall fun s _ _ hM => laplaceKernel_cstarMatrix_nonneg V τ s hM)

@[simp]
lemma coe_laplaceResolventCP (τ : ℝ) : ⇑(laplaceResolventCP V τ) = laplaceResolvent V τ :=
  rfl

/-- In finite dimension the resolvent `(1 - τ L)⁻¹` is the Laplace integral, so it is completely
positive too. -/
theorem vonNeumannResolvent_eq_laplaceResolvent [FiniteDimensional ℂ E] (τ : ℝ)
    (ρ : E →L[ℂ] E) : vonNeumannResolvent V τ ρ = laplaceResolvent V τ ρ := by
  apply injective_vonNeumannStep V.generator_isSelfAdjoint τ
  rw [vonNeumannStep_apply, vonNeumannStep_apply, vonNeumannResolvent_sub, laplaceResolvent_sub]

/-! ## D. The resolvent is a projective measurement -/

omit [CompleteSpace E] in
/-- `|b⟩⟨b| ρ |b⟩⟨b| = ⟪b, ρ b⟫ |b⟩⟨b|`. -/
lemma proj_mul_mul_proj (b : E) (ρ : E →L[ℂ] E) : proj b * ρ * proj b = ⟪b, ρ b⟫_ℂ • proj b := by
  ext x
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, proj_apply, map_smul,
    smul_apply, smul_smul, mul_comm]

/-- The diagonal entries of `L σ` vanish in an eigenbasis of a self-adjoint `σ`. -/
lemma inner_vonNeumannGenerator_apply_eq_zero {σ : E →L[ℂ] E} (hσ : IsSelfAdjoint σ) {b : E}
    {μ : ℝ} (hb : σ b = (μ : ℂ) • b) (K : E →L[ℂ] E) :
    ⟪b, vonNeumannGenerator K σ b⟫_ℂ = 0 := by
  have h1 : ⟪b, σ (K b)⟫_ℂ = μ * ⟪b, K b⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hσ.adjoint_eq, hb, inner_smul_left, conj_ofReal]
  simp only [vonNeumannGenerator_apply, smul_apply,
    sub_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    inner_smul_right, inner_sub_right, hb, map_smul, h1, sub_self, mul_zero]

/-- **The resolvent is a projective measurement.** For a density operator `ρ` there is a Hilbert
basis `(bᵢ)` of eigenvectors of `Ψ τ ρ`, with eigenvalues `μᵢ ≥ 0` summing to one, such that
the projectors `Pᵢ = |bᵢ⟩⟨bᵢ|` satisfy `Pᵢ ρ Pᵢ = μᵢ Pᵢ` and `Ψ τ ρ = ∑ᵢ Pᵢ ρ Pᵢ` strongly. -/
theorem exists_hilbertBasis_laplaceResolvent (τ : ℝ) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (μ : w → ℝ),
      (∀ i, laplaceResolvent V τ ρ (b i) = (μ i : ℂ) • b i) ∧ (∀ i, 0 ≤ μ i) ∧ HasSum μ 1 ∧
      (∀ i, proj (b i) * ρ * proj (b i) = (μ i : ℂ) • proj (b i)) ∧
      ∀ x, HasSum (fun i => (proj (b i) * ρ * proj (b i)) x) (laplaceResolvent V τ ρ x) := by
  have hσ := isDensityOperator_laplaceResolvent V τ hρ
  obtain ⟨w, b, μ, -, hb, hμ0, hμ, -, hS⟩ := hσ.isTraceClass.exists_hasSum_rankOne hσ.nonneg
  have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hP : ∀ i, proj (b i) * ρ * proj (b i) = (μ i : ℂ) • proj (b i) := fun i => by
    rw [proj_mul_mul_proj]
    congr 1
    have h0 := inner_vonNeumannGenerator_apply_eq_zero hσ.isSelfAdjoint (hb i) V.generator
    nth_rw 1 [← laplaceResolvent_sub V τ ρ]
    rw [sub_apply, inner_sub_right, ← Complex.coe_smul,
      smul_apply, inner_smul_right, h0, mul_zero, sub_zero, hb i,
      inner_smul_right, inner_self_eq_norm_sq_to_K, hbn i]
    simp
  refine ⟨w, b, μ, hb, hμ0, by rwa [hσ.traceNorm_eq_one] at hμ, hP, fun x => ?_⟩
  have h := (hS.mapL toOperator).mapL (ContinuousLinearMap.apply ℂ E x)
  simp_rw [hP]
  exact h

/-! ## E. Second-order estimates in operator norm -/

/-- Second order for the resolvent: `Ψ τ ρ - ρ - τ L ρ = τ² L² Ψ τ ρ`. -/
lemma norm_laplaceResolvent_sub_sub_le (τ : ℝ) (ρ : E →L[ℂ] E) :
    ‖laplaceResolvent V τ ρ - ρ - τ • vonNeumannGenerator V.generator ρ‖ ≤
      4 * ‖V.generator‖ ^ 2 * ‖laplaceResolvent V τ ρ‖ * τ ^ 2 := by
  set L := vonNeumannGenerator V.generator
  set σ := laplaceResolvent V τ ρ
  have h : σ - ρ - τ • L ρ = τ • L (τ • L σ) := by
    rw [← laplaceResolvent_sub_self, map_sub, smul_sub, ← laplaceResolvent_sub_self]
  rw [h, norm_smul, Real.norm_eq_abs]
  calc |τ| * ‖L (τ • L σ)‖ ≤ |τ| * (2 * ‖V.generator‖ * ‖τ • L σ‖) := by
        gcongr
        exact norm_vonNeumannGenerator_apply_le _ _
    _ = |τ| * (2 * ‖V.generator‖ * (|τ| * ‖L σ‖)) := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |τ| * (2 * ‖V.generator‖ * (|τ| * (2 * ‖V.generator‖ * ‖σ‖))) := by
        gcongr
        exact norm_vonNeumannGenerator_apply_le _ _
    _ = 4 * ‖V.generator‖ ^ 2 * ‖σ‖ * τ ^ 2 := by rw [← sq_abs τ]; ring

/-- On density operators, `‖Ψ τ ρ - T τ ρ‖ ≤ 8 ‖K‖² τ²` in operator norm. -/
theorem norm_laplaceResolvent_sub_unitaryChannel_le {τ : ℝ} (hτ : 0 ≤ τ) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    ‖laplaceResolvent V τ ρ - unitaryChannel V τ ρ‖ ≤ 8 * ‖V.generator‖ ^ 2 * τ ^ 2 := by
  have h1 := norm_laplaceResolvent_sub_sub_le V τ ρ
  have h2 := norm_unitaryChannel_sub_sub_le V ρ hτ
  have hΨ := (isDensityOperator_laplaceResolvent V τ hρ).norm_le_one
  have hρ1 := hρ.norm_le_one
  calc ‖laplaceResolvent V τ ρ - unitaryChannel V τ ρ‖
      = ‖(laplaceResolvent V τ ρ - ρ - τ • vonNeumannGenerator V.generator ρ) -
          (unitaryChannel V τ ρ - ρ - τ • vonNeumannGenerator V.generator ρ)‖ := by
        congr 1
        abel
    _ ≤ 4 * ‖V.generator‖ ^ 2 * ‖laplaceResolvent V τ ρ‖ * τ ^ 2 +
          4 * ‖V.generator‖ ^ 2 * ‖ρ‖ * τ ^ 2 := (norm_sub_le _ _).trans (add_le_add h1 h2)
    _ ≤ 4 * ‖V.generator‖ ^ 2 * 1 * τ ^ 2 + 4 * ‖V.generator‖ ^ 2 * 1 * τ ^ 2 := by gcongr
    _ = 8 * ‖V.generator‖ ^ 2 * τ ^ 2 := by ring

/-! ## F. The largest outcome on a pure state -/

/-- A family of nonnegative reals summing to one has a largest member. -/
lemma exists_forall_le_of_hasSum {ι : Type*} {μ : ι → ℝ} (h0 : ∀ i, 0 ≤ μ i)
    (h : HasSum μ 1) : ∃ i₀, ∀ i, μ i ≤ μ i₀ := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, 0 < μ j := by
    by_contra! hc
    have : μ = 0 := funext fun i => le_antisymm (hc i) (h0 i)
    rw [this] at h
    exact one_ne_zero (h.unique hasSum_zero)
  have hfin : {i | μ j ≤ μ i}.Finite := by
    have h1 := h.summable.tendsto_cofinite_zero.eventually (gt_mem_nhds hj)
    rw [Filter.eventually_cofinite] at h1
    simpa only [not_lt] using h1
  obtain ⟨i₀, hi₀, hmax⟩ := hfin.toFinset.exists_max_image μ ⟨j, by simp⟩
  refine ⟨i₀, fun i => ?_⟩
  by_cases hi : μ j ≤ μ i
  · exact hmax i (by simpa using hi)
  · exact (not_le.mp hi).le.trans (by simpa using hi₀)

omit [CompleteSpace E] in
/-- In an eigenbasis of `σ`, `re ⟪y, σ y⟫ = ∑ᵢ μᵢ |⟪bᵢ, y⟫|²`. -/
lemma hasSum_re_inner_of_eigen {σ : E →L[ℂ] E} {w : Set E} (b : HilbertBasis w ℂ E)
    {μ : w → ℝ} (hb : ∀ i, σ (b i) = (μ i : ℂ) • b i) (y : E) :
    HasSum (fun i => μ i * ‖⟪b i, y⟫_ℂ‖ ^ 2) (⟪y, σ y⟫_ℂ).re := by
  have h := Complex.reCLM.hasSum (((b.hasSum_repr y).mapL σ).mapL (innerSL ℂ y))
  refine h.congr_fun fun i => ?_
  simp only [Complex.reCLM_apply, innerSL_apply_apply, HilbertBasis.repr_apply_apply, map_smul,
    hb, smul_eq_mul]
  rw [← inner_conj_symm y (b i), mul_left_comm, Complex.mul_conj']
  norm_cast

omit [CompleteSpace E] in
/-- A Davis–Kahan bound. Let `σ φ = x φ` with `x ≥ ½` for a unit `φ`, and `⟪w, σ w⟫ ≤ (1 - x) ‖w‖²`
for `w ⊥ φ`. If `‖σ - |u⟩⟨u|‖ ≤ δ` for a unit `u`, the component of `u` orthogonal to `φ` has norm
at most `2 δ`. -/
lemma norm_sub_inner_smul_le_of_eigen {σ : E →L[ℂ] E} {x : ℝ} (hx : 2⁻¹ ≤ x) {u φ : E}
    (hu : ‖u‖ = 1) (hφ : ‖φ‖ = 1) (hσφ : σ φ = (x : ℂ) • φ)
    (hw : ∀ w, ⟪φ, w⟫_ℂ = 0 → (⟪w, σ w⟫_ℂ).re ≤ (1 - x) * ‖w‖ ^ 2) :
    ‖u - ⟪φ, u⟫_ℂ • φ‖ ≤ 2 * ‖σ - proj u‖ := by
  set c := ⟪φ, u⟫_ℂ
  set w := u - c • φ
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hφw : ⟪φ, w⟫_ℂ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, hφφ, mul_one, c, sub_self]
  have hwφ : ⟪w, φ⟫_ℂ = 0 := inner_eq_zero_symm.mp hφw
  have hwσw := hw w hφw
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

/-- **The largest outcome on a pure state.** Let `|ψ⟩⟨ψ|` be a pure state and
`8 ‖K‖² τ² ≤ ½`. In the eigenbasis of `σ = Ψ τ |ψ⟩⟨ψ|` that realizes it as a projective
measurement, the largest eigenvalue `μ i₀` has `1 - μ i₀ ≤ 8 ‖K‖² τ²`; its eigenvector `b i₀`
satisfies `‖|b i₀⟩⟨b i₀| - T τ |ψ⟩⟨ψ|‖₁ ≤ 64 ‖K‖² τ²`, and `‖σ - T τ |ψ⟩⟨ψ|‖₁ ≤ 80 ‖K‖² τ²`. -/
theorem exists_max_laplaceResolvent_proj {ψ : E} (hψ : ‖ψ‖ = 1) {τ : ℝ} (hτ : 0 ≤ τ)
    (hδ : 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ 2⁻¹) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (μ : w → ℝ) (i₀ : w),
      (∀ i, 0 ≤ μ i) ∧ HasSum μ 1 ∧
      (∀ i, proj (b i) * proj ψ * proj (b i) = (μ i : ℂ) • proj (b i)) ∧
      (∀ x, HasSum (fun i => (proj (b i) * proj ψ * proj (b i)) x)
        (laplaceResolvent V τ (proj ψ) x)) ∧
      (∀ i, μ i ≤ μ i₀) ∧ 1 - 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ μ i₀ ∧
      traceENorm (proj (b i₀) - unitaryChannel V τ (proj ψ)) ≤
        ENNReal.ofReal (64 * ‖V.generator‖ ^ 2 * τ ^ 2) ∧
      traceENorm (laplaceResolvent V τ (proj ψ) - unitaryChannel V τ (proj ψ)) ≤
        ENNReal.ofReal (80 * ‖V.generator‖ ^ 2 * τ ^ 2) := by
  classical
  have hψd := isDensityOperator_proj hψ
  obtain ⟨w, b, μ, hb, hμ0, hμ, hP, hsum⟩ := exists_hilbertBasis_laplaceResolvent V τ hψd
  set σ := laplaceResolvent V τ (proj ψ)
  have hσ : IsDensityOperator σ := isDensityOperator_laplaceResolvent V τ hψd
  obtain ⟨i₀, hmax⟩ := exists_forall_le_of_hasSum hμ0 hμ
  set x := μ i₀
  set δ := 8 * ‖V.generator‖ ^ 2 * τ ^ 2
  have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  set u := V τ ψ
  have hu : ‖u‖ = 1 := by rw [ContinuousLinearMap.norm_map_of_mem_unitary (V.mem_unitary τ), hψ]
  have hΔ : ‖σ - proj u‖ ≤ δ := by
    rw [← unitaryChannel_proj]
    exact norm_laplaceResolvent_sub_unitaryChannel_le V hτ hψd
  -- the largest eigenvalue is at least `1 - δ`
  have hx1 : 1 - δ ≤ x := by
    have hge : 1 - ‖σ - proj u‖ ≤ (⟪u, σ u⟫_ℂ).re := by
      have h := re_inner_self_apply_sub_ge (A := σ - proj u) hu
      have h1 : (⟪u, proj u u⟫_ℂ).re = 1 := by rw [inner_proj_apply]; simp [hu]
      rw [sub_apply, inner_sub_right, Complex.sub_re, h1] at h
      linarith
    have hle : (⟪u, σ u⟫_ℂ).re ≤ x := by
      have h := hasSum_le (fun i => mul_le_mul_of_nonneg_right (hmax i) (sq_nonneg _))
        (hasSum_re_inner_of_eigen b hb u) ((hasSum_norm_sq_inner_basis b u).mul_left x)
      rwa [hu, one_pow, mul_one] at h
    linarith
  have hx12 : 2⁻¹ ≤ x := by linarith
  have hxle1 : x ≤ 1 := by
    simpa using le_hasSum hμ i₀ fun j _ => hμ0 j
  -- the other eigenvalues are at most `1 - x`
  have hother : ∀ i, i ≠ i₀ → μ i ≤ 1 - x := fun i hi => by
    have h := sum_le_hasSum ({i, i₀} : Finset w) (fun j _ => hμ0 j) hμ
    rw [Finset.sum_pair hi] at h
    linarith
  have hw : ∀ y, ⟪b i₀, y⟫_ℂ = 0 → (⟪y, σ y⟫_ℂ).re ≤ (1 - x) * ‖y‖ ^ 2 := fun y hy => by
    refine hasSum_le (fun i => ?_) (hasSum_re_inner_of_eigen b hb y)
      ((hasSum_norm_sq_inner_basis b y).mul_left (1 - x))
    by_cases hi : i = i₀
    · subst hi; simp [hy]
    · exact mul_le_mul_of_nonneg_right (hother i hi) (sq_nonneg _)
  have hDK := norm_sub_inner_smul_le_of_eigen hx12 hu (hbn i₀) (hb i₀) hw
  have hF : traceENorm (proj (b i₀) - unitaryChannel V τ (proj ψ)) ≤ ENNReal.ofReal (64 *
      ‖V.generator‖ ^ 2 * τ ^ 2) := by
    rw [unitaryChannel_proj]
    refine (traceENorm_proj_sub_proj_le hu (hbn i₀)).trans (ENNReal.ofReal_le_ofReal ?_)
    linarith
  refine ⟨w, b, μ, i₀, hμ0, hμ, hP, hsum, hmax, hx1, hF, ?_⟩
  -- `σ - x |b i₀⟩⟨b i₀|` is positive with trace `1 - x`
  set F := proj (b i₀)
  have hFsa : IsSelfAdjoint F := (proj_nonneg (b i₀)).isSelfAdjoint
  have hσF : σ * F = (x : ℂ) • F := by
    ext y
    simp only [F, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, proj_apply,
      map_smul, hb i₀, smul_apply, smul_smul, mul_comm]
    rfl
  have hFσ : F * σ = (x : ℂ) • F := by
    have h := congrArg star hσF
    rwa [star_mul, hFsa.star_eq, hσ.isSelfAdjoint.star_eq, star_smul, hFsa.star_eq,
      Complex.star_def, conj_ofReal] at h
  have hFF : F * F = F := (isIdempotentElem_rankOne_self (hbn i₀)).eq
  have hrest : σ - (x : ℂ) • F = (1 - F) * σ * star (1 - F) := by
    rw [star_sub, star_one, hFsa.star_eq]
    have h4 : (1 - F) * σ * (1 - F) = σ - F * σ - σ * F + F * (σ * F) := by noncomm_ring
    rw [h4, hFσ, hσF, mul_smul_comm, hFF]
    abel
  have hpos : 0 ≤ σ - (x : ℂ) • F := hrest ▸ star_right_conjugate_nonneg hσ.nonneg _
  have hxF : 0 ≤ (x : ℂ) • F := by
    rw [Complex.coe_smul]
    exact smul_nonneg (by linarith) (proj_nonneg _)
  have htr : traceENorm (σ - (x : ℂ) • F) = ENNReal.ofReal (1 - x) := by
    rw [traceENorm_of_nonneg hpos]
    have h := ContinuousLinearMap.posTrace_add hpos hxF
    rw [sub_add_cancel, hσ.posTrace_eq_one, ContinuousLinearMap.posTrace_smul (by linarith),
      (isDensityOperator_proj (hbn i₀)).posTrace_eq_one, mul_one] at h
    rw [ENNReal.ofReal_sub _ (by linarith : 0 ≤ x), ENNReal.ofReal_one, h,
      ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top]
  have htr2 : traceENorm ((x : ℂ) • F - F) = ENNReal.ofReal (1 - x) := by
    rw [show (x : ℂ) • F - F = ((x - 1 : ℝ) : ℂ) • F by
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul],
      traceENorm_smul _ (isTraceClass_rankOne_self _),
      (isDensityOperator_proj (hbn i₀)).traceENorm_eq_one, mul_one, ← ofReal_norm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith), neg_sub]
  have h3 : traceENorm (σ - unitaryChannel V τ (proj ψ)) ≤ traceENorm (σ - (x : ℂ) • F) +
      (traceENorm ((x : ℂ) • F - F) + traceENorm (F - unitaryChannel V τ (proj ψ))) :=
    (traceENorm_sub_le _ ((x : ℂ) • F) _).trans (add_le_add le_rfl (traceENorm_sub_le _ F _))
  rw [htr, htr2] at h3
  refine h3.trans ?_
  calc _ ≤ ENNReal.ofReal (1 - x) + (ENNReal.ofReal (1 - x) +
          ENNReal.ofReal (64 * ‖V.generator‖ ^ 2 * τ ^ 2)) := by gcongr
    _ = ENNReal.ofReal ((1 - x) + ((1 - x) + 64 * ‖V.generator‖ ^ 2 * τ ^ 2)) := by
        rw [ENNReal.ofReal_add (by linarith) (by positivity),
          ENNReal.ofReal_add (by linarith) (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

/-! ## G. Second-order estimate in trace norm -/

/-- **Second-order estimate**: on density operators, `‖Ψ τ ρ - T τ ρ‖₁ ≤ 80 ‖K‖² τ²`. -/
theorem traceENorm_laplaceResolvent_sub_unitaryChannel_le {τ : ℝ} (hτ : 0 ≤ τ)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    traceENorm (laplaceResolvent V τ ρ - unitaryChannel V τ ρ) ≤
      ENNReal.ofReal (80 * ‖V.generator‖ ^ 2 * τ ^ 2) := by
  refine traceENorm_apply_le_of_forall_proj (laplaceResolvent V τ - unitaryChannelL V τ)
    (by positivity) (fun ψ hψ => ?_) hρ
  rw [sub_apply, unitaryChannelL_apply]
  by_cases hδ : 8 * ‖V.generator‖ ^ 2 * τ ^ 2 ≤ 2⁻¹
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := exists_max_laplaceResolvent_proj V hψ hτ hδ
    exact h
  · have hψd := isDensityOperator_proj hψ
    refine (traceENorm_sub_le_add _ _).trans ?_
    rw [(isDensityOperator_laplaceResolvent V τ hψd).traceENorm_eq_one,
      (isDensityOperator_unitaryChannel V τ hψd).traceENorm_eq_one, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by push Not at hδ; nlinarith)

/-! ## H. The exponential formula and the generator -/

/-- Errors of at most `ε` per step against the unitary step accumulate to at most `n ε` in the
trace norm, because the unitary channel does not increase it. -/
lemma traceENorm_sub_unitaryChannel_le_of_step {x : ℕ → E →L[ℂ] E} {τ : ℝ} {ε : ℝ≥0∞} (n : ℕ)
    (h : ∀ k < n, traceENorm (x (k + 1) - unitaryChannel V τ (x k)) ≤ ε) :
    traceENorm (x n - unitaryChannel V (n * τ) (x 0)) ≤ n * ε := by
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
    refine (traceENorm_add_le _ _).trans ?_
    calc _ ≤ ε + n * ε := add_le_add (h n (by omega))
          ((traceENorm_unitaryChannel_le V _ _).trans (ih fun k hk => h k (by omega)))
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

lemma isDensityOperator_laplaceResolvent_iterate (τ : ℝ) (n : ℕ) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) : IsDensityOperator ((laplaceResolvent V τ)^[n] ρ) := by
  induction n with
  | zero => exact hρ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact isDensityOperator_laplaceResolvent V τ ih

/-- **The resolvent exponential formula**, with error: `‖(Ψ (t / n))ⁿ ρ - T t ρ‖₁ ≤ 80 ‖K‖² t² / n`
for density operators. -/
theorem traceENorm_laplaceResolvent_iterate_sub_le {t : ℝ} (ht : 0 ≤ t) {n : ℕ} (hn : 0 < n)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    traceENorm ((laplaceResolvent V (t / n))^[n] ρ - unitaryChannel V t ρ) ≤
      ENNReal.ofReal (80 * ‖V.generator‖ ^ 2 * t ^ 2 / n) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h := traceENorm_sub_unitaryChannel_le_of_step V
    (x := fun k => (laplaceResolvent V (t / n))^[k] ρ) (τ := t / n)
    (ε := ENNReal.ofReal (80 * ‖V.generator‖ ^ 2 * (t / n) ^ 2)) n fun k _ => by
      simp only [Function.iterate_succ_apply']
      exact traceENorm_laplaceResolvent_sub_unitaryChannel_le V (by positivity)
        (isDensityOperator_laplaceResolvent_iterate V _ k hρ)
  rw [mul_div_cancel₀ t hn'] at h
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  congr 1
  field_simp

theorem tendsto_laplaceResolvent_iterate {t : ℝ} (ht : 0 ≤ t) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    Tendsto (fun n : ℕ => traceENorm ((laplaceResolvent V (t / n))^[n] ρ -
      unitaryChannel V t ρ)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal (80 * ‖V.generator‖ ^ 2 * t ^ 2 / n)) atTop
      (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat _)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact traceENorm_laplaceResolvent_iterate_sub_le V ht hn hρ

lemma isTraceClass_vonNeumannGenerator (K : E →L[ℂ] E) {X : E →L[ℂ] E}
    (hX : IsTraceClass X) : IsTraceClass (vonNeumannGenerator K X) := by
  rw [vonNeumannGenerator_apply, sub_eq_add_neg]
  refine isTraceClass_smul _ (isTraceClass_add ?_ (isTraceClass_neg ?_))
  · simpa using isTraceClass_mul_mul (A := K) (B := 1) hX
  · simpa using isTraceClass_mul_mul (A := 1) (B := K) hX

/-- `‖L X‖₁ ≤ 2 ‖K‖ ‖X‖₁`. -/
lemma traceENorm_vonNeumannGenerator_le (K : E →L[ℂ] E) {X : E →L[ℂ] E}
    (hX : IsTraceClass X) :
    traceENorm (vonNeumannGenerator K X) ≤ 2 * ‖K‖ₑ * traceENorm X := by
  have h1 : ‖(1 : E →L[ℂ] E)‖ₑ ≤ 1 := by
    rw [← ofReal_norm, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ContinuousLinearMap.norm_id_le
  have hKX : traceENorm (K * X) ≤ ‖K‖ₑ * traceENorm X := by
    have h := traceENorm_mul_mul_le K 1 hX
    rw [mul_one] at h
    calc _ ≤ ‖K‖ₑ * traceENorm X * ‖(1 : E →L[ℂ] E)‖ₑ := h
      _ ≤ ‖K‖ₑ * traceENorm X * 1 := by gcongr
      _ = _ := mul_one _
  have hXK : traceENorm (X * K) ≤ ‖K‖ₑ * traceENorm X := by
    have h := traceENorm_mul_mul_le 1 K hX
    rw [one_mul] at h
    calc _ ≤ ‖(1 : E →L[ℂ] E)‖ₑ * traceENorm X * ‖K‖ₑ := h
      _ ≤ 1 * traceENorm X * ‖K‖ₑ := by gcongr
      _ = _ := by rw [one_mul, mul_comm]
  have hY : IsTraceClass (K * X - X * K) := by
    rw [sub_eq_add_neg]
    refine isTraceClass_add ?_ (isTraceClass_neg ?_)
    · simpa using isTraceClass_mul_mul (A := K) (B := 1) hX
    · simpa using isTraceClass_mul_mul (A := 1) (B := K) hX
  rw [vonNeumannGenerator_apply, traceENorm_smul _ hY, ← ofReal_norm, norm_neg, Complex.norm_I,
    ENNReal.ofReal_one, one_mul]
  exact (traceENorm_sub_le_add _ _).trans ((add_le_add hKX hXK).trans_eq (by ring))

/-- The resolvent is infinitesimal with generator `L`: `‖(Ψ τ ρ - ρ) / τ - L ρ‖₁ ≤ 4 ‖K‖² τ`. -/
theorem traceENorm_inv_smul_laplaceResolvent_sub_le {τ : ℝ} (hτ : 0 < τ) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    traceENorm (τ⁻¹ • (laplaceResolvent V τ ρ - ρ) - vonNeumannGenerator V.generator ρ) ≤
      4 * ‖V.generator‖ₑ ^ 2 * ENNReal.ofReal τ := by
  set L := vonNeumannGenerator V.generator
  set σ := laplaceResolvent V τ ρ
  have hσ := isDensityOperator_laplaceResolvent V τ hρ
  have hLσ := isTraceClass_vonNeumannGenerator V.generator hσ.isTraceClass
  have h : τ⁻¹ • (σ - ρ) - L ρ = (τ : ℂ) • L (L σ) := by
    rw [laplaceResolvent_sub_self, inv_smul_smul₀ hτ.ne', ← map_sub, laplaceResolvent_sub_self,
      ContinuousLinearMap.map_smul_of_tower, Complex.coe_smul]
  rw [h, traceENorm_smul _ (isTraceClass_vonNeumannGenerator _ hLσ)]
  have h1 := traceENorm_vonNeumannGenerator_le V.generator hLσ
  have h2 := traceENorm_vonNeumannGenerator_le V.generator hσ.isTraceClass
  rw [hσ.traceENorm_eq_one, mul_one] at h2
  have hτe : ‖(τ : ℂ)‖ₑ = ENNReal.ofReal τ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  calc ‖(τ : ℂ)‖ₑ * traceENorm (L (L σ)) ≤ ENNReal.ofReal τ * (2 * ‖V.generator‖ₑ *
        (2 * ‖V.generator‖ₑ)) := by
        rw [hτe]
        gcongr
        exact h1.trans (by gcongr)
    _ = 4 * ‖V.generator‖ₑ ^ 2 * ENNReal.ofReal τ := by ring

theorem tendsto_inv_smul_laplaceResolvent_sub {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    Tendsto (fun τ : ℝ => traceENorm (τ⁻¹ • (laplaceResolvent V τ ρ - ρ) -
      vonNeumannGenerator V.generator ρ)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun τ : ℝ => 4 * ‖V.generator‖ₑ ^ 2 * ENNReal.ofReal τ) (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal
      ((tendsto_id (x := 𝓝 (0 : ℝ))).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    rw [ENNReal.ofReal_zero] at h
    have := ENNReal.Tendsto.const_mul h (Or.inr (by finiteness : 4 * ‖V.generator‖ₑ ^ 2 ≠ ⊤))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact traceENorm_inv_smul_laplaceResolvent_sub_le V hτ hρ

end QuantumMechanics
