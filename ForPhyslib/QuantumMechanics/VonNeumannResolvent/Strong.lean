/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.ProbabilisticTheory.CStarAlgebra.Stinespring.Kernel
public import ForPhyslib.QuantumMechanics.ForwardHamiltonian
public import ForPhyslib.QuantumMechanics.VonNeumannResolvent.Laplace

/-!
# The resolvent of a strongly continuous unitary group

## i. Overview

Let `V` be a strongly continuous unitary group on a complex Hilbert space of any dimension; its
self-adjoint generator `H` may be unbounded. The unitary channel `T u ρ = V u ρ V u†` is then only
strongly continuous in `u`, so the Laplace integral

  `Ψ τ ρ = ∫₀^∞ e^{-s} T (τ s) ρ ds`

of `VonNeumannResolvent.Laplace` is taken pointwise, `(Ψ τ ρ) x = ∫₀^∞ e^{-s} T (τ s) ρ x ds`, a
Bochner integral in `E`. This is the resolvent `(1 - τ L)⁻¹` of the generator `L ρ = -i [H, ρ]`,
used directly, without spectral truncation. It is a contraction on `E →L[ℂ] E`, agrees with the
Laplace resolvent when `V` is norm continuous, preserves positivity, and maps density operators to
density operators: on a positive trace-class `ρ` the integrand is trace-norm continuous, so the
integral also converges in the trace class.

The resolvent is a projective measurement adapted to its output, as for a bounded generator, but
the proof cannot use `⟪b, L σ b⟫ = 0`, since `L σ` need not be an operator. Instead, for
`σ = Ψ τ ρ` and an eigenvector `σ b = μ b`:

* the shifted Laplace integral `T u σ x = e^{u/τ} (σ x - ∫₀^{u/τ} e^{-s} T (τ s) ρ x ds)` shows
  that `u ↦ T u σ x` is differentiable at `0`, with derivative `(σ x - ρ x) / τ`;
* `⟪b, (T u σ - σ) (V u b)⟫ = 0` exactly, so `⟪b, T u σ b⟫ - μ = ⟪(T u σ - σ) b, b - V u b⟫` is
  `O(u) · o(1)`.

Comparing the two derivatives gives `⟪b, ρ b⟫ = μ`, so `Ψ τ ρ = ∑ᵢ Pᵢ ρ Pᵢ` for the projectors
onto an eigenbasis.

On a pure state `|χ⟩⟨χ|` whose orbit is Lipschitz, `‖V u χ - χ‖ ≤ D |u|` (this holds on the domain
of `H`, with `D = ‖H χ‖`), the largest eigenvalue `q` of `Ψ τ |χ⟩⟨χ|` has `1 - q ≤ 2 D² τ²`: test
it on `χ`, with `1 - |⟪χ, V u χ⟫|² ≤ ‖V u χ - χ‖²` and `∫₀^∞ s² e^{-s} ds = 2`. Its eigenvector
`φ = q⁻¹ ∫₀^∞ e^{-s} ⟪V (τ s) χ, φ⟫ V (τ s) χ ds` has a Lipschitz orbit with constant `D / q`.

The resolvent is completely positive. The integral of completely positive maps in
`ForMathlib.Analysis.CStarAlgebra.CompletelyPositiveMap` needs convergence in operator norm, which
fails here. Instead, a `k × k` matrix `M` of operators is positive exactly when
`∑ᵢⱼ ⟪xᵢ, Mᵢⱼ xⱼ⟫ ≥ 0` for every `x ∈ Eᵏ`, and for the matrix of `Ψ τ Mᵢⱼ` this sum is
`∫₀^∞ e^{-s} ∑ᵢⱼ ⟪xᵢ, T (τ s) Mᵢⱼ xⱼ⟫ ds`, an integral of nonnegative numbers.

We set `ħ = 1`.

## ii. Key results

- `QuantumMechanics.StronglyContinuousUnitaryGroup.resolvent`: `Ψ τ`, pointwise.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.resolvent_eq_laplaceResolvent`: agreement with
  the Laplace resolvent of a norm-continuous group.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.resolvent_nonneg`,
  `QuantumMechanics.StronglyContinuousUnitaryGroup.isDensityOperator_resolvent`: `Ψ τ` preserves
  positivity and density operators.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.resolventCP`: `Ψ τ` is completely positive.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.hasDerivAt_conj_resolvent_apply`: the derivative
  of `u ↦ T u (Ψ τ ρ) x` at `0`.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.inner_apply_eq_of_resolvent_apply`:
  `⟪b, ρ b⟫ = ⟪b, Ψ τ ρ b⟫` on an eigenvector `b` of `Ψ τ ρ`.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.exists_hilbertBasis_resolvent`:
  `Ψ τ ρ = ∑ᵢ Pᵢ ρ Pᵢ` for the projectors onto an eigenbasis of `Ψ τ ρ`.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.exists_max_resolvent_proj`: the largest outcome
  on a pure state with a Lipschitz orbit.
- `QuantumMechanics.StronglyContinuousUnitaryGroup.norm_apply_sub_le_of_mem_domain`: the orbit of
  a vector in the domain of the generator is Lipschitz.

## iii. Table of contents

- A. The group
- B. The resolvent
- C. Positivity and density operators
- D. The resolvent is a projective measurement
- E. The largest outcome on a pure state
- F. Lipschitz orbits
- G. Complete positivity

## iv. References

- K.-J. Engel, R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Springer
  (2000), Thm II.1.10 (the Laplace representation of the resolvent).
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder Topology ENNReal CStarAlgebra
open InnerProductSpace QuantumMechanics.Wigner Complex Set Filter MeasureTheory
  ProbabilisticTheory ProbabilisticTheory.TraceClass
open ContinuousLinearMap (re_inner_apply_nonneg posTrace)

namespace QuantumMechanics.StronglyContinuousUnitaryGroup

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (V : StronglyContinuousUnitaryGroup E)

/-! ## A. The group -/

lemma norm_apply (t : ℝ) (x : E) : ‖V t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (V.mem_unitary t) x

lemma norm_le_one (t : ℝ) : ‖V t‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [norm_apply, one_mul]

lemma star_eq (t : ℝ) : star (V t) = V (-t) := by
  have h := V.map_add t (-t)
  rw [add_neg_cancel, V.map_zero] at h
  have hu := Unitary.mem_iff.mp (V.mem_unitary t)
  calc star (V t) = star (V t) * (V t * V (-t)) := by rw [← h, mul_one]
    _ = V (-t) := by rw [← mul_assoc, hu.1, one_mul]

lemma apply_neg_apply (t : ℝ) (x : E) : V (-t) (V t x) = x := by
  change (V (-t) * V t) x = x
  rw [← V.map_add, neg_add_cancel, V.map_zero]
  rfl

lemma star_mul_self (t : ℝ) : star (V t) * V t = 1 := (Unitary.mem_iff.mp (V.mem_unitary t)).1

/-- The unitary channel `T t ρ = V t ρ V t†`. -/
def conj (t : ℝ) (ρ : E →L[ℂ] E) : E →L[ℂ] E := V t * ρ * star (V t)

lemma conj_apply (t : ℝ) (ρ : E →L[ℂ] E) (x : E) : V.conj t ρ x = V t (ρ (V (-t) x)) := by
  rw [conj, star_eq]
  rfl

lemma norm_conj_apply_le (t : ℝ) (ρ : E →L[ℂ] E) (x : E) : ‖V.conj t ρ x‖ ≤ ‖ρ‖ * ‖x‖ := by
  rw [conj_apply, norm_apply]
  exact (ρ.le_opNorm _).trans_eq (by rw [norm_apply])

lemma conj_add (s t : ℝ) (ρ : E →L[ℂ] E) : V.conj s (V.conj t ρ) = V.conj (s + t) ρ := by
  simp only [conj, V.map_add, star_mul, mul_assoc]

lemma conj_eq_of_eq (W : UnitaryOneParameterGroup E) {t : ℝ} (h : V t = W t) (ρ : E →L[ℂ] E) :
    V.conj t ρ = unitaryChannel W t ρ := by
  rw [conj, unitaryChannel, h]

lemma isSelfAdjoint_conj (t : ℝ) {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) :
    IsSelfAdjoint (V.conj t ρ) :=
  hρ.conjugate (V t)

lemma conj_sub (t : ℝ) (ρ σ : E →L[ℂ] E) : V.conj t ρ - V.conj t σ = V.conj t (ρ - σ) := by
  simp only [conj, mul_sub, sub_mul]

/-- The unitary channel does not increase the trace norm. -/
lemma traceENorm_conj_le (t : ℝ) (X : E →L[ℂ] E) : traceENorm (V.conj t X) ≤ traceENorm X := by
  by_cases h : IsTraceClass X
  · refine (traceENorm_mul_mul_le _ _ h).trans ?_
    have h1 : ‖V t‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (V.norm_le_one t)
    have h2 : ‖star (V t)‖ₑ ≤ 1 := by rwa [← ofReal_norm, norm_star, ofReal_norm]
    calc ‖V t‖ₑ * traceENorm X * ‖star (V t)‖ₑ ≤ 1 * traceENorm X * 1 := by gcongr
      _ = traceENorm X := by rw [one_mul, mul_one]
  · simp [traceENorm_eq_top h]

/-- `(t, x) ↦ V t x` is jointly continuous. -/
lemma continuous_apply_apply {X : Type*} [TopologicalSpace X] {f : X → ℝ} {g : X → E}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => V (f a) (g a) := by
  refine continuous_iff_continuousAt.mpr fun a₀ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun a => ‖g a - g a₀‖) (𝓝 a₀) (𝓝 0) := by
    simpa using ((hg.tendsto a₀).sub_const (g a₀)).norm
  have h2 : Tendsto (fun a => ‖V (f a) (g a₀) - V (f a₀) (g a₀)‖) (𝓝 a₀) (𝓝 0) := by
    simpa using ((((V.continuous_apply (g a₀)).comp hf).tendsto a₀).sub_const
      (V (f a₀) (g a₀))).norm
  refine squeeze_zero (fun _ => norm_nonneg _) (fun a => ?_) (by simpa using h1.add h2)
  calc ‖V (f a) (g a) - V (f a₀) (g a₀)‖ =
        ‖V (f a) (g a - g a₀) + (V (f a) (g a₀) - V (f a₀) (g a₀))‖ := by
        rw [map_sub]; abel_nf
    _ ≤ _ := (norm_add_le _ _).trans_eq (by rw [norm_apply])

lemma continuous_conj_apply {f : ℝ → ℝ} (hf : Continuous f) (ρ : E →L[ℂ] E) (x : E) :
    Continuous fun s => V.conj (f s) ρ x := by
  simp only [conj_apply]
  exact V.continuous_apply_apply hf
    (ρ.continuous.comp (V.continuous_apply_apply hf.neg continuous_const))

/-! ## B. The resolvent -/

/-- The integrand `s ↦ e^{-s} T (τ s) ρ x` of the resolvent. -/
def kernel (τ : ℝ) (ρ : E →L[ℂ] E) (x : E) (s : ℝ) : E :=
  Real.exp (-s) • V.conj (τ * s) ρ x

lemma continuous_kernel (τ : ℝ) (ρ : E →L[ℂ] E) (x : E) : Continuous (V.kernel τ ρ x) :=
  (Real.continuous_exp.comp continuous_neg).smul
    (V.continuous_conj_apply (continuous_const.mul continuous_id) ρ x)

lemma norm_kernel_le (τ : ℝ) (ρ : E →L[ℂ] E) (x : E) (s : ℝ) :
    ‖V.kernel τ ρ x s‖ ≤ Real.exp (-s) * (‖ρ‖ * ‖x‖) := by
  rw [kernel, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (V.norm_conj_apply_le _ ρ x) (Real.exp_pos _).le

lemma integrableOn_kernel (τ : ℝ) (ρ : E →L[ℂ] E) (x : E) :
    IntegrableOn (V.kernel τ ρ x) (Ioi 0) :=
  ((integrableOn_exp_neg_Ioi 0).mul_const _).mono' (V.continuous_kernel τ ρ x).aestronglyMeasurable
    (Eventually.of_forall fun s => V.norm_kernel_le τ ρ x s)

lemma norm_integral_kernel_le (τ : ℝ) (ρ : E →L[ℂ] E) (x : E) :
    ‖∫ s in Ioi (0 : ℝ), V.kernel τ ρ x s‖ ≤ ‖ρ‖ * ‖x‖ := by
  refine (norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).mul_const _)
    (Eventually.of_forall fun s => V.norm_kernel_le τ ρ x s)).trans_eq ?_
  rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

lemma kernel_add_left (τ : ℝ) (ρ ρ' : E →L[ℂ] E) (x : E) (s : ℝ) :
    V.kernel τ (ρ + ρ') x s = V.kernel τ ρ x s + V.kernel τ ρ' x s := by
  simp only [kernel, conj, mul_add, add_mul, add_apply, smul_add]

lemma kernel_smul_left (τ : ℝ) (c : ℂ) (ρ : E →L[ℂ] E) (x : E) (s : ℝ) :
    V.kernel τ (c • ρ) x s = c • V.kernel τ ρ x s := by
  simp only [kernel, conj, mul_smul_comm, smul_mul_assoc, smul_apply, smul_comm c]

lemma kernel_add_right (τ : ℝ) (ρ : E →L[ℂ] E) (x y : E) (s : ℝ) :
    V.kernel τ ρ (x + y) s = V.kernel τ ρ x s + V.kernel τ ρ y s := by
  simp only [kernel, ContinuousLinearMap.map_add, smul_add]

lemma kernel_smul_right (τ : ℝ) (c : ℂ) (ρ : E →L[ℂ] E) (x : E) (s : ℝ) :
    V.kernel τ ρ (c • x) s = c • V.kernel τ ρ x s := by
  simp only [kernel, map_smul, smul_comm c]

/-- **The resolvent** `Ψ τ ρ = ∫₀^∞ e^{-s} T (τ s) ρ ds`, taken pointwise on vectors. -/
def resolvent (τ : ℝ) : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun ρ x => ∫ s in Ioi (0 : ℝ), V.kernel τ ρ x s)
      (fun ρ ρ' x => by
        simp only [kernel_add_left]
        exact integral_add (V.integrableOn_kernel τ ρ x) (V.integrableOn_kernel τ ρ' x))
      (fun c ρ x => by simp only [kernel_smul_left, integral_smul])
      (fun ρ x y => by
        simp only [kernel_add_right]
        exact integral_add (V.integrableOn_kernel τ ρ x) (V.integrableOn_kernel τ ρ y))
      (fun c ρ x => by simp only [kernel_smul_right, integral_smul]))
    1 fun ρ x => by
      rw [one_mul]
      exact V.norm_integral_kernel_le τ ρ x

lemma resolvent_apply_apply (τ : ℝ) (ρ : E →L[ℂ] E) (x : E) :
    V.resolvent τ ρ x = ∫ s in Ioi (0 : ℝ), V.kernel τ ρ x s :=
  rfl

/-- On a norm-continuous group `W` agreeing with `V`, the resolvent is the Laplace resolvent. -/
theorem resolvent_eq_laplaceResolvent (W : UnitaryOneParameterGroup E) {ρ : E →L[ℂ] E}
    (h : ∀ s, V.conj s ρ = unitaryChannel W s ρ) (τ : ℝ) :
    V.resolvent τ ρ = laplaceResolvent W τ ρ := by
  ext x
  rw [resolvent_apply_apply, laplaceResolvent_apply,
    ContinuousLinearMap.integral_apply (integrableOn_laplaceKernel_apply W τ ρ)]
  simp only [kernel, h, smul_apply]

/-! ## C. Positivity and density operators -/

lemma inner_resolvent_apply (τ : ℝ) (ρ : E →L[ℂ] E) (x y : E) :
    ⟪y, V.resolvent τ ρ x⟫_ℂ =
      ∫ s in Ioi (0 : ℝ), (Real.exp (-s) : ℂ) * ⟪y, V.conj (τ * s) ρ x⟫_ℂ := by
  rw [resolvent_apply_apply, ← integral_inner (V.integrableOn_kernel τ ρ x)]
  simp only [kernel, ← Complex.coe_smul, inner_smul_right]

lemma integrable_inner_conj (τ : ℝ) (ρ : E →L[ℂ] E) (x y : E) :
    Integrable (fun s => (Real.exp (-s) : ℂ) * ⟪y, V.conj (τ * s) ρ x⟫_ℂ)
      (volume.restrict (Ioi 0)) := by
  refine ((V.integrableOn_kernel τ ρ x).const_inner y).congr (Eventually.of_forall fun s => ?_)
  simp only [kernel, ← Complex.coe_smul, inner_smul_right]

lemma isSelfAdjoint_resolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsSelfAdjoint ρ) :
    IsSelfAdjoint (V.resolvent τ ρ) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_resolvent_apply, inner_resolvent_apply, ← integral_conj]
  congr 1
  funext s
  rw [map_mul, Complex.conj_ofReal, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, (V.isSelfAdjoint_conj (τ * s) hρ).star_eq]

/-- The resolvent preserves positivity. -/
theorem resolvent_nonneg (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) : 0 ≤ V.resolvent τ ρ := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
  refine ⟨V.isSelfAdjoint_resolvent τ hρ.isSelfAdjoint, fun x => ?_⟩
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm, inner_resolvent_apply,
    ← integral_re (V.integrable_inner_conj τ ρ x x)]
  refine setIntegral_nonneg measurableSet_Ioi fun s _ => ?_
  rw [RCLike.re_to_complex, Complex.re_ofReal_mul]
  exact mul_nonneg (Real.exp_pos _).le
    (re_inner_apply_nonneg (star_right_conjugate_nonneg hρ (V (τ * s))) x)

/-- **The resolvent maps density operators to density operators.** On a positive trace-class `ρ`
the integrand is trace-norm continuous, so the integral also converges in the trace class, where
the trace is continuous. -/
theorem isDensityOperator_resolvent (τ : ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (V.resolvent τ ρ) := by
  set f : ℝ → TraceClass E := fun s => (Real.exp (-s) : ℂ) •
    ofOperator (V (τ * s) * ρ * star (V (τ * s))) (isTraceClass_mul_mul hρ.isTraceClass)
  have hfc : Continuous f := by
    refine (continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).smul ?_
    exact continuous_conj (U := fun s => V (τ * s)) (fun s => V.norm_le_one _)
      (fun x => (V.continuous_apply x).comp (continuous_const.mul continuous_id))
      hρ.nonneg hρ.isTraceClass
  have hnorm : ∀ s, ‖ofOperator (V (τ * s) * ρ * star (V (τ * s)))
      (isTraceClass_mul_mul hρ.isTraceClass)‖ = 1 := fun s =>
    (hρ.conj (V.star_mul_self (τ * s))).norm_ofOperator
  have hf : IntegrableOn f (Ioi 0) := by
    refine (integrableOn_exp_neg_Ioi 0).mono' hfc.aestronglyMeasurable
      (Eventually.of_forall fun s => ?_)
    rw [norm_smul, hnorm, mul_one, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  set S := ∫ s in Ioi (0 : ℝ), f s
  have hS : S.1 = V.resolvent τ ρ := by
    ext x
    rw [← toOperator_apply, ← toOperator.integral_comp_comm hf,
      ContinuousLinearMap.integral_apply (toOperator.integrable_comp hf), resolvent_apply_apply]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    change ((Real.exp (-s) : ℂ) • (V (τ * s) * ρ * star (V (τ * s)))) x = _
    rw [Complex.coe_smul]
    rfl
  have htc : IsTraceClass (V.resolvent τ ρ) := hS ▸ S.2
  refine ⟨V.resolvent_nonneg τ hρ.nonneg, htc, ?_⟩
  have htr : ∀ s, tracePairing 1 (f s) = (Real.exp (-s) : ℂ) := fun s => by
    rw [map_smul, tracePairing_apply, smul_eq_mul]
    have h := (hρ.conj (V.star_mul_self (τ * s))).trace_eq_one
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

/-! ## D. The resolvent is a projective measurement -/

lemma conj_zero (ρ : E →L[ℂ] E) : V.conj 0 ρ = ρ := by
  rw [conj, V.map_zero, star_one, one_mul, mul_one]

/-- `∫₀^∞ f (s + c) ds = ∫_c^∞ f s ds`. -/
lemma setIntegral_Ioi_comp_add_right {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (c : ℝ) : ∫ s in Ioi (0 : ℝ), f (s + c) = ∫ s in Ioi c, f s := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  conv_rhs => rw [← integral_add_right_eq_self _ c]
  congr 1
  funext s
  simp only [indicator_apply, mem_Ioi, lt_add_iff_pos_left]

/-- **The shifted Laplace integral**: for `τ > 0`,
`T u (Ψ τ ρ) x = e^{u/τ} (Ψ τ ρ x - ∫₀^{u/τ} e^{-s} T (τ s) ρ x ds)`. -/
lemma conj_resolvent_apply {τ : ℝ} (hτ : 0 < τ) (ρ : E →L[ℂ] E) (x : E) (u : ℝ) :
    V.conj u (V.resolvent τ ρ) x =
      Real.exp (u / τ) • (V.resolvent τ ρ x - ∫ s in (0 : ℝ)..u / τ, V.kernel τ ρ x s) := by
  set c := u / τ
  have h1 : V.conj u (V.resolvent τ ρ) x =
      ∫ s in Ioi (0 : ℝ), Real.exp c • V.kernel τ ρ x (s + c) := by
    rw [conj_apply, resolvent_apply_apply,
      ← (V u).integral_comp_comm (V.integrableOn_kernel τ ρ _)]
    congr 1
    funext s
    have hτs : u + τ * s = τ * (s + c) := by
      simp only [c]
      field_simp
      ring
    rw [kernel, kernel, ContinuousLinearMap.map_smul_of_tower, smul_smul, ← Real.exp_add,
      show c + -(s + c) = -s by ring, ← hτs, ← conj_add]
    simp only [conj_apply]
  have hint : ∀ a : ℝ, IntegrableOn (V.kernel τ ρ x) (Ici a) := fun a => by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact ((integrableOn_exp_neg_Ioi a).mul_const _).mono'
      (V.continuous_kernel τ ρ x).aestronglyMeasurable
      (Eventually.of_forall fun s => V.norm_kernel_le τ ρ x s)
  rw [h1, integral_smul, setIntegral_Ioi_comp_add_right (V.kernel τ ρ x) c,
    ← intervalIntegral.integral_Ici_sub_Ici' (hint 0) (hint c), integral_Ici_eq_integral_Ioi,
    integral_Ici_eq_integral_Ioi, resolvent_apply_apply, sub_sub_cancel]

/-- **The derivative of the evolved resolvent**: for `τ > 0`, `u ↦ T u (Ψ τ ρ) x` has derivative
`(Ψ τ ρ x - ρ x) / τ` at `0`. This is `L (Ψ τ ρ) = (Ψ τ ρ - ρ) / τ`, without a domain for `L`. -/
theorem hasDerivAt_conj_resolvent_apply {τ : ℝ} (hτ : 0 < τ) (ρ : E →L[ℂ] E) (x : E) :
    HasDerivAt (fun u => V.conj u (V.resolvent τ ρ) x)
      (τ⁻¹ • (V.resolvent τ ρ x - ρ x)) 0 := by
  set J := fun c : ℝ => ∫ s in (0 : ℝ)..c, V.kernel τ ρ x s
  have hJ : HasDerivAt J (V.kernel τ ρ x 0) (0 / τ) := by
    rw [zero_div]
    exact ((V.continuous_kernel τ ρ x).integral_hasStrictDerivAt 0 0).hasDerivAt
  have hJc : HasDerivAt (fun u => J (u / τ)) (τ⁻¹ • V.kernel τ ρ x 0) 0 := by
    have h := hJ.scomp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).div_const τ)
    simpa [Function.comp_def, div_eq_inv_mul] using h
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (u / τ)) (Real.exp (0 / τ) * (1 / τ)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).div_const τ).exp
  have h := hexp.smul ((hasDerivAt_const (0 : ℝ) (V.resolvent τ ρ x)).sub hJc)
  have hk0 : V.kernel τ ρ x 0 = ρ x := by rw [kernel, mul_zero, conj_zero, neg_zero,
    Real.exp_zero, one_smul]
  have hJ0 : J 0 = 0 := by simp [J]
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun u =>
    V.conj_resolvent_apply hτ ρ x u)).congr_deriv ?_
  simp only [Pi.sub_apply, zero_div, hJ0, hk0, Real.exp_zero, one_smul, one_mul, sub_zero,
    zero_sub, one_div, smul_sub]
  abel

/-- **Eq. (11) without a domain.** For `τ > 0` and self-adjoint `ρ`, an eigenvector `b` of
`σ = Ψ τ ρ` has `⟪b, ρ b⟫ = ⟪b, σ b⟫`. Both sides are derivatives at `0` of
`u ↦ ⟪b, T u σ b⟫`: the first by `hasDerivAt_conj_resolvent_apply`, the second because
`⟪b, (T u σ - σ) (V u b)⟫ = 0` makes the difference quotient `O(u) · o(1) / u`. -/
theorem inner_apply_eq_of_resolvent_apply {τ : ℝ} (hτ : 0 < τ) {ρ : E →L[ℂ] E}
    (hρ : IsSelfAdjoint ρ) {b : E} {μ : ℝ} (hb : V.resolvent τ ρ b = (μ : ℂ) • b) :
    ⟪b, ρ b⟫_ℂ = ⟪b, V.resolvent τ ρ b⟫_ℂ := by
  set σ := V.resolvent τ ρ
  have hσ : IsSelfAdjoint σ := V.isSelfAdjoint_resolvent τ hρ
  set Φ := fun u => V.conj u σ b
  have hΦ := V.hasDerivAt_conj_resolvent_apply hτ ρ b
  set G := fun u => ⟪b, Φ u⟫_ℂ
  have hG : HasDerivAt G ⟪b, τ⁻¹ • (σ b - ρ b)⟫_ℂ 0 := by
    exact ((innerSL ℂ b).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hΦ
  have hΦ0 : Φ 0 = σ b := by simp [Φ, conj_zero]
  -- `G u - G 0 = ⟪Φ u - Φ 0, b - V u b⟫`
  have hdiff : ∀ u, G u - G 0 = ⟪Φ u - Φ 0, b - V u b⟫_ℂ := fun u => by
    have hC : IsSelfAdjoint (V.conj u σ) := V.isSelfAdjoint_conj u hσ
    have hVb : V.conj u σ (V u b) = (μ : ℂ) • V u b := by
      rw [conj_apply, V.apply_neg_apply, hb, map_smul]
    have hσVb : ⟪b, σ (V u b)⟫_ℂ = μ * ⟪b, V u b⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hσ.star_eq, hb, inner_smul_left, Complex.conj_ofReal]
    have hsym : ∀ y, ⟪Φ u - Φ 0, y⟫_ℂ = ⟪b, V.conj u σ y - σ y⟫_ℂ := fun y => by
      rw [hΦ0, inner_sub_left, inner_sub_right, ← ContinuousLinearMap.adjoint_inner_left,
        ← ContinuousLinearMap.adjoint_inner_left (A := σ), ← ContinuousLinearMap.star_eq_adjoint,
        ← ContinuousLinearMap.star_eq_adjoint, hC.star_eq, hσ.star_eq]
    rw [hsym, map_sub, map_sub, inner_sub_right, inner_sub_right, inner_sub_right, hVb,
      inner_smul_right, hσVb]
    simp only [G, hΦ0]
    ring
  -- so `G` has derivative `0`
  have hG0 : HasDerivAt G 0 0 := by
    rw [hasDerivAt_iff_isLittleO]
    have h1 : (fun u => ‖Φ u - Φ 0‖) =O[𝓝 0] fun u => u - 0 := hΦ.isBigO_sub.norm_left
    have h2 : (fun u => ‖b - V u b‖) =o[𝓝 0] fun _ => (1 : ℝ) := by
      rw [Asymptotics.isLittleO_one_iff]
      have h := ((V.continuous_apply b).tendsto 0).const_sub b
      rw [V.map_zero, one_apply_eq_self, sub_self] at h
      simpa using h.norm
    have h3 := h1.mul_isLittleO h2
    simp only [mul_one] at h3
    refine Asymptotics.IsBigO.trans_isLittleO ?_ h3
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun u => ?_)
    rw [sub_zero, smul_zero, sub_zero, hdiff, one_mul, norm_mul, norm_norm, norm_norm]
    exact norm_inner_le_norm _ _
  have h := hG.unique hG0
  rw [← Complex.coe_smul, inner_smul_right, inner_sub_right, mul_eq_zero, sub_eq_zero] at h
  rcases h with h | h
  · exact absurd h (by exact_mod_cast inv_ne_zero hτ.ne')
  · exact h.symm

/-- **The resolvent is a projective measurement.** For `τ > 0` and a density operator `ρ` there
is a Hilbert basis `(bᵢ)` of eigenvectors of `Ψ τ ρ`, with eigenvalues `μᵢ ≥ 0` summing to one,
such that the projectors `Pᵢ = |bᵢ⟩⟨bᵢ|` satisfy `Pᵢ ρ Pᵢ = μᵢ Pᵢ` and `Ψ τ ρ = ∑ᵢ Pᵢ ρ Pᵢ`
strongly. -/
theorem exists_hilbertBasis_resolvent {τ : ℝ} (hτ : 0 < τ) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (μ : w → ℝ),
      (∀ i, V.resolvent τ ρ (b i) = (μ i : ℂ) • b i) ∧ (∀ i, 0 ≤ μ i) ∧ HasSum μ 1 ∧
      (∀ i, proj (b i) * ρ * proj (b i) = (μ i : ℂ) • proj (b i)) ∧
      ∀ x, HasSum (fun i => (proj (b i) * ρ * proj (b i)) x) (V.resolvent τ ρ x) := by
  have hσ := V.isDensityOperator_resolvent τ hρ
  obtain ⟨w, b, μ, -, hb, hμ0, hμ, -, hS⟩ := hσ.isTraceClass.exists_hasSum_rankOne hσ.nonneg
  have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hP : ∀ i, proj (b i) * ρ * proj (b i) = (μ i : ℂ) • proj (b i) := fun i => by
    rw [proj_mul_mul_proj, V.inner_apply_eq_of_resolvent_apply hτ hρ.isSelfAdjoint (hb i), hb i,
      inner_smul_right, inner_self_eq_norm_sq_to_K, hbn i]
    simp
  refine ⟨w, b, μ, hb, hμ0, by rwa [hσ.traceNorm_eq_one] at hμ, hP, fun x => ?_⟩
  have h := (hS.mapL toOperator).mapL (ContinuousLinearMap.apply ℂ E x)
  simp_rw [hP]
  exact h

/-! ## E. The largest outcome on a pure state -/

lemma conj_proj (t : ℝ) (χ : E) : V.conj t (proj χ) = proj (V t χ) :=
  mul_proj_mul_star _ χ

omit [CompleteSpace E] in
/-- `1 - |⟪χ, y⟫|² ≤ ‖y - χ‖²` for unit vectors. -/
lemma one_sub_norm_inner_sq_le {χ y : E} (hχ : ‖χ‖ = 1) (hy : ‖y‖ = 1) :
    1 - ‖⟪y, χ⟫_ℂ‖ ^ 2 ≤ ‖y - χ‖ ^ 2 := by
  rw [@norm_sub_sq ℂ, hχ, hy, Complex.sq_norm, Complex.normSq_apply]
  have hre : RCLike.re ⟪y, χ⟫_ℂ = (⟪y, χ⟫_ℂ).re := rfl
  rw [hre]
  nlinarith [sq_nonneg (1 - (⟪y, χ⟫_ℂ).re)]

/-- `∫₀^∞ s² e^{-s} ds = 2`. -/
lemma integral_exp_neg_mul_sq : ∫ s in Ioi (0 : ℝ), Real.exp (-s) * s ^ 2 = 2 := by
  have h3 : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [← h3, Real.Gamma_eq_integral (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma integrableOn_exp_neg_mul_sq : IntegrableOn (fun s : ℝ => Real.exp (-s) * s ^ 2) (Ioi 0) := by
  refine (Real.GammaIntegral_convergent (s := 3) (by norm_num)).congr_fun (fun x _ => ?_)
    measurableSet_Ioi
  dsimp only
  rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The resolvent of a pure state moves a unit vector by at most as much as the group moves
the state: `‖V u (Ψ τ |χ⟩⟨χ| φ) - Ψ τ |χ⟩⟨χ| φ‖ ≤ ‖V u χ - χ‖`. -/
lemma norm_apply_resolvent_proj_sub_le (τ : ℝ) {χ : E} (hχ : ‖χ‖ = 1) {φ : E} (hφ : ‖φ‖ = 1)
    (u : ℝ) :
    ‖V u (V.resolvent τ (proj χ) φ) - V.resolvent τ (proj χ) φ‖ ≤ ‖V u χ - χ‖ := by
  have hk := V.integrableOn_kernel τ (proj χ) φ
  rw [resolvent_apply_apply, ← (V u).integral_comp_comm hk,
    ← integral_sub ((V u).integrable_comp hk) hk]
  have hb : ∀ s, ‖V u (V.kernel τ (proj χ) φ s) - V.kernel τ (proj χ) φ s‖ ≤
      Real.exp (-s) * ‖V u χ - χ‖ := fun s => by
    set y := V (τ * s) χ
    have hy : ‖y‖ = 1 := by rw [norm_apply, hχ]
    have hc : ‖⟪y, φ⟫_ℂ‖ ≤ 1 := (norm_inner_le_norm y φ).trans (by rw [hy, hφ, one_mul])
    have hV : V u y - y = V (τ * s) (V u χ - χ) := by
      simp only [y, map_sub]
      change (V u * V (τ * s)) χ - _ = (V (τ * s) * V u) χ - _
      rw [← V.map_add, ← V.map_add, add_comm]
    rw [kernel, conj_proj, proj_apply, ContinuousLinearMap.map_smul_of_tower, map_smul, ← smul_sub,
      ← smul_sub, hV, norm_smul, norm_smul, norm_apply, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hc)
      (Real.exp_pos _).le
  refine (norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi 0).mul_const _)
    (Eventually.of_forall hb)).trans_eq ?_
  rw [integral_mul_const, integral_exp_neg_Ioi_zero, one_mul]

/-- **The largest outcome on a pure state.** Let `τ > 0` and `|χ⟩⟨χ|` be a pure state. In the
eigenbasis of `σ = Ψ τ |χ⟩⟨χ|` that realizes it as a projective measurement, the largest eigenvalue
`q = μ i₀` lies in `(0, 1]`. If the orbit of `χ` is Lipschitz, `‖V u χ - χ‖ ≤ D |u|`, then
`1 - q ≤ 2 D² τ²`, and the orbit of the eigenvector `b i₀` is Lipschitz with constant `D / q`. -/
theorem exists_max_resolvent_proj {τ : ℝ} (hτ : 0 < τ) {χ : E} (hχ : ‖χ‖ = 1) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (μ : w → ℝ) (i₀ : w),
      (∀ i, 0 ≤ μ i) ∧ HasSum μ 1 ∧
      (∀ i, proj (b i) * proj χ * proj (b i) = (μ i : ℂ) • proj (b i)) ∧
      (∀ x, HasSum (fun i => (proj (b i) * proj χ * proj (b i)) x)
        (V.resolvent τ (proj χ) x)) ∧
      (∀ i, μ i ≤ μ i₀) ∧ 0 < μ i₀ ∧ μ i₀ ≤ 1 ∧
      ∀ D : ℝ, (∀ u, ‖V u χ - χ‖ ≤ D * |u|) →
        1 - 2 * D ^ 2 * τ ^ 2 ≤ μ i₀ ∧ ∀ u, ‖V u (b i₀) - b i₀‖ ≤ D / μ i₀ * |u| := by
  have hχd := isDensityOperator_proj hχ
  obtain ⟨w, b, μ, hb, hμ0, hμ, hP, hsum⟩ := V.exists_hilbertBasis_resolvent hτ hχd
  obtain ⟨i₀, hmax⟩ := exists_forall_le_of_hasSum hμ0 hμ
  set σ := V.resolvent τ (proj χ)
  set q := μ i₀
  have hq0 : 0 < q := by
    by_contra! h
    have : μ = 0 := funext fun i => le_antisymm ((hmax i).trans h) (hμ0 i)
    rw [this] at hμ
    exact one_ne_zero (hμ.unique hasSum_zero)
  have hq1 : q ≤ 1 := by simpa using le_hasSum hμ i₀ fun j _ => hμ0 j
  refine ⟨w, b, μ, i₀, hμ0, hμ, hP, hsum, hmax, hq0, hq1, fun D hD => ⟨?_, fun u => ?_⟩⟩
  · -- the largest eigenvalue is at least `⟪χ, σ χ⟫ ≥ 1 - 2 D² τ²`
    have hD0 : 0 ≤ D := by
      have h := (norm_nonneg _).trans (hD 1)
      rwa [abs_one, mul_one] at h
    have hle : (⟪χ, σ χ⟫_ℂ).re ≤ q := by
      have h := hasSum_le (fun i => mul_le_mul_of_nonneg_right (hmax i) (sq_nonneg _))
        (hasSum_re_inner_of_eigen b hb χ) ((hasSum_norm_sq_inner_basis b χ).mul_left q)
      rwa [hχ, one_pow, mul_one] at h
    have hint := V.integrable_inner_conj τ (proj χ) χ χ
    have hpt : ∀ s, Real.exp (-s) * (1 - D ^ 2 * τ ^ 2 * s ^ 2) ≤
        RCLike.re ((Real.exp (-s) : ℂ) * ⟪χ, V.conj (τ * s) (proj χ) χ⟫_ℂ) := fun s => by
      rw [conj_proj, inner_proj_apply, ← Complex.ofReal_mul, RCLike.re_to_complex,
        Complex.ofReal_re]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      have h1 := one_sub_norm_inner_sq_le hχ (V.norm_apply (τ * s) χ ▸ hχ :
        ‖V (τ * s) χ‖ = 1)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (hD (τ * s)) 2
      rw [mul_pow, sq_abs, mul_pow] at h2
      linarith
    have hlow : ∫ s in Ioi (0 : ℝ), Real.exp (-s) * (1 - D ^ 2 * τ ^ 2 * s ^ 2) =
        1 - 2 * D ^ 2 * τ ^ 2 := by
      have h : ∀ s, Real.exp (-s) * (1 - D ^ 2 * τ ^ 2 * s ^ 2) =
          Real.exp (-s) - D ^ 2 * τ ^ 2 * (Real.exp (-s) * s ^ 2) := fun s => by ring
      simp_rw [h]
      rw [integral_sub (integrableOn_exp_neg_Ioi 0) (integrableOn_exp_neg_mul_sq.const_mul _),
        integral_const_mul, integral_exp_neg_Ioi_zero, integral_exp_neg_mul_sq]
      ring
    have hmono := setIntegral_mono_on (((integrableOn_exp_neg_Ioi 0).sub
      (integrableOn_exp_neg_mul_sq.const_mul (D ^ 2 * τ ^ 2))).congr_fun
        (fun s _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi) hint.re
      measurableSet_Ioi fun s _ => hpt s
    rw [hlow, integral_re hint, ← inner_resolvent_apply, RCLike.re_to_complex] at hmono
    linarith
  · -- the eigenvector moves by at most `‖V u χ - χ‖ / q`
    have hφ : ‖b i₀‖ = 1 := b.orthonormal.1 i₀
    have hσφ : σ (b i₀) = (q : ℂ) • b i₀ := hb i₀
    have h := V.norm_apply_resolvent_proj_sub_le τ hχ hφ u
    rw [hσφ, map_smul, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hq0] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hq0, mul_comm]
    exact h.trans (hD u)

/-! ## F. Lipschitz orbits -/

/-- A vector with a right derivative `v` of its orbit at `0` has a Lipschitz orbit:
`‖V u ψ - ψ‖ ≤ ‖v‖ |u|`. -/
theorem norm_apply_sub_le_of_hasDerivWithinAt {ψ v : E}
    (h : HasDerivWithinAt (fun t => V t ψ) v (Ici 0) 0) (u : ℝ) :
    ‖V u ψ - ψ‖ ≤ ‖v‖ * |u| := by
  have hpos : ∀ u, 0 ≤ u → ‖V u ψ - ψ‖ ≤ ‖v‖ * u := fun u hu => by
    have hderiv : ∀ t ∈ Ico (0 : ℝ) u, HasDerivWithinAt (fun t => V t ψ) (V t v) (Ici t) t := by
      intro t _
      have hg : HasDerivWithinAt (fun r => V (r - t) ψ) v (Ici t) t := by
        have h0 : HasDerivWithinAt (fun t => V t ψ) v (Ici 0) (t - t) := by rwa [sub_self]
        have hlin : HasDerivWithinAt (fun r : ℝ => r - t) 1 (Ici t) t :=
          ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
        have h' := HasDerivWithinAt.scomp (h := fun r : ℝ => r - t) t h0 hlin
          fun r (hr : t ≤ r) => (sub_nonneg.mpr hr : (0 : ℝ) ≤ r - t)
        simpa [Function.comp_def] using h'
      have hf := ((V t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hg
      refine (hf.congr (fun r _ => ?_) ?_)
      · change V r ψ = (V t * V (r - t)) ψ
        rw [← V.map_add, add_sub_cancel]
      · change V t ψ = (V t * V (t - t)) ψ
        rw [← V.map_add, add_sub_cancel]
    have hcont : ContinuousOn (fun t => V t ψ) (Icc 0 u) := (V.continuous_apply ψ).continuousOn
    have h' := norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv
      (fun t _ => (V.norm_apply t v).le) u (right_mem_Icc.mpr hu)
    simpa [V.map_zero] using h'
  rcases le_total 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    exact hpos u hu
  · have h' := hpos (-u) (neg_nonneg.mpr hu)
    calc ‖V u ψ - ψ‖ = ‖V (-u) (V u ψ - ψ)‖ := (V.norm_apply _ _).symm
      _ = ‖V (-u) ψ - ψ‖ := by rw [map_sub, V.apply_neg_apply, norm_sub_rev]
      _ ≤ ‖v‖ * |u| := by rwa [abs_of_nonpos hu]

/-- **The domain of the generator has Lipschitz orbits**: for `ψ` in the domain of the forward
Hamiltonian `H` of `V` (with `ħ = 1`), `‖V u ψ - ψ‖ ≤ ‖H ψ‖ |u|`. -/
theorem norm_apply_sub_le_of_mem_domain (ψ : (forwardHamiltonian V.toFun 1).domain) (u : ℝ) :
    ‖V u ψ - ψ‖ ≤ ‖forwardHamiltonian V.toFun 1 ψ‖ * |u| := by
  have h := hasDerivWithinAt_forwardHamiltonian one_ne_zero ψ
  refine (V.norm_apply_sub_le_of_hasDerivWithinAt h u).trans_eq ?_
  rw [norm_smul, Complex.ofReal_one, mul_one, norm_inv, Complex.norm_I, inv_one, one_mul]

/-! ## G. Complete positivity -/

/-- Conjugation by `V t` is completely positive: it is a ⋆-automorphism. -/
lemma conj_cstarMatrix_nonneg (t : ℝ) {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) (E →L[ℂ] E)}
    (hM : 0 ≤ M) : 0 ≤ M.map (V.conj t) := by
  have h : 0 ≤ M.map (Unitary.conjStarAlgAut ℂ (E →L[ℂ] E) ⟨V t, V.mem_unitary t⟩) :=
    CompletelyPositiveMapClass.map_cstarMatrix_nonneg' _ k M hM
  convert h using 3
  funext ρ
  rw [Unitary.conjStarAlgAut_apply]
  rfl

/-- The resolvent applied to the entries of a positive matrix gives a positive matrix: in
`∑ᵢⱼ ⟪xᵢ, Ψ τ Mᵢⱼ xⱼ⟫ = ∫₀^∞ e^{-s} ∑ᵢⱼ ⟪xᵢ, T (τ s) Mᵢⱼ xⱼ⟫ ds` the integrand is nonnegative,
since `T (τ s)` is completely positive. -/
theorem resolvent_cstarMatrix_nonneg (τ : ℝ) {k : ℕ}
    {M : CStarMatrix (Fin k) (Fin k) (E →L[ℂ] E)} (hM : 0 ≤ M) : 0 ≤ M.map (V.resolvent τ) := by
  rw [cstarMatrix_nonneg_iff]
  intro x
  set f : Fin k → Fin k → ℝ → ℂ :=
    fun i j s => (Real.exp (-s) : ℂ) * ⟪x i, V.conj (τ * s) (M i j) (x j)⟫_ℂ
  have hint : ∀ i j, Integrable (f i j) (volume.restrict (Ioi 0)) := fun i j =>
    V.integrable_inner_conj τ (M i j) (x j) (x i)
  have hf : ∀ s, 0 ≤ ∑ i, ∑ j, f i j s := fun s => by
    simp_rw [f, ← Finset.mul_sum]
    exact mul_nonneg (Complex.zero_le_real.mpr (Real.exp_pos _).le)
      (cstarMatrix_nonneg_iff.mp (V.conj_cstarMatrix_nonneg (τ * s) hM) x)
  have hsum : ∑ i, ∑ j, ⟪x i, M.map (V.resolvent τ) i j (x j)⟫_ℂ =
      ∫ s in Ioi (0 : ℝ), ∑ i, ∑ j, f i j s := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun j _ => V.inner_resolvent_apply τ (M i j) (x j) (x i)
  have hre : ∀ s, ∑ i, ∑ j, f i j s = ((∑ i, ∑ j, f i j s).re : ℂ) := fun s =>
    Complex.eq_re_of_ofReal_le (r := 0) (by simpa using hf s)
  rw [hsum, integral_congr_ae (Eventually.of_forall hre), integral_complex_ofReal]
  exact Complex.zero_le_real.mpr (setIntegral_nonneg measurableSet_Ioi fun s _ =>
    (Complex.nonneg_iff.mp (hf s)).1)

/-- **The resolvent is completely positive**: `Ψ τ` as a completely positive map. -/
def resolventCP (τ : ℝ) : (E →L[ℂ] E) →CP (E →L[ℂ] E) where
  toLinearMap := (V.resolvent τ : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E)
  map_cstarMatrix_nonneg' _ _ hM := V.resolvent_cstarMatrix_nonneg τ hM

@[simp]
lemma coe_resolventCP (τ : ℝ) : ⇑(V.resolventCP τ) = V.resolvent τ :=
  rfl

end QuantumMechanics.StronglyContinuousUnitaryGroup
