/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DephasingFlow
public import ForPhyslib.QuantumMechanics.SpectralCutoff
public import Mathlib.Analysis.Convex.Integral
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.SpectralIntegral.SpecTheorem

/-!
# The dephasing semigroup of an unbounded observable

## i. Overview

Let `T` be a self-adjoint, in general unbounded, operator with PhyslibAlpha spectral measure `μS`
(`DomainAwareSelfAdjointSpectralTheorem T μS`), and suppose `T` has pure point spectrum: `μS` is
atomic, `∑ₐ μS({a}) = 1` strongly (`IsAtomic`). Then `μS({a})` projects onto eigenvectors of `T`
with eigenvalue `a`, and the eigenprojections form a resolution of the identity.

The dephasing equation `ρ' = T ρ T - ½ {T², ρ}` only makes sense on a domain. On the spectral window
`[-m, m]`, `T` is the bounded operator `X_m = ∫ 1_{[-m, m]}(r) r dμS(r)`
(`apply_spectralCutoffProj_apply`, from PhyslibAlpha's maximal spectral integral). So for operators
living on the window (`IsWindowed`), the equation is the bounded one with generator `X_m`.

The Gaussian average `G_t(ρ) = ∫ e^{isT} ρ e^{-isT} dN(0, t)(s)`, with PhyslibAlpha's unitary group
`e^{isT}` (`expIntegral`), extends these solutions. The integrand is only strongly continuous in
`s`, so the integral is taken in the trace class, where conjugation by a strongly continuous family
of contractions is continuous. The characteristic function of `N(0, t)` gives the blocks
`Pₐ G_t(ρ) P_b = e^{-t (a - b)² / 2} Pₐ ρ P_b`. Hence:
* `G_t` solves the bounded equation on every window, and contracts the trace norm; since the
  windowed operators are dense, it is the only extension of the windowed solutions that is
  continuous in trace norm (`IsAtomic.eq_of_isDephasingExtension`);
* `G_t` maps density operators to density operators: an average of conjugations is positive, and
  the diagonal blocks, hence the trace, are fixed;
* `G_t(ρ) → ∑ₐ Pₐ ρ Pₐ` in trace norm, by the finite truncation argument of the bounded case.

The first part (section A) is stated for any resolution of the identity `Pᵢ`, real `xᵢ` and
strongly continuous family of contractions `U s` with `Pᵢ U s = e^{isxᵢ} Pᵢ` (`IsPhaseGroup`).

## ii. Key results

- `QuantumMechanics.IsPhaseGroup.tendsto_traceENorm_gaussianConj`: equilibration in trace norm.
- `QuantumMechanics.IsAtomic.isPhaseGroup`: `e^{isT}` is a phase group for the eigenprojections.
- `QuantumMechanics.IsAtomic.commute_iff`: commuting with every `μS(S)` means commuting with every
  eigenprojection.
- `QuantumMechanics.apply_spectralCutoffProj_apply`, `QuantumMechanics.apply_pointProj_apply`: `T`
  on spectral windows and on eigenvectors.
- `QuantumMechanics.IsAtomic.hasDerivAt_dephasingSemigroup`: the semigroup solves the dephasing
  equation on spectral windows.
- `QuantumMechanics.IsAtomic.isDephasingExtension`,
  `QuantumMechanics.IsAtomic.eq_of_isDephasingExtension`: it is the unique extension, continuous
  in trace norm.
- `QuantumMechanics.IsAtomic.isDensityOperator_dephasingSemigroup`,
  `QuantumMechanics.IsAtomic.dephasingSemigroup_add`,
  `QuantumMechanics.IsAtomic.tendsto_traceENorm_dephasingSemigroup`.

## iii. Table of contents

- A. Gaussian averages of a phase group
- B. The spectral measure of an unbounded observable
- C. The dephasing equation on spectral windows

## iv. References

- K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer (2012), Ch. 4–5.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder NNReal
open Filter Topology Set ContinuousLinearMap MeasureTheory ProbabilityTheory
  ProbabilisticTheory ProbabilisticTheory.TraceClass Complex

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

/-! ## A. Gaussian averages of a phase group -/

/-- `U` is a strongly continuous family of contractions that multiplies the range of each `Pᵢ` by
the phase `e^{isxᵢ}`: the unitary group `e^{isX}` of `X = ∑ᵢ xᵢ Pᵢ`, bounded or not. -/
structure IsPhaseGroup (P : ι → E →L[ℂ] E) (x : ι → ℝ) (U : ℝ → E →L[ℂ] E) : Prop where
  isResolutionOfIdentity : IsResolutionOfIdentity P
  norm_le : ∀ s, ‖U s‖ ≤ 1
  continuous_apply : ∀ v, Continuous fun s => U s v
  mul_eq : ∀ s i, P i * U s = Complex.exp (s * I * x i) • P i

/-- The Gaussian average `G_v(ρ) = ∫ U s ρ (U s)† dN(0, v)(s)`. -/
def gaussianConj (U : ℝ → E →L[ℂ] E) (v : ℝ≥0) (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  ∫ s, U s * ρ * star (U s) ∂(gaussianReal 0 v)

namespace IsPhaseGroup

variable {P : ι → E →L[ℂ] E} {x : ι → ℝ} {U : ℝ → E →L[ℂ] E} (hU : IsPhaseGroup P x U)
include hU

lemma star_mul (s : ℝ) (j : ι) : star (U s) * P j = Complex.exp (-(s * I * x j)) • P j := by
  have h := congrArg star (hU.mul_eq s j)
  rw [StarMul.star_mul, hU.isResolutionOfIdentity.star_eq, star_smul,
    hU.isResolutionOfIdentity.star_eq] at h
  rw [h, Complex.star_def, ← Complex.exp_conj]
  congr 2
  simp

/-- The blocks of a conjugation by `U s`. -/
lemma mul_conj_mul (s : ℝ) (i j : ι) (A : E →L[ℂ] E) :
    P i * (U s * A * star (U s)) * P j =
      Complex.exp ((x i - x j : ℝ) * s * I) • (P i * A * P j) := by
  rw [show P i * (U s * A * star (U s)) * P j = (P i * U s) * A * (star (U s) * P j) by
      simp only [mul_assoc], hU.mul_eq, hU.star_mul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma traceNorm_conj_le {T : E →L[ℂ] E} (hT : IsTraceClass T) (s : ℝ) :
    ‖ofOperator (U s * T * star (U s)) (isTraceClass_mul_mul hT)‖ ≤ traceNorm T hT := by
  rw [norm_eq_traceNorm]
  have h2 : ‖star (U s)‖ ≤ 1 := by rw [norm_star]; exact hU.norm_le s
  calc _ ≤ ‖U s‖ * traceNorm T hT * ‖star (U s)‖ := traceNorm_mul_mul_le hT _
    _ ≤ 1 * traceNorm T hT * 1 := by
        have h0 := traceNorm_nonneg T hT
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hU.norm_le s) h0) h2 (norm_nonneg _)
          (by positivity)
    _ = traceNorm T hT := by ring

/-- The integrand, as a trace-class operator, is integrable. -/
lemma integrable_conj (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    Integrable (fun s => ofOperator (U s * ρ * star (U s)) (isTraceClass_mul_mul hρ))
      (gaussianReal 0 v) :=
  (integrable_const (traceNorm ρ hρ)).mono'
    (continuous_conj hU.norm_le hU.continuous_apply hρ0 hρ).aestronglyMeasurable
    (ae_of_all _ (hU.traceNorm_conj_le hρ))

/-- The Gaussian average is the integral computed in the trace class. -/
lemma gaussianConj_eq (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    gaussianConj U v ρ =
      (∫ s, ofOperator (U s * ρ * star (U s)) (isTraceClass_mul_mul hρ) ∂(gaussianReal 0 v)).1 := by
  rw [← toOperator_apply, ← toOperator.integral_comp_comm (hU.integrable_conj v hρ0 hρ)]
  rfl

lemma integrable_conj_op (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    Integrable (fun s => U s * ρ * star (U s)) (gaussianReal 0 v) :=
  toOperator.integrable_comp (hU.integrable_conj v hρ0 hρ)

lemma isTraceClass_gaussianConj (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    IsTraceClass (gaussianConj U v ρ) := by
  rw [hU.gaussianConj_eq v hρ0 hρ]
  exact isTraceClass_coe _

lemma gaussianConj_nonneg (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    0 ≤ gaussianConj U v ρ := by
  have hc : Convex ℝ {A : E →L[ℂ] E | 0 ≤ A} := by
    intro A hA B hB a b ha hb _
    simp only [mem_ofPred_eq] at hA hB ⊢
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    exact add_nonneg (smul_nonneg (by exact_mod_cast ha) hA) (smul_nonneg (by exact_mod_cast hb) hB)
  exact Convex.integral_mem hc CStarAlgebra.isClosed_nonneg
    (ae_of_all _ fun s => star_right_conjugate_nonneg hρ0 (U s)) (hU.integrable_conj_op v hρ0 hρ)

/-- **The blocks of the Gaussian average**: `Pᵢ G_v(ρ) Pⱼ = e^{-v (xᵢ - xⱼ)² / 2} Pᵢ ρ Pⱼ`. -/
theorem mul_gaussianConj_mul (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ)
    (i j : ι) :
    P i * gaussianConj U v ρ * P j = Real.exp (-(v * ((x i - x j) ^ 2 / 2))) • (P i * ρ * P j) := by
  set M : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
    (mul ℂ (E →L[ℂ] E) (P i)).comp ((mul ℂ (E →L[ℂ] E)).flip (P j))
  have hM : ∀ A, M A = P i * A * P j := fun A => by
    simp only [M, comp_apply, flip_apply, mul_apply', mul_assoc]
  rw [← hM, gaussianConj, ← M.integral_comp_comm (hU.integrable_conj_op v hρ0 hρ)]
  simp_rw [hM, hU.mul_conj_mul]
  rw [integral_smul_const, ← charFun_apply_real, charFun_gaussianReal]
  have h : Complex.exp ((x i - x j : ℝ) * (0 : ℝ) * I - (v : ℝ) * ((x i - x j : ℝ) : ℂ) ^ 2 / 2) =
      ((Real.exp (-(v * ((x i - x j) ^ 2 / 2))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h, Complex.coe_smul]

/-- `G_0 = id`. -/
theorem gaussianConj_zero {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    gaussianConj U 0 ρ = ρ :=
  hU.isResolutionOfIdentity.ext_block fun i j => by
    rw [hU.mul_gaussianConj_mul 0 hρ0 hρ]
    simp

/-- **The semigroup property** `G_{v + w} = G_v ∘ G_w`. -/
theorem gaussianConj_add (v w : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    gaussianConj U (v + w) ρ = gaussianConj U v (gaussianConj U w ρ) :=
  hU.isResolutionOfIdentity.ext_block fun i j => by
    rw [hU.mul_gaussianConj_mul _ hρ0 hρ,
      hU.mul_gaussianConj_mul _ (hU.gaussianConj_nonneg w hρ0 hρ)
      (hU.isTraceClass_gaussianConj w hρ0 hρ), hU.mul_gaussianConj_mul _ hρ0 hρ, smul_smul,
      ← Real.exp_add]
    congr 2
    push_cast
    ring

/-- The diagonal blocks are fixed, so the Gaussian average has the same pinching. -/
lemma pinching_gaussianConj (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    hU.isResolutionOfIdentity.pinching (gaussianConj U v ρ) =
      hU.isResolutionOfIdentity.pinching ρ :=
  hU.isResolutionOfIdentity.ext_block fun i j => by
    rw [hU.isResolutionOfIdentity.mul_pinching_mul, hU.isResolutionOfIdentity.mul_pinching_mul]
    split_ifs with hij
    · rw [hij, hU.mul_gaussianConj_mul v hρ0 hρ]
      simp
    · rfl

/-- **The Gaussian average maps density operators to density operators.** -/
theorem isDensityOperator_gaussianConj (v : ℝ≥0) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (gaussianConj U v ρ) := by
  have h0 := hU.gaussianConj_nonneg v hρ.nonneg hρ.isTraceClass
  refine isDensityOperator_iff.mpr ⟨h0, ?_⟩
  rw [← hU.isResolutionOfIdentity.posTrace_pinching h0,
    hU.pinching_gaussianConj v hρ.nonneg hρ.isTraceClass,
    hU.isResolutionOfIdentity.posTrace_pinching hρ.nonneg, hρ.posTrace_eq_one]

/-- **The Gaussian average contracts the trace norm** on differences of positive trace-class
operators. -/
theorem traceENorm_gaussianConj_sub_le (v : ℝ≥0) {ρ σ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ)
    (hρ : IsTraceClass ρ) (hσ0 : 0 ≤ σ) (hσ : IsTraceClass σ) :
    traceENorm (gaussianConj U v ρ - gaussianConj U v σ) ≤ traceENorm (ρ - σ) := by
  have hρσ : IsTraceClass (ρ - σ) := by
    rw [sub_eq_add_neg]
    exact isTraceClass_add hρ (isTraceClass_neg hσ)
  set f : ℝ → TraceClass E := fun s =>
    ofOperator (U s * ρ * star (U s)) (isTraceClass_mul_mul hρ)
  set g : ℝ → TraceClass E := fun s =>
    ofOperator (U s * σ * star (U s)) (isTraceClass_mul_mul hσ)
  have hfi : Integrable f (gaussianReal 0 v) := hU.integrable_conj v hρ0 hρ
  have hgi : Integrable g (gaussianReal 0 v) := hU.integrable_conj v hσ0 hσ
  have hfg : ∀ s, f s - g s =
      ofOperator (U s * (ρ - σ) * star (U s)) (isTraceClass_mul_mul hρσ) :=
    fun s => Subtype.ext (by
      change (f s).1 - (g s).1 = _
      simp [f, g, mul_sub, sub_mul])
  rw [hU.gaussianConj_eq v hρ0 hρ, hU.gaussianConj_eq v hσ0 hσ]
  change traceENorm ((∫ s, f s ∂(gaussianReal 0 v)) - ∫ s, g s ∂(gaussianReal 0 v)).1 ≤ _
  rw [← integral_sub hfi hgi, traceENorm_eq_ofReal (isTraceClass_coe _), ← norm_eq_traceNorm,
    traceENorm_eq_ofReal hρσ]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := MeasureTheory.norm_integral_le_of_norm_le_const (μ := gaussianReal 0 v)
    (f := fun s => f s - g s) (C := traceNorm (ρ - σ) hρσ)
    (ae_of_all _ fun s => by rw [hfg]; exact hU.traceNorm_conj_le hρσ s)
  simpa using h

/-- **Equilibration in trace norm**: for distinct `xᵢ`, `G_t(ρ) → ∑ᵢ Pᵢ ρ Pᵢ` in trace norm for
every density operator `ρ`. The off-diagonal blocks of a finite truncation decay, and the
truncation error is uniform in `t` by the contraction. -/
theorem tendsto_traceENorm_gaussianConj (hx : Function.Injective x) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    Tendsto (fun t : ℝ => traceENorm (gaussianConj U t.toNNReal ρ -
      hU.isResolutionOfIdentity.pinching ρ)) atTop (𝓝 0) := by
  classical
  have hP := hU.isResolutionOfIdentity
  have hPρ := hP.isDensityOperator_pinching hρ
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη0, hηε⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal (3 * η) ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · refine ⟨ε.toReal / 3, by have := ENNReal.toReal_pos hε.ne' hne; positivity, ?_⟩
      rw [mul_div_cancel₀ _ (by norm_num : (3 : ℝ) ≠ 0), ENNReal.ofReal_toReal hne]
  have hη := ENNReal.ofReal_pos.mpr hη0
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
  set a : ℝ → ι × ι → ℝ := fun t p =>
    Real.exp (-(t * ((x p.1 - x p.2) ^ 2 / 2))) - if p.1 = p.2 then 1 else 0
  have ha : ∀ p : ι × ι, Tendsto (fun t => ENNReal.ofReal |a t p|) atTop (𝓝 0) := fun p => by
    rw [← ENNReal.ofReal_zero]
    refine ENNReal.tendsto_ofReal ?_
    by_cases h : p.1 = p.2
    · simp [a, h]
    · have hc0 : 0 < (x p.1 - x p.2) ^ 2 / 2 := by
        have : x p.1 - x p.2 ≠ 0 := sub_ne_zero.mpr (hx.ne h)
        positivity
      have hlim : Tendsto (fun t => Real.exp (-(t * ((x p.1 - x p.2) ^ 2 / 2)))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hc0))
      simpa [a, h] using hlim.abs
  have hsum := tendsto_finsetSum (F ×ˢ F) fun p _ => ha p
  simp only [Finset.sum_const_zero] at hsum
  filter_upwards [hsum.eventually (gt_mem_nhds hη), eventually_ge_atTop 0] with t ht ht0
  have hfin : gaussianConj U t.toNNReal σ - hP.pinching σ =
      ∑ p ∈ F ×ˢ F, a t p • (P p.1 * ρ * P p.2) :=
    hP.ext_block fun k l => by
      rw [mul_sub, sub_mul, hU.mul_gaussianConj_mul _ hσ0 hσtc, hP.mul_pinching_mul,
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
  have hsplit : gaussianConj U t.toNNReal ρ - hP.pinching ρ =
      (gaussianConj U t.toNNReal ρ - gaussianConj U t.toNNReal σ) +
        (gaussianConj U t.toNNReal σ - hP.pinching σ) +
        (Q * hP.pinching ρ * Q - hP.pinching ρ) := by
    rw [hpin]
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
  calc traceENorm (gaussianConj U t.toNNReal ρ - hP.pinching ρ)
      ≤ traceENorm (gaussianConj U t.toNNReal ρ - gaussianConj U t.toNNReal σ) +
          traceENorm (gaussianConj U t.toNNReal σ - hP.pinching σ) +
          traceENorm (Q * hP.pinching ρ * Q - hP.pinching ρ) := by
        rw [hsplit]
        exact (traceENorm_add_le _ _).trans (by gcongr; exact traceENorm_add_le _ _)
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal η + ENNReal.ofReal η := by
        gcongr
        · refine (hU.traceENorm_gaussianConj_sub_le _ hρ.nonneg hρ.isTraceClass hσ0
            hσtc).trans ?_
          rw [traceENorm_sub_comm]
          exact hF1.le
        · rw [hfin]
          exact ((traceENorm_sum_le _ _).trans (Finset.sum_le_sum hterm)).trans ht.le
    _ = ENNReal.ofReal (3 * η) := by
        rw [← ENNReal.ofReal_add hη0.le hη0.le, ← ENNReal.ofReal_add (by positivity) hη0.le]
        ring_nf
    _ ≤ ε := hηε

end IsPhaseGroup

/-! ## B. The spectral measure of an unbounded observable -/

section Spectral

open ProbabilisticTheory.QuantumMechanics ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure

variable (μS : WOTSpectralMeasure ℝ E)

lemma singleton_mul_boundedIntegral {f : ℝ → ℂ} (hf : Measurable f) (hb : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (a : ℝ) : μS {a} * boundedIntegral μS f hf hb = f a • μS {a} := by
  rw [← boundedIntegral_indicator μS (measurableSet_singleton a), ← boundedIntegral_mul,
    ← boundedIntegral_smul]
  exact boundedIntegral_congr μS _ _ _ _ fun r => by
    by_cases hr : r = a
    · subst hr; simp
    · simp [hr]

lemma boundedIntegral_mul_singleton {f : ℝ → ℂ} (hf : Measurable f) (hb : ∃ C, ∀ r, ‖f r‖ ≤ C)
    (a : ℝ) : boundedIntegral μS f hf hb * μS {a} = f a • μS {a} := by
  rw [← boundedIntegral_indicator μS (measurableSet_singleton a), ← boundedIntegral_mul,
    ← boundedIntegral_smul]
  exact boundedIntegral_congr μS _ _ _ _ fun r => by
    by_cases hr : r = a
    · subst hr; simp
    · simp [hr]

/-- The eigenprojection `μS({a})`. -/
def pointProj (a : ℝ) : E →L[ℂ] E := (μS {a}).toCLM

/-- The unitary group `e^{isT} = ∫ e^{isr} dμS(r)` (PhyslibAlpha's `expIntegral`). -/
def phaseUnitary (s : ℝ) : E →L[ℂ] E := (expIntegral μS s).toCLM

/-- `μS` is atomic, `∑ₐ μS({a}) = 1` strongly: the operator it resolves has pure point spectrum. -/
def IsAtomic : Prop := ∀ v, HasSum (fun a => pointProj μS a v) v

lemma isStarProjection_pointProj (a : ℝ) : IsStarProjection (pointProj μS a) := by
  have h := μS.isStarProjection {a}
  exact ⟨congrArg ContinuousLinearMapWOT.toCLM h.isIdempotentElem.eq,
    congrArg ContinuousLinearMapWOT.toCLM h.isSelfAdjoint.star_eq⟩

/-- The eigenprojections of an atomic spectral measure form a resolution of the identity. -/
lemma IsAtomic.isResolutionOfIdentity {μS : WOTSpectralMeasure ℝ E} (h : IsAtomic μS) :
    IsResolutionOfIdentity (pointProj μS) where
  isStarProjection := isStarProjection_pointProj μS
  mul_eq_zero a b hab := by
    change (μS {a} * μS {b}).toCLM = 0
    rw [μS.comp_of_disjoint (disjoint_singleton.mpr hab) (measurableSet_singleton _)
      (measurableSet_singleton _)]
    rfl
  hasSum := h

lemma phaseUnitary_mem_unitary (s : ℝ) : phaseUnitary μS s ∈ unitary (E →L[ℂ] E) := by
  have h := Unitary.mem_iff.mp (expIntegral_mem_unitary μS s)
  exact Unitary.mem_iff.mpr ⟨congrArg ContinuousLinearMapWOT.toCLM h.1,
    congrArg ContinuousLinearMapWOT.toCLM h.2⟩

lemma norm_phaseUnitary_le (s : ℝ) : ‖phaseUnitary μS s‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun v => by
    rw [norm_map_of_mem_unitary (phaseUnitary_mem_unitary μS s), one_mul]

lemma pointProj_mul_phaseUnitary (s a : ℝ) :
    pointProj μS a * phaseUnitary μS s = Complex.exp (s * I * a) • pointProj μS a := by
  change (μS {a} * expIntegral μS s).toCLM = _
  rw [expIntegral, singleton_mul_boundedIntegral]
  change expFunction s a • (μS {a}).toCLM = _
  congr 1
  simp only [expFunction]
  congr 1
  push_cast
  ring

/-- `e^{isT}` multiplies the eigenspace of `a` by `e^{isa}`. -/
theorem IsAtomic.isPhaseGroup {μS : WOTSpectralMeasure ℝ E} (h : IsAtomic μS) :
    IsPhaseGroup (pointProj μS) id (phaseUnitary μS) where
  isResolutionOfIdentity := h.isResolutionOfIdentity
  norm_le := norm_phaseUnitary_le μS
  continuous_apply v := expIntegral_continuous μS v
  mul_eq s a := pointProj_mul_phaseUnitary μS s a

/-- **An operator commutes with the observable** (with every spectral projection `μS(S)`) iff it
commutes with every eigenprojection. -/
theorem IsAtomic.commute_iff {μS : WOTSpectralMeasure ℝ E} (h : IsAtomic μS) {σ : E →L[ℂ] E} :
    (∀ S, Commute σ (μS S).toCLM) ↔ ∀ a, Commute σ (pointProj μS a) := by
  classical
  refine ⟨fun hc a => hc {a}, fun hc S => ?_⟩
  by_cases hS : MeasurableSet S
  · set M := (μS S).toCLM
    have hMP : ∀ a, M * pointProj μS a = if a ∈ S then pointProj μS a else 0 := fun a => by
      change (μS S * μS {a}).toCLM = _
      rw [μS.comp_eq_of_inter hS (measurableSet_singleton a)]
      split_ifs with ha
      · rw [inter_eq_right.mpr (singleton_subset_iff.mpr ha)]; rfl
      · rw [inter_singleton_eq_empty.mpr ha, μS.empty]; rfl
    have hM : ∀ w, HasSum (fun a => if a ∈ S then pointProj μS a w else 0) (M w) := fun w => by
      convert M.hasSum (h w) using 1
      funext a
      change _ = (M * pointProj μS a) w
      rw [hMP]
      split_ifs <;> rfl
    ext v
    have h1 := σ.hasSum (hM v)
    have h2 := hM (σ v)
    have e : ∀ a, σ (if a ∈ S then pointProj μS a v else 0) =
        if a ∈ S then pointProj μS a (σ v) else 0 := fun a => by
      split_ifs
      · exact congrArg (fun T => T v) (hc a).eq
      · exact map_zero σ
    simp only [e] at h1
    exact h1.unique h2
  · rw [μS.apply_eq_zero_of_not_measurableSet hS]
    exact Commute.zero_right σ

/-- The dephasing semigroup `ρ ↦ ∫ e^{isT} ρ e^{-isT} dN(0, t)(s)` of the observable `T` with
spectral measure `μS`. -/
def dephasingSemigroup (t : ℝ) (ρ : E →L[ℂ] E) : E →L[ℂ] E :=
  gaussianConj (phaseUnitary μS) t.toNNReal ρ

end Spectral

/-! ## C. The dephasing equation on spectral windows -/

omit [CompleteSpace E] in
/-- The generator acts blockwise when `X` acts as `yᵢ` on the range of `Pᵢ`. -/
lemma mul_dephasingGenerator_mul_of {X : E →L[ℂ] E} {P : ι → E →L[ℂ] E} {y : ι → ℝ}
    (hl : ∀ i, P i * X = (y i : ℂ) • P i) (hr : ∀ i, X * P i = (y i : ℂ) • P i) (i j : ι)
    (A : E →L[ℂ] E) :
    P i * dephasingGenerator X A * P j = (-((y i - y j) ^ 2 / 2)) • (P i * A * P j) := by
  have hl' : ∀ B : E →L[ℂ] E, P i * (X * B) = y i • (P i * B) := fun B => by
    rw [← mul_assoc, hl, Complex.coe_smul, smul_mul_assoc]
  have hr' : X * P j = y j • P j := by rw [hr, Complex.coe_smul]
  rw [dephasingGenerator_apply]
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc, hl', hr',
    smul_smul]
  module

omit [CompleteSpace E] in
/-- **The blocks of a solution**, when `X` acts as `yᵢ` on the range of `Pᵢ`:
`Pᵢ r(t) Pⱼ = e^{-t (yᵢ - yⱼ)² / 2} Pᵢ r(0) Pⱼ` for `t ≥ 0`. -/
theorem mul_eq_of_hasDerivAt_of {X : E →L[ℂ] E} {P : ι → E →L[ℂ] E} {y : ι → ℝ}
    (hl : ∀ i, P i * X = (y i : ℂ) • P i) (hr : ∀ i, X * P i = (y i : ℂ) • P i)
    {r : ℝ → E →L[ℂ] E} (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator X (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) (i j : ι) {t : ℝ} (ht : 0 ≤ t) :
    P i * r t * P j = Real.exp (-(t * ((y i - y j) ^ 2 / 2))) • (P i * r 0 * P j) := by
  set c := (y i - y j) ^ 2 / 2
  let f : ℝ → E →L[ℂ] E := fun s => P i * r s * P j
  let g : ℝ → E →L[ℂ] E := fun s => Real.exp (s * c) • f s
  have hg : ∀ s, 0 < s → HasDerivAt g 0 s := fun s hs => by
    have hf : HasDerivAt f (P i * dephasingGenerator X (r s) * P j) s :=
      ((hd s hs).const_mul _).mul_const _
    rw [mul_dephasingGenerator_mul_of hl hr] at hf
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

section Window

open ProbabilisticTheory.QuantumMechanics ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure

/-- The identity cut off to `[-m, m]`. -/
def cutoffId (m : ℝ) : ℝ → ℝ := (Icc (-m) m).indicator id

lemma measurable_cutoffId (m : ℝ) : Measurable fun r => (cutoffId m r : ℂ) :=
  Complex.measurable_ofReal.comp (measurable_id.indicator measurableSet_Icc)

lemma bounded_cutoffId (m : ℝ) : ∃ C, ∀ r, ‖(cutoffId m r : ℂ)‖ ≤ C :=
  ⟨|m|, fun r => by
    by_cases hr : r ∈ Icc (-m) m
    · rw [cutoffId, indicator_of_mem hr, Complex.norm_real, Real.norm_eq_abs, id]
      exact abs_le_abs hr.2 (by linarith [hr.1])
    · rw [cutoffId, indicator_of_notMem hr]
      simp⟩

variable (μS : WOTSpectralMeasure ℝ E)

/-- The observable on the spectral cutoffId `[-m, m]`: the bounded operator
`X_m = ∫ 1_{[-m, m]}(r) r dμS(r)`. -/
def windowObservable (m : ℝ) : E →L[ℂ] E :=
  (boundedIntegral μS _ (measurable_cutoffId m) (bounded_cutoffId m)).toCLM

lemma pointProj_mul_windowObservable (m a : ℝ) :
    pointProj μS a * windowObservable μS m = (cutoffId m a : ℂ) • pointProj μS a := by
  change (μS {a} * boundedIntegral μS _ (measurable_cutoffId m) (bounded_cutoffId m)).toCLM = _
  rw [singleton_mul_boundedIntegral]
  rfl

lemma windowObservable_mul_pointProj (m a : ℝ) :
    windowObservable μS m * pointProj μS a = (cutoffId m a : ℂ) • pointProj μS a := by
  change (boundedIntegral μS _ (measurable_cutoffId m) (bounded_cutoffId m) * μS {a}).toCLM = _
  rw [boundedIntegral_mul_singleton]
  rfl

open Classical in
lemma pointProj_mul_spectralCutoffProj (m a : ℝ) :
    pointProj μS a * spectralCutoffProj μS m =
      if a ∈ Icc (-m) m then pointProj μS a else 0 := by
  change (μS {a} * μS (Icc (-m) m)).toCLM = _
  rw [μS.comp_eq_of_inter (measurableSet_singleton a) measurableSet_Icc]
  split_ifs with ha
  · rw [inter_eq_left.mpr (singleton_subset_iff.mpr ha)]; rfl
  · rw [singleton_inter_eq_empty.mpr ha, μS.empty]; rfl

open Classical in
lemma spectralCutoffProj_mul_pointProj (m a : ℝ) :
    spectralCutoffProj μS m * pointProj μS a =
      if a ∈ Icc (-m) m then pointProj μS a else 0 := by
  change (μS (Icc (-m) m) * μS {a}).toCLM = _
  rw [μS.comp_eq_of_inter measurableSet_Icc (measurableSet_singleton a)]
  split_ifs with ha
  · rw [inter_eq_right.mpr (singleton_subset_iff.mpr ha)]; rfl
  · rw [inter_singleton_eq_empty.mpr ha, μS.empty]; rfl

lemma norm_mul_cutoffIndicator_le (m a : ℝ) : ‖(a : ℂ) * cutoffIndicator m a‖ ≤ |m| := by
  by_cases ha : a ∈ Icc (-m) m
  · rw [cutoffIndicator, indicator_of_mem ha, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le_abs ha.2 (by linarith [ha.1])
  · rw [cutoffIndicator, indicator_of_notMem ha]
    simp

variable {T : E →ₗ.[ℂ] E} {μS} (D : DomainAwareSelfAdjointSpectralTheorem T μS)
include D

/-- The spectral projection `μS([-m, m])` maps into the domain of `T`. -/
theorem spectralCutoffProj_apply_mem_domain (m : ℝ) (v : E) :
    spectralCutoffProj μS m v ∈ T.domain := by
  rw [← D.maximal_eq, spectralCutoffProj_eq]
  exact boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS _ _
    ⟨|m|, abs_nonneg m, norm_mul_cutoffIndicator_le m⟩ v

/-- **On a spectral cutoffId, `T` is the bounded operator `X_m`**: `T (μS([-m, m]) v) = X_m v`. -/
theorem apply_spectralCutoffProj_apply (m : ℝ) (v : E) :
    T ⟨spectralCutoffProj μS m v, spectralCutoffProj_apply_mem_domain D m v⟩ =
      windowObservable μS m v := by
  have e := D.maximal_eq
  subst e
  have h2 := boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS
    (measurable_cutoffIndicator m) (bounded_cutoffIndicator m)
    ⟨|m|, abs_nonneg m, norm_mul_cutoffIndicator_le m⟩ v
  have hx : (⟨spectralCutoffProj μS m v, spectralCutoffProj_apply_mem_domain D m v⟩ :
      (maximalSpectralIntegral μS).domain) =
      ⟨boundedIntegral μS (cutoffIndicator m) (measurable_cutoffIndicator m)
        (bounded_cutoffIndicator m) v, h2⟩ :=
    Subtype.ext (congrArg (fun A : E →L[ℂ] E => A v) (spectralCutoffProj_eq μS m))
  rw [hx, maximalSpectralIntegral_apply_boundedMultiplier_of_bound μS
    (measurable_cutoffIndicator m) (bounded_cutoffIndicator m)
    ⟨|m|, abs_nonneg m, norm_mul_cutoffIndicator_le m⟩
    (Complex.measurable_ofReal.mul (measurable_cutoffIndicator m))]
  refine congrArg (fun A : E →WOT[ℂ] E => A v) (boundedIntegral_congr μS _ _ _ _ fun a => ?_)
  by_cases ha : a ∈ Icc (-m) m
  · simp [cutoffIndicator, cutoffId, ha]
  · simp [cutoffIndicator, cutoffId, ha]

/-- Every eigenprojection maps into the domain of `T`. -/
theorem pointProj_apply_mem_domain (a : ℝ) (v : E) : pointProj μS a v ∈ T.domain := by
  have h : spectralCutoffProj μS |a| (pointProj μS a v) = pointProj μS a v := by
    change (spectralCutoffProj μS |a| * pointProj μS a) v = _
    rw [spectralCutoffProj_mul_pointProj]
    simp [neg_abs_le, le_abs_self]
  rw [← h]
  exact spectralCutoffProj_apply_mem_domain D _ _

/-- **The eigenprojections project onto eigenvectors**: `T (μS({a}) v) = a μS({a}) v`. -/
theorem apply_pointProj_apply (a : ℝ) (v : E) :
    T ⟨pointProj μS a v, pointProj_apply_mem_domain D a v⟩ = (a : ℂ) • pointProj μS a v := by
  have h : spectralCutoffProj μS |a| (pointProj μS a v) = pointProj μS a v := by
    change (spectralCutoffProj μS |a| * pointProj μS a) v = _
    rw [spectralCutoffProj_mul_pointProj]
    simp [neg_abs_le, le_abs_self]
  have hx : (⟨pointProj μS a v, pointProj_apply_mem_domain D a v⟩ : T.domain) =
      ⟨spectralCutoffProj μS |a| (pointProj μS a v),
        spectralCutoffProj_apply_mem_domain D _ _⟩ := Subtype.ext h.symm
  rw [hx, apply_spectralCutoffProj_apply D]
  change (windowObservable μS |a| * pointProj μS a) v = _
  rw [windowObservable_mul_pointProj, cutoffId,
    indicator_of_mem (show a ∈ Icc (-|a|) |a| from ⟨neg_abs_le a, le_abs_self a⟩)]
  rfl

end Window

section Extension

open ProbabilisticTheory.QuantumMechanics

variable {μS : WOTSpectralMeasure ℝ E}

/-- `ρ` lives on the spectral cutoffId `[-m, m]`. -/
def IsWindowed (μS : WOTSpectralMeasure ℝ E) (m : ℝ) (ρ : E →L[ℂ] E) : Prop :=
  spectralCutoffProj μS m * ρ * spectralCutoffProj μS m = ρ

lemma IsWindowed.mul_mul_eq_zero {m : ℝ} {ρ : E →L[ℂ] E} (hQ : IsWindowed μS m ρ) {a b : ℝ}
    (hab : a ∉ Icc (-m) m ∨ b ∉ Icc (-m) m) : pointProj μS a * ρ * pointProj μS b = 0 := by
  rw [← hQ, show pointProj μS a * (spectralCutoffProj μS m * ρ * spectralCutoffProj μS m) *
      pointProj μS b = (pointProj μS a * spectralCutoffProj μS m) * ρ *
        (spectralCutoffProj μS m * pointProj μS b) by simp only [mul_assoc],
    pointProj_mul_spectralCutoffProj, spectralCutoffProj_mul_pointProj]
  rcases hab with h | h <;> simp [h]

/-- **On a spectral cutoffId, the dephasing equation has the Gaussian average as its solution**: a
solution of `ρ' = X_m ρ X_m - ½ {X_m², ρ}` starting at a windowed `ρ` is `G_t(ρ)`. -/
theorem IsAtomic.eq_dephasingSemigroup (h : IsAtomic μS) {m : ℝ} {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ)
    (hρ : IsTraceClass ρ) (hQ : IsWindowed μS m ρ) {r : ℝ → E →L[ℂ] E} (h0 : r 0 = ρ)
    (hd : ∀ t, 0 < t → HasDerivAt r (dephasingGenerator (windowObservable μS m) (r t)) t)
    (hc : ContinuousWithinAt r (Ici 0) 0) {t : ℝ} (ht : 0 ≤ t) :
    r t = dephasingSemigroup μS t ρ :=
  h.isResolutionOfIdentity.ext_block fun a b => by
    rw [mul_eq_of_hasDerivAt_of (pointProj_mul_windowObservable μS m)
      (windowObservable_mul_pointProj μS m) hd hc a b ht, h0, dephasingSemigroup,
      h.isPhaseGroup.mul_gaussianConj_mul _ hρ0 hρ, Real.coe_toNNReal _ ht]
    by_cases ha : a ∈ Icc (-m) m
    · by_cases hb : b ∈ Icc (-m) m
      · simp [cutoffId, ha, hb]
      · simp [hQ.mul_mul_eq_zero (Or.inr hb)]
    · simp [hQ.mul_mul_eq_zero (Or.inl ha)]

/-- On a spectral cutoffId, the Gaussian average is the bounded dephasing flow of `X_m`. -/
theorem IsAtomic.dephasingFlow_eq (h : IsAtomic μS) {m : ℝ} {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ)
    (hρ : IsTraceClass ρ) (hQ : IsWindowed μS m ρ) {t : ℝ} (ht : 0 ≤ t) :
    dephasingFlow (windowObservable μS m) t ρ = dephasingSemigroup μS t ρ :=
  h.eq_dephasingSemigroup hρ0 hρ hQ (dephasingFlow_zero _ _)
    (fun t _ => hasDerivAt_dephasingFlow _ _ t)
    (hasDerivAt_dephasingFlow _ ρ 0).continuousAt.continuousWithinAt ht

/-- **The semigroup solves the dephasing equation on spectral windows.** -/
theorem IsAtomic.hasDerivAt_dephasingSemigroup (h : IsAtomic μS) {m : ℝ} {ρ : E →L[ℂ] E}
    (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) (hQ : IsWindowed μS m ρ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => dephasingSemigroup μS s ρ)
      (dephasingGenerator (windowObservable μS m) (dephasingSemigroup μS t ρ)) t := by
  have hd := hasDerivAt_dephasingFlow (windowObservable μS m) ρ t
  rw [h.dephasingFlow_eq hρ0 hρ hQ ht.le] at hd
  exact hd.congr_of_eventuallyEq (by
    filter_upwards [lt_mem_nhds ht] with _s hs
    exact (h.dephasingFlow_eq hρ0 hρ hQ hs.le).symm)

lemma IsAtomic.continuousWithinAt_dephasingSemigroup (h : IsAtomic μS) {m : ℝ} {ρ : E →L[ℂ] E}
    (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) (hQ : IsWindowed μS m ρ) :
    ContinuousWithinAt (fun s => dephasingSemigroup μS s ρ) (Ici 0) 0 :=
  (hasDerivAt_dephasingFlow (windowObservable μS m) ρ 0).continuousAt.continuousWithinAt.congr
    (fun _ hs => (h.dephasingFlow_eq hρ0 hρ hQ hs).symm)
    (h.dephasingFlow_eq hρ0 hρ hQ le_rfl).symm

lemma IsAtomic.dephasingSemigroup_zero (h : IsAtomic μS) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ)
    (hρ : IsTraceClass ρ) : dephasingSemigroup μS 0 ρ = ρ := by
  rw [dephasingSemigroup, Real.toNNReal_zero]
  exact h.isPhaseGroup.gaussianConj_zero hρ0 hρ

variable (μS) in
/-- `S` **extends the dephasing equation from the spectral windows**: on positive trace-class
operators living on a cutoffId `[-m, m]`, `t ↦ S t ρ` solves `ρ' = X_m ρ X_m - ½ {X_m², ρ}` with
`S 0 ρ = ρ`; and each `S t` is continuous in trace norm on positive trace-class operators. -/
structure IsDephasingExtension (S : ℝ → (E →L[ℂ] E) → E →L[ℂ] E) : Prop where
  zero : ∀ m ρ, 0 ≤ ρ → IsTraceClass ρ → IsWindowed μS m ρ → S 0 ρ = ρ
  hasDerivAt : ∀ m ρ, 0 ≤ ρ → IsTraceClass ρ → IsWindowed μS m ρ → ∀ t, 0 < t →
    HasDerivAt (fun s => S s ρ) (dephasingGenerator (windowObservable μS m) (S t ρ)) t
  continuousWithinAt : ∀ m ρ, 0 ≤ ρ → IsTraceClass ρ → IsWindowed μS m ρ →
    ContinuousWithinAt (fun s => S s ρ) (Ici 0) 0
  tendsto : ∀ t, 0 ≤ t → ∀ (ρ : E →L[ℂ] E) (ρn : ℕ → E →L[ℂ] E), 0 ≤ ρ → IsTraceClass ρ →
    (∀ n, 0 ≤ ρn n) → (∀ n, IsTraceClass (ρn n)) →
    Tendsto (fun n => traceENorm (ρn n - ρ)) atTop (𝓝 0) →
    Tendsto (fun n => traceENorm (S t (ρn n) - S t ρ)) atTop (𝓝 0)

/-- **The Gaussian average extends the dephasing equation** from the spectral windows. -/
theorem IsAtomic.isDephasingExtension (h : IsAtomic μS) :
    IsDephasingExtension μS (dephasingSemigroup μS) where
  zero _ _ hρ0 hρ _ := h.dephasingSemigroup_zero hρ0 hρ
  hasDerivAt _ _ hρ0 hρ hQ _ ht := h.hasDerivAt_dephasingSemigroup hρ0 hρ hQ ht
  continuousWithinAt _ _ hρ0 hρ hQ := h.continuousWithinAt_dephasingSemigroup hρ0 hρ hQ
  tendsto _ _ _ _ hρ0 hρ hn0 hn hlim :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      fun n => h.isPhaseGroup.traceENorm_gaussianConj_sub_le _ (hn0 n) (hn n) hρ0 hρ

/-- The windowed truncations `μS([-n, n]) ρ μS([-n, n])` of a density operator tend to it in trace
norm. -/
lemma tendsto_traceENorm_spectralCutoffProj_conj {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    Tendsto (fun n : ℕ => traceENorm (spectralCutoffProj μS n * ρ * spectralCutoffProj μS n - ρ))
      atTop (𝓝 0) := by
  have h := tendsto_traceENorm_conj (U := fun n : ℕ => spectralCutoffProj μS n) (U₀ := 1)
    (fun n => IsStarProjection.norm_le _ (isStarProjection_spectralCutoffProj μS n)) norm_id_le
    (fun v => (tendsto_spectralCutoffProj_apply μS v).comp tendsto_natCast_atTop_atTop) hρ
  simpa only [(isStarProjection_spectralCutoffProj μS _).isSelfAdjoint.star_eq, star_one,
    one_mul, mul_one] using h

lemma isWindowed_conj (m : ℝ) (ρ : E →L[ℂ] E) :
    IsWindowed μS m (spectralCutoffProj μS m * ρ * spectralCutoffProj μS m) := by
  have hQ := (isStarProjection_spectralCutoffProj μS m).isIdempotentElem.eq
  rw [IsWindowed, show spectralCutoffProj μS m * (spectralCutoffProj μS m * ρ *
      spectralCutoffProj μS m) * spectralCutoffProj μS m = (spectralCutoffProj μS m *
        spectralCutoffProj μS m) * ρ * (spectralCutoffProj μS m * spectralCutoffProj μS m) by
      simp only [mul_assoc], hQ]

/-- **The extension is unique**: every extension of the dephasing equation from the spectral
windows is the Gaussian average on density operators. -/
theorem IsAtomic.eq_of_isDephasingExtension (h : IsAtomic μS)
    {S : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} (hS : IsDephasingExtension μS S) {t : ℝ} (ht : 0 ≤ t)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) : S t ρ = dephasingSemigroup μS t ρ := by
  set ρn : ℕ → E →L[ℂ] E := fun n => spectralCutoffProj μS n * ρ * spectralCutoffProj μS n
  have hn0 : ∀ n, 0 ≤ ρn n := fun n => by
    have h := star_right_conjugate_nonneg hρ.nonneg (spectralCutoffProj μS n)
    rwa [(isStarProjection_spectralCutoffProj μS _).isSelfAdjoint.star_eq] at h
  have hn : ∀ n, IsTraceClass (ρn n) := fun n => isTraceClass_mul_mul hρ.isTraceClass
  have hlim := tendsto_traceENorm_spectralCutoffProj_conj (μS := μS) hρ
  have heq : ∀ n, S t (ρn n) = dephasingSemigroup μS t (ρn n) := fun n =>
    h.eq_dephasingSemigroup (hn0 n) (hn n) (isWindowed_conj _ ρ) (hS.zero _ _ (hn0 n) (hn n)
      (isWindowed_conj _ ρ)) (hS.hasDerivAt _ _ (hn0 n) (hn n) (isWindowed_conj _ ρ))
      (hS.continuousWithinAt _ _ (hn0 n) (hn n) (isWindowed_conj _ ρ)) ht
  have h1 := tendsto_of_tendsto_traceENorm
    (hS.tendsto t ht ρ ρn hρ.nonneg hρ.isTraceClass hn0 hn hlim)
  have h2 := tendsto_of_tendsto_traceENorm
    (h.isDephasingExtension.tendsto t ht ρ ρn hρ.nonneg hρ.isTraceClass hn0 hn hlim)
  simp only [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- **The semigroup preserves density operators.** -/
theorem IsAtomic.isDensityOperator_dephasingSemigroup (h : IsAtomic μS) (t : ℝ) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) : IsDensityOperator (dephasingSemigroup μS t ρ) :=
  h.isPhaseGroup.isDensityOperator_gaussianConj _ hρ

/-- **The semigroup property** `e^{(s + t)L} = e^{sL} e^{tL}`. -/
theorem IsAtomic.dephasingSemigroup_add (h : IsAtomic μS) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ) (hρ : IsTraceClass ρ) :
    dephasingSemigroup μS (s + t) ρ = dephasingSemigroup μS s (dephasingSemigroup μS t ρ) := by
  rw [dephasingSemigroup, dephasingSemigroup, dephasingSemigroup, Real.toNNReal_add hs ht]
  exact h.isPhaseGroup.gaussianConj_add _ _ hρ0 hρ

/-- **Equilibration in trace norm**: `e^{tL} ρ → ∑ₐ μS({a}) ρ μS({a})` for every density
operator `ρ`. -/
theorem IsAtomic.tendsto_traceENorm_dephasingSemigroup (h : IsAtomic μS) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) :
    Tendsto (fun t => traceENorm (dephasingSemigroup μS t ρ -
      h.isResolutionOfIdentity.pinching ρ)) atTop (𝓝 0) :=
  h.isPhaseGroup.tendsto_traceENorm_gaussianConj Function.injective_id hρ

end Extension

end QuantumMechanics
