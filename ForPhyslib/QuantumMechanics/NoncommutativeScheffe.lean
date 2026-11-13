/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.TraceNorm
public import ForPhyslib.QuantumMechanics.DiscreteObservable

/-!
# The non-commutative Scheffé lemma

## i. Overview

Scheffé's lemma says that probability densities converging pointwise converge in `L¹`. Its
non-commutative version: density operators `ρₐ` converging weakly to a density operator `ρ`,
`⟪u, ρₐ v⟫ → ⟪u, ρ v⟫` for all `u, v`, converge in trace norm. In particular Hilbert–Schmidt
convergence to a density operator implies trace-norm convergence.

The proof truncates to a finite-dimensional subspace. Expand `ρ = ∑ₖ μₖ |bₖ⟩⟨bₖ|` and let
`Q = ∑_{k ∈ F} |bₖ⟩⟨bₖ|` for a finite `F` carrying most of the weight, so that
`tr(Qρ) > 1 - η²`. By weak convergence `tr(Qρₐ) → tr(Qρ)`, so eventually `tr(Qρₐ) > 1 - η²`.
The *gentle measurement* bound `‖σ - QσQ‖₁ ≤ (1 - tr(Qσ))/η + η` for density operators `σ`
then makes `ρₐ - Qρₐ Q` and `ρ - QρQ` small, and `Q(ρₐ - ρ)Q` is a finite combination of the
matrix entries `⟪bⱼ, (ρₐ - ρ) bₖ⟫`, which tend to zero.

The gentle measurement bound follows from the pure-state bound
`‖|c⟩⟨c| - |Qc⟩⟨Qc|‖₁ ≤ 2‖c - Qc‖ ≤ ‖c - Qc‖²/η + η`, averaged over the spectral expansion of
`σ` (`traceENorm_apply_le_tsum`), with `∑ᵢ μᵢ ‖cᵢ - Qcᵢ‖² = 1 - tr(Qσ)`.

## ii. Key results

- `QuantumMechanics.traceENorm_apply_le_tsum`: trace-norm bounds average over the spectral
  expansion.
- `QuantumMechanics.traceENorm_sub_finiteProj_le`: the gentle measurement bound.
- `QuantumMechanics.tendsto_traceENorm_of_tendsto_inner`: the non-commutative Scheffé lemma for
  weak convergence.
- `QuantumMechanics.tendsto_traceENorm_of_tendsto_hilbertSchmidtNorm`: the same for
  Hilbert–Schmidt convergence.

## iii. Table of contents

- A. Averaging trace-norm bounds
- B. Finite-rank projections
- C. Gentle measurement
- D. The non-commutative Scheffé lemma

## iv. References

- G. F. Dell'Antonio, *On the limits of sequences of normal states*, Comm. Pure Appl. Math. **20**
  (1967) 413–429.
- B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS (2005), Thm 2.20.
- A. Winter, *Coding theorem and strong converse for quantum channels*, IEEE Trans. Inf. Theory
  **45** (1999) 2481–2485, Lemma 9 (gentle measurement).
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open Filter Topology InnerProductSpace ProbabilisticTheory ProbabilisticTheory.TraceClass
  QuantumMechanics.Wigner

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. Averaging trace-norm bounds -/

/-- **Trace-norm bounds average over the spectral expansion.** If `σ = ∑ᵢ μᵢ |cᵢ⟩⟨cᵢ|` in
`𝒮₁(E)` with `μᵢ ≥ 0`, and a bounded linear map `D` has `‖D |cᵢ⟩⟨cᵢ|‖₁ ≤ gᵢ`, then
`‖D σ‖₁ ≤ ∑ᵢ μᵢ gᵢ`. -/
theorem traceENorm_apply_le_tsum (D : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) {ι : Type*} {c : ι → E}
    {μ : ι → ℝ} (hμ0 : ∀ i, 0 ≤ μ i) {σ : E →L[ℂ] E} (hσ : IsTraceClass σ)
    (hS : HasSum (fun i => ofOperator ((μ i : ℂ) • rankOne ℂ (c i) (c i))
      (isTraceClass_smul _ (isTraceClass_rankOne_self _))) (ofOperator σ hσ))
    {g : ι → ℝ} (hg0 : ∀ i, 0 ≤ g i) (hg : ∀ i, traceENorm (D (proj (c i))) ≤ ENNReal.ofReal (g i))
    (hgs : Summable fun i => μ i * g i) :
    traceENorm (D σ) ≤ ENNReal.ofReal (∑' i, μ i * g i) := by
  have htc : ∀ i, IsTraceClass (D (proj (c i))) := fun i =>
    traceENorm_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hg i))
  have hle : ∀ i, traceNorm (D (proj (c i))) (htc i) ≤ g i := fun i => by
    have h' := hg i
    rw [traceENorm_eq_ofReal (htc i)] at h'
    exact (ENNReal.ofReal_le_ofReal_iff (hg0 i)).mp h'
  set a : ι → TraceClass E := fun i => (μ i : ℂ) • ofOperator (D (proj (c i))) (htc i)
  have ha : ∀ i, ‖a i‖ ≤ μ i * g i := fun i => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ0 i), norm_eq_traceNorm]
    exact mul_le_mul_of_nonneg_left (hle i) (hμ0 i)
  obtain ⟨A, hA⟩ : Summable a := .of_norm_bounded hgs ha
  have hAle : ‖A‖ ≤ ∑' i, μ i * g i := hA.norm_le_of_bounded hgs.hasSum ha
  have hDA : A.1 = D σ := by
    have h1 := hA.mapL toOperator
    have h2 := (hS.mapL toOperator).mapL D
    refine h1.unique (h2.congr_fun fun i => ?_)
    simp only [a, map_smul, toOperator_apply, ofOperator_coe]
  rw [← hDA, traceENorm_eq_ofReal A.2, ← norm_eq_traceNorm]
  exact ENNReal.ofReal_le_ofReal hAle

/-! ## B. Finite-rank projections -/

section FiniteProj

variable {κ : Type*} {b : κ → E} (hb : Orthonormal ℂ b) (F : Finset κ)

/-- The projection `Q = ∑_{k ∈ F} |bₖ⟩⟨bₖ|` onto the span of finitely many orthonormal vectors. -/
def finiteProj (b : κ → E) (F : Finset κ) : E →L[ℂ] E := ∑ k ∈ F, rankOne ℂ (b k) (b k)

omit [CompleteSpace E] in
lemma finiteProj_apply (v : E) : finiteProj b F v = ∑ k ∈ F, ⟪b k, v⟫_ℂ • b k := by
  simp [finiteProj, sum_apply, rankOne_apply]

omit [CompleteSpace E] in
lemma inner_finiteProj_left (u v : E) : ⟪finiteProj b F u, v⟫_ℂ = ⟪u, finiteProj b F v⟫_ℂ := by
  simp only [finiteProj_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

include hb

omit [CompleteSpace E] in
lemma inner_sub_finiteProj {k : κ} (hk : k ∈ F) (v : E) : ⟪b k, v - finiteProj b F v⟫_ℂ = 0 := by
  rw [inner_sub_right, finiteProj_apply, hb.inner_right_sum _ hk, sub_self]

omit [CompleteSpace E] in
lemma inner_finiteProj_sub_finiteProj (v : E) :
    ⟪finiteProj b F v, v - finiteProj b F v⟫_ℂ = 0 := by
  have h : ∀ k ∈ F, ⟪b k, v - finiteProj b F v⟫_ℂ = 0 := fun k hk => inner_sub_finiteProj hb F hk v
  simp only [finiteProj_apply] at h ⊢
  rw [sum_inner]
  exact Finset.sum_eq_zero fun k hk => by rw [inner_smul_left, h k hk, mul_zero]

omit [CompleteSpace E] in
/-- `‖v‖² = ‖Qv‖² + ‖v - Qv‖²`. -/
lemma norm_sq_eq_finiteProj (v : E) :
    ‖v‖ ^ 2 = ‖finiteProj b F v‖ ^ 2 + ‖v - finiteProj b F v‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) _ _
    (inner_finiteProj_sub_finiteProj hb F v)
  rw [add_sub_cancel] at h
  simpa only [sq] using h

omit [CompleteSpace E] in
/-- `‖Qv‖² = ∑_{k ∈ F} |⟪bₖ, v⟫|²`. -/
lemma norm_finiteProj_sq (v : E) :
    ‖finiteProj b F v‖ ^ 2 = ∑ k ∈ F, ‖⟪b k, v⟫_ℂ‖ ^ 2 := by
  have h1 : ⟪finiteProj b F v, finiteProj b F v⟫_ℂ = ⟪finiteProj b F v, v⟫_ℂ := by
    have := inner_finiteProj_sub_finiteProj hb F v
    rw [inner_sub_right, sub_eq_zero] at this
    exact this.symm
  have h2 : ⟪finiteProj b F v, v⟫_ℂ = ∑ k ∈ F, ((‖⟪b k, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    rw [finiteProj_apply, sum_inner]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_left, Complex.conj_mul']
    push_cast
    rfl
  have h3 := congrArg Complex.re (h1.trans h2)
  rw [inner_self_eq_norm_sq_to_K] at h3
  simpa [← Complex.ofReal_pow] using h3

omit [CompleteSpace E] in
lemma norm_finiteProj_le (v : E) : ‖finiteProj b F v‖ ≤ ‖v‖ := by
  have h := norm_sq_eq_finiteProj hb F v
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
    (by nlinarith [sq_nonneg ‖v - finiteProj b F v‖])

omit hb [CompleteSpace E] in
/-- `Q |ψ⟩⟨ψ| Q = |Qψ⟩⟨Qψ|`. -/
lemma finiteProj_mul_proj_mul (ψ : E) :
    finiteProj b F * proj ψ * finiteProj b F = proj (finiteProj b F ψ) := by
  ext v
  simp only [mul_apply_eq_comp, rankOne_apply, map_smul]
  rw [inner_finiteProj_left]

omit hb [CompleteSpace E] in
/-- `QTQ = ∑_{j, k ∈ F} ⟪bⱼ, T bₖ⟫ |bⱼ⟩⟨bₖ|`. -/
lemma finiteProj_mul_mul_finiteProj (T : E →L[ℂ] E) :
    finiteProj b F * T * finiteProj b F =
      ∑ j ∈ F, ∑ k ∈ F, ⟪b j, T (b k)⟫_ℂ • rankOne ℂ (b j) (b k) := by
  ext v
  simp only [mul_apply_eq_comp, finiteProj_apply, map_sum, map_smul, sum_apply, smul_apply,
    rankOne_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]

end FiniteProj

/-! ## C. Gentle measurement -/

/-- `tr(Qσ) = ∑_{k ∈ F} ⟪bₖ, σ bₖ⟫`. -/
def finiteTrace {κ : Type*} (b : κ → E) (F : Finset κ) (σ : E →L[ℂ] E) : ℝ :=
  ∑ k ∈ F, (⟪b k, σ (b k)⟫_ℂ).re

private lemma traceENorm_sum_le' {κ : Type*} (s : Finset κ) (f : κ → E →L[ℂ] E) :
    traceENorm (∑ p ∈ s, f p) ≤ ∑ p ∈ s, traceENorm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (traceENorm_add_le _ _).trans (by gcongr)

private lemma two_mul_le_div_add {a η : ℝ} (hη : 0 < η) : 2 * a ≤ a ^ 2 / η + η := by
  rw [div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  nlinarith [sq_nonneg (a - η)]

section Gentle

variable {κ : Type*} {b : κ → E} (hb : Orthonormal ℂ b) (F : Finset κ)
include hb

/-- In the spectral expansion `σ = ∑ᵢ μᵢ |cᵢ⟩⟨cᵢ|` of a density operator,
`∑ᵢ μᵢ ‖cᵢ - Qcᵢ‖² = 1 - tr(Qσ)`. -/
lemma hasSum_mul_norm_sub_finiteProj_sq {σ : E →L[ℂ] E} (hσ : IsDensityOperator σ) {w : Set E}
    {c : HilbertBasis w ℂ E} {μ : w → ℝ} (hμ : HasSum μ 1)
    (hS : HasSum (fun i => ofOperator ((μ i : ℂ) • rankOne ℂ (c i) (c i))
      (isTraceClass_smul _ (isTraceClass_rankOne_self _))) (ofOperator σ hσ.isTraceClass)) :
    HasSum (fun i => μ i * ‖c i - finiteProj b F (c i)‖ ^ 2) (1 - finiteTrace b F σ) := by
  have hk : ∀ k, HasSum (fun i => μ i * ‖⟪b k, c i⟫_ℂ‖ ^ 2) (⟪b k, σ (b k)⟫_ℂ).re := fun k => by
    have h1 := ((hS.mapL toOperator).mapL (ContinuousLinearMap.apply ℂ E (b k))).mapL
      (innerSL ℂ (b k))
    have h2 := Complex.hasSum_re h1
    simp only [toOperator_apply, ofOperator_coe, ContinuousLinearMap.apply_apply,
      innerSL_apply_apply, smul_apply, rankOne_apply, inner_smul_right] at h2
    refine h2.congr_fun fun i => ?_
    rw [← inner_conj_symm (c i) (b k), Complex.conj_mul', ← Complex.ofReal_pow,
      Complex.re_ofReal_mul, Complex.ofReal_re]
  have h := hμ.sub (hasSum_sum fun k (_ : k ∈ F) => hk k)
  refine h.congr_fun fun i => ?_
  have hn := norm_sq_eq_finiteProj hb F (c i)
  rw [c.orthonormal.1 i, norm_finiteProj_sq hb] at hn
  rw [← Finset.mul_sum]
  have : ‖c i - finiteProj b F (c i)‖ ^ 2 = 1 - ∑ k ∈ F, ‖⟪b k, c i⟫_ℂ‖ ^ 2 := by
    rw [one_pow] at hn; linarith
  rw [this]
  ring

/-- **Gentle measurement**: `‖σ - QσQ‖₁ ≤ (1 - tr(Qσ))/η + η` for a density operator `σ` and
`η > 0`. With `tr(Qσ) > 1 - η²` the bound is `2η`. -/
theorem traceENorm_sub_finiteProj_le {σ : E →L[ℂ] E} (hσ : IsDensityOperator σ) {η : ℝ}
    (hη : 0 < η) :
    traceENorm (σ - finiteProj b F * σ * finiteProj b F) ≤
      ENNReal.ofReal ((1 - finiteTrace b F σ) / η + η) := by
  obtain ⟨w, c, μ, -, -, hμ0, hμ, -, hS⟩ := hσ.isTraceClass.exists_hasSum_rankOne hσ.nonneg
  rw [hσ.traceNorm_eq_one] at hμ
  set Q := finiteProj b F
  set D : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E :=
    ContinuousLinearMap.id ℂ _ - ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) Q Q
  have hD : ∀ T, D T = T - Q * T * Q := fun T => by
    simp [D, ContinuousLinearMap.mulLeftRight_apply]
  have hsum := hasSum_mul_norm_sub_finiteProj_sq hb F hσ hμ hS
  set g : w → ℝ := fun i => ‖c i - Q (c i)‖ ^ 2 / η + η
  have hg : HasSum (fun i => μ i * g i) ((1 - finiteTrace b F σ) / η + η) := by
    have := (hsum.div_const η).add (hμ.mul_right η)
    simpa only [one_mul, g, mul_add, mul_div_assoc] using this
  rw [← hD, ← hg.tsum_eq]
  refine traceENorm_apply_le_tsum D hμ0 hσ.isTraceClass hS (fun i => by positivity)
    (fun i => ?_) hg.summable
  rw [hD, finiteProj_mul_proj_mul]
  refine (traceENorm_proj_sub_le _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : ‖c i‖ = 1 := c.orthonormal.1 i
  have h2 := norm_finiteProj_le hb F (c i)
  calc (‖c i‖ + ‖Q (c i)‖) * ‖c i - Q (c i)‖ ≤ 2 * ‖c i - Q (c i)‖ := by
        gcongr
        linarith
    _ ≤ g i := two_mul_le_div_add hη

end Gentle

/-! ## D. The non-commutative Scheffé lemma -/

/-- **The non-commutative Scheffé lemma**: density operators converging weakly to a density
operator converge in trace norm. -/
theorem tendsto_traceENorm_of_tendsto_inner {α : Type*} {l : Filter α} {ρ' : α → E →L[ℂ] E}
    {ρ : E →L[ℂ] E} (hρ' : ∀ a, IsDensityOperator (ρ' a)) (hρ : IsDensityOperator ρ)
    (h : ∀ u v, Tendsto (fun a => ⟪u, ρ' a v⟫_ℂ) l (𝓝 ⟪u, ρ v⟫_ℂ)) :
    Tendsto (fun a => traceENorm (ρ' a - ρ)) l (𝓝 0) := by
  obtain ⟨w, b, μ, -, hbμ, -, hμ, -, -⟩ := hρ.isTraceClass.exists_hasSum_rankOne hρ.nonneg
  rw [hρ.traceNorm_eq_one] at hμ
  have hb := b.orthonormal
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨e, he0, he⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ ε := by
    rcases eq_or_ne ε ⊤ with rfl | hne
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hne, ENNReal.ofReal_toReal_le⟩
  set η := e / 8 with hηe
  have hη : 0 < η := by positivity
  -- a finite set carrying weight more than `1 - η²`
  obtain ⟨F, hF⟩ := (hμ.eventually (lt_mem_nhds (by nlinarith : 1 - η ^ 2 < 1))).exists
  set Q := finiteProj (⇑b) F
  have htrρ : finiteTrace (⇑b) F ρ = ∑ k ∈ F, μ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hbμ k, inner_smul_right, inner_self_eq_norm_sq_to_K, hb.1 k]
    simp
  -- `tr(Qρₐ) → tr(Qρ)`
  have htr : Tendsto (fun a => finiteTrace (⇑b) F (ρ' a)) l (𝓝 (finiteTrace (⇑b) F ρ)) :=
    tendsto_finsetSum _ fun k _ => (Complex.continuous_re.tendsto _).comp (h (b k) (b k))
  have hev1 : ∀ᶠ a in l, 1 - η ^ 2 < finiteTrace (⇑b) F (ρ' a) :=
    htr.eventually (lt_mem_nhds (htrρ ▸ hF))
  -- the matrix entries of `Q(ρₐ - ρ)Q` tend to zero
  have hmid : Tendsto (fun a => ∑ j ∈ F, ∑ k ∈ F,
      ‖⟪b j, ρ' a (b k)⟫_ℂ - ⟪b j, ρ (b k)⟫_ℂ‖ₑ) l (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∑ j ∈ F, ∑ k ∈ F, (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun k _ => ?_
    have h1 := (h (b j) (b k)).sub_const ⟪b j, ρ (b k)⟫_ℂ
    rw [sub_self] at h1
    have h2 := (continuous_enorm.tendsto 0).comp h1
    rw [enorm_zero] at h2
    exact h2
  have hev2 := hmid.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  filter_upwards [hev1, hev2] with a ha1 ha2
  have hblock : traceENorm (Q * ρ' a * Q - Q * ρ * Q) ≤
      ∑ j ∈ F, ∑ k ∈ F, ‖⟪b j, ρ' a (b k)⟫_ℂ - ⟪b j, ρ (b k)⟫_ℂ‖ₑ := by
    rw [finiteProj_mul_mul_finiteProj, finiteProj_mul_mul_finiteProj, ← Finset.sum_sub_distrib]
    refine (traceENorm_sum_le' _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine (traceENorm_sum_le' _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [← sub_smul, traceENorm_smul _ (isTraceClass_rankOne _ _)]
    calc _ ≤ ‖⟪b j, ρ' a (b k)⟫_ℂ - ⟪b j, ρ (b k)⟫_ℂ‖ₑ * 1 := by
          gcongr
          rw [traceENorm_eq_ofReal (isTraceClass_rankOne _ _)]
          refine ENNReal.ofReal_le_one.mpr ((traceNorm_rankOne_le _ _).trans ?_)
          rw [hb.1 j, hb.1 k, one_mul]
      _ = _ := mul_one _
  have hb1 : (1 - finiteTrace (⇑b) F (ρ' a)) / η + η ≤ 2 * η := by
    rw [div_add' _ _ _ hη.ne', div_le_iff₀ hη]
    nlinarith
  have hb2 : (1 - finiteTrace (⇑b) F ρ) / η + η ≤ 2 * η := by
    rw [htrρ, div_add' _ _ _ hη.ne', div_le_iff₀ hη]
    nlinarith
  have hsplit : ρ' a - ρ =
      (ρ' a - Q * ρ' a * Q) + (Q * ρ' a * Q - Q * ρ * Q) - (ρ - Q * ρ * Q) := by abel
  have t1 := (traceENorm_sub_finiteProj_le hb F (hρ' a) hη).trans (ENNReal.ofReal_le_ofReal hb1)
  have t2 := hblock.trans ha2.le
  have t3 := (traceENorm_sub_finiteProj_le hb F hρ hη).trans (ENNReal.ofReal_le_ofReal hb2)
  have hsum : ENNReal.ofReal (2 * η) + ENNReal.ofReal η + ENNReal.ofReal (2 * η) ≤ ε := by
    rw [← ENNReal.ofReal_add (by positivity) hη.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact (ENNReal.ofReal_le_ofReal (by rw [hηe]; linarith)).trans he
  rw [hsplit]
  exact ((traceENorm_sub_le_add _ _).trans
    (add_le_add ((traceENorm_add_le _ _).trans (add_le_add t1 t2)) t3)).trans hsum

/-- **The non-commutative Scheffé lemma** in the form of the brief: Hilbert–Schmidt convergence of
density operators to a density operator implies trace-norm convergence. -/
theorem tendsto_traceENorm_of_tendsto_hilbertSchmidtNorm {α : Type*} {l : Filter α}
    {ρ' : α → E →L[ℂ] E} {ρ : E →L[ℂ] E} (hρ' : ∀ a, IsDensityOperator (ρ' a))
    (hρ : IsDensityOperator ρ) (h : Tendsto (fun a => (ρ' a - ρ).hilbertSchmidtNorm) l (𝓝 0)) :
    Tendsto (fun a => traceENorm (ρ' a - ρ)) l (𝓝 0) := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis ℂ E
  refine tendsto_traceENorm_of_tendsto_inner hρ' hρ fun u v => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Tendsto (fun a => ‖u‖ * (ρ' a - ρ).hilbertSchmidtNorm * ‖v‖) l (𝓝 0) := by
    simpa using (h.const_mul ‖u‖).mul_const ‖v‖
  refine squeeze_zero (fun _ => norm_nonneg _) (fun a => ?_) hc
  rw [← inner_sub_right, ← sub_apply]
  calc ‖⟪u, (ρ' a - ρ) v⟫_ℂ‖ ≤ ‖u‖ * ‖(ρ' a - ρ) v‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖ρ' a - ρ‖ * ‖v‖) := by
        gcongr
        exact (ρ' a - ρ).le_opNorm v
    _ ≤ _ := by
        rw [← mul_assoc]
        gcongr
        exact (ρ' a - ρ).norm_le_hilbertSchmidtNorm b
          (IsResolutionOfIdentity.hilbertSchmidtEnergy_sub_ne_top (hρ' a) hρ b)

end QuantumMechanics
