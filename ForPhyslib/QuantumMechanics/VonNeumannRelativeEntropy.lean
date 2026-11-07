/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.DiscreteObservable
public import ForPhyslib.QuantumMechanics.VonNeumannEntropy
public import ForPhyslib.ProbabilisticTheory.HilbertSpace.TraceClass.CanonicalExpansion
public import ForMathlib.Analysis.InnerProductSpace.CFCEigenvector
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# The relative entropy of density operators in any dimension

## i. Overview

For density operators `ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` and `σ = ∑ⱼ μⱼ |fⱼ⟩⟨fⱼ|` on a Hilbert space of any
dimension, the relative entropy is **Lindblad's formula**
`D(ρ‖σ) = ∑ᵢⱼ |⟨eᵢ, fⱼ⟩|² (λᵢ log λᵢ - λᵢ log μⱼ + μⱼ - λᵢ) ∈ [0, ∞]`, each term being
`μ klFun(λ / μ) ≥ 0` (`+∞` when `μⱼ = 0 < λᵢ`). It is computed in eigenbases chosen once.

The cross term `-tr (ρ log σ) ∈ [0, ∞]` (`crossEntropy`) is defined without bases, as the
supremum of `tr (g_n(σ) ρ g_n(σ))` for continuous truncations `g_n² ↑ -log`. In any eigenbases
`D(ρ‖σ) + S(ρ) = -tr (ρ log σ)`. Hence, when `S(ρ) < ∞`, `D(ρ‖σ) = -tr (ρ log σ) - S(ρ)` in
every pair of eigenbases, and `D(ρ‖σ) = 0` iff `ρ = σ` (Klein's inequality with its equality
case). For `σ` commuting with a resolution of the identity `{Pᵢ}`, `-tr (ρ log σ)` does not
change when `ρ` is replaced by its pinching `P(ρ)`; with `S(P(ρ)) < ∞` this gives
`D(ρ‖P(ρ)) = S(P(ρ)) - S(ρ)` and the Pythagoras identity `D(ρ‖σ) = D(ρ‖P(ρ)) + D(P(ρ)‖σ)`.

## ii. Key results

- `QuantumMechanics.relativeEntropy`, `QuantumMechanics.lindbladSum`,
  `QuantumMechanics.crossEntropy`.
- `QuantumMechanics.crossEntropy_eq_lindbladSum_add`: `-tr (ρ log σ) = D + S(ρ)` in any
  eigenbases.
- `QuantumMechanics.relativeEntropy_eq_zero_iff`: Klein's inequality, equality case.
- `QuantumMechanics.IsResolutionOfIdentity.relativeEntropy_pinching`: `D(ρ‖P(ρ)) = S(P(ρ)) - S(ρ)`.
- `QuantumMechanics.IsResolutionOfIdentity.relativeEntropy_eq_add`: the Pythagoras identity.
- `QuantumMechanics.IsResolutionOfIdentity.relativeEntropy_pinching_lt`: `P(ρ)` is the unique
  closest commuting density operator.

## iii. Table of contents

- A. The scalar Klein term
- B. Eigenbases
- C. The cross term `-tr (ρ log σ)`
- D. Lindblad's formula and Klein's inequality
- E. Pinching

## iv. References

- G. Lindblad, *Expectations and entropy inequalities for finite quantum systems*, Commun. Math.
  Phys. **39** (1974), 111–119.
- M. Ohya, D. Petz, *Quantum Entropy and Its Use*, Springer (1993), Ch. 5.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open Filter Topology ContinuousLinearMap Real InformationTheory ProbabilisticTheory
open ContinuousLinearMap (posTrace posTrace_eq_tsum re_inner_apply_nonneg)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. The scalar Klein term -/

/-- The Lindblad term `a log a - a log b + b - a ∈ [0, ∞]`, `+∞` for `b = 0 < a`. -/
def kleinTerm (a b : ℝ) : ℝ≥0∞ :=
  if b = 0 then (if a = 0 then 0 else ⊤) else ENNReal.ofReal (a * log a - a * log b + b - a)

/-- `-log b ∈ [0, ∞]`, `+∞` at `b = 0`. -/
def negLogENNReal (b : ℝ) : ℝ≥0∞ := if b = 0 then ⊤ else ENNReal.ofReal (-log b)

lemma kleinReal_eq_mul_klFun {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a * log a - a * log b + b - a = b * klFun (a / b) := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp [klFun]
  rw [klFun, Real.log_div ha'.ne' hb.ne']
  field_simp

lemma kleinReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ a * log a - a * log b + b - a := by
  rw [kleinReal_eq_mul_klFun ha hb]
  exact mul_nonneg hb.le (klFun_nonneg (div_nonneg ha hb.le))

lemma kleinTerm_eq_zero_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : kleinTerm a b = 0 ↔ a = b := by
  unfold kleinTerm
  rcases hb.eq_or_lt with rfl | hb'
  · by_cases h : a = 0 <;> simp [h]
  simp only [hb'.ne', ↓reduceIte]
  rw [ENNReal.ofReal_eq_zero, kleinReal_eq_mul_klFun ha hb']
  constructor
  · intro h
    have h1 : klFun (a / b) ≤ 0 := by
      by_contra hc
      push Not at hc
      linarith [mul_pos hb' hc]
    have h2 := le_antisymm h1 (klFun_nonneg (div_nonneg ha hb'.le))
    rw [klFun_eq_zero_iff (div_nonneg ha hb'.le), div_eq_one_iff_eq hb'.ne'] at h2
    exact h2
  · rintro rfl
    rw [div_self hb'.ne', klFun_one, mul_zero]

/-- The scalar identity behind Lindblad's formula: `a (-log b) + b = k(a, b) + η(a) + a` in
`[0, ∞]`, for `a, b ∈ [0, 1]`. -/
lemma ofReal_mul_negLog_add {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ENNReal.ofReal a * negLogENNReal b + ENNReal.ofReal b =
      kleinTerm a b + ENNReal.ofReal (negMulLog a) + ENNReal.ofReal a := by
  unfold kleinTerm negLogENNReal
  rcases hb.eq_or_lt with rfl | hb'
  · by_cases h : a = 0
    · simp [h]
    · simp [h, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (lt_of_le_of_ne ha (Ne.symm h))).ne']
  simp only [hb'.ne', ↓reduceIte]
  have hl : 0 ≤ -log b := neg_nonneg.mpr (Real.log_nonpos hb hb1)
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add (mul_nonneg ha hl) hb,
    ← ENNReal.ofReal_add (kleinReal_nonneg ha hb') (negMulLog_nonneg ha ha1),
    ← ENNReal.ofReal_add (add_nonneg (kleinReal_nonneg ha hb') (negMulLog_nonneg ha ha1)) ha]
  congr 1
  simp only [negMulLog]
  ring

/-! ## B. Eigenbases -/

/-- `e` is a Hilbert basis of eigenvectors of `ρ`, with `ρ eᵢ = λᵢ eᵢ`. -/
structure IsEigenbasis (ρ : E →L[ℂ] E) {ι : Type*} (e : HilbertBasis ι ℂ E) (ev : ι → ℝ) :
    Prop where
  apply_eq : ∀ i, ρ (e i) = (ev i : ℂ) • e i

lemma IsDensityOperator.exists_isEigenbasis {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    ∃ (w : Set E) (e : HilbertBasis w ℂ E) (ev : w → ℝ), IsEigenbasis ρ e ev := by
  obtain ⟨w, b, μ, -, hμ, -⟩ := hρ.isTraceClass.exists_hasSum_rankOne hρ.nonneg
  exact ⟨w, b, μ, ⟨hμ⟩⟩

/-- The index set of a chosen eigenbasis of a density operator. -/
def IsDensityOperator.eigenIndex {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) : Set E :=
  hρ.exists_isEigenbasis.choose

/-- A chosen eigenbasis of a density operator. -/
def IsDensityOperator.eigenbasis {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    HilbertBasis hρ.eigenIndex ℂ E :=
  hρ.exists_isEigenbasis.choose_spec.choose

/-- The eigenvalues for the chosen eigenbasis. -/
def IsDensityOperator.eigenvalue {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    hρ.eigenIndex → ℝ :=
  hρ.exists_isEigenbasis.choose_spec.choose_spec.choose

lemma IsDensityOperator.isEigenbasis {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsEigenbasis ρ hρ.eigenbasis hρ.eigenvalue :=
  hρ.exists_isEigenbasis.choose_spec.choose_spec.choose_spec

namespace IsEigenbasis

variable {ρ : E →L[ℂ] E} {ι : Type*} {e : HilbertBasis ι ℂ E} {ev : ι → ℝ}
  (he : IsEigenbasis ρ e ev)
include he

omit [CompleteSpace E] in
lemma inner_apply (i : ι) : ⟪e i, ρ (e i)⟫_ℂ = ev i := by
  rw [he.apply_eq, inner_smul_right, inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
  simp

lemma eigenvalue_mem_Icc (hρ : IsDensityOperator ρ) (i : ι) : 0 ≤ ev i ∧ ev i ≤ 1 := by
  refine ⟨?_, ?_⟩
  · have h := re_inner_apply_nonneg hρ.nonneg (e i)
    rwa [he.inner_apply, Complex.ofReal_re] at h
  · have h : ‖ρ (e i)‖ ≤ 1 := by
      calc ‖ρ (e i)‖ ≤ ‖ρ‖ * ‖e i‖ := ρ.le_opNorm _
        _ ≤ 1 * 1 := by rw [e.orthonormal.1 i]; gcongr; exact hρ.norm_le_one
        _ = 1 := one_mul 1
    rw [he.apply_eq, norm_smul, e.orthonormal.1 i, mul_one, Complex.norm_real,
      Real.norm_eq_abs] at h
    exact (abs_le.mp h).2

lemma posTrace_eq (h0 : 0 ≤ ρ) : posTrace ρ = ∑' i, ENNReal.ofReal (ev i) := by
  rw [posTrace_eq_tsum h0 e]
  simp_rw [he.inner_apply, Complex.ofReal_re]

lemma tsum_ofReal_eq_one (hρ : IsDensityOperator ρ) : ∑' i, ENNReal.ofReal (ev i) = 1 := by
  rw [← he.posTrace_eq hρ.nonneg, hρ.posTrace_eq_one]

lemma cfc_apply (hρ : IsSelfAdjoint ρ) {g : ℝ → ℝ} (hg : ContinuousOn g (spectrum ℝ ρ))
    (i : ι) : cfc g ρ (e i) = (g (ev i) : ℂ) • e i :=
  cfc_apply_eq_smul_of_apply_eq_smul hρ hg (he.apply_eq i)

/-- The entropy in an eigenbasis: `S(ρ) = ∑ᵢ η(λᵢ)`. -/
theorem vonNeumannEntropy_eq (hρ : IsDensityOperator ρ) :
    vonNeumannEntropy ρ = ∑' i, ENNReal.ofReal (negMulLog (ev i)) := by
  rw [vonNeumannEntropy, posTrace_eq_tsum hρ.cfc_negMulLog_nonneg e]
  congr 1
  ext i
  rw [he.cfc_apply hρ.isSelfAdjoint continuous_negMulLog.continuousOn, inner_smul_right,
    inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
  simp

/-- `⟨f, ρ f⟩ = ∑ᵢ λᵢ |⟨eᵢ, f⟩|²`, in `[0, ∞]`. -/
theorem ofReal_re_inner_apply (hρ : IsDensityOperator ρ) (f : E) :
    ENNReal.ofReal (⟪f, ρ f⟫_ℂ).re =
      ∑' i, ENNReal.ofReal (ev i) * ENNReal.ofReal (‖⟪e i, f⟫_ℂ‖ ^ 2) := by
  have h1 := ρ.hasSum (e.hasSum_repr f)
  simp only [map_smul, he.apply_eq, smul_smul, HilbertBasis.repr_apply_apply] at h1
  have h2 : HasSum (fun i => (innerSL ℂ f (((⟪e i, f⟫_ℂ) * (ev i : ℂ)) • e i)).re)
      (⟪f, ρ f⟫_ℂ).re := Complex.hasSum_re ((innerSL ℂ f).hasSum h1)
  have e2 : ∀ i, (innerSL ℂ f (((⟪e i, f⟫_ℂ) * (ev i : ℂ)) • e i)).re =
      ev i * ‖⟪e i, f⟫_ℂ‖ ^ 2 := fun i => by
    rw [innerSL_apply_apply, inner_smul_right, ← inner_conj_symm f (e i),
      mul_comm (⟪e i, f⟫_ℂ) (ev i : ℂ), mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [e2] at h2
  rw [← h2.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg
    (he.eigenvalue_mem_Icc hρ i).1 (sq_nonneg _)) h2.summable]
  simp_rw [ENNReal.ofReal_mul (he.eigenvalue_mem_Icc hρ _).1]

end IsEigenbasis

/-! ## C. The cross term `-tr (ρ log σ)` -/

/-- The truncation `-log (max b e^{-n})` of `-log b`: continuous, nonnegative on `[0, 1]`,
increasing in `n`, with supremum `-log b` (`+∞` at `b = 0`). -/
def negLogTrunc (n : ℕ) (b : ℝ) : ℝ := -log (max b (exp (-n)))

lemma continuous_negLogTrunc (n : ℕ) : Continuous (negLogTrunc n) :=
  ((continuous_id.max continuous_const).log fun _ =>
    (lt_max_of_lt_right (exp_pos _)).ne').neg

lemma negLogTrunc_nonneg (n : ℕ) {b : ℝ} (hb1 : b ≤ 1) : 0 ≤ negLogTrunc n b := by
  refine neg_nonneg.mpr (Real.log_nonpos (le_max_of_le_right (exp_pos _).le) (max_le hb1 ?_))
  exact Real.exp_le_one_iff.mpr (by simp)

lemma monotone_negLogTrunc (b : ℝ) : Monotone fun n => negLogTrunc n b := by
  intro n m hnm
  simp only [negLogTrunc, neg_le_neg_iff]
  refine Real.log_le_log (lt_max_of_lt_right (exp_pos _)) (max_le_max le_rfl ?_)
  exact Real.exp_le_exp.mpr (by simpa using hnm)

lemma iSup_ofReal_negLogTrunc {b : ℝ} (hb : 0 ≤ b) :
    ⨆ n : ℕ, ENNReal.ofReal (negLogTrunc n b) = negLogENNReal b := by
  unfold negLogENNReal
  rcases hb.eq_or_lt with rfl | hb'
  · have h : ∀ n : ℕ, negLogTrunc n 0 = n := fun n => by
      rw [negLogTrunc, max_eq_right (exp_pos _).le, Real.log_exp, neg_neg]
    simp only [h, ENNReal.ofReal_natCast, ↓reduceIte]
    exact ENNReal.iSup_natCast
  simp only [hb'.ne', ↓reduceIte]
  refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal ?_) ?_
  · simp only [negLogTrunc, neg_le_neg_iff]
    exact Real.log_le_log hb' (le_max_left _ _)
  · obtain ⟨N, hN⟩ := exists_nat_gt (-log b)
    refine le_iSup_of_le N (le_of_eq ?_)
    congr 1
    rw [negLogTrunc, max_eq_left]
    have : -(N : ℝ) < log b := by linarith
    exact (Real.exp_lt_exp.mpr this).le.trans (Real.exp_log hb').le

/-- The **cross term** `-tr (ρ log σ) ∈ [0, ∞]`, as the supremum of `tr (g_n(σ) ρ g_n(σ))` with
`g_n = √(negLogTrunc n)`. No basis is involved. -/
def crossEntropy (ρ σ : E →L[ℂ] E) : ℝ≥0∞ :=
  ⨆ n : ℕ, posTrace (cfc (fun b => √(negLogTrunc n b)) σ * ρ * cfc (fun b => √(negLogTrunc n b)) σ)

/-- Monotone convergence for sums in `[0, ∞]`. -/
lemma tsum_iSup_of_monotone {α : Type*} {a : ℕ → α → ℝ≥0∞} (ha : ∀ j, Monotone fun n => a n j) :
    ∑' j, ⨆ n, a n j = ⨆ n, ∑' j, a n j := by
  classical
  have hfin : ∀ s : Finset α, ∑ j ∈ s, ⨆ n, a n j = ⨆ n, ∑ j ∈ s, a n j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, ih, ENNReal.iSup_add_iSup_of_monotone (ha j)
        (fun n m h => Finset.sum_le_sum fun k _ => ha k h)]
      simp_rw [Finset.sum_insert hj]
  rw [tsum_eq_iSup_sum]
  simp_rw [hfin]
  rw [iSup_comm]
  simp_rw [← tsum_eq_iSup_sum]

/-- The cross term in an eigenbasis of `σ`: `-tr (ρ log σ) = ∑ⱼ (-log μⱼ) ⟨fⱼ, ρ fⱼ⟩`. -/
theorem IsEigenbasis.crossEntropy_eq {σ : E →L[ℂ] E} {κ : Type*} {f : HilbertBasis κ ℂ E}
    {μ : κ → ℝ} (hf : IsEigenbasis σ f μ) (hσ : IsDensityOperator σ) {ρ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) :
    crossEntropy ρ σ = ∑' j, negLogENNReal (μ j) * ENNReal.ofReal (⟪f j, ρ (f j)⟫_ℂ).re := by
  have hμ := fun j => hf.eigenvalue_mem_Icc hσ j
  have hterm : ∀ n : ℕ, posTrace (cfc (fun b => √(negLogTrunc n b)) σ * ρ *
      cfc (fun b => √(negLogTrunc n b)) σ) = ∑' j, ENNReal.ofReal (negLogTrunc n (μ j)) *
        ENNReal.ofReal (⟪f j, ρ (f j)⟫_ℂ).re := fun n => by
    set B := cfc (fun b => √(negLogTrunc n b)) σ
    have hBsa : IsSelfAdjoint B := cfc_predicate _ _
    have hB0 : 0 ≤ B * ρ * B := by
      have h := star_right_conjugate_nonneg hρ B
      rwa [hBsa.star_eq] at h
    rw [posTrace_eq_tsum hB0 f]
    congr 1
    ext j
    have hBf : B (f j) = ((√(negLogTrunc n (μ j)) : ℝ) : ℂ) • f j :=
      hf.cfc_apply hσ.isSelfAdjoint (continuous_negLogTrunc n).sqrt.continuousOn j
    have hsq : √(negLogTrunc n (μ j)) * √(negLogTrunc n (μ j)) = negLogTrunc n (μ j) :=
      Real.mul_self_sqrt (negLogTrunc_nonneg n (hμ j).2)
    have hin : ⟪f j, (B * ρ * B) (f j)⟫_ℂ = (negLogTrunc n (μ j) : ℂ) * ⟪f j, ρ (f j)⟫_ℂ := by
      change ⟪f j, B (ρ (B (f j)))⟫_ℂ = _
      have e : ⟪B (f j), ρ (B (f j))⟫_ℂ = ⟪f j, B (ρ (B (f j)))⟫_ℂ :=
        hBsa.isSymmetric (f j) (ρ (B (f j)))
      rw [← e, hBf, inner_smul_left, map_smul, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
        ← Complex.ofReal_mul, hsq]
    rw [hin, Complex.re_ofReal_mul, ENNReal.ofReal_mul (negLogTrunc_nonneg n (hμ j).2)]
  simp_rw [crossEntropy, hterm]
  rw [← tsum_iSup_of_monotone (a := fun n j => ENNReal.ofReal (negLogTrunc n (μ j)) *
      ENNReal.ofReal (⟪f j, ρ (f j)⟫_ℂ).re) fun j n m h =>
    mul_le_mul_left (ENNReal.ofReal_le_ofReal (monotone_negLogTrunc (μ j) h)) _]
  congr 1
  ext j
  rw [← ENNReal.iSup_mul, iSup_ofReal_negLogTrunc (hμ j).1]

/-! ## D. Lindblad's formula and Klein's inequality -/

/-- **Lindblad's formula** in the eigenbases `(e, λ)` of `ρ` and `(f, μ)` of `σ`:
`∑ᵢⱼ |⟨eᵢ, fⱼ⟩|² (λᵢ log λᵢ - λᵢ log μⱼ + μⱼ - λᵢ)`. -/
def lindbladSum {ι κ : Type*} (e : HilbertBasis ι ℂ E) (ev : ι → ℝ) (f : HilbertBasis κ ℂ E)
    (μ : κ → ℝ) : ℝ≥0∞ :=
  ∑' i, ∑' j, ENNReal.ofReal (‖⟪e i, f j⟫_ℂ‖ ^ 2) * kleinTerm (ev i) (μ j)

variable {ρ σ : E →L[ℂ] E} {ι κ : Type*} {e : HilbertBasis ι ℂ E} {ev : ι → ℝ}
  {f : HilbertBasis κ ℂ E} {μ : κ → ℝ}

/-- **`-tr (ρ log σ) = D(ρ‖σ) + S(ρ)`**, with `D` given by Lindblad's formula in any eigenbases. -/
theorem crossEntropy_eq_lindbladSum_add (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (he : IsEigenbasis ρ e ev) (hf : IsEigenbasis σ f μ) :
    crossEntropy ρ σ = lindbladSum e ev f μ + vonNeumannEntropy ρ := by
  set c : ι → κ → ℝ≥0∞ := fun i j => ENNReal.ofReal (‖⟪e i, f j⟫_ℂ‖ ^ 2)
  have hrow : ∀ i, ∑' j, c i j = 1 := fun i => by
    simp_rw [c, norm_inner_symm (e i)]
    rw [f.tsum_ofReal_norm_inner_sq (e i), e.orthonormal.1 i]
    simp
  have hcol : ∀ j, ∑' i, c i j = 1 := fun j => by
    rw [e.tsum_ofReal_norm_inner_sq (f j), f.orthonormal.1 j]
    simp
  have hA : crossEntropy ρ σ =
      ∑' i, ∑' j, c i j * (ENNReal.ofReal (ev i) * negLogENNReal (μ j)) := by
    rw [hf.crossEntropy_eq hσ hρ.nonneg]
    simp_rw [he.ofReal_re_inner_apply hρ, ← ENNReal.tsum_mul_left]
    rw [tsum_comm]
    congr 1
    ext i
    congr 1
    ext j
    ring
  have hμsum : ∑' i, ∑' j, c i j * ENNReal.ofReal (μ j) = 1 := by
    rw [tsum_comm]
    simp_rw [ENNReal.tsum_mul_right, hcol, one_mul]
    exact hf.tsum_ofReal_eq_one hσ
  have hlsum : ∑' i, ∑' j, c i j * ENNReal.ofReal (ev i) = 1 := by
    simp_rw [ENNReal.tsum_mul_right, hrow, one_mul]
    exact he.tsum_ofReal_eq_one hρ
  have hηsum : ∑' i, ∑' j, c i j * ENNReal.ofReal (negMulLog (ev i)) = vonNeumannEntropy ρ := by
    simp_rw [ENNReal.tsum_mul_right, hrow, one_mul]
    exact (he.vonNeumannEntropy_eq hρ).symm
  have hsum : ∑' i, ∑' j, c i j * (ENNReal.ofReal (ev i) * negLogENNReal (μ j)) +
      ∑' i, ∑' j, c i j * ENNReal.ofReal (μ j) =
      lindbladSum e ev f μ + ∑' i, ∑' j, c i j * ENNReal.ofReal (negMulLog (ev i)) +
        ∑' i, ∑' j, c i j * ENNReal.ofReal (ev i) := by
    simp only [lindbladSum, ← tsum_add, ← mul_add]
    congr 1
    ext i
    congr 1
    ext j
    rw [ofReal_mul_negLog_add (he.eigenvalue_mem_Icc hρ i).1 (he.eigenvalue_mem_Icc hρ i).2
      (hf.eigenvalue_mem_Icc hσ j).1 (hf.eigenvalue_mem_Icc hσ j).2]
    simp only [c, mul_add]
  rw [← hA, hμsum, hηsum, hlsum] at hsum
  exact (ENNReal.add_left_inj ENNReal.one_ne_top).mp hsum

/-- **The equality case of Klein's inequality**: Lindblad's sum vanishes only for `ρ = σ`. -/
theorem eq_of_lindbladSum_eq_zero (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (he : IsEigenbasis ρ e ev) (hf : IsEigenbasis σ f μ) (h : lindbladSum e ev f μ = 0) :
    ρ = σ := by
  have hij : ∀ i j, ⟪e i, (ρ - σ) (f j)⟫_ℂ = 0 := fun i j => by
    have h1 := tsum_eq_zero_iff.mp (tsum_eq_zero_iff.mp h i) j
    have hρe : ⟪e i, ρ (f j)⟫_ℂ = ev i * ⟪e i, f j⟫_ℂ := by
      have e1 : ⟪ρ (e i), f j⟫_ℂ = ⟪e i, ρ (f j)⟫_ℂ := hρ.isSelfAdjoint.isSymmetric (e i) (f j)
      rw [← e1, he.apply_eq, inner_smul_left, Complex.conj_ofReal]
    have hσf : ⟪e i, σ (f j)⟫_ℂ = μ j * ⟪e i, f j⟫_ℂ := by rw [hf.apply_eq, inner_smul_right]
    rw [sub_apply, inner_sub_right, hρe, hσf, ← sub_mul]
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rw [ENNReal.ofReal_eq_zero] at h2
      have h3 : ‖⟪e i, f j⟫_ℂ‖ = 0 := by nlinarith [norm_nonneg ⟪e i, f j⟫_ℂ]
      rw [norm_eq_zero.mp h3, mul_zero]
    · rw [kleinTerm_eq_zero_iff (he.eigenvalue_mem_Icc hρ i).1 (hf.eigenvalue_mem_Icc hσ j).1] at h2
      rw [h2, sub_self, zero_mul]
  have hcol : ∀ j, (ρ - σ) (f j) = 0 := fun j => by
    have h3 := e.hasSum_repr ((ρ - σ) (f j))
    simp only [HilbertBasis.repr_apply_apply, hij, zero_smul] at h3
    exact h3.unique hasSum_zero
  refine sub_eq_zero.mp ?_
  ext v
  have h4 := (ρ - σ).hasSum (f.hasSum_repr v)
  simp only [map_smul, hcol, smul_zero] at h4
  exact h4.unique hasSum_zero

/-- The **relative entropy** `D(ρ‖σ) ∈ [0, ∞]` of density operators, by Lindblad's formula in
chosen eigenbases (`+∞` if `ρ` or `σ` is not a density operator). When `S(ρ) < ∞` it does not
depend on the eigenbases (`relativeEntropy_eq_lindbladSum`). -/
def relativeEntropy (ρ σ : E →L[ℂ] E) : ℝ≥0∞ :=
  open Classical in
  if h : IsDensityOperator ρ ∧ IsDensityOperator σ then
    lindbladSum h.1.eigenbasis h.1.eigenvalue h.2.eigenbasis h.2.eigenvalue
  else ⊤

theorem relativeEntropy_add_vonNeumannEntropy (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) : relativeEntropy ρ σ + vonNeumannEntropy ρ = crossEntropy ρ σ := by
  simp only [relativeEntropy, hρ, hσ, and_self, ↓reduceDIte]
  rw [
    crossEntropy_eq_lindbladSum_add hρ hσ hρ.isEigenbasis hσ.isEigenbasis]

/-- Under finite entropy, the relative entropy is Lindblad's formula in **any** eigenbases. -/
theorem relativeEntropy_eq_lindbladSum (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hS : vonNeumannEntropy ρ ≠ ⊤) (he : IsEigenbasis ρ e ev) (hf : IsEigenbasis σ f μ) :
    relativeEntropy ρ σ = lindbladSum e ev f μ :=
  (ENNReal.add_left_inj hS).mp (by
    rw [relativeEntropy_add_vonNeumannEntropy hρ hσ, crossEntropy_eq_lindbladSum_add hρ hσ he hf])

theorem relativeEntropy_self (hρ : IsDensityOperator ρ) : relativeEntropy ρ ρ = 0 := by
  simp only [relativeEntropy, hρ, and_self, ↓reduceDIte]
  rw [lindbladSum]
  refine tsum_eq_zero_iff.mpr fun i => tsum_eq_zero_iff.mpr fun j => ?_
  by_cases hij : i = j
  · subst hij
    rw [(kleinTerm_eq_zero_iff (hρ.isEigenbasis.eigenvalue_mem_Icc hρ i).1
      (hρ.isEigenbasis.eigenvalue_mem_Icc hρ i).1).mpr rfl, mul_zero]
  · rw [hρ.eigenbasis.orthonormal.2 hij]
    simp

/-- **Klein's inequality**, equality case: `D(ρ‖σ) = 0` iff `ρ = σ`. -/
theorem relativeEntropy_eq_zero_iff (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    relativeEntropy ρ σ = 0 ↔ ρ = σ := by
  refine ⟨fun h => eq_of_lindbladSum_eq_zero hρ hσ hρ.isEigenbasis hσ.isEigenbasis ?_, ?_⟩
  · simpa only [relativeEntropy, hρ, hσ, and_self, ↓reduceDIte] using h
  · rintro rfl
    exact relativeEntropy_self hρ

theorem crossEntropy_self (hρ : IsDensityOperator ρ) : crossEntropy ρ ρ = vonNeumannEntropy ρ := by
  rw [← relativeEntropy_add_vonNeumannEntropy hρ hρ, relativeEntropy_self hρ, zero_add]

/-! ## E. Pinching -/

namespace IsResolutionOfIdentity

variable {ι' : Type*} {P : ι' → E →L[ℂ] E} (hP : IsResolutionOfIdentity P)
include hP

/-- The pinching commutes with conjugation by an operator commuting with every `Pᵢ`. -/
lemma pinching_conj {B : E →L[ℂ] E} (hB : ∀ i, Commute B (P i)) (ρ : E →L[ℂ] E) :
    hP.pinching (B * ρ * B) = B * hP.pinching ρ * B :=
  hP.ext_block fun i j => by
    have e1 : P i * (B * hP.pinching ρ * B) * P j = B * (P i * hP.pinching ρ * P j) * B := by
      calc P i * (B * hP.pinching ρ * B) * P j = (P i * B) * hP.pinching ρ * (B * P j) := by
            simp only [mul_assoc]
        _ = (B * P i) * hP.pinching ρ * (P j * B) := by rw [(hB i).eq, (hB j).eq]
        _ = B * (P i * hP.pinching ρ * P j) * B := by simp only [mul_assoc]
    rw [e1, hP.mul_pinching_mul, hP.mul_pinching_mul]
    split_ifs with h
    · subst h
      calc P i * (B * ρ * B) * P i = (P i * B) * ρ * (B * P i) := by simp only [mul_assoc]
        _ = (B * P i) * ρ * (P i * B) := by rw [(hB i).eq]
        _ = B * (P i * ρ * P i) * B := by simp only [mul_assoc]
    · rw [mul_zero, zero_mul]

/-- For `σ` commuting with every `Pᵢ`, `-tr (P(ρ) log σ) = -tr (ρ log σ)`. -/
theorem crossEntropy_pinching (hρ : IsDensityOperator ρ) (hc : ∀ i, Commute σ (P i)) :
    crossEntropy (hP.pinching ρ) σ = crossEntropy ρ σ := by
  unfold crossEntropy
  congr 1
  ext n
  set B := cfc (fun b => √(negLogTrunc n b)) σ
  have hB : ∀ i, Commute B (P i) := fun i => Commute.cfc_real (hc i) _
  have hBsa : IsSelfAdjoint B := cfc_predicate _ _
  have h0 : 0 ≤ B * ρ * B := by
    have h := star_right_conjugate_nonneg hρ.nonneg B
    rwa [hBsa.star_eq] at h
  rw [← hP.pinching_conj hB, hP.posTrace_pinching h0]

/-- **Eq. (13)**: `D(ρ‖P(ρ)) = S(P(ρ)) - S(ρ)` when `S(P(ρ)) < ∞`. -/
theorem relativeEntropy_pinching (hρ : IsDensityOperator ρ)
    (hS : vonNeumannEntropy (hP.pinching ρ) ≠ ⊤) :
    relativeEntropy ρ (hP.pinching ρ) =
      vonNeumannEntropy (hP.pinching ρ) - vonNeumannEntropy ρ := by
  have hPρ := hP.isDensityOperator_pinching hρ
  have hc : ∀ i, Commute (hP.pinching ρ) (P i) :=
    hP.pinching_eq_self_iff.mp (hP.pinching_pinching ρ)
  have h := relativeEntropy_add_vonNeumannEntropy hρ hPρ
  rw [← hP.crossEntropy_pinching hρ hc, crossEntropy_self hPρ] at h
  have hSρ : vonNeumannEntropy ρ ≠ ⊤ := ne_top_of_le_ne_top hS (h ▸ le_add_self)
  exact ENNReal.eq_sub_of_add_eq hSρ h

/-- **The Pythagoras identity** for the relative entropy (eq. (12)): for `σ` commuting with every
`Pᵢ` and `S(P(ρ)) < ∞`, `D(ρ‖σ) = D(ρ‖P(ρ)) + D(P(ρ)‖σ)`. -/
theorem relativeEntropy_eq_add (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hc : ∀ i, Commute σ (P i)) (hS : vonNeumannEntropy (hP.pinching ρ) ≠ ⊤) :
    relativeEntropy ρ σ =
      relativeEntropy ρ (hP.pinching ρ) + relativeEntropy (hP.pinching ρ) σ := by
  have hPρ := hP.isDensityOperator_pinching hρ
  have hcP : ∀ i, Commute (hP.pinching ρ) (P i) :=
    hP.pinching_eq_self_iff.mp (hP.pinching_pinching ρ)
  have h1 := relativeEntropy_add_vonNeumannEntropy hρ hσ
  have h2 := relativeEntropy_add_vonNeumannEntropy hPρ hσ
  have h3 := relativeEntropy_add_vonNeumannEntropy hρ hPρ
  rw [← hP.crossEntropy_pinching hρ hcP, crossEntropy_self hPρ] at h3
  have hSρ : vonNeumannEntropy ρ ≠ ⊤ := ne_top_of_le_ne_top hS (h3 ▸ le_add_self)
  rw [← hP.crossEntropy_pinching hρ hc, ← h2, ← h3, ← add_assoc,
    add_comm (relativeEntropy (hP.pinching ρ) σ)] at h1
  exact (ENNReal.add_left_inj hSρ).mp h1

/-- **The pinching is the unique closest commuting density operator in relative entropy**, when
`S(P(ρ)) < ∞`. -/
theorem relativeEntropy_pinching_lt (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (hc : ∀ i, Commute σ (P i)) (hS : vonNeumannEntropy (hP.pinching ρ) ≠ ⊤)
    (hne : σ ≠ hP.pinching ρ) :
    relativeEntropy ρ (hP.pinching ρ) < relativeEntropy ρ σ := by
  rw [hP.relativeEntropy_eq_add hρ hσ hc hS]
  refine ENNReal.lt_add_right ?_ ?_
  · rw [hP.relativeEntropy_pinching hρ hS]
    exact ne_top_of_le_ne_top hS tsub_le_self
  · rw [Ne, relativeEntropy_eq_zero_iff (hP.isDensityOperator_pinching hρ) hσ]
    exact fun h => hne h.symm

end IsResolutionOfIdentity

end QuantumMechanics
