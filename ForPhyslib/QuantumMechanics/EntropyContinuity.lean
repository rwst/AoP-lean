/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.VonNeumannRelativeEntropy
public import ForPhyslib.QuantumMechanics.TraceNorm
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Pairing

/-!
# The von Neumann entropy is continuous at bounded energy

## i. Overview

The von Neumann entropy is not continuous in the trace norm in infinite dimension. It becomes
continuous on every set of bounded energy, for a Hamiltonian `H ≥ 0` with
`tr e^{-βH} < ∞` for all `β > 0` (Wehrl 1978, Sec. II.D; Shirokov 2005, Prop. 1a). Here `H` is
given by a Hilbert basis `bₖ` and eigenvalues `ωₖ ≥ 0`, and the energy of `ρ` is
`tr ρH = ∑ₖ ωₖ ⟨bₖ, ρ bₖ⟩ ∈ [0, ∞]`.

The proof uses neither the ordering of eigenvalues nor the semicontinuity of relative entropy.
With `ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` and `g_K(λ) = min(-log λ, K)` (`negLogTrunc K`), split
`η(λ) = -λ log λ = λ g_K(λ) + r_K(λ)`:

* **The head** `∑ᵢ λᵢ g_K(λᵢ)` is continuous in the trace norm. By Weierstrass, `g_K` is
  uniformly close on `[0, 1]` to a polynomial `q`, and `∑ᵢ λᵢ q(λᵢ)` is a combination of the
  power traces `tr ρⁿ⁺¹`, which satisfy `|tr ρⁿ - tr σⁿ| ≤ n ‖ρ - σ‖₁`.
* **The tail** `∑ᵢ r_K(λᵢ)` is at most `β tr ρH + e^{-K-1} tr e^{-βH}`, for every `β > 0`. This is
  the scalar Klein inequality `-a log a ≤ -a log b + b - a` with `b = e^{-K-1-βωₖ}`, averaged
  over the weights `|⟨bₖ, eᵢ⟩|²`.

On a set of energy at most `h`, choosing `β` and then `K` makes the tail small uniformly.

## ii. Key results

- `QuantumMechanics.traceENorm_pow_sub_pow_le`: `‖ρⁿ - σⁿ‖₁ ≤ n ‖ρ - σ‖₁`.
- `QuantumMechanics.tendsto_eigenSum`: `ρ ↦ ∑ᵢ λᵢ g(λᵢ)` is continuous in the trace norm on
  density operators, for `g` continuous on `[0, 1]`.
- `QuantumMechanics.energy`, `QuantumMechanics.tailSum_le`: the tail bound.
- `QuantumMechanics.vonNeumannEntropy_le`: `S(ρ) ≤ β tr ρH + e^{-1} tr e^{-βH}`, so the entropy is
  finite at finite energy.
- `QuantumMechanics.energy_le_of_tendsto`: the energy is lower semicontinuous.
- `QuantumMechanics.tendsto_vonNeumannEntropy`: **Wehrl's theorem.** If `‖ρₘ - ρ‖₁ → 0` and
  `tr ρₘH ≤ h`, then `S(ρₘ) → S(ρ) < ∞`.

## iii. Table of contents

- A. Powers
- B. Eigenvalue sums
- C. The tail
- D. Continuity

## iv. References

- A. Wehrl, *General properties of entropy*, Rev. Mod. Phys. **50** (1978), 221–260,
  Sec. II.D, p. 241.
- M. E. Shirokov, *Entropic characteristics of subsets of states I*, arXiv:quant-ph/0510073,
  Prop. 1a.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder NNReal
open Filter Topology Real ProbabilisticTheory ProbabilisticTheory.TraceClass
open ContinuousLinearMap (posTrace posTrace_eq_tsum re_inner_apply_nonneg)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. Powers -/

lemma isTraceClass_pow_succ {ρ : E →L[ℂ] E} (hρ : IsTraceClass ρ) (n : ℕ) :
    IsTraceClass (ρ ^ (n + 1)) := by
  have h := isTraceClass_mul_mul (A := 1) (B := ρ ^ n) hρ
  rwa [one_mul, ← pow_succ'] at h

lemma isTraceClass_pow_sub_pow {ρ σ : E →L[ℂ] E} (hρ : IsTraceClass ρ) (hσ : IsTraceClass σ)
    (n : ℕ) : IsTraceClass (ρ ^ n - σ ^ n) := by
  rcases n with _ | n
  · simpa using isTraceClass_zero
  · exact isTraceClass_sub (isTraceClass_pow_succ hρ n) (isTraceClass_pow_succ hσ n)

omit [CompleteSpace E] in
lemma norm_pow_le_one {ρ : E →L[ℂ] E} (hρ : ‖ρ‖ ≤ 1) (n : ℕ) : ‖ρ ^ n‖ ≤ 1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    rw [pow_succ]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul ih hρ (norm_nonneg _) zero_le_one).trans (one_mul 1).le)

/-- `‖ρⁿ - σⁿ‖₁ ≤ n ‖ρ - σ‖₁` for density operators. -/
theorem traceENorm_pow_sub_pow_le {ρ σ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (n : ℕ) :
    traceENorm (ρ ^ n - σ ^ n) ≤ n * traceENorm (ρ - σ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have heq : ρ ^ (n + 1) - σ ^ (n + 1) = ρ * (ρ ^ n - σ ^ n) * 1 + 1 * (ρ - σ) * σ ^ n := by
      rw [pow_succ', pow_succ' σ, mul_one, one_mul, mul_sub, sub_mul]
      abel
    rw [heq]
    refine (traceENorm_add_le _ _).trans ?_
    have h1 := traceENorm_mul_mul_le ρ 1 (isTraceClass_pow_sub_pow hρ.isTraceClass
      hσ.isTraceClass n)
    have h2 := traceENorm_mul_mul_le 1 (σ ^ n) (isTraceClass_sub hρ.isTraceClass hσ.isTraceClass)
    have hρ1 : ‖ρ‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hρ.norm_le_one
    have hσ1 : ‖σ ^ n‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (norm_pow_le_one hσ.norm_le_one n)
    have h11 : ‖(1 : E →L[ℂ] E)‖ₑ ≤ 1 := by
      rw [← ofReal_norm, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ContinuousLinearMap.norm_id_le
    calc traceENorm (ρ * (ρ ^ n - σ ^ n) * 1) + traceENorm (1 * (ρ - σ) * σ ^ n)
        ≤ 1 * traceENorm (ρ ^ n - σ ^ n) * 1 + 1 * traceENorm (ρ - σ) * 1 := by
          gcongr
          · exact h1.trans (by gcongr)
          · exact h2.trans (by gcongr)
      _ ≤ n * traceENorm (ρ - σ) + traceENorm (ρ - σ) := by
          simp only [one_mul, mul_one]
          exact add_le_add_left ih _
      _ = (n + 1 : ℕ) * traceENorm (ρ - σ) := by push_cast; ring

lemma trace_eq_of_eq {X Y : E →L[ℂ] E} (h : X = Y) (hX : IsTraceClass X) (hY : IsTraceClass Y) :
    trace X hX = trace Y hY := by
  subst h; rfl

/-- The power traces `tr ρⁿ⁺¹ = posTrace ρⁿ⁺¹` are `1`-Lipschitz in `ρⁿ⁺¹` for the trace norm. -/
lemma abs_toReal_posTrace_pow_sub_le {ρ σ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (hσ : IsDensityOperator σ) (n : ℕ) :
    |(posTrace (ρ ^ (n + 1))).toReal - (posTrace (σ ^ (n + 1))).toReal| ≤
      (traceENorm (ρ ^ (n + 1) - σ ^ (n + 1))).toReal := by
  have hρn := isTraceClass_pow_succ hρ.isTraceClass n
  have hσn := isTraceClass_pow_succ hσ.isTraceClass n
  have hd := isTraceClass_sub hρn hσn
  have h1 := trace_eq_posTrace (CStarAlgebra.pow_nonneg ρ (n + 1) hρ.nonneg) hρn
  have h2 := trace_eq_posTrace (CStarAlgebra.pow_nonneg σ (n + 1) hσ.nonneg) hσn
  have hadd : trace (ρ ^ (n + 1)) hρn = trace (σ ^ (n + 1)) hσn + trace _ hd := by
    rw [← trace_add hσn hd]
    exact trace_eq_of_eq (by abel) _ _
  have hle := norm_trace_le hd
  rw [traceENorm_eq_ofReal hd, ENNReal.toReal_ofReal (traceNorm_nonneg _ _)]
  refine le_trans ?_ hle
  have : ((posTrace (ρ ^ (n + 1))).toReal - (posTrace (σ ^ (n + 1))).toReal : ℂ) =
      trace _ hd := by
    rw [← h1, ← h2, hadd]; ring
  rw [← this, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-! ## B. Eigenvalue sums -/

namespace IsEigenbasis

variable {ρ : E →L[ℂ] E} {ι : Type*} {e : HilbertBasis ι ℂ E} {ev : ι → ℝ}

omit [CompleteSpace E] in
lemma pow_apply (he : IsEigenbasis ρ e ev) (n : ℕ) (i : ι) :
    (ρ ^ n) (e i) = ((ev i ^ n : ℝ) : ℂ) • e i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp, he.apply_eq, map_smul, ih, smul_smul]
    push_cast
    ring_nf

lemma posTrace_pow_eq (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) (n : ℕ) :
    posTrace (ρ ^ n) = ∑' i, ENNReal.ofReal (ev i ^ n) := by
  rw [posTrace_eq_tsum (CStarAlgebra.pow_nonneg ρ n hρ.nonneg) e]
  congr 1
  ext i
  rw [he.pow_apply, inner_smul_right, inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
  simp only [Complex.coe_algebraMap, Complex.ofReal_one, one_pow, mul_one]
  rw [Complex.ofReal_re]

lemma summable (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) : Summable ev :=
  (summable_iff_tsum_ofReal_ne_top fun i => (he.eigenvalue_mem_Icc hρ i).1).2
    (by rw [he.tsum_ofReal_eq_one hρ]; exact ENNReal.one_ne_top)

lemma tsum_eq_one (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) : ∑' i, ev i = 1 := by
  have h := he.tsum_ofReal_eq_one hρ
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => (he.eigenvalue_mem_Icc hρ i).1)
    (he.summable hρ)] at h
  rwa [ENNReal.ofReal_eq_one] at h

lemma summable_pow (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) (n : ℕ) :
    Summable fun i => ev i ^ (n + 1) :=
  (he.summable hρ).of_nonneg_of_le (fun i => pow_nonneg (he.eigenvalue_mem_Icc hρ i).1 _)
    fun i => pow_le_of_le_one (he.eigenvalue_mem_Icc hρ i).1 (he.eigenvalue_mem_Icc hρ i).2
      n.succ_ne_zero

lemma tsum_pow_eq (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) (n : ℕ) :
    ∑' i, ev i ^ (n + 1) = (posTrace (ρ ^ (n + 1))).toReal := by
  rw [he.posTrace_pow_eq hρ, ← ENNReal.ofReal_tsum_of_nonneg
    (fun i => pow_nonneg (he.eigenvalue_mem_Icc hρ i).1 _) (he.summable_pow hρ n),
    ENNReal.toReal_ofReal (tsum_nonneg fun i => pow_nonneg (he.eigenvalue_mem_Icc hρ i).1 _)]

/-- `∑ᵢ λᵢ g(λᵢ)` is summable for `g` bounded on `[0, 1]`. -/
lemma summable_mul (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) {g : ℝ → ℝ} {C : ℝ}
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ C) : Summable fun i => ev i * g (ev i) := by
  refine Summable.of_norm_bounded ((he.summable hρ).mul_right C) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (he.eigenvalue_mem_Icc hρ i).1]
  exact mul_le_mul_of_nonneg_left (hg _ (he.eigenvalue_mem_Icc hρ i))
    (he.eigenvalue_mem_Icc hρ i).1

/-- Two functions within `ε` on `[0, 1]` give eigenvalue sums within `ε`. -/
lemma abs_tsum_mul_sub_le (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) {g h : ℝ → ℝ}
    {C D ε : ℝ} (hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ C) (hh : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ D)
    (hgh : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x - h x| ≤ ε) :
    |∑' i, ev i * g (ev i) - ∑' i, ev i * h (ev i)| ≤ ε := by
  rw [← (he.summable_mul hρ hg).tsum_sub (he.summable_mul hρ hh)]
  have hs : Summable fun i => ev i * ε := (he.summable hρ).mul_right ε
  calc |∑' i, (ev i * g (ev i) - ev i * h (ev i))|
      ≤ ∑' i, ev i * ε := by
        rw [← Real.norm_eq_abs]
        refine tsum_of_norm_bounded hs.hasSum fun i => ?_
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (he.eigenvalue_mem_Icc hρ i).1]
        exact mul_le_mul_of_nonneg_left (hgh _ (he.eigenvalue_mem_Icc hρ i))
          (he.eigenvalue_mem_Icc hρ i).1
    _ = ε := by rw [tsum_mul_right, he.tsum_eq_one hρ, one_mul]

end IsEigenbasis


namespace IsEigenbasis

variable {ρ : E →L[ℂ] E} {ι : Type*} {e : HilbertBasis ι ℂ E} {ev : ι → ℝ}

/-- For a polynomial `q`, `∑ᵢ λᵢ q(λᵢ) = ∑ⱼ qⱼ tr ρʲ⁺¹`. -/
lemma tsum_mul_eval (he : IsEigenbasis ρ e ev) (hρ : IsDensityOperator ρ) (q : Polynomial ℝ) :
    ∑' i, ev i * q.eval (ev i) =
      ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * (posTrace (ρ ^ (j + 1))).toReal := by
  have h : ∀ i, ev i * q.eval (ev i) =
      ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * ev i ^ (j + 1) := fun i => by
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [h]
  rw [Summable.tsum_finsetSum fun j _ => (he.summable_pow hρ j).mul_left _]
  exact Finset.sum_congr rfl fun j _ => by rw [tsum_mul_left, he.tsum_pow_eq hρ]

end IsEigenbasis

open scoped Classical in
/-- `∑ᵢ λᵢ g(λᵢ)` in the chosen eigenbasis of a density operator `ρ` (and `0` otherwise). -/
def eigenSum (g : ℝ → ℝ) (ρ : E →L[ℂ] E) : ℝ :=
  if hρ : IsDensityOperator ρ then ∑' i, hρ.eigenvalue i * g (hρ.eigenvalue i) else 0

lemma eigenSum_eq (g : ℝ → ℝ) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    eigenSum g ρ = ∑' i, hρ.eigenvalue i * g (hρ.eigenvalue i) :=
  dite_eq_left hρ

/-- The power traces are continuous in the trace norm on density operators. -/
lemma tendsto_toReal_posTrace_pow {α : Type*} {l : Filter α} {ρ : α → E →L[ℂ] E}
    {σ : E →L[ℂ] E} (hρ : ∀ a, IsDensityOperator (ρ a)) (hσ : IsDensityOperator σ)
    (h : Tendsto (fun a => traceENorm (ρ a - σ)) l (𝓝 0)) (n : ℕ) :
    Tendsto (fun a => (posTrace (ρ a ^ (n + 1))).toReal) l
      (𝓝 (posTrace (σ ^ (n + 1))).toReal) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have h' : Tendsto (fun a => ((n : ℝ) + 1) * (traceENorm (ρ a - σ)).toReal) l (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).const_mul ((n : ℝ) + 1)
    simpa using this
  refine squeeze_zero (fun _ => dist_nonneg) (fun a => ?_) h'
  rw [Real.dist_eq]
  refine (abs_toReal_posTrace_pow_sub_le (hρ a) hσ n).trans ?_
  have hb := traceENorm_pow_sub_pow_le (hρ a) hσ (n + 1)
  have hfin : traceENorm (ρ a - σ) ≠ ⊤ :=
    traceENorm_ne_top_iff.2 (isTraceClass_sub (hρ a).isTraceClass hσ.isTraceClass)
  calc (traceENorm (ρ a ^ (n + 1) - σ ^ (n + 1))).toReal
      ≤ (((n + 1 : ℕ) : ℝ≥0∞) * traceENorm (ρ a - σ)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin) hb
    _ = ((n : ℝ) + 1) * (traceENorm (ρ a - σ)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]; push_cast; ring

/-- **The head is continuous.** For `g` continuous on `[0, 1]`, `ρ ↦ ∑ᵢ λᵢ g(λᵢ)` is continuous
in the trace norm on density operators. -/
theorem tendsto_eigenSum {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc 0 1)) {α : Type*}
    {l : Filter α} {ρ : α → E →L[ℂ] E} {σ : E →L[ℂ] E} (hρ : ∀ a, IsDensityOperator (ρ a))
    (hσ : IsDensityOperator σ) (h : Tendsto (fun a => traceENorm (ρ a - σ)) l (𝓝 0)) :
    Tendsto (fun a => eigenSum g (ρ a)) l (𝓝 (eigenSum g σ)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  simp_rw [Real.norm_eq_abs] at hC
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg (ε / 3) (by positivity)
  have hqb : ∀ x ∈ Set.Icc (0 : ℝ) 1, |(fun x => q.eval x) x| ≤ C + ε / 3 := fun x hx => by
    have h1 := hq x hx
    have h2 := hC x hx
    calc |q.eval x| = |(q.eval x - g x) + g x| := by ring_nf
      _ ≤ |q.eval x - g x| + |g x| := abs_add_le _ _
      _ ≤ C + ε / 3 := by linarith
  have hgq : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x - (fun x => q.eval x) x| ≤ ε / 3 := fun x hx => by
    rw [abs_sub_comm]; exact (hq x hx).le
  have hP := tendsto_finsetSum (Finset.range (q.natDegree + 1)) fun j _ =>
    (tendsto_toReal_posTrace_pow hρ hσ h j).const_mul (q.coeff j)
  filter_upwards [Metric.tendsto_nhds.1 hP (ε / 3) (by positivity)] with a ha
  have h1 := (hρ a).isEigenbasis.abs_tsum_mul_sub_le (hρ a) hC hqb hgq
  have h2 := hσ.isEigenbasis.abs_tsum_mul_sub_le hσ hC hqb hgq
  beta_reduce at h1 h2
  rw [(hρ a).isEigenbasis.tsum_mul_eval (hρ a)] at h1
  rw [hσ.isEigenbasis.tsum_mul_eval hσ] at h2
  rw [Real.dist_eq] at ha ⊢
  rw [eigenSum_eq _ (hρ a), eigenSum_eq _ hσ]
  have h1' := abs_le.1 h1
  have h2' := abs_le.1 h2
  have ha' := abs_lt.1 ha
  rw [abs_lt]
  constructor <;> linarith

/-! ## C. The tail -/

/-- The tail `r_K(λ) = η(λ) - λ g_K(λ)` of `η(λ) = -λ log λ`, with `g_K(λ) = min(-log λ, K)`. -/
def tailTerm (K : ℕ) (x : ℝ) : ℝ := negMulLog x - x * negLogTrunc K x

lemma negLogTrunc_le (K : ℕ) (x : ℝ) : negLogTrunc K x ≤ K := by
  have h : log (exp (-(K : ℝ))) ≤ log (max x (exp (-K))) :=
    Real.log_le_log (exp_pos _) (le_max_right _ _)
  rw [Real.log_exp] at h
  unfold negLogTrunc
  linarith

lemma tailTerm_nonneg (K : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ tailTerm K x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [tailTerm]
  have h : negLogTrunc K x ≤ -log x := neg_le_neg (Real.log_le_log hx (le_max_left _ _))
  have := mul_le_mul_of_nonneg_left h hx.le
  unfold tailTerm negMulLog
  linarith

/-- The scalar tail bound: `r_K(λ) ≤ β w λ + e^{-K-1} e^{-βw}`, from Klein's inequality with
`b = e^{-K-1-βw}`. -/
lemma tailTerm_le (K : ℕ) {x : ℝ} (hx : 0 ≤ x) {β w : ℝ} (hβw : 0 ≤ β * w) :
    tailTerm K x ≤ β * w * x + exp (-((K : ℝ) + 1)) * exp (-(β * w)) := by
  have hb : 0 < exp (-((K : ℝ) + 1)) * exp (-(β * w)) := by positivity
  by_cases hxK : exp (-(K : ℝ)) ≤ x
  · have h : negLogTrunc K x = -log x := by unfold negLogTrunc; rw [max_eq_left hxK]
    have h0 : tailTerm K x = 0 := by unfold tailTerm negMulLog; rw [h]; ring
    rw [h0]
    have := mul_nonneg hβw hx
    linarith
  · push Not at hxK
    have h : negLogTrunc K x = K := by
      unfold negLogTrunc; rw [max_eq_right hxK.le, Real.log_exp, neg_neg]
    have hk := kleinReal_nonneg hx hb
    rw [Real.log_mul (exp_pos _).ne' (exp_pos _).ne', Real.log_exp, Real.log_exp] at hk
    unfold tailTerm negMulLog
    rw [h]
    nlinarith

omit [CompleteSpace E] in
/-- Parseval in `[0, ∞]`: `∑ᵢ |⟨eᵢ, x⟩|² = ‖x‖²`. -/
lemma tsum_ofReal_norm_inner_sq {ι : Type*} (e : HilbertBasis ι ℂ E) (x : E) :
    ∑' i, ENNReal.ofReal (‖⟪e i, x⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (e.repr x)
  simp only [HilbertBasis.repr_apply_apply, LinearIsometryEquiv.norm_map, ENNReal.toReal_ofNat,
    Real.rpow_two] at h
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) h.summable, h.tsum_eq]

open scoped Classical in
/-- The tail sum `∑ᵢ r_K(λᵢ) ∈ [0, ∞]` in the chosen eigenbasis (and `0` otherwise). -/
def tailSum (K : ℕ) (ρ : E →L[ℂ] E) : ℝ≥0∞ :=
  if hρ : IsDensityOperator ρ then ∑' i, ENNReal.ofReal (tailTerm K (hρ.eigenvalue i)) else 0

/-- `S(ρ) = ∑ᵢ λᵢ g_K(λᵢ) + ∑ᵢ r_K(λᵢ)`. -/
theorem vonNeumannEntropy_eq_add {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (K : ℕ) :
    vonNeumannEntropy ρ = ENNReal.ofReal (eigenSum (negLogTrunc K) ρ) + tailSum K ρ := by
  have he := hρ.isEigenbasis
  have hev := fun i => he.eigenvalue_mem_Icc hρ i
  have hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, |negLogTrunc K x| ≤ K := fun x hx => by
    rw [abs_of_nonneg (negLogTrunc_nonneg K hx.2)]; exact negLogTrunc_le K x
  rw [he.vonNeumannEntropy_eq hρ, eigenSum_eq _ hρ, tailSum, dite_eq_left hρ,
    ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hev i).1 (negLogTrunc_nonneg K (hev i).2))
      (he.summable_mul hρ hg), ← tsum_add]
  congr 1
  ext i
  rw [← ENNReal.ofReal_add (mul_nonneg (hev i).1 (negLogTrunc_nonneg K (hev i).2))
    (tailTerm_nonneg K (hev i).1)]
  congr 1
  unfold tailTerm
  ring

section Energy

variable {κ : Type*} (b : HilbertBasis κ ℂ E) (ω : κ → ℝ)

/-- The energy `tr ρH = ∑ₖ ωₖ ⟨bₖ, ρ bₖ⟩ ∈ [0, ∞]` of `H = ∑ₖ ωₖ |bₖ⟩⟨bₖ|`. -/
def energy (ρ : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' k, ENNReal.ofReal (ω k) * ENNReal.ofReal (⟪b k, ρ (b k)⟫_ℂ).re

/-- The partition function `tr e^{-βH} ∈ [0, ∞]`. -/
def partitionFn (β : ℝ) : ℝ≥0∞ := ∑' k, ENNReal.ofReal (exp (-(β * ω k)))

variable {b ω}

/-- **The tail bound.** `∑ᵢ r_K(λᵢ) ≤ β tr ρH + e^{-K-1} tr e^{-βH}` for every `β ≥ 0`. -/
theorem tailSum_le {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (hω : ∀ k, 0 ≤ ω k) (K : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) :
    tailSum K ρ ≤ ENNReal.ofReal β * energy b ω ρ +
      ENNReal.ofReal (exp (-((K : ℝ) + 1))) * partitionFn ω β := by
  have he := hρ.isEigenbasis
  set ev := hρ.eigenvalue
  set e := hρ.eigenbasis
  have hev := fun i => he.eigenvalue_mem_Icc hρ i
  set c : hρ.eigenIndex → κ → ℝ≥0∞ := fun i k => ENNReal.ofReal (‖⟪b k, e i⟫_ℂ‖ ^ 2) with hc
  have hc1 : ∀ i, ∑' k, c i k = 1 := fun i => by
    rw [hc, tsum_ofReal_norm_inner_sq b, e.orthonormal.1 i]; simp
  have hc2 : ∀ k, ∑' i, c i k = 1 := fun k => by
    simp_rw [hc, norm_inner_symm (b k)]
    rw [tsum_ofReal_norm_inner_sq e, b.orthonormal.1 k]; simp
  have hE : ∀ k, ENNReal.ofReal (⟪b k, ρ (b k)⟫_ℂ).re = ∑' i, c i k * ENNReal.ofReal (ev i) := by
    intro k
    rw [he.ofReal_re_inner_apply hρ (b k)]
    refine tsum_congr fun i => ?_
    rw [hc, norm_inner_symm, mul_comm]
  set t := ENNReal.ofReal (exp (-((K : ℝ) + 1)))
  have hterm : ∀ i k, ENNReal.ofReal (tailTerm K (ev i)) ≤
      ENNReal.ofReal β * (ENNReal.ofReal (ω k) * ENNReal.ofReal (ev i)) +
        t * ENNReal.ofReal (exp (-(β * ω k))) := fun i k => by
    rw [← ENNReal.ofReal_mul (hω k), ← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_mul (exp_pos _).le,
      ← ENNReal.ofReal_add (mul_nonneg hβ (mul_nonneg (hω k) (hev i).1)) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((tailTerm_le K (hev i).1 (mul_nonneg hβ (hω k))).trans
      (le_of_eq ?_))
    ring
  calc tailSum K ρ = ∑' i, ∑' k, c i k * ENNReal.ofReal (tailTerm K (ev i)) := by
        rw [tailSum, dite_eq_left hρ]
        exact tsum_congr fun i => by rw [ENNReal.tsum_mul_right, hc1, one_mul]
    _ ≤ ∑' i, ∑' k, c i k * (ENNReal.ofReal β * (ENNReal.ofReal (ω k) * ENNReal.ofReal (ev i)) +
          t * ENNReal.ofReal (exp (-(β * ω k)))) :=
        tsum_le_tsum fun i => tsum_le_tsum fun k => by gcongr; exact hterm i k
    _ = ENNReal.ofReal β * ∑' k, ENNReal.ofReal (ω k) * ∑' i, c i k * ENNReal.ofReal (ev i) +
          t * ∑' k, ENNReal.ofReal (exp (-(β * ω k))) * ∑' i, c i k := by
        rw [tsum_comm]
        simp_rw [mul_add, tsum_add]
        congr 1
        · rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun i => by ring
        · rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun k => ?_
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          exact tsum_congr fun i => by ring
    _ = ENNReal.ofReal β * energy b ω ρ + t * partitionFn ω β := by
        simp_rw [hc2, mul_one, ← hE]
        rfl

/-- The energy is lower semicontinuous in the trace norm. -/
theorem energy_le_of_tendsto {α : Type*} {l : Filter α} [l.NeBot] {ρ : α → E →L[ℂ] E}
    {σ : E →L[ℂ] E} (h : Tendsto (fun a => traceENorm (ρ a - σ)) l (𝓝 0)) {h₀ : ℝ≥0∞}
    (hE : ∀ᶠ a in l, energy b ω (ρ a) ≤ h₀) : energy b ω σ ≤ h₀ := by
  have hρσ := tendsto_of_tendsto_traceENorm h
  rw [energy, tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hk : ∀ k, Tendsto (fun a => ENNReal.ofReal (ω k) * ENNReal.ofReal (⟪b k, ρ a (b k)⟫_ℂ).re)
      l (𝓝 (ENNReal.ofReal (ω k) * ENNReal.ofReal (⟪b k, σ (b k)⟫_ℂ).re)) := fun k => by
    have hc : Continuous fun A : E →L[ℂ] E => ENNReal.ofReal (⟪b k, A (b k)⟫_ℂ).re :=
      ENNReal.continuous_ofReal.comp (Complex.continuous_re.comp
        ((innerSL ℂ (b k)).continuous.comp (ContinuousLinearMap.apply ℂ E (b k)).continuous))
    exact ENNReal.Tendsto.const_mul ((hc.tendsto σ).comp hρσ) (Or.inr ENNReal.ofReal_ne_top)
  refine le_of_tendsto (tendsto_finsetSum s fun k _ => hk k) ?_
  filter_upwards [hE] with a ha
  exact (sum_le_tsum s).trans ha

lemma partitionFn_ne_top {β : ℝ} (hZ : Summable fun k => exp (-(β * ω k))) :
    partitionFn ω β ≠ ⊤ := by
  rw [partitionFn, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => (exp_pos _).le) hZ]
  exact ENNReal.ofReal_ne_top

/-- **The entropy is finite at finite energy**, when `tr e^{-βH} < ∞` for some `β ≥ 0`. -/
theorem vonNeumannEntropy_ne_top {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (hω : ∀ k, 0 ≤ ω k)
    {β : ℝ} (hβ : 0 ≤ β) (hZ : Summable fun k => exp (-(β * ω k))) (hE : energy b ω ρ ≠ ⊤) :
    vonNeumannEntropy ρ ≠ ⊤ := by
  rw [vonNeumannEntropy_eq_add hρ 0]
  refine ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ne_top_of_le_ne_top ?_ (tailSum_le (b := b) hρ hω 0 hβ)⟩
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (partitionFn_ne_top hZ)⟩

/-! ## D. Continuity -/

/-- **Wehrl's theorem.** Let `H = ∑ₖ ωₖ |bₖ⟩⟨bₖ| ≥ 0` with `tr e^{-βH} < ∞` for all `β > 0`. If
density operators `ρₘ` converge to `σ` in the trace norm and their energies are eventually
bounded by `h`, then `S(ρₘ) → S(σ)`, and `S(σ) < ∞`. -/
theorem tendsto_vonNeumannEntropy (hω : ∀ k, 0 ≤ ω k)
    (hZ : ∀ β > 0, Summable fun k => exp (-(β * ω k))) {α : Type*} {l : Filter α}
    {ρ : α → E →L[ℂ] E} {σ : E →L[ℂ] E} (hρ : ∀ a, IsDensityOperator (ρ a))
    (hσ : IsDensityOperator σ) (h : Tendsto (fun a => traceENorm (ρ a - σ)) l (𝓝 0)) {h₀ : ℝ≥0}
    (hE : ∀ᶠ a in l, energy b ω (ρ a) ≤ h₀) :
    Tendsto (fun a => vonNeumannEntropy (ρ a)) l (𝓝 (vonNeumannEntropy σ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  have hEσ : energy b ω σ ≤ h₀ := energy_le_of_tendsto h hE
  have hfin : ∀ τ, IsDensityOperator τ → energy b ω τ ≤ h₀ → vonNeumannEntropy τ ≠ ⊤ :=
    fun τ hτ hτE => vonNeumannEntropy_ne_top hτ hω zero_le_one (hZ 1 one_pos)
      (ne_top_of_le_ne_top ENNReal.coe_ne_top hτE)
  -- reduce to the real parts
  suffices hr : Tendsto (fun a => (vonNeumannEntropy (ρ a)).toReal) l
      (𝓝 (vonNeumannEntropy σ).toReal) by
    rw [← ENNReal.ofReal_toReal (hfin σ hσ hEσ)]
    refine (ENNReal.tendsto_ofReal hr).congr' ?_
    filter_upwards [hE] with a ha
    exact ENNReal.ofReal_toReal (hfin _ (hρ a) ha)
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose `β`, then `K`, so that the tail is below `ε / 2` on the whole energy shell
  set β : ℝ := ε / (4 * ((h₀ : ℝ) + 1)) with hβdef
  have hβ : 0 < β := by positivity
  have hβh : β * h₀ ≤ ε / 4 := by
    rw [hβdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [NNReal.coe_nonneg h₀]
  set Z : ℝ := ∑' k, exp (-(β * ω k))
  have hK : Tendsto (fun K : ℕ => exp (-((K : ℝ) + 1)) * Z) atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => -((K : ℝ) + 1)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using (Real.tendsto_exp_atBot.comp h1).mul_const Z
  obtain ⟨K, hKZ⟩ := (hK.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))).exists
  set d : ℝ := β * h₀ + exp (-((K : ℝ) + 1)) * Z
  have hd : d < ε / 2 := by simp only [d]; linarith
  have hZβ : partitionFn ω β = ENNReal.ofReal Z := by
    rw [partitionFn, ENNReal.ofReal_tsum_of_nonneg (fun _ => (exp_pos _).le) (hZ β hβ)]
  -- on the energy shell, `S(τ) = head + tail` with `0 ≤ tail ≤ d`
  have hsplit : ∀ τ, IsDensityOperator τ → energy b ω τ ≤ h₀ →
      ∃ t, 0 ≤ t ∧ t ≤ d ∧ (vonNeumannEntropy τ).toReal = eigenSum (negLogTrunc K) τ + t := by
    intro τ hτ hτE
    have htail := tailSum_le (b := b) hτ hω K hβ.le
    have hdle : ENNReal.ofReal β * energy b ω τ +
        ENNReal.ofReal (exp (-((K : ℝ) + 1))) * partitionFn ω β ≤ ENNReal.ofReal d := by
      rw [hZβ, ← ENNReal.ofReal_mul (exp_pos _).le]
      have : ENNReal.ofReal β * energy b ω τ ≤ ENNReal.ofReal (β * h₀) := by
        rw [ENNReal.ofReal_mul hβ.le, ENNReal.ofReal_coe_nnreal]
        gcongr
      refine (add_le_add_left this _).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    have htop : tailSum K τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (htail.trans hdle)
    refine ⟨(tailSum K τ).toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
    · exact ENNReal.toReal_le_of_le_ofReal (by positivity) (htail.trans hdle)
    · have hhead : 0 ≤ eigenSum (negLogTrunc K) τ := by
        rw [eigenSum_eq _ hτ]
        exact tsum_nonneg fun i => mul_nonneg (hτ.isEigenbasis.eigenvalue_mem_Icc hτ i).1
          (negLogTrunc_nonneg K (hτ.isEigenbasis.eigenvalue_mem_Icc hτ i).2)
      rw [vonNeumannEntropy_eq_add hτ K, ENNReal.toReal_add ENNReal.ofReal_ne_top htop,
        ENNReal.toReal_ofReal hhead]
  have hhead := Metric.tendsto_nhds.1
    (tendsto_eigenSum (continuous_negLogTrunc K).continuousOn hρ hσ h) (ε / 2) (by positivity)
  filter_upwards [hhead, hE] with a ha haE
  obtain ⟨t, ht0, htd, ht⟩ := hsplit _ (hρ a) haE
  obtain ⟨s, hs0, hsd, hs⟩ := hsplit _ hσ hEσ
  rw [Real.dist_eq] at ha ⊢
  rw [ht, hs]
  have ha' := abs_lt.1 ha
  rw [abs_lt]
  constructor <;> linarith

end Energy

end QuantumMechanics
