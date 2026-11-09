/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.SpecialFunctions.Pow.NegMulLog
public import ForPhyslib.QuantumMechanics.VonNeumannEntropyMixture
public import ForPhyslib.QuantumMechanics.VonNeumannResolvent.Irreversible

/-!
# The quasi-static limit of the resolvent is reversible

A reversible quasi-static process in thermodynamics is a limit of equilibration steps: each step
is irreversible and produces entropy, but the production is quadratic in the step, so over `n`
steps it is `O(1/n)` and vanishes in the limit. The same holds for the resolvent
`Ψ τ = (1 - τ L)⁻¹` of the von Neumann generator `L ρ = -i (K ρ - ρ K)` on a finite-dimensional
complex Hilbert space, with irreversibility measured by purity or by entropy.

*Purity.* With `‖A‖₂² = tr (A† A)` the squared Hilbert–Schmidt norm, `‖L σ‖₂ ≤ 2 ‖K‖ ‖σ‖₂`, and
`‖ρ‖₂² - ‖Ψ τ ρ‖₂² = τ² ‖L Ψ τ ρ‖₂²` (skewness of `L`). So one step loses at most
`4 ‖K‖² τ² ‖ρ‖₂²` of the purity, and `n` steps of duration `t / n` at most
`4 ‖K‖² t² ‖ρ‖₂² / n`. The loss of a single step is positive unless `L ρ = 0`
(`re_trace_star_mul_self_vonNeumannResolvent_lt`).

*Entropy.* For a density operator `σ` in dimension `d`, `S(σ) ≤ 8 d (1 - tr σ²)^{3/4}`
(`Real.sum_negMulLog_le` on the eigenvalues). On a pure input one step therefore produces entropy
at most `8 d a √a` with `a = 2 ‖K‖ |τ|`, and along any sequence of pure states the entropy produced
in `n` steps of duration `t / n` is at most `8 d c √(c / n)`, `c = 2 ‖K‖ |t|`.

## Main definitions

* `QuantumMechanics.hsNormSq`: the squared Hilbert–Schmidt norm `tr (A† A)`.

## Main results

* `QuantumMechanics.hsNormSq_vonNeumannGenerator_le`: `‖L σ‖₂² ≤ 4 ‖K‖² ‖σ‖₂²`.
* `QuantumMechanics.hsNormSq_sub_hsNormSq_vonNeumannResolvent_le`: the purity loss of one step.
* `QuantumMechanics.tendsto_hsNormSq_sub_hsNormSq_vonNeumannResolvent_iterate`: the purity loss of
  `(Ψ (t / n))ⁿ` tends to zero.
* `QuantumMechanics.tendsto_sum_one_sub_hsNormSq_vonNeumannResolvent_proj`: so does the total
  purity loss along any sequence of pure states.
* `QuantumMechanics.Wigner.IsDensity.vonNeumannEntropy_le`: `S(σ) ≤ 8 d (1 - tr σ²)^{3/4}`.
* `QuantumMechanics.tendsto_sum_vonNeumannEntropy_vonNeumannResolvent_proj`: the total entropy
  produced along any sequence of pure states tends to zero.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ComplexOrder ENNReal Topology
open InnerProductSpace QuantumMechanics.Wigner Complex Filter

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

/-! ## A. The Hilbert–Schmidt norm -/

/-- The squared Hilbert–Schmidt norm `‖A‖₂² = tr (A† A)`. -/
def hsNormSq (A : E →L[ℂ] E) : ℝ := re (LinearMap.trace ℂ E ↑(star A * A))

omit [FiniteDimensional ℂ E] in
lemma hsNormSq_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) (A : E →L[ℂ] E) :
    hsNormSq A = ∑ i, ‖A (b i)‖ ^ 2 :=
  re_trace_star_mul_self A b

lemma hsNormSq_nonneg (A : E →L[ℂ] E) : 0 ≤ hsNormSq A := by
  rw [hsNormSq_eq_sum (stdOrthonormalBasis ℂ E)]
  positivity

lemma hsNormSq_proj {ψ : E} (hψ : ‖ψ‖ = 1) : hsNormSq (proj ψ) = 1 :=
  re_trace_star_proj_mul_proj hψ

omit [FiniteDimensional ℂ E] in
lemma hsNormSq_star (A : E →L[ℂ] E) : hsNormSq (star A) = hsNormSq A := by
  rw [hsNormSq, hsNormSq, star_star, ContinuousLinearMap.toLinearMap_mul,
    LinearMap.trace_mul_comm, ← ContinuousLinearMap.toLinearMap_mul]

lemma hsNormSq_mul_le_left (A B : E →L[ℂ] E) : hsNormSq (A * B) ≤ ‖A‖ ^ 2 * hsNormSq B := by
  rw [hsNormSq_eq_sum (stdOrthonormalBasis ℂ E), hsNormSq_eq_sum (stdOrthonormalBasis ℂ E),
    Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2

lemma hsNormSq_mul_le_right (A B : E →L[ℂ] E) : hsNormSq (A * B) ≤ hsNormSq A * ‖B‖ ^ 2 := by
  rw [← hsNormSq_star, star_mul, ← hsNormSq_star A, mul_comm (hsNormSq _), ← norm_star B]
  exact hsNormSq_mul_le_left _ _

lemma hsNormSq_sub_le (A B : E →L[ℂ] E) :
    hsNormSq (A - B) ≤ 2 * hsNormSq A + 2 * hsNormSq B := by
  simp only [hsNormSq_eq_sum (stdOrthonormalBasis ℂ E), Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  set a := A (stdOrthonormalBasis ℂ E i)
  set b := B (stdOrthonormalBasis ℂ E i)
  rw [sub_apply]
  have h := norm_sub_le a b
  nlinarith [mul_self_le_mul_self (norm_nonneg _) h, sq_nonneg (‖a‖ - ‖b‖)]

lemma hsNormSq_smul (c : ℂ) (A : E →L[ℂ] E) : hsNormSq (c • A) = ‖c‖ ^ 2 * hsNormSq A := by
  simp only [hsNormSq_eq_sum (stdOrthonormalBasis ℂ E), Finset.mul_sum, smul_apply, norm_smul,
    mul_pow]

/-- `‖L σ‖₂² ≤ 4 ‖K‖² ‖σ‖₂²`. -/
lemma hsNormSq_vonNeumannGenerator_le (K σ : E →L[ℂ] E) :
    hsNormSq (vonNeumannGenerator K σ) ≤ 4 * ‖K‖ ^ 2 * hsNormSq σ := by
  rw [vonNeumannGenerator_apply, hsNormSq_smul, norm_neg, norm_I, one_pow, one_mul]
  calc hsNormSq (K * σ - σ * K) ≤ 2 * hsNormSq (K * σ) + 2 * hsNormSq (σ * K) :=
        hsNormSq_sub_le _ _
    _ ≤ 2 * (‖K‖ ^ 2 * hsNormSq σ) + 2 * (hsNormSq σ * ‖K‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left (hsNormSq_mul_le_left _ _) zero_le_two)
          (mul_le_mul_of_nonneg_left (hsNormSq_mul_le_right _ _) zero_le_two)
    _ = 4 * ‖K‖ ^ 2 * hsNormSq σ := by ring

/-! ## B. Purity -/

variable (V : UnitaryOneParameterGroup E)

lemma hsNormSq_vonNeumannResolvent_le (τ : ℝ) (ρ : E →L[ℂ] E) :
    hsNormSq (vonNeumannResolvent V τ ρ) ≤ hsNormSq ρ := by
  have h := re_trace_star_mul_self_eq_vonNeumannResolvent V τ ρ
  change hsNormSq ρ = hsNormSq (vonNeumannResolvent V τ ρ) +
    τ ^ 2 * hsNormSq (vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ)) at h
  nlinarith [hsNormSq_nonneg (vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ)),
    sq_nonneg τ]

/-- **One step loses at most `4 ‖K‖² τ²` of the purity**, relative to `‖ρ‖₂²`. -/
theorem hsNormSq_sub_hsNormSq_vonNeumannResolvent_le (τ : ℝ) (ρ : E →L[ℂ] E) :
    hsNormSq ρ - hsNormSq (vonNeumannResolvent V τ ρ) ≤
      4 * ‖V.generator‖ ^ 2 * τ ^ 2 * hsNormSq ρ := by
  have h := re_trace_star_mul_self_eq_vonNeumannResolvent V τ ρ
  change hsNormSq ρ = hsNormSq (vonNeumannResolvent V τ ρ) +
    τ ^ 2 * hsNormSq (vonNeumannGenerator V.generator (vonNeumannResolvent V τ ρ)) at h
  have h1 := mul_le_mul_of_nonneg_left
    (hsNormSq_vonNeumannGenerator_le V.generator (vonNeumannResolvent V τ ρ)) (sq_nonneg τ)
  have h2 := mul_le_mul_of_nonneg_left (hsNormSq_vonNeumannResolvent_le V τ ρ)
    (by positivity : 0 ≤ 4 * ‖V.generator‖ ^ 2 * τ ^ 2)
  linarith

lemma hsNormSq_vonNeumannResolvent_iterate_le (τ : ℝ) (ρ : E →L[ℂ] E) (n : ℕ) :
    hsNormSq ((vonNeumannResolvent V τ)^[n] ρ) ≤ hsNormSq ρ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hsNormSq_vonNeumannResolvent_le V τ _).trans ih

/-- `n` steps lose at most `n · 4 ‖K‖² τ²` of the purity, relative to `‖ρ‖₂²`. -/
theorem hsNormSq_sub_hsNormSq_vonNeumannResolvent_iterate_le (τ : ℝ) (ρ : E →L[ℂ] E) (n : ℕ) :
    hsNormSq ρ - hsNormSq ((vonNeumannResolvent V τ)^[n] ρ) ≤
      n * (4 * ‖V.generator‖ ^ 2 * τ ^ 2) * hsNormSq ρ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 := hsNormSq_sub_hsNormSq_vonNeumannResolvent_le V τ
      ((vonNeumannResolvent V τ)^[n] ρ)
    have h2 := mul_le_mul_of_nonneg_left (hsNormSq_vonNeumannResolvent_iterate_le V τ ρ n)
      (by positivity : 0 ≤ 4 * ‖V.generator‖ ^ 2 * τ ^ 2)
    push_cast
    linarith

/-- **The quasi-static limit is reversible**: the purity lost by `n` steps of duration `t / n`
is at most `4 ‖K‖² t² ‖ρ‖₂² / n`, and tends to zero. -/
theorem tendsto_hsNormSq_sub_hsNormSq_vonNeumannResolvent_iterate (t : ℝ) (ρ : E →L[ℂ] E) :
    Tendsto (fun n : ℕ => hsNormSq ρ - hsNormSq ((vonNeumannResolvent V (t / n))^[n] ρ))
      atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n =>
    sub_nonneg.mpr (hsNormSq_vonNeumannResolvent_iterate_le V _ ρ n)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (4 * ‖V.generator‖ ^ 2 * t ^ 2 * hsNormSq ρ))
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine (hsNormSq_sub_hsNormSq_vonNeumannResolvent_iterate_le V _ ρ n).trans_eq ?_
  field_simp

/-- A pure input loses at most `4 ‖K‖² τ²` of its purity. -/
lemma one_sub_hsNormSq_vonNeumannResolvent_proj_le (τ : ℝ) {ψ : E} (hψ : ‖ψ‖ = 1) :
    1 - hsNormSq (vonNeumannResolvent V τ (proj ψ)) ≤ 4 * ‖V.generator‖ ^ 2 * τ ^ 2 := by
  simpa [hsNormSq_proj hψ] using hsNormSq_sub_hsNormSq_vonNeumannResolvent_le V τ (proj ψ)

lemma one_sub_hsNormSq_vonNeumannResolvent_proj_nonneg (τ : ℝ) {ψ : E} (hψ : ‖ψ‖ = 1) :
    0 ≤ 1 - hsNormSq (vonNeumannResolvent V τ (proj ψ)) := by
  simpa [hsNormSq_proj hψ] using hsNormSq_vonNeumannResolvent_le V τ (proj ψ)

/-- **Along any sequence of pure states the total purity loss vanishes**: for unit vectors
`ψ n k`, `∑_{k < n} (1 - tr (Ψ (t / n) |ψ n k⟩⟨ψ n k|)²) → 0`. -/
theorem tendsto_sum_one_sub_hsNormSq_vonNeumannResolvent_proj (t : ℝ) {ψ : ℕ → ℕ → E}
    (hψ : ∀ n k, ‖ψ n k‖ = 1) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      (1 - hsNormSq (vonNeumannResolvent V (t / n) (proj (ψ n k))))) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun n => Finset.sum_nonneg fun k _ =>
    one_sub_hsNormSq_vonNeumannResolvent_proj_nonneg V _ (hψ n k)) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (4 * ‖V.generator‖ ^ 2 * t ^ 2))
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  refine (Finset.sum_le_sum fun k _ =>
    one_sub_hsNormSq_vonNeumannResolvent_proj_le V (t / n) (hψ n k)).trans_eq ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-! ## C. Entropy -/

omit [CompleteSpace E] in
private lemma sq_rpow_three_div_four {a : ℝ} (ha : 0 ≤ a) : (a ^ 2) ^ (3 / 4 : ℝ) = a * √a := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]
  rw [show ((2 : ℕ) : ℝ) * (3 / 4) = 1 + 1 / 2 by norm_num, Real.rpow_add' ha (by norm_num),
    Real.rpow_one]

/-- **Entropy is bounded by the purity loss**: `S(σ) ≤ 8 d (1 - tr σ²)^{3/4}` for a density
operator `σ` in dimension `d`. -/
theorem Wigner.IsDensity.vonNeumannEntropy_le {σ : E →L[ℂ] E} (hσ : IsDensity σ) :
    vonNeumannEntropy σ ≤
      ENNReal.ofReal (8 * Module.finrank ℂ E * (1 - hsNormSq σ) ^ (3 / 4 : ℝ)) := by
  set hT := hσ.isPositive.isSymmetric
  set b := hT.eigenvectorBasis rfl
  set μ := hT.eigenvalues rfl
  have hμ0 : ∀ i, 0 ≤ μ i := hσ.isPositive.nonneg_eigenvalues rfl
  have hμ1 : ∑ i, μ i = 1 := hσ.sum_eigenvalues
  have hμle : ∀ i, μ i ≤ 1 := fun i =>
    hμ1 ▸ Finset.single_le_sum (fun j _ => hμ0 j) (Finset.mem_univ i)
  have hS : vonNeumannEntropy σ = ENNReal.ofReal (∑ i, Real.negMulLog (μ i)) := by
    conv_lhs => rw [hσ.eq_sum_proj, ← tsum_fintype (L := SummationFilter.unconditional _)]
    have hμs : HasSum μ 1 := by
      rw [← hμ1]
      exact hasSum_fintype μ
    rw [vonNeumannEntropy_tsum_smul_proj b.orthonormal hμ0 hμs,
      tsum_fintype, ENNReal.ofReal_sum_of_nonneg fun i _ =>
        Real.negMulLog_nonneg (hμ0 i) (hμle i)]
  have hP : hsNormSq σ = ∑ i, μ i ^ 2 := by
    rw [hsNormSq_eq_sum b]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := hT.apply_eigenvectorBasis rfl i
    simp only [ContinuousLinearMap.coe_coe] at h
    rw [h, norm_smul, b.orthonormal.1 i, mul_one, RCLike.norm_ofReal, sq_abs]
  rw [hS, hP]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa using Real.sum_negMulLog_le Finset.univ (fun i _ => hμ0 i) hμ1

/-- One step on a pure input produces entropy at most `8 d a √a`, with `a = 2 ‖K‖ |τ|`. -/
theorem vonNeumannEntropy_vonNeumannResolvent_proj_le (τ : ℝ) {ψ : E} (hψ : ‖ψ‖ = 1) :
    vonNeumannEntropy (vonNeumannResolvent V τ (proj ψ)) ≤
      ENNReal.ofReal (8 * Module.finrank ℂ E * (2 * ‖V.generator‖ * |τ|) *
        √(2 * ‖V.generator‖ * |τ|)) := by
  refine (isDensity_vonNeumannResolvent V τ (isDensity_proj hψ)).vonNeumannEntropy_le.trans
    (ENNReal.ofReal_le_ofReal ?_)
  have ha : 0 ≤ 2 * ‖V.generator‖ * |τ| := by positivity
  have h1 : 1 - hsNormSq (vonNeumannResolvent V τ (proj ψ)) ≤ (2 * ‖V.generator‖ * |τ|) ^ 2 := by
    have he : (2 * ‖V.generator‖ * |τ|) ^ 2 = 4 * ‖V.generator‖ ^ 2 * τ ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
      norm_num
    rw [he]
    exact one_sub_hsNormSq_vonNeumannResolvent_proj_le V τ hψ
  have h2 := Real.rpow_le_rpow (one_sub_hsNormSq_vonNeumannResolvent_proj_nonneg V τ hψ) h1
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [sq_rpow_three_div_four ha] at h2
  rw [mul_assoc _ (2 * ‖V.generator‖ * |τ|)]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **The quasi-static limit produces no entropy**: along any sequence of pure states `ψ n k`,
the total entropy `∑_{k < n} S(Ψ (t / n) |ψ n k⟩⟨ψ n k|)` produced by `n` steps of duration
`t / n` is at most `8 d c √(c / n)`, `c = 2 ‖K‖ |t|`, and tends to zero. -/
theorem tendsto_sum_vonNeumannEntropy_vonNeumannResolvent_proj (t : ℝ) {ψ : ℕ → ℕ → E}
    (hψ : ∀ n k, ‖ψ n k‖ = 1) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      vonNeumannEntropy (vonNeumannResolvent V (t / n) (proj (ψ n k)))) atTop (𝓝 0) := by
  set c := 2 * ‖V.generator‖ * |t|
  have hb : ∀ n : ℕ, n ≠ 0 → ∑ k ∈ Finset.range n,
      vonNeumannEntropy (vonNeumannResolvent V (t / n) (proj (ψ n k))) ≤
        ENNReal.ofReal (8 * Module.finrank ℂ E * c * √(c / n)) := fun n hn => by
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have he : 2 * ‖V.generator‖ * |t / n| = c / n := by
      rw [abs_div, Nat.abs_cast]
      ring
    refine (Finset.sum_le_sum fun k _ =>
      vonNeumannEntropy_vonNeumannResolvent_proj_le V (t / n) (hψ n k)).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), he]
    congr 1
    field_simp
  have hlim : Tendsto (fun n : ℕ => 8 * Module.finrank ℂ E * c * √(c / n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_def] using
      ((Real.continuous_sqrt.tendsto 0).comp
        (tendsto_const_div_atTop_nhds_zero_nat c)).const_mul (8 * Module.finrank ℂ E * c)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hlim)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ne_atTop 0] with n hn using hb n hn

end QuantumMechanics
