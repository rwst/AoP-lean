/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Entropy is not continuous in standard probability spaces.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

On a measure space `(X, μ)`, consider probability densities `ρ` with finite entropy
`S(ρ) = -∫ ρ log₂ ρ dμ`. The Jensen–Shannon divergence and the `L¹` distance define the same
convergence (Prop. 10), but the entropy is not `L¹`-continuous as soon as `X` contains disjoint
finite-measure sets of arbitrarily large measure (Thm. 21). Conversely, a topology in which
mixing and entropy are continuous is finer than the `L¹` topology (Thm. 46).

Formalized here:
* `kernel_bounds`   Lemma 4: `u²/(2 ln 2) ≤ f(u) ≤ |u|` on `[-1, 1]`;
* `jsd_bounds`      Prop. 10, eq. (11): `‖ρ-σ‖²/(8 ln 2) ≤ JSD(ρ,σ) ≤ ‖ρ-σ‖/2`;
* `tendsto_jsd_iff` Prop. 10, eq. (12): `JSD → 0 ↔ L¹ → 0`;
* `entropy_unif`, `entropy_mix`  eqs. (26), (32)–(34);
* `entropy_not_l1_continuous`, `not_tendsto_entropy`  Thm. 21;
* `tendsto_entropy_mix_atTop`  the second remark after Thm. 21, eqs. (40)–(45);
* `eventually_jsd_lt`, `eventually_l1dist_lt`  Thm. 46.

Densities are functions `X → ℝ`, not `L¹` classes, and are required to be measurable and
pointwise nonnegative. Logarithms are natural inside proofs; `entropy` and `jsd` are in bits.
-/
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Integral.Bochner.Set

open Real MeasureTheory Filter Topology Set

@[expose] public noncomputable section

namespace EntropyTopology

/-! ### Lemma 4 -/

/-- The function `f(u) = ½[(1+u) log₂(1+u) + (1-u) log₂(1-u)]` of eq. (5). -/
def kernel (u : ℝ) : ℝ := ((1 + u) * logb 2 (1 + u) + (1 - u) * logb 2 (1 - u)) / 2

lemma hasDerivAt_binEntropy_add_sq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun p => binEntropy p + 2 * (p - 1 / 2) ^ 2)
      (log (1 - y) - log y + 4 * (y - 1 / 2)) y := by
  have h1 := hasDerivAt_binEntropy hy0.ne' hy1.ne
  have h2 : HasDerivAt (fun p : ℝ => 2 * (p - 1 / 2) ^ 2) (4 * (y - 1 / 2)) y := by
    convert (((hasDerivAt_id' y).sub_const (1 / 2 : ℝ)).pow 2).const_mul (2 : ℝ) using 1
    norm_num
    ring
  exact h1.add h2

lemma hasDerivAt_deriv_binEntropy_add_sq {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun p => log (1 - p) - log p + 4 * (p - 1 / 2))
      (-1 / (1 - y) - y⁻¹ + 4) y := by
  have ha : HasDerivAt (fun p => log (1 - p)) (-1 / (1 - y)) y := by
    simpa using ((hasDerivAt_id y).const_sub 1).log (by simp; linarith)
  have hb := hasDerivAt_log hy0.ne'
  have hc : HasDerivAt (fun p : ℝ => 4 * (p - 1 / 2)) 4 y := by
    convert ((hasDerivAt_id' y).sub_const (1 / 2 : ℝ)).const_mul (4 : ℝ) using 1
    ring
  exact (ha.sub hb).add hc

/-- `p ↦ H(p) + 2(p - ½)²` is concave on `[0, 1]`, since `H'' = -1/(p(1-p)) ≤ -4`. -/
lemma concaveOn_binEntropy_add_sq :
    ConcaveOn ℝ (Icc 0 1) (fun p => binEntropy p + 2 * (p - 1 / 2) ^ 2) := by
  have heq : ∀ y ∈ Ioo (0 : ℝ) 1, deriv (fun p => binEntropy p + 2 * (p - 1 / 2) ^ 2)
      =ᶠ[𝓝 y] fun p => log (1 - p) - log p + 4 * (p - 1 / 2) := fun y hy => by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with p hp
    exact (hasDerivAt_binEntropy_add_sq hp.1 hp.2).deriv
  apply concaveOn_of_deriv2_nonpos (convex_Icc 0 1)
  · exact (binEntropy_continuous.add (by fun_prop)).continuousOn
  · rw [interior_Icc]
    intro y hy
    exact (hasDerivAt_binEntropy_add_sq hy.1 hy.2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    exact ((hasDerivAt_deriv_binEntropy_add_sq hy.1 hy.2).differentiableAt.congr_of_eventuallyEq
      (heq y hy)).differentiableWithinAt
  · rw [interior_Icc]
    intro y hy
    rw [Function.iterate_succ_apply, Function.iterate_one, (heq y hy).deriv_eq,
      (hasDerivAt_deriv_binEntropy_add_sq hy.1 hy.2).deriv]
    have h0 := hy.1
    have h1 : 0 < 1 - y := by linarith [hy.2]
    have : -1 / (1 - y) - y⁻¹ + 4 = -((2 * y - 1) ^ 2 / (y * (1 - y))) := by
      field_simp
      ring
    rw [this, neg_nonpos]
    positivity

/-- The lower bound of Lemma 4, in terms of `p = (1+u)/2` and natural logarithms. -/
lemma sq_le_log_two_sub_binEntropy {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (2 * p - 1) ^ 2 / 2 ≤ log 2 - binEntropy p := by
  have h := concaveOn_binEntropy_add_sq.2 (show p ∈ Icc (0 : ℝ) 1 from ⟨hp0, hp1⟩)
    (show 1 - p ∈ Icc (0 : ℝ) 1 from ⟨by linarith, by linarith⟩)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simp only [smul_eq_mul, binEntropy_one_sub] at h
  rw [show 1 / 2 * p + 1 / 2 * (1 - p) = (2 : ℝ)⁻¹ by ring, binEntropy_two_inv] at h
  nlinarith [h]

lemma log_two_mul_le_binEntropy {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) :
    2 * p * log 2 ≤ binEntropy p := by
  have h := strictConcave_binEntropy.concaveOn.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from
    ⟨le_rfl, zero_le_one⟩) (show (2⁻¹ : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num, by norm_num⟩)
    (show 0 ≤ 1 - 2 * p by linarith) (show 0 ≤ 2 * p by linarith)
    (by ring : 1 - 2 * p + 2 * p = 1)
  simp only [smul_eq_mul, binEntropy_zero, binEntropy_two_inv, mul_zero, zero_add] at h
  rwa [show 2 * p * 2⁻¹ = p by ring] at h

/-- The upper bound of Lemma 4, in terms of `p = (1+u)/2` and natural logarithms. -/
lemma log_two_sub_binEntropy_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    log 2 - binEntropy p ≤ log 2 * |2 * p - 1| := by
  rcases le_total p (1 / 2) with hp | hp
  · have := log_two_mul_le_binEntropy hp0 hp
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have := log_two_mul_le_binEntropy (p := 1 - p) (by linarith) (by linarith)
    rw [binEntropy_one_sub] at this
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma mul_log_two_mul (q : ℝ) : 2 * q * log (2 * q) = 2 * q * log 2 - 2 * negMulLog q := by
  have := negMulLog_mul 2 q
  simp only [negMulLog] at this ⊢
  linarith

lemma kernel_eq {u : ℝ} : kernel u = 1 - binEntropy ((1 + u) / 2) / log 2 := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  obtain ⟨p, rfl⟩ : ∃ p, u = 2 * p - 1 := ⟨(1 + u) / 2, by ring⟩
  rw [show (1 + (2 * p - 1)) / 2 = p by ring, kernel, show 1 + (2 * p - 1) = 2 * p by ring,
    show 1 - (2 * p - 1) = 2 * (1 - p) by ring, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  calc (2 * p * logb 2 (2 * p) + 2 * (1 - p) * logb 2 (2 * (1 - p))) / 2
      = (2 * p * log (2 * p) + 2 * (1 - p) * log (2 * (1 - p))) / (2 * log 2) := by
        rw [logb, logb]
        ring
    _ = _ := by
        rw [mul_log_two_mul, mul_log_two_mul]
        field_simp
        ring

/-- Lemma 4. -/
theorem kernel_bounds {u : ℝ} (hu : u ∈ Icc (-1) 1) :
    u ^ 2 / (2 * log 2) ≤ kernel u ∧ kernel u ≤ |u| := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hp0 : 0 ≤ (1 + u) / 2 := by linarith [hu.1]
  have hp1 : (1 + u) / 2 ≤ 1 := by linarith [hu.2]
  have hu' : 2 * ((1 + u) / 2) - 1 = u := by ring
  have hA := sq_le_log_two_sub_binEntropy hp0 hp1
  have hB := log_two_sub_binEntropy_le hp0 hp1
  rw [hu'] at hA hB
  rw [kernel_eq]
  constructor
  · rw [div_le_iff₀ (by positivity)]
    have : (1 - binEntropy ((1 + u) / 2) / log 2) * (2 * log 2) =
        2 * (log 2 - binEntropy ((1 + u) / 2)) := by field_simp
    rw [this]
    linarith
  · have : 1 - binEntropy ((1 + u) / 2) / log 2 = (log 2 - binEntropy ((1 + u) / 2)) / log 2 := by
      field_simp
    rw [this, div_le_iff₀ h2]
    linarith

/-! ### Pointwise Jensen–Shannon density -/

/-- The integrand of `JSD` in nats: `η((a+b)/2) - η(a)/2 - η(b)/2`, with `η = negMulLog`. -/
def jsdDensity (a b : ℝ) : ℝ := negMulLog ((a + b) / 2) - negMulLog a / 2 - negMulLog b / 2

lemma jsdDensity_mul (s p : ℝ) :
    jsdDensity (s * p) (s * (1 - p)) = s / 2 * (log 2 - binEntropy p) := by
  have hhalf : negMulLog (1 / 2 : ℝ) = log 2 / 2 := by
    simp [negMulLog, log_inv]
    ring
  rw [jsdDensity, show (s * p + s * (1 - p)) / 2 = s * (1 / 2) by ring, negMulLog_mul,
    negMulLog_mul, negMulLog_mul, hhalf, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring

/-- Eq. (16), pointwise: the integrand is `m · f(u)` with `m = (a+b)/2`, `u = (a-b)/(a+b)`. -/
lemma jsdDensity_eq {a b : ℝ} (hs : a + b ≠ 0) :
    jsdDensity a b = (a + b) / 2 * (log 2 - binEntropy (a / (a + b))) := by
  have ea : (a + b) * (a / (a + b)) = a := by field_simp
  have eb : (a + b) * (1 - a / (a + b)) = b := by field_simp; ring
  have := jsdDensity_mul (a + b) (a / (a + b))
  rwa [ea, eb] at this

lemma abs_sub_le_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |a - b| ≤ a + b :=
  abs_le.mpr ⟨by linarith, by linarith⟩

/-- Eq. (17), pointwise. -/
lemma jsdDensity_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a - b) ^ 2 / (a + b) / 4 ≤ jsdDensity a b ∧ jsdDensity a b ≤ log 2 / 2 * |a - b| := by
  rcases (add_nonneg ha hb).eq_or_lt with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    simp [jsdDensity]
  have hp0 : 0 ≤ a / (a + b) := div_nonneg ha hs.le
  have hp1 : a / (a + b) ≤ 1 := (div_le_one hs).mpr (by linarith)
  have h2p : 2 * (a / (a + b)) - 1 = (a - b) / (a + b) := by field_simp; ring
  have hA := sq_le_log_two_sub_binEntropy hp0 hp1
  have hB := log_two_sub_binEntropy_le hp0 hp1
  rw [h2p] at hA hB
  rw [abs_div, abs_of_pos hs] at hB
  rw [jsdDensity_eq hs.ne']
  constructor
  · calc (a - b) ^ 2 / (a + b) / 4 = (a + b) / 2 * (((a - b) / (a + b)) ^ 2 / 2) := by
          field_simp; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hA (by positivity)
  · calc (a + b) / 2 * (log 2 - binEntropy (a / (a + b)))
        ≤ (a + b) / 2 * (log 2 * (|a - b| / (a + b))) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = log 2 / 2 * |a - b| := by field_simp

lemma sq_div_le_abs {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a - b) ^ 2 / (a + b) ≤ |a - b| := by
  rcases (add_nonneg ha hb).eq_or_lt with hs | hs
  · rw [← hs, div_zero]
    exact abs_nonneg _
  rw [div_le_iff₀ hs, ← sq_abs]
  nlinarith [abs_sub_le_add ha hb, abs_nonneg (a - b)]

/-- The pointwise inequality behind eq. (18): `|a-b| ≤ q/(2c) + c(a+b)/2` with
`q = (a-b)²/(a+b)`, for every `c > 0`. -/
lemma abs_sub_le_amgm {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    |a - b| ≤ (a - b) ^ 2 / (a + b) / (2 * c) + c * (a + b) / 2 := by
  rcases (add_nonneg ha hb).eq_or_lt with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0
    simp
  have : (a - b) ^ 2 / (a + b) / (2 * c) + c * (a + b) / 2 =
      ((a - b) ^ 2 + c ^ 2 * (a + b) ^ 2) / (2 * c * (a + b)) := by
    field_simp
  rw [this, le_div_iff₀ (by positivity), ← sq_abs (a - b)]
  nlinarith [sq_nonneg (|a - b| - c * (a + b))]

/-! ### Densities, entropy and the Jensen–Shannon divergence -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- `ρ ∈ P_μ`: a probability density with respect to `μ` with finite entropy. -/
structure IsDensity (μ : Measure X) (ρ : X → ℝ) : Prop where
  measurable : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  integrable : Integrable ρ μ
  integral_eq_one : ∫ x, ρ x ∂μ = 1
  integrable_negMulLog : Integrable (fun x => negMulLog (ρ x)) μ

/-- The entropy `S(ρ) = -∫ ρ log₂ ρ dμ`, eq. (24). -/
def entropy (μ : Measure X) (ρ : X → ℝ) : ℝ := (∫ x, negMulLog (ρ x) ∂μ) / log 2

/-- The `L¹` distance of eq. (1). -/
def l1dist (μ : Measure X) (ρ σ : X → ℝ) : ℝ := ∫ x, |ρ x - σ x| ∂μ

/-- The equal mixture `(ρ + σ)/2`. -/
def mid (ρ σ : X → ℝ) : X → ℝ := fun x => (ρ x + σ x) / 2

/-- The Jensen–Shannon divergence of eq. (3). -/
def jsd (μ : Measure X) (ρ σ : X → ℝ) : ℝ :=
  entropy μ (mid ρ σ) - entropy μ ρ / 2 - entropy μ σ / 2

variable {ρ σ : X → ℝ}

lemma measurable_negMulLog_comp (hρ : Measurable ρ) : Measurable fun x => negMulLog (ρ x) :=
  continuous_negMulLog.measurable.comp hρ

lemma integrable_jsdDensity (hρ : IsDensity μ ρ) (hσ : IsDensity μ σ) :
    Integrable (fun x => jsdDensity (ρ x) (σ x)) μ := by
  have hm : Measurable fun x => jsdDensity (ρ x) (σ x) :=
    ((measurable_negMulLog_comp ((hρ.measurable.add hσ.measurable).div_const 2)).sub
      ((measurable_negMulLog_comp hρ.measurable).div_const 2)).sub
      ((measurable_negMulLog_comp hσ.measurable).div_const 2)
  refine Integrable.mono' ((hρ.integrable.sub hσ.integrable).abs.const_mul (log 2 / 2))
    hm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have h := jsdDensity_bounds (hρ.nonneg x) (hσ.nonneg x)
  have h0 : 0 ≤ jsdDensity (ρ x) (σ x) :=
    le_trans (by have := hρ.nonneg x; have := hσ.nonneg x; positivity) h.1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h.2

lemma integrable_sqDiv (hρ : IsDensity μ ρ) (hσ : IsDensity μ σ) :
    Integrable (fun x => (ρ x - σ x) ^ 2 / (ρ x + σ x)) μ := by
  refine Integrable.mono' (hρ.integrable.sub hσ.integrable).abs
    (((hρ.measurable.sub hσ.measurable).pow_const 2).div
      (hρ.measurable.add hσ.measurable)).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have := hρ.nonneg x
  have := hσ.nonneg x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact sq_div_le_abs (hρ.nonneg x) (hσ.nonneg x)

/-- Equal mixtures of finite-entropy densities have finite entropy. -/
lemma isDensity_mid (hρ : IsDensity μ ρ) (hσ : IsDensity μ σ) : IsDensity μ (mid ρ σ) where
  measurable := (hρ.measurable.add hσ.measurable).div_const 2
  nonneg x := div_nonneg (add_nonneg (hρ.nonneg x) (hσ.nonneg x)) zero_le_two
  integrable := (hρ.integrable.add hσ.integrable).div_const 2
  integral_eq_one := by
    simp only [mid]
    rw [integral_div, integral_add hρ.integrable hσ.integrable, hρ.integral_eq_one,
      hσ.integral_eq_one]
    norm_num
  integrable_negMulLog := by
    refine (((integrable_jsdDensity hρ hσ).add (hρ.integrable_negMulLog.div_const 2)).add
      (hσ.integrable_negMulLog.div_const 2)).congr (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, jsdDensity, mid]
    ring

lemma jsd_eq_integral (hρ : IsDensity μ ρ) (hσ : IsDensity μ σ) :
    jsd μ ρ σ = (∫ x, jsdDensity (ρ x) (σ x) ∂μ) / log 2 := by
  have hm := (isDensity_mid hρ hσ).integrable_negMulLog
  have h1 : Integrable (fun x => negMulLog (mid ρ σ x) - negMulLog (ρ x) / 2) μ :=
    hm.sub (hρ.integrable_negMulLog.div_const 2)
  have h2 : Integrable (fun x => negMulLog (σ x) / 2) μ := hσ.integrable_negMulLog.div_const 2
  have h3 : Integrable (fun x => negMulLog (ρ x) / 2) μ := hρ.integrable_negMulLog.div_const 2
  have e : ∫ x, jsdDensity (ρ x) (σ x) ∂μ =
      ∫ x, (negMulLog (mid ρ σ x) - negMulLog (ρ x) / 2) - negMulLog (σ x) / 2 ∂μ := rfl
  rw [e, integral_sub h1 h2, integral_sub hm h3, integral_div, integral_div]
  simp only [jsd, entropy]
  ring

/-- Eq. (18)–(19): `‖ρ - σ‖₁² ≤ 2 ∫ (ρ-σ)²/(ρ+σ) dμ`. -/
lemma l1dist_sq_le (hρ : IsDensity μ ρ) (hσ : IsDensity μ σ) :
    l1dist μ ρ σ ^ 2 ≤ 2 * ∫ x, (ρ x - σ x) ^ 2 / (ρ x + σ x) ∂μ := by
  set D := l1dist μ ρ σ
  set Q := ∫ x, (ρ x - σ x) ^ 2 / (ρ x + σ x) ∂μ
  have hD0 : 0 ≤ D := integral_nonneg fun x => abs_nonneg _
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => by
    have := hρ.nonneg x
    have := hσ.nonneg x
    positivity
  rcases hD0.eq_or_lt with hD | hD
  · rw [← hD]
    linarith
  have hc : 0 < D / 2 := by positivity
  have hle : D ≤ Q / (2 * (D / 2)) + D / 2 / 2 * (1 + 1) := by
    have i1 : Integrable (fun x => (ρ x - σ x) ^ 2 / (ρ x + σ x) / (2 * (D / 2))) μ :=
      (integrable_sqDiv hρ hσ).div_const _
    have i2 : Integrable (fun x => D / 2 * (ρ x + σ x) / 2) μ :=
      ((hρ.integrable.add hσ.integrable).const_mul _).div_const _
    have hint : Integrable (fun x => (ρ x - σ x) ^ 2 / (ρ x + σ x) / (2 * (D / 2)) +
        D / 2 * (ρ x + σ x) / 2) μ := i1.add i2
    calc D ≤ ∫ x, ((ρ x - σ x) ^ 2 / (ρ x + σ x) / (2 * (D / 2)) +
          D / 2 * (ρ x + σ x) / 2) ∂μ :=
          integral_mono (hρ.integrable.sub hσ.integrable).abs hint
            fun x => abs_sub_le_amgm (hρ.nonneg x) (hσ.nonneg x) hc
      _ = Q / (2 * (D / 2)) + D / 2 / 2 * (1 + 1) := by
          rw [integral_add i1 i2, integral_div, integral_div, integral_const_mul,
            integral_add hρ.integrable hσ.integrable, hρ.integral_eq_one, hσ.integral_eq_one]
          ring
  have : Q / (2 * (D / 2)) = Q / D := by ring_nf
  rw [this] at hle
  have h' : D / 2 ≤ Q / D := by linarith
  rw [le_div_iff₀ hD] at h'
  nlinarith

/-- Prop. 10, eq. (11). -/
theorem jsd_bounds (hρ : IsDensity μ ρ) (hσ : IsDensity μ σ) :
    l1dist μ ρ σ ^ 2 / (8 * log 2) ≤ jsd μ ρ σ ∧ jsd μ ρ σ ≤ l1dist μ ρ σ / 2 := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hJ := integrable_jsdDensity hρ hσ
  rw [jsd_eq_integral hρ hσ]
  constructor
  · have hlow : (∫ x, (ρ x - σ x) ^ 2 / (ρ x + σ x) ∂μ) / 4 ≤ ∫ x, jsdDensity (ρ x) (σ x) ∂μ := by
      rw [← integral_div]
      exact integral_mono ((integrable_sqDiv hρ hσ).div_const 4) hJ
        fun x => (jsdDensity_bounds (hρ.nonneg x) (hσ.nonneg x)).1
    have := l1dist_sq_le hρ hσ
    rw [div_le_div_iff₀ (by positivity) h2]
    nlinarith
  · have hup : ∫ x, jsdDensity (ρ x) (σ x) ∂μ ≤ log 2 / 2 * l1dist μ ρ σ := by
      rw [l1dist, ← integral_const_mul]
      exact integral_mono hJ ((hρ.integrable.sub hσ.integrable).abs.const_mul _)
        fun x => (jsdDensity_bounds (hρ.nonneg x) (hσ.nonneg x)).2
    rw [div_le_iff₀ h2]
    linarith

lemma jsd_nonneg (hρ : IsDensity μ ρ) (hσ : IsDensity μ σ) : 0 ≤ jsd μ ρ σ :=
  le_trans (by have := log_pos one_lt_two; positivity) (jsd_bounds hρ hσ).1

/-- Prop. 10, eq. (12): Jensen–Shannon convergence is `L¹` convergence. -/
theorem tendsto_jsd_iff {ι : Type*} {l : Filter ι} {ρs : ι → X → ℝ}
    (hρs : ∀ i, IsDensity μ (ρs i)) (hρ : IsDensity μ ρ) :
    Tendsto (fun i => jsd μ (ρs i) ρ) l (𝓝 0) ↔ Tendsto (fun i => l1dist μ (ρs i) ρ) l (𝓝 0) := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  have hd0 : ∀ i, 0 ≤ l1dist μ (ρs i) ρ := fun i => integral_nonneg fun x => abs_nonneg _
  constructor
  · intro h
    have h' : Tendsto (fun i => 8 * log 2 * jsd μ (ρs i) ρ) l (𝓝 0) := by
      simpa using h.const_mul (8 * log 2)
    have hs : Tendsto (fun i => √(8 * log 2 * jsd μ (ρs i) ρ)) l (𝓝 0) := by
      have := h'.sqrt
      rwa [sqrt_zero] at this
    refine squeeze_zero hd0 (fun i => ?_) hs
    rw [le_sqrt (hd0 i)]
    · have := (jsd_bounds (hρs i) hρ).1
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    · exact mul_nonneg (by positivity) (jsd_nonneg (hρs i) hρ)
  · intro h
    refine squeeze_zero (fun i => jsd_nonneg (hρs i) hρ) (fun i => (jsd_bounds (hρs i) hρ).2) ?_
    simpa using h.div_const 2

/-! ### Theorem 21: entropy is not `L¹`-continuous -/

/-- The uniform density `1_U / μ(U)` of eq. (25). -/
def unif (μ : Measure X) (U : Set X) : X → ℝ := U.indicator fun _ => (μ.real U)⁻¹

/-- The mixture `(1-ε) u_B + ε u_A` of eq. (30). -/
def mix (μ : Measure X) (ε : ℝ) (A B : Set X) : X → ℝ :=
  fun x => (1 - ε) * unif μ B x + ε * unif μ A x

variable {A B U : Set X}

lemma mul_negMulLog_inv {t : ℝ} (ht : 0 < t) : t * negMulLog t⁻¹ = log t := by
  simp only [negMulLog, log_inv]
  field_simp

lemma integral_indicator_const' (hU : MeasurableSet U) (c : ℝ) :
    ∫ x, U.indicator (fun _ => c) x ∂μ = μ.real U * c := by
  rw [integral_indicator_const c hU, smul_eq_mul]

lemma integrable_indicator_const' (hU : MeasurableSet U) (hfin : μ U ≠ ⊤) (c : ℝ) :
    Integrable (U.indicator fun _ => c) μ :=
  (integrable_indicator_iff hU).mpr (integrableOn_const hfin)

lemma isDensity_unif (hU : MeasurableSet U) (hfin : μ U ≠ ⊤) (hpos : 0 < μ.real U) :
    IsDensity μ (unif μ U) where
  measurable := measurable_const.indicator hU
  nonneg x := indicator_nonneg (fun _ _ => inv_nonneg.mpr hpos.le) x
  integrable := integrable_indicator_const' hU hfin _
  integral_eq_one := by
    rw [unif, integral_indicator_const' hU, mul_inv_cancel₀ hpos.ne']
  integrable_negMulLog := by
    refine (integrable_indicator_const' hU hfin (negMulLog (μ.real U)⁻¹)).congr
      (ae_of_all _ fun x => ?_)
    by_cases hx : x ∈ U <;> simp [unif, hx]

/-- Eq. (26): `S(u_U) = log₂ μ(U)`. -/
theorem entropy_unif (hU : MeasurableSet U) (hpos : 0 < μ.real U) :
    entropy μ (unif μ U) = logb 2 (μ.real U) := by
  have : (fun x => negMulLog (unif μ U x)) = U.indicator fun _ => negMulLog (μ.real U)⁻¹ := by
    funext x
    by_cases hx : x ∈ U <;> simp [unif, hx]
  rw [entropy, this, integral_indicator_const' hU, mul_negMulLog_inv hpos, logb]

lemma negMulLog_mix (hAB : Disjoint A B) (ε : ℝ) (x : X) :
    negMulLog (mix μ ε A B x) = B.indicator (fun _ => negMulLog ((1 - ε) * (μ.real B)⁻¹)) x +
      A.indicator (fun _ => negMulLog (ε * (μ.real A)⁻¹)) x := by
  by_cases hB : x ∈ B
  · have hA : x ∉ A := fun hA => hAB.ne_of_mem hA hB rfl
    simp [mix, unif, hA, hB]
  · by_cases hA : x ∈ A <;> simp [mix, unif, hA, hB]

lemma isDensity_mix (hA : MeasurableSet A) (hAfin : μ A ≠ ⊤) (hApos : 0 < μ.real A)
    (hB : MeasurableSet B) (hBfin : μ B ≠ ⊤) (hBpos : 0 < μ.real B) (hAB : Disjoint A B)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : IsDensity μ (mix μ ε A B) := by
  have uA := isDensity_unif hA hAfin hApos
  have uB := isDensity_unif hB hBfin hBpos
  refine ⟨(uB.measurable.const_mul _).add (uA.measurable.const_mul _), fun x => ?_,
    (uB.integrable.const_mul _).add (uA.integrable.const_mul _), ?_, ?_⟩
  · have := uA.nonneg x
    have := uB.nonneg x
    have : 0 ≤ 1 - ε := by linarith
    simp only [mix]
    positivity
  · simp only [mix]
    rw [integral_add (uB.integrable.const_mul _) (uA.integrable.const_mul _),
      integral_const_mul, integral_const_mul, uA.integral_eq_one, uB.integral_eq_one]
    ring
  · exact ((integrable_indicator_const' hB hBfin _).add
      (integrable_indicator_const' hA hAfin _)).congr
      (ae_of_all _ fun x => (negMulLog_mix hAB ε x).symm)

/-- Eqs. (32)–(34): `S((1-ε) u_B + ε u_A) = h₂(ε) + (1-ε) log₂ μ(B) + ε log₂ μ(A)`. -/
theorem entropy_mix (hA : MeasurableSet A) (hApos : 0 < μ.real A) (hB : MeasurableSet B)
    (hBpos : 0 < μ.real B) (hAB : Disjoint A B) (ε : ℝ) :
    entropy μ (mix μ ε A B) =
      binEntropy ε / log 2 + (1 - ε) * logb 2 (μ.real B) + ε * logb 2 (μ.real A) := by
  have hAfin : μ A ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hApos).2.ne
  have hBfin : μ B ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hBpos).2.ne
  rw [entropy, funext (negMulLog_mix hAB ε),
    integral_add (integrable_indicator_const' hB hBfin _)
      (integrable_indicator_const' hA hAfin _),
    integral_indicator_const' hB, integral_indicator_const' hA, negMulLog_mul, negMulLog_mul]
  have eB : μ.real B * ((μ.real B)⁻¹ * negMulLog (1 - ε) + (1 - ε) * negMulLog (μ.real B)⁻¹) =
      negMulLog (1 - ε) + (1 - ε) * log (μ.real B) := by
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hBpos.ne', one_mul, mul_left_comm,
      mul_negMulLog_inv hBpos]
  have eA : μ.real A * ((μ.real A)⁻¹ * negMulLog ε + ε * negMulLog (μ.real A)⁻¹) =
      negMulLog ε + ε * log (μ.real A) := by
    rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul, mul_left_comm,
      mul_negMulLog_inv hApos]
  rw [eB, eA, binEntropy_eq_negMulLog_add_negMulLog_one_sub, logb, logb]
  ring

/-- Eq. (31): `‖(1-ε) u_B + ε u_A - u_B‖₁ = 2ε`. -/
theorem l1dist_mix (hA : MeasurableSet A) (hApos : 0 < μ.real A) (hB : MeasurableSet B)
    (hBpos : 0 < μ.real B) (hAB : Disjoint A B) {ε : ℝ} (hε0 : 0 ≤ ε) :
    l1dist μ (mix μ ε A B) (unif μ B) = 2 * ε := by
  have hAfin : μ A ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hApos).2.ne
  have hBfin : μ B ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hBpos).2.ne
  have hpt : ∀ x, |mix μ ε A B x - unif μ B x| =
      ε * unif μ B x + ε * unif μ A x := by
    intro x
    by_cases hxB : x ∈ B
    · have hxA : x ∉ A := fun h => hAB.ne_of_mem h hxB rfl
      simp only [mix, unif, indicator_of_mem hxB, indicator_of_notMem hxA]
      rw [show (1 - ε) * (μ.real B)⁻¹ + ε * 0 - (μ.real B)⁻¹ = -(ε * (μ.real B)⁻¹) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
      ring
    · simp only [mix, unif, indicator_of_notMem hxB]
      by_cases hxA : x ∈ A
      · simp only [indicator_of_mem hxA]
        rw [show (1 - ε) * 0 + ε * (μ.real A)⁻¹ - 0 = ε * (μ.real A)⁻¹ by ring,
          abs_of_nonneg (by positivity)]
        ring
      · simp [indicator_of_notMem hxA]
  have uA := isDensity_unif hA hAfin hApos
  have uB := isDensity_unif hB hBfin hBpos
  rw [l1dist, funext hpt, integral_add (uB.integrable.const_mul _) (uA.integrable.const_mul _),
    integral_const_mul, integral_const_mul, uA.integral_eq_one, uB.integral_eq_one]
  ring

/-- The hypotheses of Thm. 21: `0 < μ(B) < ∞`, and `Aₙ` disjoint from `B` with
`μ(Aₙ) < ∞` and `μ(Aₙ) → ∞`. -/
structure Thm21Hyp (μ : Measure X) (A : ℕ → Set X) (B : Set X) : Prop where
  measurableSet_B : MeasurableSet B
  pos_B : 0 < μ.real B
  measurableSet_A : ∀ n, MeasurableSet (A n)
  finite_A : ∀ n, μ (A n) ≠ ⊤
  disjoint : ∀ n, Disjoint (A n) B
  tendsto_A : Tendsto (fun n => μ.real (A n)) atTop atTop

variable {As : ℕ → Set X}

lemma Thm21Hyp.eventually_pos (h : Thm21Hyp μ As B) : ∀ᶠ n in atTop, 0 < μ.real (As n) :=
  h.tendsto_A.eventually_gt_atTop 0

lemma Thm21Hyp.tendsto_logb (h : Thm21Hyp μ As B) :
    Tendsto (fun n => logb 2 (μ.real (As n))) atTop atTop :=
  (tendsto_logb_atTop one_lt_two).comp h.tendsto_A

/-- For `εₙ ∈ [0, 1]`, `εₙ → 0`: the densities `ρₙ = (1-εₙ) u_B + εₙ u_{Aₙ}` are eventually in
`P_μ` and tend to `u_B` in `L¹`, and their entropy is `h₂(εₙ) + (1-εₙ) log₂ μ(B) + εₙ log₂ μ(Aₙ)`. -/
lemma Thm21Hyp.mix_facts (h : Thm21Hyp μ As B) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hε01 : ∀ᶠ n in atTop, ε n ∈ Icc 0 1) :
    (∀ᶠ n in atTop, IsDensity μ (mix μ (ε n) (As n) B)) ∧
      Tendsto (fun n => l1dist μ (mix μ (ε n) (As n) B) (unif μ B)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, entropy μ (mix μ (ε n) (As n) B) =
        binEntropy (ε n) / log 2 + (1 - ε n) * logb 2 (μ.real B) +
          ε n * logb 2 (μ.real (As n)) := by
  have hBfin : μ B ≠ ⊤ := (ENNReal.toReal_pos_iff.mp h.pos_B).2.ne
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hε01, h.eventually_pos] with n hn hpos
    exact isDensity_mix (h.measurableSet_A n) (h.finite_A n) hpos h.measurableSet_B hBfin
      h.pos_B (h.disjoint n) hn.1 hn.2
  · have h2 : Tendsto (fun n => 2 * ε n) atTop (𝓝 0) := by simpa using hε.const_mul 2
    refine h2.congr' ?_
    filter_upwards [hε01, h.eventually_pos] with n hn hpos
    exact (l1dist_mix (h.measurableSet_A n) hpos h.measurableSet_B h.pos_B (h.disjoint n)
      hn.1).symm
  · filter_upwards [h.eventually_pos] with n hpos
    exact entropy_mix (h.measurableSet_A n) hpos h.measurableSet_B h.pos_B (h.disjoint n) _

omit [MeasurableSpace X] in
lemma tendsto_rest {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (L : ℝ) :
    Tendsto (fun n => binEntropy (ε n) / log 2 + (1 - ε n) * L) atTop (𝓝 L) := by
  have h1 : Tendsto (fun n => binEntropy (ε n)) atTop (𝓝 (binEntropy 0)) :=
    (binEntropy_continuous.tendsto 0).comp hε
  rw [binEntropy_zero] at h1
  have h3 := (h1.div_const (log 2)).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub hε).mul_const L)
  simpa using h3

/-- The sequence `εₙ = 1/log₂ μ(Aₙ)` of eq. (29). -/
def epsSeq (μ : Measure X) (As : ℕ → Set X) (n : ℕ) : ℝ := (logb 2 (μ.real (As n)))⁻¹

lemma Thm21Hyp.epsSeq_facts (h : Thm21Hyp μ As B) :
    Tendsto (epsSeq μ As) atTop (𝓝 0) ∧ (∀ᶠ n in atTop, epsSeq μ As n ∈ Icc 0 1) ∧
      ∀ᶠ n in atTop, epsSeq μ As n * logb 2 (μ.real (As n)) = 1 := by
  refine ⟨tendsto_inv_atTop_zero.comp h.tendsto_logb, ?_, ?_⟩
  · filter_upwards [h.tendsto_logb.eventually_ge_atTop 1] with n hn
    exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hn⟩
  · filter_upwards [h.tendsto_logb.eventually_ge_atTop 1] with n hn
    exact inv_mul_cancel₀ (by linarith)

/-- Theorem 21. With `ρ = u_B` and `ρₙ = (1-εₙ) u_B + εₙ u_{Aₙ}`, `εₙ = 1/log₂ μ(Aₙ)`:
`ρₙ → ρ` in `L¹`, but `S(ρₙ) → S(ρ) + 1`. -/
theorem entropy_not_l1_continuous (h : Thm21Hyp μ As B) :
    IsDensity μ (unif μ B) ∧
      (∀ᶠ n in atTop, IsDensity μ (mix μ (epsSeq μ As n) (As n) B)) ∧
      Tendsto (fun n => l1dist μ (mix μ (epsSeq μ As n) (As n) B) (unif μ B)) atTop (𝓝 0) ∧
      Tendsto (fun n => entropy μ (mix μ (epsSeq μ As n) (As n) B)) atTop
        (𝓝 (entropy μ (unif μ B) + 1)) := by
  have hBfin : μ B ≠ ⊤ := (ENNReal.toReal_pos_iff.mp h.pos_B).2.ne
  obtain ⟨hε, hε01, hε1⟩ := h.epsSeq_facts
  obtain ⟨hd, hl1, hS⟩ := h.mix_facts hε hε01
  refine ⟨isDensity_unif h.measurableSet_B hBfin h.pos_B, hd, hl1, ?_⟩
  rw [entropy_unif h.measurableSet_B h.pos_B]
  refine ((tendsto_rest hε (logb 2 (μ.real B))).add tendsto_const_nhds).congr' ?_
  filter_upwards [hS, hε1] with n hn h1
  rw [hn, h1]

/-- Theorem 21, as a failure of continuity: an `L¹`-convergent sequence in `P_μ` whose
entropies do not converge to the entropy of the limit. -/
theorem not_tendsto_entropy (h : Thm21Hyp μ As B) :
    ∃ ρ : X → ℝ, IsDensity μ ρ ∧ ∃ ρs : ℕ → X → ℝ, (∀ᶠ n in atTop, IsDensity μ (ρs n)) ∧
      Tendsto (fun n => l1dist μ (ρs n) ρ) atTop (𝓝 0) ∧
      ¬ Tendsto (fun n => entropy μ (ρs n)) atTop (𝓝 (entropy μ ρ)) := by
  obtain ⟨hρ, hd, hl1, hS⟩ := entropy_not_l1_continuous h
  exact ⟨_, hρ, _, hd, hl1, fun h' => by linarith [tendsto_nhds_unique hS h']⟩

/-- The second remark after Thm. 21, eqs. (40)–(45): with `εₙ = 1/√(log₂ μ(Aₙ))`,
still `ρₙ → u_B` in `L¹`, but `S(ρₙ) → ∞`. -/
theorem tendsto_entropy_mix_atTop (h : Thm21Hyp μ As B) :
    let ε := fun n => (√(logb 2 (μ.real (As n))))⁻¹
    (∀ᶠ n in atTop, IsDensity μ (mix μ (ε n) (As n) B)) ∧
      Tendsto (fun n => l1dist μ (mix μ (ε n) (As n) B) (unif μ B)) atTop (𝓝 0) ∧
      Tendsto (fun n => entropy μ (mix μ (ε n) (As n) B)) atTop atTop := by
  intro ε
  have hsq : Tendsto (fun n => √(logb 2 (μ.real (As n)))) atTop atTop :=
    tendsto_sqrt_atTop.comp h.tendsto_logb
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hsq
  have hε01 : ∀ᶠ n in atTop, ε n ∈ Icc 0 1 := by
    filter_upwards [hsq.eventually_ge_atTop 1] with n hn
    exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hn⟩
  obtain ⟨hd, hl1, hS⟩ := h.mix_facts hε hε01
  refine ⟨hd, hl1, ?_⟩
  refine ((tendsto_rest hε (logb 2 (μ.real B))).add_atTop hsq).congr' ?_
  filter_upwards [hS, h.tendsto_logb.eventually_ge_atTop 1] with n hn hl
  rw [hn]
  have hpos : 0 < √(logb 2 (μ.real (As n))) := sqrt_pos.mpr (by linarith)
  have : ε n * logb 2 (μ.real (As n)) = √(logb 2 (μ.real (As n))) := by
    simp only [ε]
    rw [← sq_sqrt (show 0 ≤ logb 2 (μ.real (As n)) by linarith), sqrt_sq hpos.le]
    field_simp
  rw [this]

/-! ### Theorem 46: continuity of mixing and entropy forces the `L¹` topology -/

/-- The space `P_μ` of finite-entropy probability densities. -/
abbrev Density (μ : Measure X) := {ρ : X → ℝ // IsDensity μ ρ}

/-- Equal mixing on `P_μ`. -/
def Density.mid (ρ σ : Density μ) : Density μ := ⟨EntropyTopology.mid ρ.1 σ.1, isDensity_mid ρ.2 σ.2⟩

omit [MeasurableSpace X] in
lemma mid_self (ρ : X → ℝ) : mid ρ ρ = ρ := by
  funext x
  simp only [mid]
  ring

/-- Theorem 46, Jensen–Shannon form: if equal mixing `P_μ × P_μ → P_μ` and the entropy
`P_μ → ℝ` are continuous for a topology `τ`, every Jensen–Shannon ball around `ρ` is a
`τ`-neighbourhood of `ρ`. -/
theorem eventually_jsd_lt [TopologicalSpace (Density μ)]
    (hmid : Continuous fun p : Density μ × Density μ => Density.mid p.1 p.2)
    (hS : Continuous fun ρ : Density μ => entropy μ ρ.1) (ρ : Density μ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ σ in 𝓝 ρ, jsd μ σ.1 ρ.1 < δ := by
  have hc : Continuous fun σ : Density μ => jsd μ σ.1 ρ.1 :=
    ((hS.comp (hmid.comp (continuous_id.prodMk continuous_const))).sub
      (hS.div_const 2)).sub continuous_const
  have h0 : jsd μ ρ.1 ρ.1 = 0 := by
    simp only [jsd, mid_self]
    ring
  exact (hc.tendsto ρ).eventually (gt_mem_nhds (h0 ▸ hδ))

/-- Theorem 46, `L¹` form: under the same hypotheses, `τ` is finer than the `L¹` topology. -/
theorem eventually_l1dist_lt [TopologicalSpace (Density μ)]
    (hmid : Continuous fun p : Density μ × Density μ => Density.mid p.1 p.2)
    (hS : Continuous fun ρ : Density μ => entropy μ ρ.1) (ρ : Density μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ σ in 𝓝 ρ, l1dist μ σ.1 ρ.1 < ε := by
  have h2 : (0 : ℝ) < log 2 := log_pos one_lt_two
  filter_upwards [eventually_jsd_lt hmid hS ρ (δ := ε ^ 2 / (8 * log 2)) (by positivity)]
    with σ hσ
  have hb := (jsd_bounds σ.2 ρ.2).1
  have hd0 : 0 ≤ l1dist μ σ.1 ρ.1 := integral_nonneg fun x => abs_nonneg _
  have : l1dist μ σ.1 ρ.1 ^ 2 < ε ^ 2 := by
    have := hb.trans_lt hσ
    rwa [div_lt_div_iff_of_pos_right (by positivity)] at this
  exact lt_of_pow_lt_pow_left₀ 2 hε.le this

end EntropyTopology
