/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import UnitaryEntropy.VaryingPhase

/-!
# The `√t` boundary phase solves the Cauchy problem

This continues `UnitaryEntropy.VaryingPhase`, with `α(t) = α₀ + √t` and `ħ = 1`. There, the
forward Hamiltonian at `t₀ = 0` was shown to be the minimal momentum on `H¹₀(0, 1)`, which is not
self-adjoint. Here the propagator `U(t, s)` is shown to solve the Cauchy problem `u̇ = -iH(t) u`,
`H(t) = H_{α(t)}`, in the sense of Engel–Nagel (Def. VI.9.2), on `[0, ∞)`. The spaces of initial
values are the forward domains: `Y t = D(H_{α(t)})` for `t > 0` and `Y 0 = H¹₀(0, 1)`, a proper
subspace of `D(H_{α₀})`. So a unitary evolution can solve the Cauchy problem for a continuous
family of self-adjoint `H(t)` while its generator on `Y 0` is not self-adjoint.

## Proof

The time derivative is computed without differentiating in `x`. For `τ ≥ 0`,
`U(t + τ, s) = U(t + τ, s + τ) U(s + τ, s)`, and `U(t + τ, s + τ)` is `U(t, s)` for the shifted
phase `r ↦ α(r + τ)` (`phasePropagator_add_time`). Shifting the phase changes `U(t, s) φ` only
through the collected phase `e^{-i Σⱼ α(sⱼ + τ)}`, over the wrap-around times `sⱼ` of the point.
Its derivative in `τ` is `-i (Σⱼ α'(sⱼ)) U(t, s) φ` (`hasDerivAt_phasePropagator_shift`), by
dominated convergence, as `|√(r + τ) - √r| ≤ |τ| / √r`. The bound needed is on
`(Σⱼ α'(sⱼ)) |φ|`:

* for `s > 0`, `α' ≤ 1/(2√s)` at every wrap-around time and `φ ∈ D(H_{α(s)})` is bounded;
* for `s = 0` and `φ ∈ H¹₀`, the first wrap-around time of the point `z` is `1 - z`, and
  `|φ(z)| ≤ √(1 - z) ‖φ'‖` (`norm_integral_le_sqrt`) compensates `α'(1 - z) = 1/(2√(1 - z))`.

With the strong continuity of `U` (`continuous_phasePropagator_apply`), the product rule gives
the right derivative `U(t, s) w' - i (Σⱼ α'(sⱼ)) U(t, s) φ` of `t ↦ U(t, s) φ` at every `t ≥ s`,
where `w'` is its right derivative at `s`. This is continuous in `t`, again by dominated
convergence, so `t ↦ U(t, s) φ` is `C¹` on `[s, ∞)` (`hasDerivWithinAt_of_hasDerivWithinAt_Ici`).
The right derivative at `t` puts `U(t, s) φ` into the forward domain at `t`, so `U(t, s) Y s ⊆ Y t`,
and identifies the derivative with `-iH(t) U(t, s) φ`.

## Main results

* `continuous_phasePropagator_apply`: `(t, s) ↦ U(t, s) f` is continuous.
* `hasDerivAt_phasePropagator_shift`: the derivative in the time shift of the phase.
* `exists_classical_solution`: `t ↦ U(t, s) φ` is `C¹` on `[s, ∞)` for `φ` in the forward
  domain at `s ≥ 0`.
* `SolvesCauchyProblem`: Engel–Nagel's Def. VI.9.2, on `[0, ∞)`.
* `sqrtPhase_solvesCauchyProblem`, `sqrtPhase_cauchyProblem`: `U` solves the Cauchy problem on the
  forward domains, with `Y 0 = H¹₀(0, 1) ⊊ D(H_{α₀})` and a generator on `Y 0` that is not
  self-adjoint.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy

open MeasureTheory Filter Topology Set AddCircle QuantumMechanics
open scoped ENNReal InnerProductSpace ComplexConjugate Real LinearPMap

/-- The circle `ℝ/ℤ`. -/
local notation "𝕋" => AddCircle (1 : ℝ)

/-- Haar probability measure on `ℝ/ℤ`, which is Lebesgue measure on `[0, 1)`. -/
local notation "μc" => (haarAddCircle : Measure 𝕋)

/-- `L²(0, 1)`, as `L²` of the circle. -/
local notation "L²" => Lp ℂ 2 μc

local notation "V" => phasePropagator

/-! ### Dominated convergence and strong continuity -/

/-- **Dominated convergence in `L²(0, 1)`**, with explicit representatives. -/
lemma tendsto_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {u : ι → L²} {v : L²} {F : ι → 𝕋 → ℂ} {f : 𝕋 → ℂ} {G : 𝕋 → ℝ} (hG : MemLp G 2 μc)
    (hu : ∀ᶠ i in l, u i =ᵐ[μc] F i) (hv : v =ᵐ[μc] f)
    (hFm : ∀ᶠ i in l, AEStronglyMeasurable (F i) μc) (hfm : AEStronglyMeasurable f μc)
    (hb : ∀ᶠ i in l, ∀ᵐ x ∂μc, ‖F i x‖ ≤ G x) (hfb : ∀ᵐ x ∂μc, ‖f x‖ ≤ G x)
    (hlim : ∀ᵐ x ∂μc, Tendsto (fun i => F i x) l (𝓝 (f x))) : Tendsto u l (𝓝 v) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have key := tendsto_eLpNorm_of_dominated (μ := μc) (p := 2)
    (f := fun i x => F i x - f x) (F := fun x => G x + G x) ENNReal.ofNat_ne_top
    (hFm.mono fun i hi => hi.sub hfm) (hG.add hG)
    (hb.mono fun i hi => by
      filter_upwards [hi, hfb] with x h1 h2
      exact (norm_sub_le _ _).trans (add_le_add h1 h2))
    (hlim.mono fun x hx => by simpa using hx.sub_const (f x))
  refine key.congr' ?_
  filter_upwards [hu] with i hi
  refine eLpNorm_congr_ae ?_
  filter_upwards [hi, hv] with x h1 h2
  simp [h1, h2]

lemma circleShift_eq_twistedTranslation (s : ℝ) : circleShift s = twistedTranslation 0 s := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  filter_upwards [coeFn_circleShift s f, coeFn_twistedTranslation 0 s f] with x h₁ h₂
  rw [h₁, h₂, twistPhase]
  simp

/-- Translation on `L²(ℝ/ℤ)` is strongly continuous (Stone: it is `e^{-isH_0}`). -/
lemma continuous_circleShift_apply (f : L²) : Continuous fun s => circleShift s f := by
  obtain ⟨W, hW⟩ := exists_stronglyContinuousUnitaryGroup_of_solvesSchrodinger one_ne_zero
    (isSelfAdjoint_momentum (α := 0)) (by simp [twistedTranslation_zero])
    (solvesSchrodinger_twistedTranslation 1 0)
  have h := W.continuous_apply f
  rw [hW] at h
  simpa [div_one, circleShift_eq_twistedTranslation] using h

/-- Near a point `z₀ ∉ ℤ`, `⌊z⌋` is constant. -/
lemma eventually_floor_eq {z₀ : ℝ} (h : z₀ ≠ ⌊z₀⌋) : ∀ᶠ z in 𝓝 z₀, ⌊z⌋ = ⌊z₀⌋ := by
  have h1 : (⌊z₀⌋ : ℝ) < z₀ := lt_of_le_of_ne (Int.floor_le z₀) (Ne.symm h)
  filter_upwards [Ioo_mem_nhds h1 (Int.lt_floor_add_one z₀)] with z hz
  exact Int.floor_eq_iff.mpr ⟨hz.1.le, hz.2⟩

/-- `rep x - c ∈ ℤ` only at the point `x = c`. -/
lemma ae_sub_ne_floor (c : ℝ) :
    ∀ᵐ x ∂μc, circleRep x - c ≠ ⌊circleRep x - c⌋ := by
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (c : 𝕋))] with x hx h
  refine hx ?_
  have h0 : ((circleRep x - c : ℝ) : 𝕋) = 0 :=
    (AddCircle.coe_eq_zero_iff _).mpr ⟨⌊circleRep x - c⌋, by rw [zsmul_one]; exact h.symm⟩
  rw [AddCircle.coe_sub, coe_circleRep, sub_eq_zero] at h0
  exact h0

lemma continuousAt_crossPhase {α : ℝ → ℝ} (hα : Continuous α) {y : ℝ} {p₀ : ℝ × ℝ}
    (h : y - (p₀.1 - p₀.2) ≠ ⌊y - (p₀.1 - p₀.2)⌋) :
    ContinuousAt (fun p : ℝ × ℝ => crossPhase α p.1 (p.1 - p.2) y) p₀ := by
  have hz : ContinuousAt (fun p : ℝ × ℝ => y - (p.1 - p.2)) p₀ := by fun_prop
  have hev := hz.tendsto.eventually (eventually_floor_eq h)
  refine ContinuousAt.congr (f := fun p : ℝ × ℝ =>
    ∑ m ∈ Finset.Ioc ⌊y - (p₀.1 - p₀.2)⌋ ⌊y⌋, α (p.1 - y + m)) ?_ ?_
  · exact (continuous_finsetSum _ fun m _ => hα.comp (by fun_prop)).continuousAt
  · filter_upwards [hev] with p hp
    rw [crossPhase, hp]

/-- **The propagator is jointly strongly continuous**, for a continuous phase `α`. -/
lemma continuous_phasePropagator_apply {α : ℝ → ℝ} (hα : Continuous α) (f : L²) :
    Continuous fun p : ℝ × ℝ => V α p.1 p.2 f := by
  rw [continuous_iff_continuousAt]
  intro p₀
  set w : ℝ × ℝ → 𝕋 → ℂ := fun p => wrapPhase α p.1 (p.1 - p.2)
  set c : ℝ × ℝ → L² := fun p => circleShift (p.1 - p.2) f
  have hc : Continuous c := (continuous_circleShift_apply f).comp (by fun_prop)
  have hwm : ∀ p, Measurable (w p) := fun p => measurable_wrapPhase hα.measurable _ _
  have h1 : Tendsto (fun p => Lp.mulL (w p) (c p - c p₀)) (𝓝 p₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_mulL_of_norm_eq_one (hwm _) (norm_wrapPhase α _ _)]
    exact tendsto_iff_norm_sub_tendsto_zero.mp (hc.tendsto p₀)
  have h2 : Tendsto (fun p => Lp.mulL (w p) (c p₀)) (𝓝 p₀) (𝓝 (Lp.mulL (w p₀) (c p₀))) := by
    refine Lp.tendsto_mulL_apply ENNReal.ofNat_ne_top (C := 1)
      (.of_forall fun p => (hwm p).aestronglyMeasurable) (hwm p₀).aestronglyMeasurable
      (.of_forall fun p => .of_forall fun x => (norm_wrapPhase α _ _ x).le)
      (.of_forall fun x => (norm_wrapPhase α _ _ x).le) ?_ (c p₀)
    filter_upwards [ae_sub_ne_floor (p₀.1 - p₀.2)] with x hx
    have hcont := continuousAt_crossPhase hα (y := circleRep x) hx
    exact ((by fun_prop : Continuous fun r : ℝ => Complex.exp (-(Complex.I * (r : ℂ)))).tendsto
      _).comp hcont
  have h3 := h1.add h2
  rw [zero_add] at h3
  refine h3.congr fun p => ?_
  change Lp.mulL (w p) (c p - c p₀) + Lp.mulL (w p) (c p₀) = Lp.mulL (w p) (c p)
  rw [← map_add, sub_add_cancel]

/-! ### Shifting the phase in time -/

lemma crossPhase_add_time (α : ℝ → ℝ) (t T τ y : ℝ) :
    crossPhase α (t + τ) T y = crossPhase (fun r => α (r + τ)) t T y :=
  Finset.sum_congr rfl fun m _ => congrArg α (by ring)

/-- `U(t + τ, s + τ)` is `U(t, s)` for the phase `r ↦ α(r + τ)`. -/
lemma phasePropagator_add_time (α : ℝ → ℝ) (t s τ : ℝ) :
    V α (t + τ) (s + τ) = V (fun r => α (r + τ)) t s := by
  have h : t + τ - (s + τ) = t - s := by ring
  have hw : wrapPhase α (t + τ) (t - s) = wrapPhase (fun r => α (r + τ)) t (t - s) := by
    funext x
    rw [wrapPhase, wrapPhase, crossPhase_add_time]
  rw [phasePropagator, phasePropagator, h, hw]

lemma abs_sqrt_add_sub_sqrt_le {r : ℝ} (hr : 0 < r) (τ : ℝ) :
    |√(r + τ) - √r| ≤ |τ| / √r := by
  have hs : 0 < √r := Real.sqrt_pos.mpr hr
  rw [le_div_iff₀ hs]
  rcases le_or_gt 0 (r + τ) with h | h
  · have h1 := Real.sq_sqrt h
    have h2 := Real.sq_sqrt hr.le
    have h3 := Real.sqrt_nonneg (r + τ)
    have key : |√(r + τ) - √r| * (√(r + τ) + √r) = |τ| := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ √(r + τ) + √r), ← abs_mul]
      congr 1
      linear_combination h1 - h2
    nlinarith [abs_nonneg (√(r + τ) - √r)]
  · rw [Real.sqrt_eq_zero'.mpr h.le, zero_sub, abs_neg, abs_of_pos hs,
      abs_of_neg (by linarith [hr] : τ < 0)]
    nlinarith [Real.sq_sqrt hr.le]

lemma norm_phasePropagator_apply {α : ℝ → ℝ} (hα : Measurable α) (t s : ℝ) (f : L²) :
    ‖V α t s f‖ = ‖f‖ := by
  rw [phasePropagator, ContinuousLinearMap.comp_apply,
    norm_mulL_of_norm_eq_one (measurable_wrapPhase hα _ _) (norm_wrapPhase α _ _), norm_circleShift]

/-! ### The derivative in the time shift -/

/-- The sum of `α'(r) = 1/(2√r)` over the wrap-around times `t - y + m` of `U(t, t - T)` at `y`,
for `α = α₀ + √·`. -/
def wrapRate (t T y : ℝ) : ℝ := ∑ m ∈ Finset.Ioc ⌊y - T⌋ ⌊y⌋, 1 / (2 * √(t - y + m))

/-- The wrap-around times of `U(t, t - T)` are after `t - T`. -/
lemma sub_lt_of_mem_Ioc {t T y : ℝ} {m : ℤ} (hm : m ∈ Finset.Ioc ⌊y - T⌋ ⌊y⌋) :
    t - T < t - y + m := by
  have h1 := Int.lt_floor_add_one (y - T)
  have h2 : ((⌊y - T⌋ + 1 : ℤ) : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ioc.mp hm).1
  push_cast at h2
  linarith

lemma wrapRate_nonneg (t T y : ℝ) : 0 ≤ wrapRate t T y :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma measurable_wrapRate (t T : ℝ) : Measurable (wrapRate t T) := by
  have hq : ∀ q : ℤ × ℤ, Measurable fun y : ℝ =>
      ∑ m ∈ Finset.Ioc q.1 q.2, 1 / (2 * √(t - y + m)) :=
    fun q => Finset.measurable_fun_sum _ fun _ _ => by fun_prop
  have h : Measurable fun p : ℝ × (ℤ × ℤ) =>
      ∑ m ∈ Finset.Ioc p.2.1 p.2.2, 1 / (2 * √(t - p.1 + m)) :=
    measurable_from_prod_countable_left hq
  have hg : Measurable fun y : ℝ => (y, (⌊y - T⌋, ⌊y⌋)) :=
    measurable_id.prodMk ((Int.measurable_floor.comp (measurable_id.sub_const T)).prodMk
      Int.measurable_floor)
  have := h.comp hg
  unfold wrapRate
  exact this

lemma sqrtPhase_add_zero (α₀ : ℝ) : (fun r => sqrtPhase α₀ (r + 0)) = sqrtPhase α₀ := by
  funext r
  rw [add_zero]

lemma hasDerivAt_crossPhase_shift (α₀ : ℝ) {t T : ℝ} (hT : T ≤ t) (y : ℝ) :
    HasDerivAt (fun τ => crossPhase (fun r => sqrtPhase α₀ (r + τ)) t T y) (wrapRate t T y) 0 := by
  have h : ∀ m ∈ Finset.Ioc ⌊y - T⌋ ⌊y⌋, HasDerivAt (fun τ => sqrtPhase α₀ (t - y + m + τ))
      (1 / (2 * √(t - y + m))) 0 := fun m hm => by
    have hr : 0 < t - y + m := by linarith [sub_lt_of_mem_Ioc (t := t) hm]
    convert (((hasDerivAt_id' (0 : ℝ)).const_add (t - y + m)).sqrt
      (by simpa using hr.ne')).const_add α₀ using 1 <;> simp [sqrtPhase]
  unfold crossPhase wrapRate
  exact HasDerivAt.fun_sum h

lemma abs_crossPhase_shift_sub_le (α₀ : ℝ) {t T : ℝ} (hT : T ≤ t) (τ y : ℝ) :
    |crossPhase (fun r => sqrtPhase α₀ (r + τ)) t T y - crossPhase (sqrtPhase α₀) t T y| ≤
      |τ| * (2 * wrapRate t T y) := by
  rw [crossPhase, crossPhase, ← Finset.sum_sub_distrib, wrapRate, Finset.mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hr : 0 < t - y + m := by linarith [sub_lt_of_mem_Ioc (t := t) hm]
  have hs : 0 < √(t - y + m) := Real.sqrt_pos.mpr hr
  simp only [sqrtPhase, add_sub_add_left_eq_sub]
  calc |√(t - y + m + τ) - √(t - y + m)| ≤ |τ| / √(t - y + m) := abs_sqrt_add_sub_sqrt_le hr τ
    _ = |τ| * (2 * (1 / (2 * √(t - y + m)))) := by field_simp

/-- The pointwise derivative of `U_{α(· + τ)}(t, s) φ` at `τ = 0`:
`-i (Σⱼ α'(sⱼ)) U(t, s) φ`, over the wrap-around times `sⱼ`. -/
def rateTerm (α₀ t s : ℝ) (Φ : 𝕋 → ℂ) (x : 𝕋) : ℂ :=
  -(Complex.I * wrapRate t (t - s) (circleRep x)) *
    (wrapPhase (sqrtPhase α₀) t (t - s) x * Φ (x - ((t - s : ℝ) : 𝕋)))

lemma measurable_rateTerm (α₀ t s : ℝ) {Φ : 𝕋 → ℂ} (hΦ : Measurable Φ) :
    Measurable (rateTerm α₀ t s Φ) := by
  have h1 := (measurable_wrapRate t (t - s)).comp measurable_circleRep
  have h2 := measurable_wrapPhase (continuous_sqrtPhase α₀).measurable t (t - s)
  have h3 := hΦ.comp (measurable_sub_const ((t - s : ℝ) : 𝕋))
  unfold rateTerm
  exact (((Complex.measurable_ofReal.comp h1).const_mul Complex.I).neg).mul (h2.mul h3)

lemma norm_rateTerm (α₀ t s : ℝ) (Φ : 𝕋 → ℂ) (x : 𝕋) :
    ‖rateTerm α₀ t s Φ x‖ = wrapRate t (t - s) (circleRep x) * ‖Φ (x - ((t - s : ℝ) : 𝕋))‖ := by
  rw [rateTerm, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (wrapRate_nonneg _ _ _), norm_mul, norm_wrapPhase, one_mul]

open Classical in
/-- `rateTerm` as a vector of `L²`, when it is in `L²`. -/
def rateVec (α₀ t s : ℝ) (Φ : 𝕋 → ℂ) : L² :=
  if h : MemLp (rateTerm α₀ t s Φ) 2 μc then h.toLp else 0

lemma coeFn_rateVec {α₀ t s : ℝ} {Φ : 𝕋 → ℂ} (h : MemLp (rateTerm α₀ t s Φ) 2 μc) :
    rateVec α₀ t s Φ =ᵐ[μc] rateTerm α₀ t s Φ := by
  simp only [rateVec, h, ↓reduceDIte]
  exact h.coeFn_toLp

lemma memLp_rateTerm {α₀ t s : ℝ} {Φ : 𝕋 → ℂ} (hΦ : Measurable Φ) {C : ℝ}
    (hC : ∀ x, wrapRate t (t - s) (circleRep x) * ‖Φ (x - ((t - s : ℝ) : 𝕋))‖ ≤ C) :
    MemLp (rateTerm α₀ t s Φ) 2 μc :=
  MemLp.of_bound (measurable_rateTerm α₀ t s hΦ).aestronglyMeasurable C
    (.of_forall fun x => (norm_rateTerm α₀ t s Φ x).trans_le (hC x))

/-- **The derivative in the time shift**: `τ ↦ U_{α(· + τ)}(t, s) φ` has the derivative
`-i (Σⱼ α'(sⱼ)) U(t, s) φ` at `0`, if `(Σⱼ α'(sⱼ)) |φ|` is bounded. -/
theorem hasDerivAt_phasePropagator_shift (α₀ : ℝ) {t s : ℝ} (hs : 0 ≤ s)
    {φ : L²} {Φ : 𝕋 → ℂ} (hΦ : Measurable Φ) (hφ : φ =ᵐ[μc] Φ) {C : ℝ}
    (hC : ∀ x, wrapRate t (t - s) (circleRep x) * ‖Φ (x - ((t - s : ℝ) : 𝕋))‖ ≤ C) :
    HasDerivAt (fun τ => V (fun r => sqrtPhase α₀ (r + τ)) t s φ) (rateVec α₀ t s Φ) 0 := by
  set T := t - s with hTdef
  have hT : T ≤ t := by linarith
  have hC0 : 0 ≤ C := (mul_nonneg (wrapRate_nonneg _ _ _) (norm_nonneg _)).trans (hC 0)
  have hmeas : ∀ τ : ℝ, Measurable fun r => sqrtPhase α₀ (r + τ) := fun τ =>
    ((continuous_sqrtPhase α₀).comp (continuous_id.add continuous_const)).measurable
  have hshift : (fun x => φ (x - (T : 𝕋))) =ᵐ[μc] fun x => Φ (x - (T : 𝕋)) :=
    (measurePreserving_sub (T : ℝ)).quasiMeasurePreserving.ae_eq_comp hφ
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_of_dominated (G := fun _ => 2 * C) (memLp_const _)
    (F := fun τ x => τ⁻¹ • (wrapPhase (fun r => sqrtPhase α₀ (r + τ)) t T x -
      wrapPhase (sqrtPhase α₀) t T x) * Φ (x - (T : 𝕋)))
    (f := rateTerm α₀ t s Φ) (.of_forall fun τ => ?_)
    (coeFn_rateVec (memLp_rateTerm hΦ hC)) (.of_forall fun τ => ?_)
    (measurable_rateTerm α₀ t s hΦ).aestronglyMeasurable ?_ ?_ (.of_forall fun x => ?_)
  · rw [slope_def_module, sqrtPhase_add_zero]
    filter_upwards [Lp.coeFn_smul (τ - 0)⁻¹ (V (fun r => sqrtPhase α₀ (r + τ)) t s φ -
        V (sqrtPhase α₀) t s φ),
      Lp.coeFn_sub (V (fun r => sqrtPhase α₀ (r + τ)) t s φ) (V (sqrtPhase α₀) t s φ),
      coeFn_phasePropagator (hmeas τ) t s φ,
      coeFn_phasePropagator (continuous_sqrtPhase α₀).measurable t s φ, hshift]
      with x h₁ h₂ h₃ h₄ h₅
    rw [h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, h₄, ← hTdef, h₅, sub_zero, ← sub_mul,
      smul_mul_assoc]
  · have h1 := measurable_wrapPhase (hmeas τ) t T
    have h2 := measurable_wrapPhase (continuous_sqrtPhase α₀).measurable t T
    have h3 : Measurable fun x => Φ (x - (T : 𝕋)) := hΦ.comp (measurable_sub_const _)
    exact (((h1.sub h2).const_smul τ⁻¹).mul h3).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with τ (hτ : τ ≠ 0)
    refine .of_forall fun x => ?_
    rw [norm_mul, norm_smul, norm_inv, Real.norm_eq_abs]
    have hτ' : 0 < |τ| := abs_pos.mpr hτ
    calc |τ|⁻¹ * ‖wrapPhase (fun r => sqrtPhase α₀ (r + τ)) t T x -
          wrapPhase (sqrtPhase α₀) t T x‖ * ‖Φ (x - (T : 𝕋))‖
        ≤ |τ|⁻¹ * (|τ| * (2 * wrapRate t T (circleRep x))) * ‖Φ (x - (T : 𝕋))‖ := by
          gcongr
          exact (norm_exp_neg_I_sub_le _ _).trans (abs_crossPhase_shift_sub_le α₀ hT τ _)
      _ = 2 * (wrapRate t T (circleRep x) * ‖Φ (x - (T : 𝕋))‖) := by
          field_simp
      _ ≤ 2 * C := by gcongr; exact hC x
  · exact .of_forall fun x => (norm_rateTerm α₀ t s Φ x).trans_le
      ((hC x).trans (by linarith))
  · have hd := hasDerivAt_crossPhase_shift α₀ hT (circleRep x)
    have hw := ((hd.ofReal_comp.const_mul Complex.I).neg).cexp
    have hlim := (hasDerivAt_iff_tendsto_slope.mp hw).mul_const (Φ (x - (T : 𝕋)))
    convert hlim using 1
    · funext τ
      rw [slope_def_module, sub_zero]
      simp only [wrapPhase, Pi.neg_apply, add_zero]
    · rw [rateTerm, ← hTdef]
      simp only [wrapPhase, Pi.neg_apply, add_zero]
      ring_nf

/-- **Product rule for a strongly continuous family of contractions.** -/
lemma hasDerivWithinAt_apply_apply {A : ℝ → L² →L[ℂ] L²} {w : ℝ → L²} {w' D : L²} {S : Set ℝ}
    (hA : ∀ τ f, ‖A τ f‖ ≤ ‖f‖) (hAc : Tendsto (fun τ => A τ w') (𝓝[S] 0) (𝓝 (A 0 w')))
    (hD : HasDerivWithinAt (fun τ => A τ (w 0)) D S 0) (hw : HasDerivWithinAt w w' S 0) :
    HasDerivWithinAt (fun τ => A τ (w τ)) (A 0 w' + D) S 0 := by
  rw [hasDerivWithinAt_iff_isLittleO] at hD hw ⊢
  have h1 : (fun τ => A τ (w τ - w 0 - (τ - 0) • w')) =o[𝓝[S] 0] fun τ => τ - 0 :=
    (Asymptotics.IsBigO.of_bound 1 (.of_forall fun τ => by
      rw [one_mul]; exact hA τ _)).trans_isLittleO hw
  have h2 : (fun τ => (τ - 0) • (A τ w' - A 0 w')) =o[𝓝[S] 0] fun τ => τ - 0 := by
    have h0 : (fun τ => A τ w' - A 0 w') =o[𝓝[S] 0] fun _ => (1 : ℝ) :=
      (Asymptotics.isLittleO_one_iff ℝ).mpr (by simpa using hAc.sub_const (A 0 w'))
    simpa using (Asymptotics.isBigO_refl (fun τ : ℝ => τ - 0) (𝓝[S] 0)).smul_isLittleO h0
  refine ((h1.add h2).add hD).congr_left fun τ => ?_
  simp only [map_sub, ContinuousLinearMap.map_smul_of_tower]
  module

attribute [local irreducible] phasePropagator crossPhase wrapPhase wrapRate

lemma continuous_phasePropagator_apply_comp {α : ℝ → ℝ} (hα : Continuous α) (f : L²)
    {X : Type*} [TopologicalSpace X] {a b : X → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous fun x => V α (a x) (b x) f :=
  (continuous_phasePropagator_apply hα f).comp (ha.prodMk hb)

/-! ### The right derivative of `t ↦ U(t, s) φ` -/

/-- **The right derivative at `t`**: if `τ ↦ U(s + τ, s) φ` has the right derivative `w'` at `0`
(`φ` is in the forward domain at `s`), then `τ ↦ U(t + τ, s) φ` has the right derivative
`U(t, s) w' - i (Σⱼ α'(sⱼ)) U(t, s) φ` at `0`. -/
theorem hasDerivWithinAt_phasePropagator_sqrtPhase (α₀ : ℝ) {t s : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) {φ w' : L²}
    (hw : HasDerivWithinAt (fun τ => V (sqrtPhase α₀) (s + τ) s φ) w' (Ici 0) 0)
    {Φ : 𝕋 → ℂ} (hΦ : Measurable Φ) (hφ : φ =ᵐ[μc] Φ) {C : ℝ}
    (hC : ∀ x, wrapRate t (t - s) (circleRep x) * ‖Φ (x - ((t - s : ℝ) : 𝕋))‖ ≤ C) :
    HasDerivWithinAt (fun τ => V (sqrtPhase α₀) (t + τ) s φ)
      (V (sqrtPhase α₀) t s w' + rateVec α₀ t s Φ) (Ici 0) 0 := by
  have hα := (continuous_sqrtPhase α₀).measurable
  have hAeq : ∀ τ, V (fun r => sqrtPhase α₀ (r + τ)) t s = V (sqrtPhase α₀) (t + τ) (s + τ) :=
    fun τ => (phasePropagator_add_time _ t s τ).symm
  have hw0 : V (sqrtPhase α₀) (s + 0) s φ = φ := by
    rw [add_zero, phasePropagator_self hα]
    rfl
  have key := hasDerivWithinAt_apply_apply (A := fun τ => V (fun r => sqrtPhase α₀ (r + τ)) t s)
    (w := fun τ => V (sqrtPhase α₀) (s + τ) s φ) (S := Ici 0) (D := rateVec α₀ t s Φ)
    (fun τ f => (norm_phasePropagator_apply
      ((continuous_sqrtPhase α₀).comp (continuous_id.add continuous_const)).measurable _ _ f).le)
    ?_ ?_ hw
  · simp only [sqrtPhase_add_zero] at key
    have heq : ∀ τ ∈ Ici (0 : ℝ), V (sqrtPhase α₀) (t + τ) s φ =
        V (fun r => sqrtPhase α₀ (r + τ)) t s (V (sqrtPhase α₀) (s + τ) s φ) := fun τ hτ => by
      have hτ : (0 : ℝ) ≤ τ := hτ
      rw [hAeq, ← ContinuousLinearMap.comp_apply,
        phasePropagator_comp hα (by linarith) (by linarith)]
    exact key.congr heq (heq 0 (Set.mem_Ici.mpr le_rfl))
  · have hc : Continuous fun τ : ℝ => V (sqrtPhase α₀) (t + τ) (s + τ) w' :=
      continuous_phasePropagator_apply_comp (continuous_sqrtPhase α₀) w'
        (continuous_const.add continuous_id) (continuous_const.add continuous_id)
    have hc' : Continuous fun τ : ℝ => V (fun r => sqrtPhase α₀ (r + τ)) t s w' :=
      hc.congr fun τ => by rw [hAeq]
    exact (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
  · show HasDerivWithinAt (fun τ => V (fun r => sqrtPhase α₀ (r + τ)) t s
      (V (sqrtPhase α₀) (s + 0) s φ)) _ _ _
    rw [hw0]
    exact (hasDerivAt_phasePropagator_shift α₀ hs hΦ hφ hC).hasDerivWithinAt

/-- The right derivative at `0` of `τ ↦ f (t + τ)`, as the right derivative of `f` at `t`. -/
lemma hasDerivWithinAt_Ici_of_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' : E} {t : ℝ} (h : HasDerivWithinAt (fun τ => f (t + τ)) f' (Ici 0) 0) :
    HasDerivWithinAt f f' (Ici t) t := by
  have h' : HasDerivWithinAt (fun τ => f (t + τ)) f' (Ici 0) (t - t) := by rwa [sub_self]
  have := HasDerivWithinAt.scomp (h := fun r => r - t) (s := Ici t) t h'
    ((hasDerivAt_id' t).sub_const t).hasDerivWithinAt
    (fun r (hr : t ≤ r) => show (0 : ℝ) ≤ r - t by linarith)
  rw [one_smul] at this
  exact this.congr (fun r _ => by simp) (by simp)

/-- **A continuous right derivative is a derivative**: if `u` and `v` are continuous on `[s, ∞)`
and `v t` is the right derivative of `u` at every `t ≥ s`, then `u` is `C¹` on `[s, ∞)`. -/
lemma hasDerivWithinAt_of_hasDerivWithinAt_Ici {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {u v : ℝ → E} {s : ℝ} (hu : ContinuousOn u (Ici s))
    (hv : ContinuousOn v (Ici s)) (hd : ∀ t, s ≤ t → HasDerivWithinAt u (v t) (Ici t) t)
    {t : ℝ} (ht : s ≤ t) : HasDerivWithinAt u (v t) (Ici s) t := by
  set v' : ℝ → E := fun r => v (max s r)
  have hv' : Continuous v' :=
    hv.comp_continuous (continuous_const.max continuous_id) fun r => le_max_left s r
  have hvv : ∀ r, s ≤ r → v' r = v r := fun r hr => by simp [v', max_eq_right hr]
  have hI : ∀ r, HasDerivAt (fun r => ∫ x in s..r, v' x) (v' r) r := fun r =>
    (hv'.integral_hasStrictDerivAt s r).hasDerivAt
  have hcst : ∀ r, s ≤ r → u r = u s + ∫ x in s..r, v' x := fun r hr => by
    have h := constant_of_has_deriv_right_zero (f := fun r => u r - ∫ x in s..r, v' x)
      (a := s) (b := r) ((hu.mono Icc_subset_Ici_self).sub
        (continuous_iff_continuousAt.mpr fun r => (hI r).continuousAt).continuousOn)
      (fun x hx => by
        have := (hd x hx.1).sub (hI x).hasDerivWithinAt
        rwa [hvv x hx.1, sub_self] at this) r ⟨hr, le_rfl⟩
    simp only [intervalIntegral.integral_same, sub_zero] at h
    rw [← h]
    abel
  have := ((hI t).const_add (u s)).hasDerivWithinAt (s := Ici s)
  rw [hvv t ht] at this
  exact this.congr (fun r hr => hcst r hr) (hcst t ht)

/-! ### Continuity of the derivative -/

lemma continuousAt_wrapRate {s y t₀ : ℝ} (hs : 0 ≤ s) (h : y - (t₀ - s) ≠ ⌊y - (t₀ - s)⌋) :
    ContinuousAt (fun t => wrapRate t (t - s) y) t₀ := by
  have hz : ContinuousAt (fun t : ℝ => y - (t - s)) t₀ := by fun_prop
  have hev := hz.tendsto.eventually (eventually_floor_eq h)
  refine ContinuousAt.congr (f := fun t =>
    ∑ m ∈ Finset.Ioc ⌊y - (t₀ - s)⌋ ⌊y⌋, 1 / (2 * √(t - y + m))) ?_ ?_
  · refine tendsto_finsetSum _ fun m hm => ?_
    have hr : 0 < t₀ - y + m := by linarith [sub_lt_of_mem_Ioc (t := t₀) hm]
    exact ((continuousAt_const.div (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
      (by fun_prop : ContinuousAt (fun t : ℝ => t - y + m) t₀)))
      (mul_pos two_pos (Real.sqrt_pos.mpr hr)).ne')).tendsto
  · filter_upwards [hev] with t ht
    rw [wrapRate, ht]

/-- For `Φ = G ∘ rep` with `G` continuous, `t ↦ Φ(x - (t - s))` is continuous at `t₀` away from
the point `x = t₀ - s`. -/
lemma continuousAt_comp_sub {G : ℝ → ℂ} (hG : Continuous G) {s t₀ : ℝ} {x : 𝕋}
    (h : circleRep x - (t₀ - s) ≠ ⌊circleRep x - (t₀ - s)⌋) :
    ContinuousAt (fun t : ℝ => G (circleRep (x - ((t - s : ℝ) : 𝕋)))) t₀ := by
  have hr : ∀ t : ℝ, circleRep (x - ((t - s : ℝ) : 𝕋)) =
      circleRep x - (t - s) - ⌊circleRep x - (t - s)⌋ := fun t => by
    conv_lhs => rw [← coe_circleRep x]
    rw [← AddCircle.coe_sub, circleRep_coe, Int.fract]
  simp_rw [hr]
  have hz : ContinuousAt (fun t : ℝ => circleRep x - (t - s)) t₀ := by fun_prop
  have hev := hz.tendsto.eventually (eventually_floor_eq h)
  refine ContinuousAt.congr (f := fun t : ℝ =>
    G (circleRep x - (t - s) - ⌊circleRep x - (t₀ - s)⌋)) ?_ ?_
  · exact hG.continuousAt.comp (by fun_prop)
  · filter_upwards [hev] with t ht
    rw [ht]

/-- **The derivative is continuous**: `t ↦ -i (Σⱼ α'(sⱼ)) U(t, s) φ` is continuous on `[s, ∞)`,
for `φ = G ∘ rep` with `G` continuous and a locally bounded `(Σⱼ α'(sⱼ)) |φ|`. -/
theorem continuousOn_rateVec (α₀ : ℝ) {s : ℝ} (hs : 0 ≤ s) {G : ℝ → ℂ} (hG : Continuous G)
    {K : ℝ} (hK : ∀ t, s ≤ t → ∀ x : 𝕋,
      wrapRate t (t - s) (circleRep x) * ‖G (circleRep (x - ((t - s : ℝ) : 𝕋)))‖ ≤
        K * (t - s + 1)) :
    ContinuousOn (fun t => rateVec α₀ t s (fun x => G (circleRep x))) (Ici s) := by
  have hΦ : Measurable fun x : 𝕋 => G (circleRep x) := hG.measurable.comp measurable_circleRep
  intro t₀ ht₀
  have ht₀' : s ≤ t₀ := ht₀
  refine tendsto_of_dominated (G := fun _ => K * (t₀ - s + 2)) (memLp_const _)
    (F := fun t => rateTerm α₀ t s fun x => G (circleRep x)) ?_
    (coeFn_rateVec (memLp_rateTerm hΦ (hK t₀ ht₀')))
    (.of_forall fun t => (measurable_rateTerm α₀ t s hΦ).aestronglyMeasurable)
    (measurable_rateTerm α₀ t₀ s hΦ).aestronglyMeasurable ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with t (ht : s ≤ t)
    exact coeFn_rateVec (memLp_rateTerm hΦ (hK t ht))
  · have hK0 : 0 ≤ K := by
      have := (mul_nonneg (wrapRate_nonneg _ _ _) (norm_nonneg _)).trans (hK s le_rfl 0)
      linarith [show K * (s - s + 1) = K by ring]
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds
      (show t₀ < t₀ + 1 by linarith))] with t (ht : s ≤ t) (ht1 : t < t₀ + 1)
    refine .of_forall fun x => (norm_rateTerm α₀ t s _ x).trans_le ((hK t ht x).trans ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) hK0
  · have hK0 : 0 ≤ K := by
      have := (mul_nonneg (wrapRate_nonneg _ _ _) (norm_nonneg _)).trans (hK s le_rfl 0)
      linarith [show K * (s - s + 1) = K by ring]
    refine .of_forall fun x => (norm_rateTerm α₀ t₀ s _ x).trans_le ((hK t₀ ht₀' x).trans ?_)
    exact mul_le_mul_of_nonneg_left (by linarith) hK0
  · filter_upwards [ae_sub_ne_floor (t₀ - s)] with x hx
    have h1 := continuousAt_wrapRate (y := circleRep x) hs hx
    have h2 : ContinuousAt (fun t => wrapPhase (sqrtPhase α₀) t (t - s) x) t₀ := by
      have hc := continuousAt_crossPhase (continuous_sqrtPhase α₀) (y := circleRep x)
        (p₀ := (t₀, s)) hx
      have hc2 : ContinuousAt (fun t : ℝ => crossPhase (sqrtPhase α₀) t (t - s) (circleRep x))
          t₀ :=
        ContinuousAt.comp (x := t₀) (g := fun p : ℝ × ℝ =>
          crossPhase (sqrtPhase α₀) p.1 (p.1 - p.2) (circleRep x)) hc
          (continuousAt_id.prodMk continuousAt_const)
      unfold wrapPhase
      exact ((Complex.continuous_ofReal.continuousAt.comp hc2).const_mul Complex.I).neg.cexp
    have h3 := continuousAt_comp_sub hG hx
    have h4 : ContinuousAt (fun t => rateTerm α₀ t s (fun x => G (circleRep x)) x) t₀ := by
      unfold rateTerm
      exact ((Complex.continuous_ofReal.continuousAt.comp h1).const_mul _).neg.mul (h2.mul h3)
    exact h4.tendsto.mono_left nhdsWithin_le_nhds

/-! ### The bounds on `(Σⱼ α'(sⱼ)) |φ|` -/

lemma card_Ioc_floor_le {y T : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) (hT : 0 ≤ T) :
    ((Finset.Ioc ⌊y - T⌋ ⌊y⌋).card : ℝ) ≤ T + 1 := by
  have h0 : ⌊y⌋ = 0 := Int.floor_eq_zero_iff.mpr hy
  have hle : ⌊y - T⌋ ≤ 0 := h0 ▸ Int.floor_mono (by linarith)
  have h1 := Int.lt_floor_add_one (y - T)
  rw [Int.card_Ioc, h0, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  push_cast
  linarith [hy.1]

/-- The wrap-around times of `U(t, t - T)` at `y` are at least `t - T + (1 - fract (y - T))`. -/
lemma le_of_mem_Ioc_floor {t T y : ℝ} {m : ℤ} (hm : m ∈ Finset.Ioc ⌊y - T⌋ ⌊y⌋) :
    t - T + (1 - Int.fract (y - T)) ≤ t - y + m := by
  have h2 : ((⌊y - T⌋ + 1 : ℤ) : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Ioc.mp hm).1
  push_cast at h2
  rw [Int.fract]
  linarith

lemma circleRep_sub_eq_fract (x : 𝕋) (T : ℝ) :
    circleRep (x - (T : 𝕋)) = Int.fract (circleRep x - T) := by
  conv_lhs => rw [← coe_circleRep x]
  rw [← AddCircle.coe_sub, circleRep_coe]

/-- For `s > 0`, `α' ≤ 1/(2√s)` at all wrap-around times. -/
lemma wrapRate_le {t s : ℝ} (hs : 0 < s) (hst : s ≤ t) {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    wrapRate t (t - s) y ≤ (t - s + 1) * (1 / (2 * √s)) := by
  have hcard := card_Ioc_floor_le hy (sub_nonneg.mpr hst)
  have h2s : 0 < 2 * √s := mul_pos two_pos (Real.sqrt_pos.mpr hs)
  rw [wrapRate]
  refine (Finset.sum_le_card_nsmul _ _ (1 / (2 * √s)) fun m hm => ?_).trans ?_
  · have hr := sub_lt_of_mem_Ioc (t := t) hm
    rw [sub_sub_cancel] at hr
    exact one_div_le_one_div_of_le h2s
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr.le) two_pos.le)
  · rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **Cauchy–Schwarz at the right end**: for `∫₀¹ g = 0`, `|∫₀ᶻ g| = |∫_z¹ g| ≤ √(1 - z) ‖g‖`. -/
lemma norm_integral_le_sqrt {g : L²} (hg : ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0) {z : ℝ}
    (hz : z ∈ Ico (0 : ℝ) 1) : ‖∫ u in (0 : ℝ)..z, g (u : 𝕋)‖ ≤ √(1 - z) * ‖g‖ := by
  rcases hz.1.eq_or_lt with rfl | hz0
  · simp
  set S : Set 𝕋 := {x | 1 - (1 - z) ≤ circleRep x}
  have hS : MeasurableSet S := measurableSet_tail (1 - z)
  have hμS := measureReal_tail (show 0 ≤ 1 - z by linarith [hz.2]) (show 1 - z < 1 by linarith)
  have hind : S.indicator (fun x => g x) =
      fun x => (Ici z).indicator (fun u : ℝ => g (u : 𝕋)) (circleRep x) := by
    funext x
    by_cases h : z ≤ circleRep x
    · rw [Set.indicator_of_mem (show x ∈ S by simp [S, h]),
        Set.indicator_of_mem (show circleRep x ∈ Ici z from h), coe_circleRep]
    · rw [Set.indicator_of_notMem (show x ∉ S by simp [S, h]),
        Set.indicator_of_notMem (show circleRep x ∉ Ici z from h)]
  have hint : ∫ x in S, g x ∂μc = ∫ u in z..1, g (u : 𝕋) := by
    rw [← integral_indicator hS, hind, integral_comp_circleRep,
      intervalIntegral.integral_of_le zero_le_one, setIntegral_indicator measurableSet_Ici,
      intervalIntegral.integral_of_le hz.2.le,
      show Ioc (0 : ℝ) 1 ∩ Ici z = Icc z 1 by
        ext u
        simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨by linarith [h.1], h.2⟩, h.1⟩⟩,
      integral_Icc_eq_integral_Ioc]
  have hinner := L2.inner_indicatorConstLp_one hS (measure_ne_top μc S) g
  have hnorm : ‖indicatorConstLp 2 hS (measure_ne_top μc S) (1 : ℂ)‖ = √(1 - z) := by
    rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul, hμS,
      Real.sqrt_eq_rpow]
    norm_num
  have hsplit : ∫ u in (0 : ℝ)..z, g (u : 𝕋) = -∫ u in z..1, g (u : 𝕋) := by
    have h := intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_lift g 0 z)
      (intervalIntegrable_lift g z 1)
    rw [hg] at h
    linear_combination h
  rw [hsplit, norm_neg, ← hint, ← hinner, ← hnorm]
  exact norm_inner_le_norm _ _

/-- For `φ ∈ H¹₀(0, 1)` and `s = 0`, `(Σⱼ α'(sⱼ)) |φ(x - t)| ≤ (t + 1) ‖φ'‖ / 2`: the first
wrap-around time `1 - z` of the point `z = x - t` compensates `|φ(z)| ≤ √(1 - z) ‖φ'‖`. -/
lemma wrapRate_mul_le_of_sobolevZero {g : L²} (hg : ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0) {t : ℝ}
    (ht : 0 ≤ t) (x : 𝕋) :
    wrapRate t t (circleRep x) * ‖∫ u in (0 : ℝ)..circleRep (x - (t : 𝕋)), g (u : 𝕋)‖ ≤
      ‖g‖ / 2 * (t + 1) := by
  set y := circleRep x
  rw [circleRep_sub_eq_fract]
  set z := Int.fract (y - t) with hzdef
  have hz : z ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hG := norm_integral_le_sqrt hg hz
  have hcard := card_Ioc_floor_le (circleRep_mem x) ht
  rw [wrapRate, Finset.sum_mul]
  refine (Finset.sum_le_card_nsmul _ _ (‖g‖ / 2) fun m hm => ?_).trans ?_
  · have hr := le_of_mem_Ioc_floor (t := t) hm
    rw [sub_self, zero_add, ← hzdef] at hr
    have h1z : 0 < 1 - z := by linarith [hz.2]
    have hpos : 0 < √(t - y + m) := Real.sqrt_pos.mpr (by linarith)
    calc 1 / (2 * √(t - y + m)) * ‖∫ u in (0 : ℝ)..z, g (u : 𝕋)‖
        ≤ 1 / (2 * √(t - y + m)) * (√(t - y + m) * ‖g‖) := by
          gcongr
          exact hG.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hr) (norm_nonneg _))
      _ = ‖g‖ / 2 := by field_simp
  · rw [nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hcard (by positivity)

lemma sqrtPhase_holder' (α₀ t₀ : ℝ) :
    ∃ C δ, 0 < δ ∧ ∀ s ∈ Icc (0 : ℝ) δ, |sqrtPhase α₀ (t₀ + s) - sqrtPhase α₀ t₀| ≤ C * √s := by
  rcases eq_or_ne t₀ 0 with rfl | ht
  · exact sqrtPhase_holder α₀
  · obtain ⟨δ, hδ, h⟩ := sqrtPhase_littleO α₀ ht 1 one_pos
    exact ⟨1, δ, hδ, h⟩

/-- **A continuous representative with the bound**: every `φ` in the forward domain at `s ≥ 0` is
`G ∘ rep` with `G` continuous, and `(Σⱼ α'(sⱼ)) |φ|` grows at most linearly in `t`. -/
lemma exists_rep_of_mem_forwardDomain (α₀ : ℝ) {s : ℝ} (hs : 0 ≤ s) {φ : L²}
    (hφ : φ ∈ forwardDomain (sqrtPhase α₀) s) :
    ∃ G : ℝ → ℂ, Continuous G ∧ φ =ᵐ[μc] (fun x => G (circleRep x)) ∧ ∃ K, ∀ t, s ≤ t →
      ∀ x : 𝕋, wrapRate t (t - s) (circleRep x) * ‖G (circleRep (x - ((t - s : ℝ) : 𝕋)))‖ ≤
        K * (t - s + 1) := by
  have hα := (continuous_sqrtPhase α₀).measurable
  rcases hs.eq_or_lt with rfl | hs0
  · have hφ' : φ ∈ sobolevZero := by
      rw [← forwardDomain_sqrtPhase α₀]
      exact hφ
    obtain ⟨g, hg, rfl⟩ := hφ'
    refine ⟨fun y => ∫ u in (0 : ℝ)..y, g (u : 𝕋), continuous_primitive_lift g,
      (memLp_primitiveFun g).coeFn_toLp, ‖g‖ / 2, fun t ht x => ?_⟩
    simp only [sub_zero]
    exact wrapRate_mul_le_of_sobolevZero hg ht x
  · have hmem : φ ∈ (momentum (sqrtPhase α₀ s)).domain :=
      (forwardHamiltonian_le_momentum hα (sqrtPhase_holder' α₀ s)).1 hφ
    have hp := mem_graph_momentum.mp ((momentum (sqrtPhase α₀ s)).mem_graph ⟨φ, hmem⟩)
    change IsMomentumPair _ φ _ at hp
    obtain ⟨c, g, -, hφeq, -⟩ := hp
    obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (continuous_primitive_lift g).continuousOn
    set M := ‖c‖ + max C₁ 0
    refine ⟨fun y => c + ∫ u in (0 : ℝ)..y, g (u : 𝕋),
      continuous_const.add (continuous_primitive_lift g), ?_, M * (1 / (2 * √s)),
      fun t ht x => ?_⟩
    · rw [hφeq]
      filter_upwards [Lp.coeFn_add (c • planeWave 0) (primitive g), Lp.coeFn_smul c (planeWave 0),
        (memLp_planeWaveFun 0).coeFn_toLp, (memLp_primitiveFun g).coeFn_toLp]
        with y h₁ h₂ h₃ h₄
      rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, planeWave, h₃, primitive, h₄, smul_eq_mul]
      simp [planeWaveFun, primitiveFun]
    · have hb : ‖c + ∫ u in (0 : ℝ)..circleRep (x - ((t - s : ℝ) : 𝕋)), g (u : 𝕋)‖ ≤ M :=
        (norm_add_le _ _).trans (add_le_add le_rfl ((hC₁ _ (Ico_subset_Icc_self
          (circleRep_mem _))).trans (le_max_left _ _)))
      have hw := wrapRate_le hs0 ht (circleRep_mem x)
      calc wrapRate t (t - s) (circleRep x) *
            ‖c + ∫ u in (0 : ℝ)..circleRep (x - ((t - s : ℝ) : 𝕋)), g (u : 𝕋)‖
          ≤ (t - s + 1) * (1 / (2 * √s)) * M :=
            mul_le_mul hw hb (norm_nonneg _) (by have := sub_nonneg.mpr ht; positivity)
        _ = M * (1 / (2 * √s)) * (t - s + 1) := by ring

/-! ### Classical solutions -/

/-- **Classical solutions from every `φ` in the forward domain at `s ≥ 0`**: `t ↦ U(t, s) φ` is
`C¹` on `[s, ∞)`, and its derivative at `t` is also the right derivative of
`τ ↦ U(t + τ, t) U(t, s) φ` at `0`. -/
theorem exists_classical_solution (α₀ : ℝ) {s : ℝ} (hs : 0 ≤ s) {φ : L²}
    (hφ : φ ∈ forwardDomain (sqrtPhase α₀) s) :
    ∃ v : ℝ → L², ContinuousOn v (Ici s) ∧ ∀ t, s ≤ t →
      HasDerivWithinAt (fun r => V (sqrtPhase α₀) r s φ) (v t) (Ici s) t ∧
      HasDerivWithinAt (fun τ => V (sqrtPhase α₀) (t + τ) t (V (sqrtPhase α₀) t s φ)) (v t)
        (Ici 0) 0 := by
  have hα := (continuous_sqrtPhase α₀).measurable
  obtain ⟨G, hG, hφG, K, hK⟩ := exists_rep_of_mem_forwardDomain α₀ hs hφ
  have hΦ : Measurable fun x : 𝕋 => G (circleRep x) := hG.measurable.comp measurable_circleRep
  have hw := (mem_forwardDomain.mp hφ).hasDerivWithinAt
  set w' := derivWithin (fun τ => V (sqrtPhase α₀) (s + τ) s φ) (Ici 0) 0
  set v : ℝ → L² := fun t =>
    V (sqrtPhase α₀) t s w' + rateVec α₀ t s (fun x => G (circleRep x)) with hvdef
  have hright : ∀ t, s ≤ t →
      HasDerivWithinAt (fun τ => V (sqrtPhase α₀) (t + τ) s φ) (v t) (Ici 0) 0 :=
    fun t ht => hasDerivWithinAt_phasePropagator_sqrtPhase α₀ hs ht hw hΦ hφG (hK t ht)
  have hv : ContinuousOn v (Ici s) :=
    (continuous_phasePropagator_apply_comp (continuous_sqrtPhase α₀) w' continuous_id
      continuous_const).continuousOn.add (continuousOn_rateVec α₀ hs hG hK)
  have hu : ContinuousOn (fun r => V (sqrtPhase α₀) r s φ) (Ici s) :=
    (continuous_phasePropagator_apply_comp (continuous_sqrtPhase α₀) φ continuous_id
      continuous_const).continuousOn
  refine ⟨v, hv, fun t ht => ⟨hasDerivWithinAt_of_hasDerivWithinAt_Ici hu hv
    (fun r hr => hasDerivWithinAt_Ici_of_add (hright r hr)) ht, ?_⟩⟩
  refine (hright t ht).congr (fun τ (hτ : 0 ≤ τ) => ?_) ?_
  · rw [← ContinuousLinearMap.comp_apply, phasePropagator_comp hα ht (by linarith)]
  · rw [← ContinuousLinearMap.comp_apply, phasePropagator_comp hα ht (by linarith)]

/-- **Engel–Nagel, Def. VI.9.2, on `[0, ∞)` and for `u̇ = -iH(t) u`**: `U` is an evolution
family, and it solves the Cauchy problem on the spaces `Y t`. These are dense subspaces of the
domains of the `H t`, with `U(t, s) Y s ⊆ Y t`, and `t ↦ U(t, s) x` is a classical solution for
`x ∈ Y s`: `C¹` on `[s, ∞)`, in the domain of `H t`, with derivative `-iH(t) U(t, s) x`. -/
structure SolvesCauchyProblem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : ℝ → ℝ → E →L[ℂ] E) (H : ℝ → E →ₗ.[ℂ] E) (Y : ℝ → Submodule ℂ E) : Prop where
  comp : ∀ t r s, 0 ≤ s → s ≤ r → r ≤ t → U t r ∘L U r s = U t s
  self : ∀ s, U s s = 1
  continuousOn : ∀ x, ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2 x) {p | 0 ≤ p.2 ∧ p.2 ≤ p.1}
  dense : ∀ s, 0 ≤ s → Dense (Y s : Set E)
  le_domain : ∀ s, 0 ≤ s → Y s ≤ (H s).domain
  mapsTo : ∀ s t, 0 ≤ s → s ≤ t → ∀ x ∈ Y s, U t s x ∈ Y t
  solution : ∀ s, 0 ≤ s → ∀ x ∈ Y s, ∃ u' : ℝ → E, ContinuousOn u' (Ici s) ∧ ∀ t, s ≤ t →
    HasDerivWithinAt (fun r => U r s x) (u' t) (Ici s) t ∧
      ∃ h : U t s x ∈ (H t).domain, u' t = (-Complex.I) • H t ⟨U t s x, h⟩

/-- **`U` solves the Cauchy problem for `H(t) = H_{α₀ + √t}`** on the forward domains. -/
theorem sqrtPhase_solvesCauchyProblem (α₀ : ℝ) :
    SolvesCauchyProblem (V (sqrtPhase α₀)) (fun t => momentum (sqrtPhase α₀ t))
      (forwardDomain (sqrtPhase α₀)) where
  comp _ _ _ _ hsr hrt := phasePropagator_comp (continuous_sqrtPhase α₀).measurable hsr hrt
  self := phasePropagator_self (continuous_sqrtPhase α₀).measurable
  continuousOn x := (continuous_phasePropagator_apply (continuous_sqrtPhase α₀) x).continuousOn
  dense s hs := by
    have hα := (continuous_sqrtPhase α₀).measurable
    rw [show (forwardDomain (sqrtPhase α₀) s : Set L²) =
      ((forwardHamiltonian (sqrtPhase α₀) s).domain : Set L²) from rfl]
    rcases hs.eq_or_lt with rfl | hs0
    · rw [forwardHamiltonian_sqrtPhase]
      exact dense_switchedDomain
    · rw [forwardHamiltonian_eq_momentum hα (sqrtPhase_littleO α₀ hs0.ne')]
      exact dense_domain_momentum
  le_domain s _ :=
    (forwardHamiltonian_le_momentum (continuous_sqrtPhase α₀).measurable
      (sqrtPhase_holder' α₀ s)).1
  mapsTo s t hs hst x hx := by
    obtain ⟨v, -, hv⟩ := exists_classical_solution α₀ hs hx
    exact mem_forwardDomain.mpr (hv t hst).2.differentiableWithinAt
  solution s hs x hx := by
    obtain ⟨v, hvc, hv⟩ := exists_classical_solution α₀ hs hx
    refine ⟨v, hvc, fun t ht => ⟨(hv t ht).1, ?_⟩⟩
    obtain ⟨h, hH⟩ := momentum_of_hasDerivWithinAt_phasePropagator
      (continuous_sqrtPhase α₀).measurable (sqrtPhase_holder' α₀ t) (hv t ht).2
    refine ⟨h, ?_⟩
    rw [hH, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

/-- **Solving the Cauchy problem does not make the generator self-adjoint.** The propagator of
`H(t) = H_{α₀ + √t}` solves the Cauchy problem (Engel–Nagel, Def. VI.9.2) on the spaces
`Y t = D(H_{α(t)})` for `t > 0` and `Y 0 = H¹₀(0, 1)`, a proper subspace of `D(H_{α₀})`. The
generator on `Y 0`, the forward Hamiltonian at `0`, is the restriction of `H_{α₀}` to `Y 0`, and it
is not self-adjoint. -/
theorem sqrtPhase_cauchyProblem (α₀ : ℝ) :
    SolvesCauchyProblem (V (sqrtPhase α₀)) (fun t => momentum (sqrtPhase α₀ t))
        (forwardDomain (sqrtPhase α₀)) ∧
      (∀ t, 0 < t → forwardDomain (sqrtPhase α₀) t = (momentum (sqrtPhase α₀ t)).domain) ∧
      (forwardDomain (sqrtPhase α₀) 0 : Set L²) = sobolevZero ∧
      forwardDomain (sqrtPhase α₀) 0 < (momentum α₀).domain ∧
      forwardHamiltonian (sqrtPhase α₀) 0 ≤ momentum α₀ ∧
      ¬ IsSelfAdjoint (forwardHamiltonian (sqrtPhase α₀) 0) := by
  have hα := (continuous_sqrtPhase α₀).measurable
  have hγ : sqrtPhase α₀ 0 = α₀ := by simp [sqrtPhase]
  have hle : forwardHamiltonian (sqrtPhase α₀) 0 ≤ momentum α₀ := by
    have h := forwardHamiltonian_le_momentum hα (sqrtPhase_holder α₀)
    rwa [hγ] at h
  refine ⟨sqrtPhase_solvesCauchyProblem α₀, fun t ht => congrArg LinearPMap.domain
    (forwardHamiltonian_eq_momentum hα (sqrtPhase_littleO α₀ ht.ne')),
    forwardDomain_sqrtPhase α₀, lt_of_le_of_ne hle.1 fun heq => ?_, hle,
    not_isSelfAdjoint_forwardHamiltonian_sqrtPhase α₀⟩
  refine not_isSelfAdjoint_forwardHamiltonian_sqrtPhase α₀ ?_
  rw [LinearPMap.eq_of_le_of_domain_eq hle heq]
  exact isSelfAdjoint_momentum

end UnitaryEntropy
