/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Equivalence of sup-norm, L¹, and L² seminorms on the Schwartz space.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

For smooth `f : ℝ → ℂ` the brief compares three families of seminorms of `x^α ∂^β f`
(`weighted α β f`): sup (1), `L¹` (2) and `L²` (3). They are taken with values in `[0, ∞]`, so
that the finiteness conditions of Theorem 5 make sense for every smooth `f`.

The three steps of the proof:
* `l2Norm_sq_le`  eq. (6), sup controls `L²`;
* `l1Norm_le`     eq. (7), `L²` controls `L¹` (Cauchy–Schwarz with weight `1/(1+x²)`);
* `supNorm_le`    eq. (9), `L¹` controls sup, under the hypothesis `‖f‖^{L¹}_{α,β} < ∞` that
  the brief uses but does not state; `not_supNorm_le_const` shows that it is needed.

Theorem 5:
* `tfae_finite`  (i) ⇔ (ii) ⇔ (iii);
* `exists_schwartzMap_iff`, `supNorm_eq_seminorm`  the space (4) and its sup seminorms are
  Mathlib's `𝓢(ℝ, ℂ)` and `SchwartzMap.seminorm`;
* `withSeminorms_l1_l2`  the `L¹` family `l1Family` and the `L²` family `l2Family` both generate
  the topology of `𝓢(ℝ, ℂ)` (Step 4, via `WithSeminorms.congr_of_cycle` in `ForMathlib`).

Remark (sesquilinear forms):
* `enorm_moment_le`  eq. (10), `|⟨f|X^α P^β|f⟩| ≤ |ħ|^β ‖f‖^{L²}_{0,0} ‖f‖^{L²}_{α,β}`, with the
  moments of `SchwartzMomentProblem`. The brief omits the factor `|ħ|^β`.
-/
public import ForMathlib.Analysis.LocallyConvex.WithSeminorms
public import ForMathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import ForMathlib.MeasureTheory.Integral.IntegralEqImproper
public import SchwartzMomentProblem

open Real MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace SchwartzNorms

/-- `x^α ∂^β f(x)`. -/
def weighted (α β : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ) ^ α * iteratedDeriv β f x

/-- The sup seminorm (1), with values in `[0, ∞]`. -/
def supNorm (α β : ℕ) (f : ℝ → ℂ) : ℝ≥0∞ := ⨆ x, ‖weighted α β f x‖ₑ

/-- The `L¹` seminorm (2). -/
def l1Norm (α β : ℕ) (f : ℝ → ℂ) : ℝ≥0∞ := eLpNorm (weighted α β f) 1 volume

/-- The `L²` seminorm (3). -/
def l2Norm (α β : ℕ) (f : ℝ → ℂ) : ℝ≥0∞ := eLpNorm (weighted α β f) 2 volume

variable {f : ℝ → ℂ}

lemma enorm_ofReal (x : ℝ) : ‖(x : ℂ)‖ₑ = ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real]

lemma enorm_weighted_succ (α β : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    ‖weighted (α + 1) β f x‖ₑ = ‖x‖ₑ * ‖weighted α β f x‖ₑ := by
  simp only [weighted, pow_succ, enorm_mul, enorm_ofReal]
  ring

lemma continuous_weighted (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) : Continuous (weighted α β f) :=
  (Complex.continuous_ofReal.pow α).mul (hf.continuous_iteratedDeriv β (by exact_mod_cast le_top))

lemma l1Norm_eq (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) :
    l1Norm α β f = ∫⁻ x, ‖weighted α β f x‖ₑ :=
  eLpNorm_one_eq_lintegral_enorm (continuous_weighted hf α β).aestronglyMeasurable

lemma l2Norm_eq (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) :
    l2Norm α β f = (∫⁻ x, ‖weighted α β f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [l2Norm, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (continuous_weighted hf α β).aestronglyMeasurable]
  simp

lemma l2Norm_sq (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) :
    l2Norm α β f ^ 2 = ∫⁻ x, ‖weighted α β f x‖ₑ ^ 2 := by
  rw [l2Norm_eq hf, ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
  simp

/-! ### Step 1: sup controls `L²` -/

lemma lintegral_compl_Icc_inv_sq :
    ∫⁻ x in (Icc (-1 : ℝ) 1)ᶜ, ENNReal.ofReal (x ^ 2)⁻¹ = 2 := by
  have hc : (Icc (-1 : ℝ) 1)ᶜ = Iio (-1) ∪ Ioi 1 := by
    ext x
    rw [mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi, not_and_or, not_le, not_le]
  rw [hc, lintegral_union measurableSet_Ioi
      (disjoint_left.mpr fun x (h1 : x < -1) (h2 : 1 < x) => by linarith),
    ← ofReal_integral_eq_lintegral_ofReal integrableOn_Iio_neg_one_inv_sq
      (ae_of_all _ fun _ => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal integrableOn_Ioi_one_inv_sq
      (ae_of_all _ fun _ => by positivity),
    integral_Iio_neg_one_inv_sq, integral_Ioi_one_inv_sq]
  norm_num

/-- Eq. (6): `(‖f‖^{L²}_{α,β})² ≤ 2 (‖f‖^{sup}_{α,β})² + 2 (‖f‖^{sup}_{α+1,β})²`. -/
theorem l2Norm_sq_le (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) :
    l2Norm α β f ^ 2 ≤ 2 * supNorm α β f ^ 2 + 2 * supNorm (α + 1) β f ^ 2 := by
  set a := supNorm α β f
  set b := supNorm (α + 1) β f
  set S := Icc (-1 : ℝ) 1
  have hpt : ∀ x, ‖weighted α β f x‖ₑ ^ 2 ≤
      S.indicator (fun _ => a ^ 2) x +
        Sᶜ.indicator (fun x => b ^ 2 * ENNReal.ofReal (x ^ 2)⁻¹) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, indicator_of_notMem (notMem_compl_iff.mpr hx), add_zero]
      exact pow_le_pow_left₀ (by simp) (le_iSup (fun x => ‖weighted α β f x‖ₑ) x) 2
    · rw [indicator_of_notMem hx, indicator_of_mem (mem_compl hx), zero_add]
      have h1 : 1 < |x| := by
        by_contra h
        exact hx (abs_le.mp (not_lt.mp h))
      have hb : ‖x‖ₑ * ‖weighted α β f x‖ₑ ≤ b := by
        rw [← enorm_weighted_succ]
        exact le_iSup (fun x => ‖weighted (α + 1) β f x‖ₑ) x
      have hx0' : x ≠ 0 := by rintro rfl; norm_num at h1
      have hx2 : ENNReal.ofReal (x ^ 2)⁻¹ = (‖x‖ₑ ^ 2)⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos (pow_pos (abs_pos.mpr hx0') 2 |>.trans_eq (sq_abs x)),
          Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]
      have hx0 : ‖x‖ₑ ^ 2 ≠ 0 := by simpa using hx0'
      rw [hx2, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le (Or.inl hx0) (Or.inl (by simp)),
        ← mul_pow, mul_comm]
      exact pow_le_pow_left₀ (by simp) hb 2
  calc l2Norm α β f ^ 2 = ∫⁻ x, ‖weighted α β f x‖ₑ ^ 2 := l2Norm_sq hf α β
    _ ≤ ∫⁻ x, (S.indicator (fun _ => a ^ 2) x +
          Sᶜ.indicator (fun x => b ^ 2 * ENNReal.ofReal (x ^ 2)⁻¹) x) := lintegral_mono hpt
    _ = a ^ 2 * 2 + b ^ 2 * 2 := by
      rw [lintegral_add_left (measurable_const.indicator measurableSet_Icc),
        lintegral_indicator_const measurableSet_Icc, Real.volume_Icc,
        lintegral_indicator measurableSet_Icc.compl,
        lintegral_const_mul _ (by fun_prop), lintegral_compl_Icc_inv_sq]
      norm_num
    _ = 2 * a ^ 2 + 2 * b ^ 2 := by ring

/-! ### Step 2: `L²` controls `L¹` -/

lemma lintegral_inv_one_add_sq_sq :
    ∫⁻ x : ℝ, ((1 + ‖x‖ₑ ^ 2) ^ 2)⁻¹ = ENNReal.ofReal (π / 2) := by
  rw [← integral_univ_inv_one_add_sq_sq, ofReal_integral_eq_lintegral_ofReal
    integrable_inv_one_add_sq_sq (ae_of_all _ fun _ => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add zero_le_one (sq_nonneg x), ENNReal.ofReal_one, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

lemma rpow_half_le (A B C : ℝ≥0∞) :
    (A ^ 2 + 2 * B ^ 2 + C ^ 2) ^ (1 / 2 : ℝ) ≤ A + 2 * B + C := by
  calc (A ^ 2 + 2 * B ^ 2 + C ^ 2) ^ (1 / 2 : ℝ) ≤ ((A + 2 * B + C) ^ 2) ^ (1 / 2 : ℝ) := by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        calc A ^ 2 + 2 * B ^ 2 + C ^ 2
            ≤ A ^ 2 + 2 * B ^ 2 + C ^ 2 + (2 * B ^ 2 + 4 * A * B + 2 * A * C + 4 * B * C) :=
              le_self_add
          _ = (A + 2 * B + C) ^ 2 := by ring
    _ = A + 2 * B + C := by
      rw [show (1 / 2 : ℝ) = ((2 : ℕ) : ℝ)⁻¹ by norm_num, ENNReal.pow_rpow_inv_natCast two_ne_zero]

/-- Eq. (7): Cauchy–Schwarz with the weight `1/(1+x²)`. -/
theorem l1Norm_le (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) :
    l1Norm α β f ≤ ENNReal.ofReal √(π / 2) *
      (l2Norm α β f + 2 * l2Norm (α + 1) β f + l2Norm (α + 2) β f) := by
  let w : ℕ → ℝ → ℝ≥0∞ := fun k x => ‖weighted k β f x‖ₑ
  have hw : ∀ k, Measurable (w k) := fun k => (continuous_weighted hf k β).measurable.enorm
  let ρ : ℝ → ℝ≥0∞ := fun x => 1 + ‖x‖ₑ ^ 2
  have hρ : Measurable ρ := by fun_prop
  have key : ∀ x, (ρ x * w α x) ^ 2 = w α x ^ 2 + 2 * w (α + 1) x ^ 2 + w (α + 2) x ^ 2 := by
    intro x
    simp only [w, ρ, enorm_weighted_succ]
    ring
  calc l1Norm α β f = ∫⁻ x, ((fun x => (ρ x)⁻¹) * fun x => ρ x * w α x) x := by
        rw [l1Norm_eq hf]
        congr 1
        funext x
        have h0 : ρ x ≠ 0 := by simp [ρ]
        have hT : ρ x ≠ ⊤ := by simp [ρ]
        simp only [Pi.mul_apply]
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 hT, one_mul]
    _ ≤ (∫⁻ x, (ρ x)⁻¹ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∫⁻ x, (ρ x * w α x) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
          hρ.inv.aemeasurable (hρ.mul (hw α)).aemeasurable
    _ = ENNReal.ofReal √(π / 2) *
          (l2Norm α β f ^ 2 + 2 * l2Norm (α + 1) β f ^ 2 + l2Norm (α + 2) β f ^ 2) ^
            (1 / 2 : ℝ) := by
        have hinv (a : ℝ≥0∞) (n : ℕ) : a⁻¹ ^ n = (a ^ n)⁻¹ := ENNReal.inv_pow.symm
        simp only [ENNReal.rpow_two, hinv, key, ρ]
        rw [lintegral_inv_one_add_sq_sq, lintegral_add_right _ ((hw _).pow_const 2),
          lintegral_add_left ((hw _).pow_const 2), lintegral_const_mul _ ((hw _).pow_const 2),
          l2Norm_sq hf, l2Norm_sq hf, l2Norm_sq hf, Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    _ ≤ _ := by gcongr; exact rpow_half_le _ _ _

/-! ### Step 3: `L¹` controls sup -/

lemma hasDerivAt_weighted (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) (x : ℝ) :
    HasDerivAt (weighted α β f) (α * weighted (α - 1) β f x + weighted α (β + 1) f x) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ α) (α * (x : ℂ) ^ (α - 1)) x :=
    (hasDerivAt_pow α (x : ℂ)).comp_ofReal
  have h2 : HasDerivAt (iteratedDeriv β f) (iteratedDeriv (β + 1) f x) x := by
    rw [iteratedDeriv_succ]
    exact ((hf.differentiable_iteratedDeriv β
      (by exact_mod_cast ENat.natCast_lt_top β)) x).hasDerivAt
  refine (h1.mul h2).congr_deriv ?_
  simp only [weighted]
  ring

/-- Eq. (9), `‖f‖^{sup}_{α,β} ≤ α ‖f‖^{L¹}_{α-1,β} + ‖f‖^{L¹}_{α,β+1}`. It needs
`‖f‖^{L¹}_{α,β} < ∞`, so that `g = x^α ∂^β f` tends to `0` at `-∞`: for `f = 1` and
`α = β = 0` the left side is `1` and the right side is `0`. -/
theorem supNorm_le (hf : ContDiff ℝ (⊤ : ℕ∞) f) (α β : ℕ) (h : l1Norm α β f ≠ ⊤) :
    supNorm α β f ≤ α * l1Norm (α - 1) β f + l1Norm α (β + 1) f := by
  have hbound : ∫⁻ x, ‖(α : ℂ) * weighted (α - 1) β f x + weighted α (β + 1) f x‖ₑ ≤
      α * l1Norm (α - 1) β f + l1Norm α (β + 1) f := by
    calc ∫⁻ x, ‖(α : ℂ) * weighted (α - 1) β f x + weighted α (β + 1) f x‖ₑ
        ≤ ∫⁻ x, ((α : ℝ≥0∞) * ‖weighted (α - 1) β f x‖ₑ + ‖weighted α (β + 1) f x‖ₑ) :=
          lintegral_mono fun x => (enorm_add_le _ _).trans <| by
            rw [enorm_mul, ← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
      _ = _ := by
        rw [lintegral_add_left ((continuous_weighted hf _ β).measurable.enorm.const_mul _),
          lintegral_const_mul _ (continuous_weighted hf _ β).measurable.enorm, l1Norm_eq hf,
          l1Norm_eq hf]
  rcases eq_or_ne (α * l1Norm (α - 1) β f + l1Norm α (β + 1) f) ⊤ with hR | hR
  · rw [hR]
    exact le_top
  have hint : Integrable (weighted α β f) :=
    memLp_one_iff_integrable.mp h.lt_top
  have hint' : Integrable fun x => (α : ℂ) * weighted (α - 1) β f x + weighted α (β + 1) f x :=
    ⟨((continuous_const.mul (continuous_weighted hf _ β)).add
      (continuous_weighted hf _ _)).aestronglyMeasurable, hbound.trans_lt hR.lt_top⟩
  exact iSup_le fun x =>
    (enorm_le_lintegral_enorm_deriv (hasDerivAt_weighted hf α β) hint' hint x).trans hbound

/-- Without `‖f‖^{L¹}_{α,β} < ∞`, eq. (9) fails: for `f = 1` and `α = β = 0` the left side is `1`
and the right side is `0`. -/
theorem not_supNorm_le_const :
    ¬ supNorm 0 0 (fun _ => 1) ≤ 0 * l1Norm (0 - 1) 0 (fun _ => 1) + l1Norm 0 1 (fun _ => 1) := by
  have h1 : supNorm 0 0 (fun _ : ℝ => (1 : ℂ)) = 1 := by simp [supNorm, weighted]
  have h0 : weighted 0 1 (fun _ : ℝ => (1 : ℂ)) = 0 := by
    funext x
    simp [weighted, iteratedDeriv_one]
  have h2 : l1Norm 0 1 (fun _ : ℝ => (1 : ℂ)) = 0 := by simp [l1Norm, h0]
  simp [h1, h2]

/-! ### Theorem 5: the three finiteness conditions are equivalent -/

/-- Theorem 5, first part: for smooth `f`, all sup seminorms are finite iff all `L¹` seminorms
are iff all `L²` seminorms are. -/
theorem tfae_finite (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    List.TFAE [∀ α β, supNorm α β f < ⊤, ∀ α β, l1Norm α β f < ⊤, ∀ α β, l2Norm α β f < ⊤] := by
  tfae_have 1 → 3 := fun h α β => by
    have h' := (l2Norm_sq_le hf α β).trans_lt <| ENNReal.add_lt_top.2
      ⟨ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top (h α β)),
        ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top (h (α + 1) β))⟩
    simpa using h'
  tfae_have 3 → 2 := fun h α β =>
    (l1Norm_le hf α β).trans_lt <| ENNReal.mul_lt_top ENNReal.ofReal_lt_top <|
      ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨h α β,
        ENNReal.mul_lt_top (by simp) (h (α + 1) β)⟩, h (α + 2) β⟩
  tfae_have 2 → 1 := fun h α β =>
    (supNorm_le hf α β (h α β).ne).trans_lt <|
      ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) (h (α - 1) β), h α (β + 1)⟩
  tfae_finish

/-! ### Mathlib's Schwartz space is the space (4) -/

open SchwartzMap

lemma enorm_weighted_eq (α β : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    ‖weighted α β f x‖ₑ = ENNReal.ofReal (|x| ^ α * ‖iteratedDeriv β f x‖) := by
  rw [weighted, enorm_mul, enorm_pow, enorm_ofReal, Real.enorm_eq_ofReal_abs, ← ofReal_norm,
    ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity)]

/-- On `𝓢(ℝ)`, the brief's sup seminorm (1) is Mathlib's `SchwartzMap.seminorm`. -/
theorem supNorm_eq_seminorm (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    supNorm α β F = ENNReal.ofReal (SchwartzMap.seminorm ℂ α β F) := by
  have h1 : supNorm α β F ≤ ENNReal.ofReal (SchwartzMap.seminorm ℂ α β F) :=
    iSup_le fun x => by
      rw [enorm_weighted_eq]
      exact ENNReal.ofReal_le_ofReal (le_seminorm' ℂ α β F x)
  have hfin : supNorm α β F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  refine le_antisymm h1 ?_
  rw [ENNReal.ofReal_le_iff_le_toReal hfin]
  refine seminorm_le_bound' ℂ α β F ENNReal.toReal_nonneg fun x => ?_
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin, ← enorm_weighted_eq]
  exact le_iSup (fun x => ‖weighted α β F x‖ₑ) x

/-- A smooth function is (the coercion of) a Mathlib Schwartz function iff all its sup
seminorms (1) are finite, i.e. Mathlib's `𝓢(ℝ, ℂ)` is the space (4). -/
theorem exists_schwartzMap_iff (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (∃ F : 𝓢(ℝ, ℂ), ⇑F = f) ↔ ∀ α β, supNorm α β f < ⊤ := by
  constructor
  · rintro ⟨F, rfl⟩ α β
    rw [supNorm_eq_seminorm]
    exact ENNReal.ofReal_lt_top
  · intro h
    refine ⟨⟨f, hf, fun k n => ⟨(supNorm k n f).toReal, fun x => ?_⟩⟩, rfl⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
      ← ENNReal.ofReal_le_iff_le_toReal (h k n).ne, ← enorm_weighted_eq]
    exact le_iSup (fun x => ‖weighted k n f x‖ₑ) x

lemma supNorm_lt_top (F : 𝓢(ℝ, ℂ)) (α β : ℕ) : supNorm α β F < ⊤ :=
  (exists_schwartzMap_iff (F.smooth ⊤)).mp ⟨F, rfl⟩ α β

lemma l1Norm_lt_top (F : 𝓢(ℝ, ℂ)) (α β : ℕ) : l1Norm α β F < ⊤ := by
  have h := (tfae_finite (F.smooth ⊤)).out 1 2 rfl rfl one_ne_zero two_ne_zero
  exact h.mp (supNorm_lt_top F) α β

lemma l2Norm_lt_top (F : 𝓢(ℝ, ℂ)) (α β : ℕ) : l2Norm α β F < ⊤ := by
  have h := (tfae_finite (F.smooth ⊤)).out 1 3 rfl rfl one_ne_zero three_ne_zero
  exact h.mp (supNorm_lt_top F) α β

/-! ### The `L¹` and `L²` seminorm families -/

lemma weighted_add (α β : ℕ) (F G : 𝓢(ℝ, ℂ)) :
    weighted α β ⇑(F + G) = weighted α β F + weighted α β G := by
  have hc : ⇑(F + G) = ⇑F + ⇑G := by ext x; simp
  funext x
  simp only [weighted, hc, Pi.add_apply]
  rw [iteratedDeriv_add ((F.smooth β).contDiffAt) ((G.smooth β).contDiffAt), mul_add]

lemma weighted_smul (α β : ℕ) (c : ℂ) (F : 𝓢(ℝ, ℂ)) :
    weighted α β ⇑(c • F) = c • weighted α β F := by
  have hc : ⇑(c • F) = c • ⇑F := by ext x; simp
  funext x
  simp only [weighted, hc, iteratedDeriv_const_smul_field, Pi.smul_apply, smul_eq_mul]
  ring

/-- `F ↦ ‖x^α ∂^β F‖_{Lᵖ}` as a seminorm on `𝓢(ℝ)`, for `p ≥ 1`, given that it is finite. -/
def lpSeminorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (α β : ℕ)
    (hfin : ∀ F : 𝓢(ℝ, ℂ), eLpNorm (weighted α β F) p volume ≠ ⊤) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  Seminorm.of (fun F => (eLpNorm (weighted α β F) p volume).toReal)
    (fun F G => by
      rw [weighted_add, ← ENNReal.toReal_add (hfin F) (hfin G)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin F, hfin G⟩)
        (eLpNorm_add_le Fact.out))
    (fun c F => by
      rw [weighted_smul, eLpNorm_const_smul, ENNReal.toReal_mul, ← ofReal_norm,
        ENNReal.toReal_ofReal (norm_nonneg c)])

/-- The `L¹` seminorm (2) on `𝓢(ℝ)`. -/
def l1Seminorm (α β : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  lpSeminorm 1 α β fun F => (l1Norm_lt_top F α β).ne

/-- The `L²` seminorm (3) on `𝓢(ℝ)`. -/
def l2Seminorm (α β : ℕ) : Seminorm ℂ 𝓢(ℝ, ℂ) :=
  lpSeminorm 2 α β fun F => (l2Norm_lt_top F α β).ne

/-- The family of `L¹` seminorms. -/
def l1Family : SeminormFamily ℂ 𝓢(ℝ, ℂ) (ℕ × ℕ) := fun i => l1Seminorm i.1 i.2

/-- The family of `L²` seminorms. -/
def l2Family : SeminormFamily ℂ 𝓢(ℝ, ℂ) (ℕ × ℕ) := fun i => l2Seminorm i.1 i.2

lemma l1Norm_eq_ofReal (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    l1Norm α β F = ENNReal.ofReal (l1Family (α, β) F) :=
  (ENNReal.ofReal_toReal (l1Norm_lt_top F α β).ne).symm

lemma l2Norm_eq_ofReal (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    l2Norm α β F = ENNReal.ofReal (l2Family (α, β) F) :=
  (ENNReal.ofReal_toReal (l2Norm_lt_top F α β).ne).symm

lemma supNorm_eq_ofReal (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    supNorm α β F = ENNReal.ofReal (schwartzSeminormFamily ℂ ℝ ℂ (α, β) F) :=
  supNorm_eq_seminorm F α β

lemma ofReal_le_finset_sup {ι : Type*} {p : SeminormFamily ℂ 𝓢(ℝ, ℂ) ι} {s : Finset ι} {j : ι}
    (hj : j ∈ s) (F : 𝓢(ℝ, ℂ)) :
    ENNReal.ofReal (p j F) ≤ ENNReal.ofReal ((s.sup p) F) :=
  ENNReal.ofReal_le_ofReal (Seminorm.le_finset_sup_apply hj)

/-- Step 1 as a bound between the families: sup controls `L²`. -/
theorem isBounded_sup_l2 :
    Seminorm.IsBounded (schwartzSeminormFamily ℂ ℝ ℂ) l2Family LinearMap.id := by
  refine Seminorm.IsBounded.of_real fun ⟨α, β⟩ => ⟨{(α, β), (α + 1, β)}, 2, fun F => ?_⟩
  set T := ENNReal.ofReal (({(α, β), (α + 1, β)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ ℝ ℂ) F)
  have ha : supNorm α β F ≤ T := by
    rw [supNorm_eq_ofReal]; exact ofReal_le_finset_sup (by simp) F
  have hb : supNorm (α + 1) β F ≤ T := by
    rw [supNorm_eq_ofReal]; exact ofReal_le_finset_sup (by simp) F
  have h : l2Norm α β F ≤ 2 * T := by
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
    calc l2Norm α β F ^ 2 ≤ 2 * supNorm α β F ^ 2 + 2 * supNorm (α + 1) β F ^ 2 :=
          l2Norm_sq_le (F.smooth ⊤) α β
      _ ≤ 2 * T ^ 2 + 2 * T ^ 2 := by gcongr
      _ = (2 * T) ^ 2 := by ring
  simp only [LinearMap.id_apply]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) <| by
    rwa [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

/-- Step 2 as a bound between the families: `L²` controls `L¹`. -/
theorem isBounded_l2_l1 : Seminorm.IsBounded l2Family l1Family LinearMap.id := by
  refine Seminorm.IsBounded.of_real fun ⟨α, β⟩ =>
    ⟨{(α, β), (α + 1, β), (α + 2, β)}, 4 * √(π / 2), fun F => ?_⟩
  set T := ENNReal.ofReal (({(α, β), (α + 1, β), (α + 2, β)} : Finset (ℕ × ℕ)).sup
    l2Family F)
  have hA : l2Norm α β F ≤ T := by
    rw [l2Norm_eq_ofReal]; exact ofReal_le_finset_sup (by simp) F
  have hB : l2Norm (α + 1) β F ≤ T := by
    rw [l2Norm_eq_ofReal]; exact ofReal_le_finset_sup (by simp) F
  have hC : l2Norm (α + 2) β F ≤ T := by
    rw [l2Norm_eq_ofReal]; exact ofReal_le_finset_sup (by simp) F
  have h : l1Norm α β F ≤ ENNReal.ofReal (4 * √(π / 2)) * T := by
    calc l1Norm α β F ≤ ENNReal.ofReal √(π / 2) *
          (l2Norm α β F + 2 * l2Norm (α + 1) β F + l2Norm (α + 2) β F) := l1Norm_le (F.smooth ⊤) α β
      _ ≤ ENNReal.ofReal √(π / 2) * (T + 2 * T + T) := by gcongr
      _ = ENNReal.ofReal (4 * √(π / 2)) * T := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring
  simp only [LinearMap.id_apply]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) <| by
    rwa [ENNReal.ofReal_mul (by positivity)]

/-- Step 3 as a bound between the families: `L¹` controls sup. -/
theorem isBounded_l1_sup :
    Seminorm.IsBounded l1Family (schwartzSeminormFamily ℂ ℝ ℂ) LinearMap.id := by
  refine Seminorm.IsBounded.of_real fun ⟨α, β⟩ =>
    ⟨{(α - 1, β), (α, β + 1)}, α + 1, fun F => ?_⟩
  set T := ENNReal.ofReal (({(α - 1, β), (α, β + 1)} : Finset (ℕ × ℕ)).sup l1Family F)
  have hA : l1Norm (α - 1) β F ≤ T := by
    rw [l1Norm_eq_ofReal]; exact ofReal_le_finset_sup (by simp) F
  have hB : l1Norm α (β + 1) F ≤ T := by
    rw [l1Norm_eq_ofReal]; exact ofReal_le_finset_sup (by simp) F
  have h : supNorm α β F ≤ ENNReal.ofReal (α + 1) * T := by
    calc supNorm α β F ≤ α * l1Norm (α - 1) β F + l1Norm α (β + 1) F :=
          supNorm_le (F.smooth ⊤) α β (l1Norm_lt_top F α β).ne
      _ ≤ α * T + T := by gcongr
      _ = ENNReal.ofReal (α + 1) * T := by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]
        ring
  simp only [LinearMap.id_apply]
  rw [supNorm_eq_ofReal, ← ENNReal.ofReal_mul (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

/-- Theorem 5, second part: the `L¹` and the `L²` seminorm families both generate the topology
of `𝓢(ℝ)`, which Mathlib defines by the sup seminorms. -/
theorem withSeminorms_l1_l2 : WithSeminorms l1Family ∧ WithSeminorms l2Family :=
  ((schwartz_withSeminorms ℂ ℝ ℂ).congr_of_cycle isBounded_sup_l2 isBounded_l2_l1
    isBounded_l1_sup).symm

/-! ### Remark: expectation values are controlled by the `L²` seminorms -/

/-- Eq. (10), with the factor `ħ^β` that the brief omits:
`|⟨f|X^α P^β|f⟩| ≤ |ħ|^β ‖f‖^{L²}_{0,0} ‖f‖^{L²}_{α,β}`. -/
theorem enorm_moment_le (ħ : ℝ) (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    ‖SchwartzMomentProblem.moment ħ F α β‖ₑ ≤ ‖ħ‖ₑ ^ β * (l2Norm 0 0 F * l2Norm α β F) := by
  have hF := F.smooth ⊤
  have hw : ∀ k n, Measurable fun x => ‖weighted k n F x‖ₑ :=
    fun k n => (continuous_weighted hF k n).measurable.enorm
  have hpt : ∀ x, ‖SchwartzMomentProblem.density ħ F α β x‖ₑ =
      ‖ħ‖ₑ ^ β * ((fun x => ‖weighted 0 0 F x‖ₑ) * fun x => ‖weighted α β F x‖ₑ) x := by
    intro x
    have hI : ‖Complex.I‖ₑ = 1 := by rw [← ofReal_norm, Complex.norm_I, ENNReal.ofReal_one]
    simp only [SchwartzMomentProblem.density, Pi.mul_apply, weighted, iteratedDeriv_zero,
      pow_zero, one_mul, enorm_mul, enorm_pow, RCLike.enorm_conj, enorm_neg, hI, enorm_ofReal]
    ring
  calc ‖SchwartzMomentProblem.moment ħ F α β‖ₑ
      ≤ ∫⁻ x, ‖SchwartzMomentProblem.density ħ F α β x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = ‖ħ‖ₑ ^ β * ∫⁻ x, ((fun x => ‖weighted 0 0 F x‖ₑ) * fun x => ‖weighted α β F x‖ₑ) x := by
        simp_rw [hpt]
        exact lintegral_const_mul _ ((hw 0 0).mul (hw α β))
    _ ≤ ‖ħ‖ₑ ^ β * (l2Norm 0 0 F * l2Norm α β F) := by
        gcongr
        rw [l2Norm_eq hF, l2Norm_eq hF]
        exact ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
          (hw 0 0).aemeasurable (hw α β).aemeasurable

end SchwartzNorms
