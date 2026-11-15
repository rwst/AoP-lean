/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import SchwartzNorms

/-!
# General `Lᵖ` seminorms

The Remark "General `Lᵖ`" of the brief: "the same arguments extend to `Lᵖ` seminorms for any
`1 ≤ p ≤ ∞`", so that every family `‖x^α ∂^β f‖_{Lᵖ}` generates the topology of `𝓢(ℝ)`.

The steps of the brief go through `L²` and the weight `1/(1 + x²)`. For general `p` the weight is
`(1 + |x|)^{-k}` with `k` large enough that it lies in `Lᵖ` (Mathlib's
`Measure.HasTemperateGrowth.exists_eLpNorm_lt_top`), and Cauchy–Schwarz becomes Hölder:

* `eLpNorm_weighted_le`  sup controls `Lᵖ`:
  `‖x^α ∂^β f‖_{Lᵖ} ≤ 2^k ‖(1 + |x|)^{-k}‖_{Lᵖ} (‖f‖^{sup}_{α,β} + ‖f‖^{sup}_{α+k,β})`;
* `eLpNorm_weighted_one_le`  `Lᵖ` controls `L¹`, by Hölder with the conjugate exponent;
* `withSeminorms_lp`  for every `1 ≤ p ≤ ∞` the family `lpFamily p` generates the topology of
  `𝓢(ℝ)`. Step 3 of the brief, `L¹` controls sup (`isBounded_l1_sup`), closes the cycle.

`lpFamily_one`, `lpFamily_two` and `lpFamily_top` identify the cases `p = 1, 2, ∞` with the
families (2), (3) and (1) of the brief.
-/

open Real MeasureTheory SchwartzMap
open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace SchwartzNorms

lemma one_add_pow_le {t : ℝ} (ht : 0 ≤ t) (k : ℕ) : (1 + t) ^ k ≤ 2 ^ k * (1 + t ^ k) := by
  rcases le_total t 1 with h | h
  · calc (1 + t) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + t ^ k) :=
        le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ht k])
  · calc (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * t ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + t ^ k) := by gcongr; linarith

lemma norm_weighted (α β : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    ‖weighted α β f x‖ = |x| ^ α * ‖iteratedDeriv β f x‖ := by
  simp [weighted, norm_pow]

/-- `(1 + |x|)^k |x^α f⁽ᵝ⁾(x)| ≤ 2^k (|x^α f⁽ᵝ⁾(x)| + |x^{α+k} f⁽ᵝ⁾(x)|)`. -/
lemma one_add_pow_mul_norm_weighted_le (k α β : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (1 + ‖x‖) ^ k * ‖weighted α β f x‖ ≤
      2 ^ k * (‖weighted α β f x‖ + ‖weighted (α + k) β f x‖) := by
  have h : ‖weighted (α + k) β f x‖ = |x| ^ k * ‖weighted α β f x‖ := by
    rw [norm_weighted, norm_weighted, pow_add]; ring
  rw [h, Real.norm_eq_abs]
  calc (1 + |x|) ^ k * ‖weighted α β f x‖ ≤ 2 ^ k * (1 + |x| ^ k) * ‖weighted α β f x‖ := by
        gcongr; exact one_add_pow_le (abs_nonneg x) k
    _ = _ := by ring

/-- The weight `(1 + |x|)^{-k}`. -/
def weight (k : ℕ) (x : ℝ) : ℝ := (1 + ‖x‖) ^ (-k : ℝ)

lemma weight_pos (k : ℕ) (x : ℝ) : 0 < weight k x := by unfold weight; positivity

lemma weight_mul (k : ℕ) (x : ℝ) : weight k x * (1 + ‖x‖) ^ k = 1 := by
  rw [weight, Real.rpow_neg (by positivity), Real.rpow_natCast, inv_mul_cancel₀ (by positivity)]

lemma continuous_weight (k : ℕ) : Continuous (weight k) :=
  Continuous.rpow_const (by fun_prop) fun x => Or.inl (by positivity)

/-- For every `p` some weight `(1 + |x|)^{-k}` lies in `Lᵖ`. -/
lemma exists_eLpNorm_weight_lt_top (p : ℝ≥0∞) : ∃ k : ℕ, eLpNorm (weight k) p volume < ⊤ :=
  (inferInstance : (volume : Measure ℝ).HasTemperateGrowth).exists_eLpNorm_lt_top p

/-! ### Sup controls `Lᵖ` -/

/-- Sup controls `Lᵖ`: `‖x^α ∂^β F‖_{Lᵖ} ≤ 2^k ‖(1 + |x|)^{-k}‖_{Lᵖ}
(‖F‖^{sup}_{α,β} + ‖F‖^{sup}_{α+k,β})`. -/
theorem eLpNorm_weighted_le (p : ℝ≥0∞) (k α β : ℕ) (F : 𝓢(ℝ, ℂ)) :
    eLpNorm (weighted α β F) p volume ≤
      ENNReal.ofReal (2 ^ k * (SchwartzMap.seminorm ℂ α β F +
        SchwartzMap.seminorm ℂ (α + k) β F)) * eLpNorm (weight k) p volume := by
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    (continuous_weighted (F.smooth ⊤) α β).aestronglyMeasurable (ae_of_all _ fun x => ?_) p
  have h1 := one_add_pow_mul_norm_weighted_le k α β F x
  have hS : ‖weighted α β F x‖ + ‖weighted (α + k) β F x‖ ≤
      SchwartzMap.seminorm ℂ α β F + SchwartzMap.seminorm ℂ (α + k) β F := by
    rw [norm_weighted, norm_weighted]
    exact add_le_add (le_seminorm' ℂ _ _ F x) (le_seminorm' ℂ _ _ F x)
  have hw := weight_mul k x
  rw [Real.norm_of_nonneg (weight_pos k x).le]
  calc ‖weighted α β F x‖ = weight k x * ((1 + ‖x‖) ^ k * ‖weighted α β F x‖) := by
        rw [← mul_assoc, hw, one_mul]
    _ ≤ weight k x * (2 ^ k * (SchwartzMap.seminorm ℂ α β F +
          SchwartzMap.seminorm ℂ (α + k) β F)) := by
        exact mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hS (by positivity)))
          (weight_pos k x).le
    _ = _ := by ring

/-- The `Lᵖ` seminorms of a Schwartz function are finite. -/
theorem eLpNorm_weighted_lt_top (p : ℝ≥0∞) (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    eLpNorm (weighted α β F) p volume < ⊤ := by
  obtain ⟨k, hk⟩ := exists_eLpNorm_weight_lt_top p
  exact (eLpNorm_weighted_le p k α β F).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk)

/-- The family of `Lᵖ` seminorms `‖x^α ∂^β f‖_{Lᵖ}`, for `1 ≤ p ≤ ∞`. -/
def lpFamily (p : ℝ≥0∞) [Fact (1 ≤ p)] : SeminormFamily ℂ 𝓢(ℝ, ℂ) (ℕ × ℕ) := fun i =>
  lpSeminorm p i.1 i.2 fun F => (eLpNorm_weighted_lt_top p F i.1 i.2).ne

lemma lpFamily_one : lpFamily 1 = l1Family := rfl

lemma lpFamily_two : lpFamily 2 = l2Family := rfl

/-- For `p = ∞` the essential supremum of the continuous `x^α ∂^β F` is its supremum. -/
lemma eLpNorm_top_weighted (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    eLpNorm (weighted α β F) ⊤ volume = supNorm α β F := by
  rw [eLpNorm_exponent_top]
  refine le_antisymm (eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x =>
    le_iSup (fun y => ‖weighted α β F y‖ₑ) x)) (iSup_le fun x => ?_)
  by_contra! hx
  have hc : Continuous fun y => ‖weighted α β F y‖ₑ :=
    (continuous_weighted (F.smooth ⊤) α β).enorm
  have hU : IsOpen {y | eLpNormEssSup (weighted α β F) volume < ‖weighted α β F y‖ₑ} :=
    isOpen_lt continuous_const hc
  have h0 := (hU.measure_pos volume ⟨x, hx⟩).ne'
  refine h0 (measure_mono_null (fun y hy => ?_) (ae_iff.1 (enorm_ae_le_eLpNormEssSup
    (weighted α β F) volume)))
  exact not_le.2 hy
  exact (continuous_weighted (F.smooth ⊤) α β).aestronglyMeasurable

/-- For `p = ∞` the family is the family of sup seminorms (1), which defines the topology of
`𝓢(ℝ)` in Mathlib. -/
lemma lpFamily_top : lpFamily ⊤ = schwartzSeminormFamily ℂ ℝ ℂ := by
  funext i
  ext F
  change (eLpNorm (weighted i.1 i.2 F) ⊤ volume).toReal = SchwartzMap.seminorm ℂ i.1 i.2 F
  rw [eLpNorm_top_weighted, supNorm_eq_seminorm, ENNReal.toReal_ofReal (apply_nonneg _ _)]

lemma eLpNorm_weighted_eq_ofReal (p : ℝ≥0∞) [Fact (1 ≤ p)] (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    eLpNorm (weighted α β F) p volume = ENNReal.ofReal (lpFamily p (α, β) F) :=
  (ENNReal.ofReal_toReal (eLpNorm_weighted_lt_top p F α β).ne).symm

/-- Sup controls `Lᵖ`, as a bound between the families. -/
theorem isBounded_sup_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Seminorm.IsBounded (schwartzSeminormFamily ℂ ℝ ℂ) (lpFamily p) LinearMap.id := by
  obtain ⟨k, hk⟩ := exists_eLpNorm_weight_lt_top p
  set W := (eLpNorm (weight k) p volume).toReal
  refine Seminorm.IsBounded.of_real fun ⟨α, β⟩ =>
    ⟨{(α, β), (α + k, β)}, 2 ^ k * W * 2, fun F => ?_⟩
  set T := ({(α, β), (α + k, β)} : Finset (ℕ × ℕ)).sup (schwartzSeminormFamily ℂ ℝ ℂ) F
  have ha : SchwartzMap.seminorm ℂ α β F ≤ T :=
    Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ) (i := (α, β)) (by simp)
  have hb : SchwartzMap.seminorm ℂ (α + k) β F ≤ T :=
    Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ) (i := (α + k, β)) (by simp)
  have h := eLpNorm_weighted_le p k α β F
  rw [← ENNReal.ofReal_toReal hk.ne, ← ENNReal.ofReal_mul (by positivity)] at h
  calc lpFamily p (α, β) F
      ≤ 2 ^ k * (SchwartzMap.seminorm ℂ α β F + SchwartzMap.seminorm ℂ (α + k) β F) * W :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) h
    _ ≤ 2 ^ k * (T + T) * W := by gcongr
    _ = 2 ^ k * W * 2 * T := by ring

/-! ### `Lᵖ` controls `L¹` -/

/-- `Lᵖ` controls `L¹`, by Hölder: `‖x^α ∂^β F‖_{L¹} ≤
2^k ‖(1 + |x|)^{-k}‖_{L^q} (‖x^α ∂^β F‖_{Lᵖ} + ‖x^{α+k} ∂^β F‖_{Lᵖ})` for `1/p + 1/q = 1`. -/
theorem eLpNorm_weighted_one_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [ENNReal.HolderConjugate q p]
    (k α β : ℕ) (F : 𝓢(ℝ, ℂ)) :
    eLpNorm (weighted α β F) 1 volume ≤ eLpNorm (weight k) q volume *
      (2 ^ k * (eLpNorm (weighted α β F) p volume +
        eLpNorm (weighted (α + k) β F) p volume)) := by
  have hc := fun a => continuous_weighted (F.smooth ⊤) a β
  set h : ℝ → ℂ := fun x => (1 + ‖x‖) ^ k • weighted α β F x
  have hsplit : weighted α β F = weight k • h := by
    funext x
    change weighted α β F x = weight k x • ((1 + ‖x‖) ^ k • weighted α β F x)
    rw [smul_smul, weight_mul, one_smul]
  have hh : eLpNorm h p volume ≤
      2 ^ k * (eLpNorm (weighted α β F) p volume + eLpNorm (weighted (α + k) β F) p volume) := by
    calc eLpNorm h p volume
        ≤ ENNReal.ofReal (2 ^ k) *
          eLpNorm (fun x => ‖weighted α β F x‖ + ‖weighted (α + k) β F x‖) p volume := by
          refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (by fun_prop) (ae_of_all _ fun x => ?_) p
          change ‖(1 + ‖x‖) ^ k • weighted α β F x‖ ≤ 2 ^ k * ‖‖weighted α β F x‖ +
            ‖weighted (α + k) β F x‖‖
          rw [norm_smul, norm_pow, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖x‖),
            Real.norm_of_nonneg (by positivity :
              (0 : ℝ) ≤ ‖weighted α β F x‖ + ‖weighted (α + k) β F x‖)]
          exact one_add_pow_mul_norm_weighted_le k α β F x
      _ ≤ ENNReal.ofReal (2 ^ k) * (eLpNorm (fun x => ‖weighted α β F x‖) p volume +
          eLpNorm (fun x => ‖weighted (α + k) β F x‖) p volume) := by
          gcongr
          exact eLpNorm_add_le Fact.out
      _ = _ := by
          rw [eLpNorm_norm _ (hc α).aestronglyMeasurable,
            eLpNorm_norm _ (hc (α + k)).aestronglyMeasurable, ENNReal.ofReal_pow zero_le_two,
            ENNReal.ofReal_ofNat]
  calc eLpNorm (weighted α β F) 1 volume = eLpNorm (weight k • h) 1 volume := by rw [hsplit]
    _ ≤ eLpNorm (weight k) q volume * eLpNorm h p volume :=
        eLpNorm_smul_le_mul_eLpNorm (continuous_weight k).aestronglyMeasurable (by fun_prop)
    _ ≤ _ := by gcongr

/-- The conjugate exponent `q` of `p ≥ 1`, `1/p + 1/q = 1`. -/
lemma holderConjugate_conj (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] :
    ENNReal.HolderConjugate (1 - p⁻¹)⁻¹ p := by
  rw [ENNReal.holderConjugate_iff, inv_inv]
  exact tsub_add_cancel_of_le (ENNReal.inv_le_one.2 hp.out)

/-- `Lᵖ` controls `L¹`, as a bound between the families. -/
theorem isBounded_lp_l1 (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Seminorm.IsBounded (lpFamily p) l1Family LinearMap.id := by
  have := holderConjugate_conj p
  obtain ⟨k, hk⟩ := exists_eLpNorm_weight_lt_top (1 - p⁻¹)⁻¹
  set W := (eLpNorm (weight k) (1 - p⁻¹)⁻¹ volume).toReal
  refine Seminorm.IsBounded.of_real fun ⟨α, β⟩ =>
    ⟨{(α, β), (α + k, β)}, W * 2 ^ k * 2, fun F => ?_⟩
  set T := ({(α, β), (α + k, β)} : Finset (ℕ × ℕ)).sup (lpFamily p) F
  have ha : lpFamily p (α, β) F ≤ T := Seminorm.le_finset_sup_apply (by simp)
  have hb : lpFamily p (α + k, β) F ≤ T := Seminorm.le_finset_sup_apply (by simp)
  have h := eLpNorm_weighted_one_le (p := p) (q := (1 - p⁻¹)⁻¹) k α β F
  rw [eLpNorm_weighted_eq_ofReal p, eLpNorm_weighted_eq_ofReal p, ← ENNReal.ofReal_toReal hk.ne,
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow zero_le_two,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at h
  simp only [LinearMap.id_apply]
  calc l1Family (α, β) F
      ≤ W * (2 ^ k * (lpFamily p (α, β) F + lpFamily p (α + k, β) F)) :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) h
    _ ≤ W * (2 ^ k * (T + T)) := by gcongr
    _ = W * 2 ^ k * 2 * T := by ring

/-- The Remark "General `Lᵖ`": for every `1 ≤ p ≤ ∞` the `Lᵖ` seminorms `‖x^α ∂^β f‖_{Lᵖ}`
generate the topology of `𝓢(ℝ)`. -/
theorem withSeminorms_lp (p : ℝ≥0∞) [Fact (1 ≤ p)] : WithSeminorms (lpFamily p) :=
  ((schwartz_withSeminorms ℂ ℝ ℂ).congr_of_cycle (isBounded_sup_lp p) (isBounded_lp_l1 p)
    isBounded_l1_sup).1

end SchwartzNorms
