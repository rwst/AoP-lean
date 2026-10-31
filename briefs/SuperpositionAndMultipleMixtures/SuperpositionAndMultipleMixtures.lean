/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Superpositions correspond to multiple decompositions.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

A pure state `ϕ` is a superposition of `ψ₁` and `ψ₂` (QSUP-PUR) if and only if some mixed state
is both a mixture of `ψ₁` and `ψ₂` and a mixture of `ϕ` and some other state (QSUP-MIX).

Formalized here, for a complex inner product space `E` of any dimension, with pure states
`ρ_ψ = |ψ⟩⟨ψ| / ⟨ψ|ψ⟩` for nonzero `ψ`:
* `QSupPur`, `QSupMix`         the two conditions;
* `proj_add_proj_hat`          eq. (2): `|ϕ⟩⟨ϕ| + |ϕ̂⟩⟨ϕ̂| = 2|c₁|² |ψ₁⟩⟨ψ₁| + 2|c₂|² |ψ₂⟩⟨ψ₂|`;
* `QSupPur.qSupMix`            QSUP-PUR ⇒ QSUP-MIX, with the probabilities of eq. (3) and the
                               decompositions of eq. (4);
* `mem_span_of_mixture_eq`     the support argument: if a mixture with a positive weight on `ϕ`
                               is a mixture of `ψ₁` and `ψ₂`, then `ϕ ∈ span {ψ₁, ψ₂}`;
* `isMixed_mixture`            a mixture of two independent states is not pure;
* `QSupMix.qSupPur`            QSUP-MIX ⇒ QSUP-PUR;
* `qSupPur_iff_qSupMix`        Theorem 1, for `ϕ ≠ 0`.

QSUP-MIX ⇒ QSUP-PUR uses neither that `ρ` is mixed nor that the weight on the other state is
positive: the linear independence of `ψ₁` and `ψ₂` follows from `ρ_ϕ ∉ {ρ_ψ₁, ρ_ψ₂}`.
-/
public import ForMathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import ForPhyslib.QuantumMechanics.Wigner.Density

open scoped InnerProductSpace
open QuantumMechanics.Wigner Submodule

@[expose] public noncomputable section

namespace SuperpositionAndMultipleMixtures

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The pure state `ρ_ψ = |ψ⟩⟨ψ| / ⟨ψ|ψ⟩`; it is `0` at `ψ = 0`. -/
def pureState (ψ : E) : E →L[ℂ] E := (((‖ψ‖ ^ 2)⁻¹ : ℝ) : ℂ) • proj ψ

/-- A mixed state: an operator that is not a pure state. -/
def IsMixed (ρ : E →L[ℂ] E) : Prop := ∀ ψ : E, ψ ≠ 0 → ρ ≠ pureState ψ

/-- The mixture `p ρ_ψ + q ρ_χ`. -/
def mixture (p : ℝ) (ψ : E) (q : ℝ) (χ : E) : E →L[ℂ] E :=
  (p : ℂ) • pureState ψ + (q : ℂ) • pureState χ

/-- Condition QSUP-PUR: `|ϕ⟩ = c₁|ψ₁⟩ + c₂|ψ₂⟩` with `ψ₁, ψ₂` linearly independent and
`c₁, c₂ ≠ 0`. -/
def QSupPur (ϕ ψ₁ ψ₂ : E) : Prop :=
  LinearIndependent ℂ ![ψ₁, ψ₂] ∧ ∃ c₁ c₂ : ℂ, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ ϕ = c₁ • ψ₁ + c₂ • ψ₂

/-- Condition QSUP-MIX: a mixed state `ρ = p₁ ρ_ψ₁ + p₂ ρ_ψ₂ = p_ϕ ρ_ϕ + p_ϕ̂ ρ_ϕ̂` with
`ρ_ϕ ∉ {ρ_ψ₁, ρ_ψ₂}`, all weights in `(0, 1)` and `p₁ + p₂ = p_ϕ + p_ϕ̂ = 1`. -/
def QSupMix (ϕ ψ₁ ψ₂ : E) : Prop :=
  ∃ (p₁ p₂ q q' : ℝ) (ϕ' : E), ϕ' ≠ 0 ∧
    p₁ ∈ Set.Ioo 0 1 ∧ p₂ ∈ Set.Ioo 0 1 ∧ q ∈ Set.Ioo 0 1 ∧ q' ∈ Set.Ioo 0 1 ∧
    p₁ + p₂ = 1 ∧ q + q' = 1 ∧
    IsMixed (mixture p₁ ψ₁ p₂ ψ₂) ∧ mixture p₁ ψ₁ p₂ ψ₂ = mixture q ϕ q' ϕ' ∧
    pureState ϕ ≠ pureState ψ₁ ∧ pureState ϕ ≠ pureState ψ₂

/-! ### Pure states -/

lemma pureState_apply (ψ x : E) :
    pureState ψ x = ((((‖ψ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ⟪ψ, x⟫_ℂ) • ψ := by
  rw [pureState, smul_apply, proj_apply, smul_smul]

lemma pureState_apply_self {ψ : E} (hψ : ψ ≠ 0) : pureState ψ ψ = ψ := by
  have hn : (‖ψ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hψ).ne'
  have h : (((‖ψ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    field_simp
    rfl
  rw [pureState_apply, h, one_smul]

lemma pureState_smul {c : ℂ} (hc : c ≠ 0) (ψ : E) : pureState (c • ψ) = pureState ψ := by
  have : ‖c‖ ^ 2 ≠ 0 := by positivity
  rw [pureState, pureState, proj_smul, smul_smul, ← Complex.ofReal_mul, norm_smul, mul_pow,
    mul_inv, mul_right_comm, inv_mul_cancel₀ this, one_mul]

/-- Two nonzero vectors with the same pure state are proportional. -/
lemma exists_eq_smul_of_pureState_eq {ϕ ψ : E} (hϕ : ϕ ≠ 0) (h : pureState ϕ = pureState ψ) :
    ∃ a : ℂ, ϕ = a • ψ := by
  refine ⟨(((‖ψ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ⟪ψ, ϕ⟫_ℂ, ?_⟩
  rw [← pureState_apply, ← h, pureState_apply_self hϕ]

/-- `⟪x, ρ_ψ x⟫ = |⟪ψ, x⟫|² / ‖ψ‖²`. -/
lemma re_inner_pureState_apply (ψ x : E) :
    (⟪x, pureState ψ x⟫_ℂ).re = ‖⟪ψ, x⟫_ℂ‖ ^ 2 / ‖ψ‖ ^ 2 := by
  rw [pureState, smul_apply, inner_smul_right, inner_proj_apply,
    ← Complex.ofReal_mul, Complex.ofReal_re, inv_mul_eq_div]

lemma re_inner_mixture_apply (p : ℝ) (ψ : E) (q : ℝ) (χ : E) (x : E) :
    (⟪x, mixture p ψ q χ x⟫_ℂ).re =
      p * (‖⟪ψ, x⟫_ℂ‖ ^ 2 / ‖ψ‖ ^ 2) + q * (‖⟪χ, x⟫_ℂ‖ ^ 2 / ‖χ‖ ^ 2) := by
  rw [mixture, add_apply, inner_add_right, Complex.add_re,
    smul_apply, smul_apply, inner_smul_right,
    inner_smul_right, Complex.re_ofReal_mul, Complex.re_ofReal_mul, re_inner_pureState_apply,
    re_inner_pureState_apply]

/-- The support argument: if a mixture with a positive weight on `ϕ` is a mixture of `ψ₁` and
`ψ₂`, then `ϕ` lies in the span of `ψ₁` and `ψ₂`. -/
theorem mem_span_of_mixture_eq {ϕ ϕ' ψ₁ ψ₂ : E} {q q' p₁ p₂ : ℝ} (hϕ : ϕ ≠ 0) (hq : 0 < q)
    (hq' : 0 ≤ q') (h : mixture q ϕ q' ϕ' = mixture p₁ ψ₁ p₂ ψ₂) :
    ϕ ∈ span ℂ {ψ₁, ψ₂} := by
  refine mem_span_of_forall_inner_eq_zero (Set.toFinite _) fun x hx => ?_
  have h0 : (⟪x, mixture q ϕ q' ϕ' x⟫_ℂ).re = 0 := by
    rw [h, re_inner_mixture_apply, hx ψ₁ (by simp), hx ψ₂ (by simp)]
    simp
  have hϕ2 : 0 < ‖ϕ‖ ^ 2 := by positivity
  have h1 : 0 ≤ ‖⟪ϕ, x⟫_ℂ‖ ^ 2 / ‖ϕ‖ ^ 2 := by positivity
  have h2 : 0 ≤ ‖⟪ϕ', x⟫_ℂ‖ ^ 2 / ‖ϕ'‖ ^ 2 := by positivity
  rw [re_inner_mixture_apply] at h0
  have e : ‖⟪ϕ, x⟫_ℂ‖ ^ 2 / ‖ϕ‖ ^ 2 = 0 := by
    nlinarith [mul_nonneg hq' h2, mul_nonneg hq.le h1]
  simpa [hϕ2.ne'] using e

lemma pureState_eq_mixture (χ : E) : pureState χ = mixture 1 χ 0 χ := by
  simp [mixture]

/-- A mixture of two linearly independent states with positive weights is not pure. -/
theorem isMixed_mixture {ψ₁ ψ₂ : E} (hind : LinearIndependent ℂ ![ψ₁, ψ₂]) {p₁ p₂ : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) : IsMixed (mixture p₁ ψ₁ p₂ ψ₂) := by
  rw [LinearIndependent.pair_iff] at hind
  have hψ₁ : ψ₁ ≠ 0 := fun h0 => one_ne_zero (hind 1 0 (by simp [h0])).1
  have hψ₂ : ψ₂ ≠ 0 := fun h0 => one_ne_zero (hind 0 1 (by simp [h0])).2
  intro χ _ heq
  rw [pureState_eq_mixture] at heq
  have h₁ := mem_span_of_mixture_eq hψ₁ hp₁ hp₂.le heq
  have h₂ := mem_span_of_mixture_eq hψ₂ hp₂ hp₁.le
    (by rw [← heq, mixture, mixture, add_comm])
  rw [Set.pair_eq_singleton, mem_span_singleton] at h₁ h₂
  obtain ⟨a, rfl⟩ := h₁
  obtain ⟨b, rfl⟩ := h₂
  have := hind b (-a) (by rw [smul_smul, smul_smul, neg_mul, neg_smul, mul_comm, add_neg_cancel])
  exact hψ₂ (by rw [this.1, zero_smul])

/-! ### QSUP-PUR implies QSUP-MIX -/

/-- `|ϕ̂⟩ = c₁|ψ₁⟩ - c₂|ψ₂⟩`. -/
abbrev hat (c₁ c₂ : ℂ) (ψ₁ ψ₂ : E) : E := c₁ • ψ₁ - c₂ • ψ₂

/-- Eq. (2): `|ϕ⟩⟨ϕ| + |ϕ̂⟩⟨ϕ̂| = 2|c₁|² |ψ₁⟩⟨ψ₁| + 2|c₂|² |ψ₂⟩⟨ψ₂|`. -/
theorem proj_add_proj_hat (c₁ c₂ : ℂ) (ψ₁ ψ₂ : E) :
    proj (c₁ • ψ₁ + c₂ • ψ₂) + proj (hat c₁ c₂ ψ₁ ψ₂) =
      ((2 * ‖c₁‖ ^ 2 : ℝ) : ℂ) • proj ψ₁ + ((2 * ‖c₂‖ ^ 2 : ℝ) : ℂ) • proj ψ₂ := by
  rw [hat, proj_add_add_proj_sub, proj_smul, proj_smul, smul_smul, smul_smul]
  push_cast
  rfl

/-- QSUP-PUR implies QSUP-MIX, with the weights of eq. (3) and the decompositions of eq. (4). -/
theorem QSupPur.qSupMix {ϕ ψ₁ ψ₂ : E} (h : QSupPur ϕ ψ₁ ψ₂) : QSupMix ϕ ψ₁ ψ₂ := by
  obtain ⟨hind₀, c₁, c₂, hc₁, hc₂, rfl⟩ := h
  have hind := LinearIndependent.pair_iff.mp hind₀
  have hψ₁ : ψ₁ ≠ 0 := fun h0 => one_ne_zero (hind 1 0 (by simp [h0])).1
  have hψ₂ : ψ₂ ≠ 0 := fun h0 => one_ne_zero (hind 0 1 (by simp [h0])).2
  have hϕ : c₁ • ψ₁ + c₂ • ψ₂ ≠ 0 := fun h0 => hc₁ (hind c₁ c₂ h0).1
  have hϕ' : hat c₁ c₂ ψ₁ ψ₂ ≠ 0 := fun h0 =>
    hc₁ (hind c₁ (-c₂) (by rw [neg_smul, ← sub_eq_add_neg]; exact h0)).1
  set ϕ := c₁ • ψ₁ + c₂ • ψ₂
  set ϕ' := hat c₁ c₂ ψ₁ ψ₂
  set N := ‖ϕ‖ ^ 2 + ‖ϕ'‖ ^ 2
  have hN : N = 2 * ‖c₁‖ ^ 2 * ‖ψ₁‖ ^ 2 + 2 * ‖c₂‖ ^ 2 * ‖ψ₂‖ ^ 2 := by
    have := parallelogram_law_with_norm ℂ (c₁ • ψ₁) (c₂ • ψ₂)
    simp only [N, ϕ, ϕ', hat, norm_smul] at this ⊢
    nlinarith [this]
  have hn : 0 < ‖ϕ‖ ^ 2 := by positivity
  have hn' : 0 < ‖ϕ'‖ ^ 2 := by positivity
  have hn₁ : 0 < 2 * ‖c₁‖ ^ 2 * ‖ψ₁‖ ^ 2 := by positivity
  have hn₂ : 0 < 2 * ‖c₂‖ ^ 2 * ‖ψ₂‖ ^ 2 := by positivity
  have hN0 : 0 < N := by positivity
  -- the mixture `ρ = (|ϕ⟩⟨ϕ| + |ϕ̂⟩⟨ϕ̂|) / N` and its two decompositions, eq. (4)
  have hϕc : (‖ϕ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hϕ).ne'
  have hϕ'c : (‖ϕ'‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hϕ').ne'
  have hψ₁c : (‖ψ₁‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hψ₁).ne'
  have hψ₂c : (‖ψ₂‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.mpr hψ₂).ne'
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hρϕ : mixture (‖ϕ‖ ^ 2 / N) ϕ (‖ϕ'‖ ^ 2 / N) ϕ' =
      ((N⁻¹ : ℝ) : ℂ) • (proj ϕ + proj ϕ') := by
    rw [mixture, pureState, pureState, smul_smul, smul_smul, smul_add]
    congr 2 <;> push_cast <;> field_simp
  have hρψ : mixture (2 * ‖c₁‖ ^ 2 * ‖ψ₁‖ ^ 2 / N) ψ₁ (2 * ‖c₂‖ ^ 2 * ‖ψ₂‖ ^ 2 / N) ψ₂ =
      ((N⁻¹ : ℝ) : ℂ) • (proj ϕ + proj ϕ') := by
    rw [proj_add_proj_hat, mixture, pureState, pureState, smul_smul, smul_smul, smul_add,
      smul_smul, smul_smul]
    congr 2 <;> push_cast <;> field_simp
  have hmem₁ : pureState ϕ ≠ pureState ψ₁ := fun heq => by
    obtain ⟨a, ha⟩ := exists_eq_smul_of_pureState_eq hϕ heq
    exact hc₂ (hind (c₁ - a) c₂ (by rw [sub_smul, ← ha, sub_add_eq_add_sub, sub_eq_zero])).2
  have hmem₂ : pureState ϕ ≠ pureState ψ₂ := fun heq => by
    obtain ⟨a, ha⟩ := exists_eq_smul_of_pureState_eq hϕ heq
    exact hc₁ (hind c₁ (c₂ - a) (by rw [sub_smul, ← ha, ← add_sub_assoc, sub_eq_zero])).1
  refine ⟨2 * ‖c₁‖ ^ 2 * ‖ψ₁‖ ^ 2 / N, 2 * ‖c₂‖ ^ 2 * ‖ψ₂‖ ^ 2 / N, ‖ϕ‖ ^ 2 / N,
    ‖ϕ'‖ ^ 2 / N, ϕ', hϕ', ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩,
    ⟨by positivity, ?_⟩, ?_, ?_, ?_, by rw [hρψ, hρϕ], hmem₁, hmem₂⟩
  · rw [div_lt_one hN0]; linarith
  · rw [div_lt_one hN0]; linarith
  · rw [div_lt_one hN0]; linarith
  · rw [div_lt_one hN0]; linarith
  · rw [← add_div, ← hN, div_self hN0.ne']
  · rw [← add_div, div_self hN0.ne']
  · exact isMixed_mixture hind₀ (by positivity) (by positivity)

/-! ### QSUP-MIX implies QSUP-PUR -/

/-- QSUP-MIX implies QSUP-PUR. -/
theorem QSupMix.qSupPur {ϕ ψ₁ ψ₂ : E} (hϕ : ϕ ≠ 0) (h : QSupMix ϕ ψ₁ ψ₂) : QSupPur ϕ ψ₁ ψ₂ := by
  obtain ⟨p₁, p₂, q, q', ϕ', -, -, -, hq, hq', -, -, -, heq, h₁, h₂⟩ := h
  obtain ⟨c₁, c₂, hc⟩ := mem_span_pair.mp (mem_span_of_mixture_eq hϕ hq.1 hq'.1.le heq.symm)
  have hc₁ : c₁ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_add] at hc
    have : c₂ ≠ 0 := by rintro rfl; simp [← hc] at hϕ
    exact h₂ (by rw [← hc, pureState_smul this])
  have hc₂ : c₂ ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hc
    exact h₁ (by rw [← hc, pureState_smul hc₁])
  refine ⟨LinearIndependent.pair_iff.mpr fun s t hst => ?_, c₁, c₂, hc₁, hc₂, hc.symm⟩
  -- if `s ψ₁ + t ψ₂ = 0` nontrivially, then `ψ₂` and so `ϕ` lie on the line of `ψ₁`
  by_contra hne
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    rcases hst with hs | h0
    · exact hne ⟨hs, rfl⟩
    · rw [h0, smul_zero, zero_add] at hc
      exact h₂ (by rw [← hc, pureState_smul hc₂])
  have hψ : ψ₂ = (-(s / t)) • ψ₁ := by
    have e : t * -(s / t) = -s := by field_simp
    refine smul_right_injective E ht ?_
    simp only
    rw [smul_smul, e, neg_smul, eq_neg_iff_add_eq_zero, add_comm, hst]
  have hϕ₁ : ϕ = (c₁ + c₂ * -(s / t)) • ψ₁ := by
    rw [← hc, hψ, smul_smul, add_smul]
  have hne0 : c₁ + c₂ * -(s / t) ≠ 0 := by
    rintro h0
    rw [h0, zero_smul] at hϕ₁
    exact hϕ hϕ₁
  exact h₁ (by rw [hϕ₁, pureState_smul hne0])

/-- **Theorem 1.** QSUP-PUR and QSUP-MIX are equivalent. -/
theorem qSupPur_iff_qSupMix {ϕ ψ₁ ψ₂ : E} (hϕ : ϕ ≠ 0) :
    QSupPur ϕ ψ₁ ψ₂ ↔ QSupMix ϕ ψ₁ ψ₂ :=
  ⟨QSupPur.qSupMix, QSupMix.qSupPur hϕ⟩

end SuperpositionAndMultipleMixtures
