/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import SuperpositionAndMultipleMixtures

/-!
# Further results: superpositions of more than two states

Not part of the brief. This file formalizes Sec. 1 of `further-results.tex` in the brief's
directory: Theorem 1 of the brief for a superposition `ϕ = ∑ᵢ cᵢ ψᵢ` of `n` states.

Pure states are `ρ_ψ = |ψ⟩⟨ψ| / ⟨ψ|ψ⟩` as in the brief's main file, in a complex inner product
space of any dimension. `ϕ` is a *component* of an operator `ρ` (`IsComponent`) if `ρ` is a finite
mixture of pure states, with probabilities, in which `ρ_ϕ` has positive weight. The conditions are:

* `QSupPurN ϕ ψ`: `ϕ = ∑ᵢ cᵢ ψᵢ` with `ψ₁, …, ψₙ` linearly independent and all `cᵢ ≠ 0`;
* `QSupMixN ϕ ψ`: `ϕ` is a component of some mixture `∑ᵢ pᵢ ρ_ψᵢ` with all `pᵢ > 0`, and of no
  mixture of the `ψⱼ` that leaves one of them out.

For `n = 2` the conditions are the brief's (`qSupPurN_pair_iff`, `qSupMixN_pair_iff`). As in the
brief, QSUP-MIX gives the linear independence of the `ψᵢ`: a linear relation would let `ϕ` be
written without one of them.

The construction generalizes `ϕ̂ = c₁ ψ₁ - c₂ ψ₂`: over all sign vectors `ε ∈ {±1}ⁿ`, the
vectors `ϕ_ε = ∑ᵢ εᵢ cᵢ ψᵢ` satisfy `∑_ε |ϕ_ε⟩⟨ϕ_ε| = 2ⁿ ∑ᵢ |cᵢ|² |ψᵢ⟩⟨ψᵢ|`, the analogue of
eq. (2), because the cross terms cancel.

The comparator lane, which certifies the main file of the brief, does not depend on this module.

## Main results

* `mem_span_of_isComponent`: the support argument; a component of `∑ᵢ pᵢ ρ_ψᵢ` lies in the span of
  the `ψᵢ` with `pᵢ ≠ 0`;
* `sum_proj_signSum`, `sum_norm_sq_signSum`: eq. (2) for `n` states, and its trace;
* `isComponent_weights`: eqs. (3), (4) for `n` states, with `pᵢ = ‖cᵢ ψᵢ‖² / ∑ⱼ ‖cⱼ ψⱼ‖²`;
* `QSupMixN.qSupPurN`, `QSupPurN.qSupMixN`, `qSupPurN_iff_qSupMixN`: Theorem 1 for `n` states;
* `qSupPurN_pair_iff`, `qSupMixN_pair_iff`: for `n = 2`, the brief's conditions.
-/

open scoped InnerProductSpace
open InnerProductSpace QuantumMechanics.Wigner Submodule Finset

@[expose] public noncomputable section

namespace SuperpositionAndMultipleMixtures.FurtherResults

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section Many

variable {κ : Type*} [Fintype κ]

/-- The mixture `∑ₖ pₖ ρ_χₖ`. -/
def mixtureOf (p : κ → ℝ) (χ : κ → E) : E →L[ℂ] E := ∑ k, (p k : ℂ) • pureState (χ k)

lemma re_inner_mixtureOf_apply (p : κ → ℝ) (χ : κ → E) (x : E) :
    (⟪x, mixtureOf p χ x⟫_ℂ).re = ∑ k, p k * (‖⟪χ k, x⟫_ℂ‖ ^ 2 / ‖χ k‖ ^ 2) := by
  simp only [mixtureOf, _root_.sum_apply, smul_apply, inner_sum,
    inner_smul_right, Complex.re_sum, Complex.re_ofReal_mul, re_inner_pureState_apply]

/-- `ϕ` is a component of `ρ`: `ρ` is a finite mixture of pure states, with probabilities, in
which `ϕ` has positive weight. -/
def IsComponent (ϕ : E) (ρ : E →L[ℂ] E) : Prop :=
  ∃ (μ : Type) (_ : Fintype μ) (r : μ → ℝ) (χ : μ → E) (k : μ), (∀ j, 0 ≤ r j) ∧
    ∑ j, r j = 1 ∧ ρ = mixtureOf r χ ∧ χ k = ϕ ∧ 0 < r k

/-- The support argument for `n` states: if `ϕ` is a component of `∑ᵢ pᵢ ρ_ψᵢ`, then `ϕ` lies in the
span of the `ψᵢ` with `pᵢ ≠ 0`. -/
theorem mem_span_of_isComponent {ϕ : E} (hϕ : ϕ ≠ 0) {p : κ → ℝ} {ψ : κ → E}
    (h : IsComponent ϕ (mixtureOf p ψ)) : ϕ ∈ span ℂ (ψ '' {i | p i ≠ 0}) := by
  obtain ⟨μ, _, r, χ, k, hr, -, heq, rfl, hk⟩ := h
  refine mem_span_of_forall_inner_eq_zero ((Set.toFinite _).image _) fun x hx => ?_
  have h0 : (⟪x, mixtureOf p ψ x⟫_ℂ).re = 0 := by
    rw [re_inner_mixtureOf_apply]
    refine sum_eq_zero fun i _ => ?_
    by_cases hi : p i = 0
    · simp [hi]
    · simp [hx _ ⟨i, hi, rfl⟩]
  rw [heq, re_inner_mixtureOf_apply] at h0
  have hle : r k * (‖⟪χ k, x⟫_ℂ‖ ^ 2 / ‖χ k‖ ^ 2) ≤ 0 :=
    h0 ▸ single_le_sum (f := fun j => r j * (‖⟪χ j, x⟫_ℂ‖ ^ 2 / ‖χ j‖ ^ 2))
      (fun j _ => mul_nonneg (hr j) (by positivity)) (mem_univ k)
  have hn : 0 < ‖χ k‖ ^ 2 := by positivity
  have : ‖⟪χ k, x⟫_ℂ‖ ^ 2 / ‖χ k‖ ^ 2 = 0 :=
    le_antisymm ((mul_nonpos_iff_pos_imp_nonpos.mp hle).1 hk) (by positivity)
  simpa [hn.ne'] using this

/-! ### Sign vectors -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sign `εᵢ ∈ {±1}` as a complex number. -/
abbrev sgn (ε : ι → ℤˣ) (i : ι) : ℂ := ((ε i : ℤ) : ℂ)

/-- `∑_ε εᵢ εⱼ = 2ⁿ δᵢⱼ` over the sign vectors `ε : ι → {±1}`. -/
lemma sum_sgn_mul_sgn (i j : ι) :
    ∑ ε : ι → ℤˣ, sgn ε i * sgn ε j = if i = j then (2 ^ Fintype.card ι : ℂ) else 0 := by
  split_ifs with hij
  · subst hij
    simp [sgn, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  · -- flipping the sign at `j` negates every term
    let e : (ι → ℤˣ) ≃ (ι → ℤˣ) :=
      ⟨fun ε => Function.update ε j (-ε j), fun ε => Function.update ε j (-ε j),
        fun ε => by simp, fun ε => by simp⟩
    have h := e.sum_comp (fun ε => sgn ε i * sgn ε j)
    simp only [e, Equiv.coe_fn_mk, sgn, Function.update_of_ne hij, Function.update_self,
      Units.val_neg, Int.cast_neg, mul_neg, sum_neg_distrib] at h
    linear_combination (-1 / 2 : ℂ) * h

/-- Sign sums kill the cross terms: `∑_ε ∑ᵢⱼ εᵢ εⱼ Tᵢⱼ = 2ⁿ ∑ᵢ Tᵢᵢ`. -/
lemma sum_sgn_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (T : ι → ι → M) :
    ∑ ε : ι → ℤˣ, ∑ i, ∑ j, (sgn ε i * sgn ε j) • T i j =
      (2 ^ Fintype.card ι : ℂ) • ∑ i, T i i := by
  calc _ = ∑ i, ∑ j, (∑ ε : ι → ℤˣ, sgn ε i * sgn ε j) • T i j := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_comm]
        simp_rw [sum_smul]
    _ = _ := by
        simp_rw [sum_sgn_mul_sgn, ite_smul, zero_smul, sum_ite_eq, mem_univ, ite_true, smul_sum]

/-- `ϕ_ε = ∑ᵢ εᵢ aᵢ`. -/
def signSum (a : ι → E) (ε : ι → ℤˣ) : E := ∑ i, sgn ε i • a i

omit [DecidableEq ι] in
lemma signSum_one (a : ι → E) : signSum a 1 = ∑ i, a i := by simp [signSum, sgn]

/-- **Eq. (2) for `n` states:** `∑_ε |ϕ_ε⟩⟨ϕ_ε| = 2ⁿ ∑ᵢ |aᵢ⟩⟨aᵢ|`. -/
theorem sum_proj_signSum (a : ι → E) :
    ∑ ε, proj (signSum a ε) = (2 ^ Fintype.card ι : ℂ) • ∑ i, proj (a i) := by
  ext x
  have h (ε : ι → ℤˣ) : proj (signSum a ε) x =
      ∑ i, ∑ j, (sgn ε i * sgn ε j) • (⟪a i, x⟫_ℂ • a j) := by
    rw [proj_apply, signSum, sum_inner, sum_smul]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, sgn, map_intCast]
    module
  simp only [_root_.sum_apply, smul_apply, h, sum_sgn_smul, proj_apply]

/-- `∑_ε ‖ϕ_ε‖² = 2ⁿ ∑ᵢ ‖aᵢ‖²`. -/
lemma sum_norm_sq_signSum (a : ι → E) :
    ∑ ε, ‖signSum a ε‖ ^ 2 = (2 ^ Fintype.card ι : ℝ) * ∑ i, ‖a i‖ ^ 2 := by
  have h (ε : ι → ℤˣ) : ⟪signSum a ε, signSum a ε⟫_ℂ =
      ∑ i, ∑ j, (sgn ε i * sgn ε j) • ⟪a i, a j⟫_ℂ := by
    rw [signSum, sum_inner]
    refine sum_congr rfl fun i _ => ?_
    rw [inner_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_smul_right, sgn, map_intCast, smul_eq_mul]
    ring
  have h' := congrArg Complex.re ((sum_congr rfl fun ε _ => h ε).trans (sum_sgn_smul _))
  simp only [inner_self_eq_norm_sq_to_K, smul_eq_mul, Complex.re_sum] at h'
  have h2 : ((2 : ℂ) ^ Fintype.card ι).re = 2 ^ Fintype.card ι := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, Complex.ofReal_re]
  simpa [← Complex.ofReal_pow, ← Complex.ofReal_sum, h2] using h'

/-! ### Eqs. (3), (4) for `n` states -/

/-- `‖v‖² ρ_v = |v⟩⟨v|`. -/
lemma norm_sq_smul_pureState (v : E) : (((‖v‖ ^ 2 : ℝ)) : ℂ) • pureState v = proj v := by
  by_cases hv : v = 0
  · subst hv; ext; simp
  have hn : ‖v‖ ^ 2 ≠ 0 := by positivity
  rw [pureState, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn, Complex.ofReal_one,
    one_smul]

/-- The weights `pᵢ = ‖cᵢ ψᵢ‖² / ∑ⱼ ‖cⱼ ψⱼ‖²` of eq. (3). -/
def weights (c : ι → ℂ) (ψ : ι → E) (i : ι) : ℝ :=
  ‖c i • ψ i‖ ^ 2 / ∑ j, ‖c j • ψ j‖ ^ 2

omit [DecidableEq ι] in
lemma weights_nonneg (c : ι → ℂ) (ψ : ι → E) (i : ι) : 0 ≤ weights c ψ i := by
  unfold weights; positivity

omit [DecidableEq ι] in
lemma weights_eq_zero {c : ι → ℂ} (ψ : ι → E) {i : ι} (hc : c i = 0) : weights c ψ i = 0 := by
  simp [weights, hc]

omit [DecidableEq ι] in
lemma sum_norm_sq_pos {c : ι → ℂ} {ψ : ι → E} (h : ∑ i, c i • ψ i ≠ 0) :
    0 < ∑ j, ‖c j • ψ j‖ ^ 2 := by
  refine lt_of_le_of_ne (by positivity) fun h0 => h ?_
  have := (sum_eq_zero_iff_of_nonneg fun j _ => by positivity).mp h0.symm
  exact sum_eq_zero fun j hj => by simpa using this j hj

omit [DecidableEq ι] in
lemma sum_weights {c : ι → ℂ} {ψ : ι → E} (h : ∑ i, c i • ψ i ≠ 0) : ∑ i, weights c ψ i = 1 := by
  simp only [weights]
  rw [← sum_div, div_self (sum_norm_sq_pos h).ne']

omit [DecidableEq ι] in
lemma weights_pos {c : ι → ℂ} {ψ : ι → E} (h : ∑ i, c i • ψ i ≠ 0) {i : ι} (hc : c i ≠ 0)
    (hψ : ψ i ≠ 0) : 0 < weights c ψ i :=
  div_pos (pow_pos (norm_pos_iff.mpr (smul_ne_zero hc hψ)) 2) (sum_norm_sq_pos h)

/-- **Eqs. (3), (4) for `n` states.** If `ϕ = ∑ᵢ cᵢ ψᵢ ≠ 0`, then `ϕ` is a component of the mixture
`∑ᵢ pᵢ ρ_ψᵢ` with the weights `pᵢ = ‖cᵢ ψᵢ‖² / ∑ⱼ ‖cⱼ ψⱼ‖²`: that mixture is also
`∑_ε (‖ϕ_ε‖² / N) ρ_ϕ_ε`, over the vectors `ϕ_ε = ∑ᵢ εᵢ cᵢ ψᵢ` for all signs `ε`, and `ϕ = ϕ_1`. -/
theorem isComponent_weights (c : ι → ℂ) (ψ : ι → E) (h : ∑ i, c i • ψ i ≠ 0) :
    IsComponent (∑ i, c i • ψ i) (mixtureOf (weights c ψ) ψ) := by
  set a : ι → E := fun i => c i • ψ i with ha
  have hS := sum_norm_sq_pos h
  set S := ∑ j, ‖c j • ψ j‖ ^ 2
  have h2 : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hN := sum_norm_sq_signSum a
  refine ⟨ι → ℤˣ, inferInstance, fun ε => ‖signSum a ε‖ ^ 2 / (2 ^ Fintype.card ι * S),
    signSum a, 1, fun _ => by positivity, ?_, ?_, signSum_one a, ?_⟩
  · rw [← sum_div, hN, div_self (by positivity)]
  · have hl : mixtureOf (weights c ψ) ψ = ((S⁻¹ : ℝ) : ℂ) • ∑ i, proj (a i) := by
      rw [mixtureOf, smul_sum]
      refine sum_congr rfl fun i _ => ?_
      by_cases hc : c i = 0
      · simp [weights, hc, a]
      rw [← norm_sq_smul_pureState, smul_smul, weights, ← pureState_smul hc (ψ i),
        ← Complex.ofReal_mul, div_eq_inv_mul]
    have hr : mixtureOf (fun ε => ‖signSum a ε‖ ^ 2 / (2 ^ Fintype.card ι * S)) (signSum a) =
        (((2 ^ Fintype.card ι * S)⁻¹ : ℝ) : ℂ) • ∑ ε, proj (signSum a ε) := by
      rw [mixtureOf, smul_sum]
      refine sum_congr rfl fun ε _ => ?_
      rw [← norm_sq_smul_pureState, smul_smul, ← Complex.ofReal_mul, div_eq_inv_mul]
    rw [hl, hr, sum_proj_signSum, smul_smul]
    congr 1
    push_cast
    field_simp
  · have : signSum a 1 ≠ 0 := by rwa [signSum_one]
    exact div_pos (pow_pos (norm_pos_iff.mpr this) 2) (by positivity)

/-! ### Theorem 1 for `n` states -/

/-- Condition QSUP-PUR for `n` states: `ϕ = ∑ᵢ cᵢ ψᵢ` with `ψ₁, …, ψₙ` linearly independent and
all `cᵢ ≠ 0`. -/
def QSupPurN (ϕ : E) (ψ : ι → E) : Prop :=
  LinearIndependent ℂ ψ ∧ ∃ c : ι → ℂ, (∀ i, c i ≠ 0) ∧ ϕ = ∑ i, c i • ψ i

/-- Condition QSUP-MIX for `n` states: `ϕ` is a component of a mixture of all the `ψᵢ` with
positive weights, and of no mixture of the `ψⱼ` that leaves one of them out. -/
def QSupMixN (ϕ : E) (ψ : ι → E) : Prop :=
  (∃ p : ι → ℝ, (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧ IsComponent ϕ (mixtureOf p ψ)) ∧
    ∀ i (w : ι → ℝ), (∀ j, 0 ≤ w j) → ∑ j, w j = 1 → w i = 0 → ¬ IsComponent ϕ (mixtureOf w ψ)

/-- Under QSUP-MIX, `ϕ` is not a combination of the `ψⱼ` without `ψᵢ`. -/
lemma QSupMixN.ne_sum {ϕ : E} {ψ : ι → E} (hϕ : ϕ ≠ 0) (h : QSupMixN ϕ ψ) {c : ι → ℂ} {i : ι}
    (hc : c i = 0) : ϕ ≠ ∑ j, c j • ψ j := by
  rintro rfl
  exact h.2 i (weights c ψ) (weights_nonneg c ψ) (sum_weights hϕ) (weights_eq_zero ψ hc)
    (isComponent_weights c ψ hϕ)

/-- QSUP-MIX implies QSUP-PUR for `n` states, linear independence included. -/
theorem QSupMixN.qSupPurN {ϕ : E} {ψ : ι → E} (hϕ : ϕ ≠ 0) (h : QSupMixN ϕ ψ) :
    QSupPurN ϕ ψ := by
  obtain ⟨p, hp, -, hcomp⟩ := h.1
  have hspan := mem_span_of_isComponent hϕ hcomp
  have hall : {i | p i ≠ 0} = Set.univ := Set.eq_univ_of_forall fun i => (hp i).ne'
  rw [hall, Set.image_univ] at hspan
  obtain ⟨c, hc⟩ := (mem_span_range_iff_exists_fun ℂ).mp hspan
  refine ⟨Fintype.linearIndependent_iff.mpr fun g hg i => ?_, c,
    fun i hci => h.ne_sum hϕ hci hc.symm, hc.symm⟩
  -- otherwise `ϕ = ∑ⱼ (cⱼ - (cᵢ / gᵢ) gⱼ) ψⱼ` leaves out `ψᵢ`
  by_contra hgi
  refine h.ne_sum hϕ (c := c - (c i / g i) • g) (i := i) (by simp [div_mul_cancel₀ _ hgi]) ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, sum_sub_distrib, mul_smul,
    ← smul_sum, hg, smul_zero, sub_zero, hc]

/-- QSUP-PUR implies QSUP-MIX for `n` states. -/
theorem QSupPurN.qSupMixN {ϕ : E} {ψ : ι → E} (hϕ : ϕ ≠ 0) (h : QSupPurN ϕ ψ) :
    QSupMixN ϕ ψ := by
  obtain ⟨hind, c, hc, rfl⟩ := h
  refine ⟨⟨weights c ψ, fun i => weights_pos hϕ (hc i) (hind.ne_zero i), sum_weights hϕ,
    isComponent_weights c ψ hϕ⟩, fun i w _ _ hwi hcomp => ?_⟩
  -- `ϕ` lies in the span of the `ψⱼ`, `j ≠ i`, and so would `ψᵢ`
  have hsub : ψ '' {j | w j ≠ 0} ⊆ ψ '' {j | j ≠ i} :=
    Set.image_mono fun j hj => by rintro rfl; exact hj hwi
  have hϕs := span_mono hsub (mem_span_of_isComponent hϕ hcomp)
  have hrest : ∑ j ∈ univ.erase i, c j • ψ j ∈ span ℂ (ψ '' {j | j ≠ i}) :=
    sum_mem fun j hj => smul_mem _ _ (subset_span ⟨j, ne_of_mem_erase hj, rfl⟩)
  have hψi : ψ i ∈ span ℂ (ψ '' {j | j ≠ i}) := by
    have := smul_mem _ (c i)⁻¹ (sub_mem hϕs hrest)
    rwa [← add_sum_erase _ _ (mem_univ i), add_sub_cancel_right, smul_smul,
      inv_mul_cancel₀ (hc i), one_smul] at this
  exact hind.notMem_span_image (by simp) hψi

/-- **Theorem 1 for `n` states.** For `ϕ ≠ 0`, QSUP-PUR and QSUP-MIX are equivalent. -/
theorem qSupPurN_iff_qSupMixN {ϕ : E} {ψ : ι → E} (hϕ : ϕ ≠ 0) :
    QSupPurN ϕ ψ ↔ QSupMixN ϕ ψ :=
  ⟨QSupPurN.qSupMixN hϕ, QSupMixN.qSupPurN hϕ⟩

/-- For `n = 2` the conditions are the brief's. -/
theorem qSupPurN_pair_iff {ϕ ψ₁ ψ₂ : E} : QSupPurN ϕ ![ψ₁, ψ₂] ↔ QSupPur ϕ ψ₁ ψ₂ := by
  constructor
  · rintro ⟨hind, c, hc, rfl⟩
    exact ⟨hind, c 0, c 1, hc 0, hc 1, by simp [Fin.sum_univ_two]⟩
  · rintro ⟨hind, c₁, c₂, h₁, h₂, rfl⟩
    exact ⟨hind, ![c₁, c₂], by simp [Fin.forall_fin_two, h₁, h₂], by simp [Fin.sum_univ_two]⟩

/-- For `n = 2` the conditions are the brief's: for `ϕ ≠ 0`, QSUP-MIX for the pair `![ψ₁, ψ₂]` is
QSUP-MIX of the brief. -/
theorem qSupMixN_pair_iff {ϕ ψ₁ ψ₂ : E} (hϕ : ϕ ≠ 0) :
    QSupMixN ϕ ![ψ₁, ψ₂] ↔ QSupMix ϕ ψ₁ ψ₂ := by
  rw [← qSupPurN_iff_qSupMixN hϕ, ← qSupPur_iff_qSupMix hϕ, qSupPurN_pair_iff]

end Many

end SuperpositionAndMultipleMixtures.FurtherResults
