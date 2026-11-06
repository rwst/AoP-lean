/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Linear ordinary differential equations

For a continuous family `L : ℝ → E →L[ℝ] E` of operators on a Banach space, the linear equation
`x'(t) = L(t) x(t)` has a unique solution on all of `ℝ` with any initial value. The
Picard-Lindelöf theorem of Mathlib gives solutions only on short intervals, since a linear vector
field is unbounded. On `[t₀ - T, t₀ + T]` we therefore solve the equation for the field
`L(t) π(x)`, where `π` is the radial retraction onto a large ball, which is bounded and globally
Lipschitz; by Grönwall's inequality the solution never leaves the ball, so it solves the linear
equation. These interval solutions agree by uniqueness and glue to a global one.

## Main results

* `exists_hasDerivAt_clm_apply`, `eq_of_hasDerivAt_clm_apply`: global existence and uniqueness
  for `x' = L(t) x`.
* `exists_hasDerivAt_mul`, `eq_of_hasDerivAt_mul`: the same for `U' = A(t) U` in a Banach
  algebra.
* `mul_star_self_eq_one_of_hasDerivAt`: if `U' = X U` with `X t` skew-adjoint and
  `U t₀ U t₀† = 1`, then `U t U t† = 1` for all `t`.
* `exists_hasDerivAt_mul_mem_unitary`: the propagator of a continuous skew-adjoint `X` is unitary.
-/

@[expose] public section

open Set Metric Filter Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : ℝ → E →L[ℝ] E}

namespace LinearODE

/-! ### The radial retraction -/

/-- The radial retraction of `E` onto the closed ball of radius `R` about `0`. -/
noncomputable def retraction (R : ℝ) (x : E) : E := min 1 (R / ‖x‖) • x

variable {R : ℝ}

omit [NormedSpace ℝ E] in
lemma coeff_nonneg (hR : 0 ≤ R) (x : E) : 0 ≤ min 1 (R / ‖x‖) :=
  le_min zero_le_one (div_nonneg hR (norm_nonneg _))

lemma norm_retraction_le (hR : 0 ≤ R) (x : E) : ‖retraction R x‖ ≤ ‖x‖ := by
  rw [retraction, norm_smul, Real.norm_of_nonneg (coeff_nonneg hR x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (min_le_left _ _)

lemma norm_retraction_le_radius (hR : 0 ≤ R) (x : E) : ‖retraction R x‖ ≤ R := by
  rw [retraction, norm_smul, Real.norm_of_nonneg (coeff_nonneg hR x)]
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [← h, mul_zero]
    exact hR
  · calc min 1 (R / ‖x‖) * ‖x‖ ≤ R / ‖x‖ * ‖x‖ := by gcongr; exact min_le_right _ _
      _ = R := div_mul_cancel₀ R h.ne'

lemma retraction_eq_self {x : E} (hx : ‖x‖ ≤ R) : retraction R x = x := by
  rcases (norm_nonneg x).eq_or_lt with h | h
  · rw [norm_eq_zero.mp h.symm, retraction, smul_zero]
  · rw [retraction, min_eq_left ((one_le_div h).mpr hx), one_smul]

lemma abs_coeff_sub_mul_le {a b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b) (hba : b ≤ a) :
    |min 1 (R / a) - min 1 (R / b)| * b ≤ a - b := by
  rcases hb.eq_or_lt with rfl | hb
  · rw [mul_zero]
    linarith
  have ha : 0 < a := hb.trans_le hba
  have h1 : R / a ≤ R / b := div_le_div_of_nonneg_left hR hb hba
  rw [abs_of_nonpos (sub_nonpos.mpr (min_le_min_left _ h1)), neg_sub]
  rcases le_total 1 (R / b) with h | h
  · rw [min_eq_left h]
    rcases le_total 1 (R / a) with h' | h'
    · rw [min_eq_left h']
      linarith
    · rw [min_eq_right h']
      have hRa : R ≤ a := by rwa [div_le_iff₀ ha, one_mul] at h'
      have hbR : b ≤ R := by rwa [le_div_iff₀ hb, one_mul] at h
      have h2 : (1 - R / a) * b ≤ (1 - R / a) * a :=
        mul_le_mul_of_nonneg_left hba (by rw [sub_nonneg]; exact h')
      have h3 : (1 - R / a) * a = a - R := by field_simp
      linarith
  · rw [min_eq_right h, min_eq_right (h1.trans h)]
    have hRb : R ≤ b := by rwa [div_le_iff₀ hb, one_mul] at h
    have h2 : (R / b - R / a) * b = R * (a - b) / a := by field_simp
    rw [h2, div_le_iff₀ ha]
    nlinarith [mul_le_mul_of_nonneg_right (hRb.trans hba) (sub_nonneg.mpr hba)]

lemma norm_retraction_sub_le (hR : 0 ≤ R) (x y : E) :
    ‖retraction R x - retraction R y‖ ≤ 2 * ‖x - y‖ := by
  wlog h : ‖y‖ ≤ ‖x‖ generalizing x y
  · rw [norm_sub_rev, norm_sub_rev x]
    exact this y x (le_of_not_ge h)
  have hxy : retraction R x - retraction R y =
      min 1 (R / ‖x‖) • (x - y) + (min 1 (R / ‖x‖) - min 1 (R / ‖y‖)) • y := by
    simp only [retraction, smul_sub, sub_smul]
    abel
  rw [hxy]
  calc _ ≤ ‖min 1 (R / ‖x‖) • (x - y)‖ + ‖(min 1 (R / ‖x‖) - min 1 (R / ‖y‖)) • y‖ :=
        norm_add_le _ _
    _ = min 1 (R / ‖x‖) * ‖x - y‖ + |min 1 (R / ‖x‖) - min 1 (R / ‖y‖)| * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (coeff_nonneg hR x), Real.norm_eq_abs]
    _ ≤ 1 * ‖x - y‖ + (‖x‖ - ‖y‖) :=
        add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
          (abs_coeff_sub_mul_le hR (norm_nonneg _) h)
    _ ≤ 2 * ‖x - y‖ := by linarith [norm_sub_norm_le x y]

lemma lipschitzWith_retraction (hR : 0 ≤ R) : LipschitzWith 2 (retraction (E := E) R) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_ofNat]
    exact norm_retraction_sub_le hR x y

/-! ### Grönwall bounds on both sides of `t₀` -/

lemma norm_le_mul_exp_right {x x' : ℝ → E} {t₀ T M : ℝ}
    (hx : ∀ t ∈ Icc t₀ (t₀ + T), HasDerivWithinAt x (x' t) (Icc t₀ (t₀ + T)) t)
    (hb : ∀ t ∈ Icc t₀ (t₀ + T), ‖x' t‖ ≤ M * ‖x t‖) :
    ∀ t ∈ Icc t₀ (t₀ + T), ‖x t‖ ≤ ‖x t₀‖ * Real.exp (M * (t - t₀)) := by
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn hx)
    (fun s hs => (hx s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) le_rfl
    (fun s hs => by rw [add_zero]; exact hb s (Ico_subset_Icc_self hs)) t ht
  rwa [gronwallBound_ε0] at h

/-- Grönwall's inequality on `[t₀ - T, t₀ + T]`: if `‖x'‖ ≤ M ‖x‖`, then
`‖x t‖ ≤ ‖x t₀‖ e^{MT}`. -/
lemma norm_le_mul_exp {x x' : ℝ → E} {t₀ T M : ℝ} (hM : 0 ≤ M)
    (hx : ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivWithinAt x (x' t) (Icc (t₀ - T) (t₀ + T)) t)
    (hb : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖x' t‖ ≤ M * ‖x t‖) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖x t‖ ≤ ‖x t₀‖ * Real.exp (M * T) := by
  intro t ht
  have hT : 0 ≤ T := by linarith [ht.1, ht.2]
  have hsub : Icc t₀ (t₀ + T) ⊆ Icc (t₀ - T) (t₀ + T) := Icc_subset_Icc (by linarith) le_rfl
  rcases le_total t₀ t with h | h
  · refine (norm_le_mul_exp_right (fun s hs => (hx s (hsub hs)).mono hsub)
      (fun s hs => hb s (hsub hs)) t ⟨h, ht.2⟩).trans ?_
    gcongr
    linarith [ht.2]
  · -- reflect: `y u = x (2 t₀ - u)` on `[t₀, t₀ + T]`
    have hmaps : MapsTo (fun u => 2 * t₀ - u) (Icc t₀ (t₀ + T)) (Icc (t₀ - T) (t₀ + T)) :=
      fun u hu => ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hy : ∀ u ∈ Icc t₀ (t₀ + T), HasDerivWithinAt (x ∘ fun u => 2 * t₀ - u)
        ((-1 : ℝ) • x' (2 * t₀ - u)) (Icc t₀ (t₀ + T)) u := fun u hu =>
      (hx _ (hmaps hu)).scomp u ((hasDerivAt_id' u).const_sub (2 * t₀)).hasDerivWithinAt hmaps
    have h2 := norm_le_mul_exp_right hy (fun u hu => by
      rw [norm_smul, norm_neg, norm_one, one_mul]
      exact hb _ (hmaps hu)) (2 * t₀ - t) ⟨by linarith, by linarith [ht.1]⟩
    simp only [Function.comp_apply, show 2 * t₀ - (2 * t₀ - t) = t by ring,
      show 2 * t₀ - t₀ = t₀ by ring] at h2
    refine h2.trans ?_
    gcongr
    linarith [ht.1]

end LinearODE

open LinearODE

/-! ### Linear equations in a Banach space -/

/-- **Linear ODE on an interval**: `x' = L(t) x` has a solution on `[t₀ - T, t₀ + T]` with any
initial value. -/
theorem exists_hasDerivWithinAt_clm_apply_Icc [CompleteSpace E] (hL : Continuous L) (t₀ : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (x₀ : E) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt x (L t (x t)) (Icc (t₀ - T) (t₀ + T)) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := t₀ - T) (b := t₀ + T)).exists_bound_of_continuousOn
    hL.continuousOn
  set M : ℝ≥0 := C.toNNReal
  have hM : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖L t‖ ≤ M := fun t ht => by
    rw [Real.coe_toNNReal']
    exact le_max_of_le_left (hC t ht)
  have hMn : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖L t‖₊ ≤ M := fun t ht => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hM t ht
  set R : ℝ := ‖x₀‖ * Real.exp (M * T) + 1
  have hR : 0 < R := by positivity
  have ht₀ : t₀ ∈ Icc (t₀ - T) (t₀ + T) := ⟨by linarith, by linarith⟩
  set B : ℝ≥0 := M * R.toNNReal
  have hB : (B : ℝ) = M * R := by rw [NNReal.coe_mul, Real.coe_toNNReal _ hR.le]
  have hPL : IsPicardLindelof (fun t y => L t (retraction R y)) (⟨t₀, ht₀⟩ : Icc _ _) 0
      (‖x₀‖₊ + B * T.toNNReal) ‖x₀‖₊ B (M * 2) := by
    refine ⟨fun t ht => ?_, fun y _ => (hL.clm_apply continuous_const).continuousOn,
      fun t ht y _ => ?_, ?_⟩
    · exact (((L t).lipschitzWith.comp (lipschitzWith_retraction hR.le)).weaken
        (by gcongr; exact hMn t ht)).lipschitzOnWith
    · rw [hB]
      exact ((L t).le_opNorm _).trans (mul_le_mul (hM t ht) (norm_retraction_le_radius hR.le _)
        (norm_nonneg _) M.2)
    · simp only [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ hT, coe_nnnorm]
      rw [show t₀ + T - t₀ = T by ring, show t₀ - (t₀ - T) = T by ring, max_self]
      linarith
  obtain ⟨x, hx₀, hx⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (x := x₀) (mem_closedBall_zero_iff.mpr (by rw [coe_nnnorm]))
  have hbound := norm_le_mul_exp M.2 hx fun t ht =>
    ((L t).le_opNorm _).trans (mul_le_mul (hM t ht) (norm_retraction_le hR.le _)
      (norm_nonneg _) M.2)
  have hx₀' : x t₀ = x₀ := hx₀
  refine ⟨x, hx₀', fun t ht => ?_⟩
  have h := hx t ht
  have hle : ‖x t‖ ≤ R := by
    have := hbound t ht
    rw [hx₀'] at this
    exact this.trans (le_add_of_nonneg_right zero_le_one)
  rwa [retraction_eq_self hle] at h

/-- **Uniqueness for a linear ODE on an interval.** -/
theorem eqOn_Icc_of_hasDerivWithinAt_clm_apply (hL : Continuous L) {t₀ T : ℝ} (hT : 0 < T)
    {x y : ℝ → E}
    (hx : ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivWithinAt x (L t (x t)) (Icc (t₀ - T) (t₀ + T)) t)
    (hy : ∀ t ∈ Icc (t₀ - T) (t₀ + T), HasDerivWithinAt y (L t (y t)) (Icc (t₀ - T) (t₀ + T)) t)
    (h : x t₀ = y t₀) : EqOn x y (Icc (t₀ - T) (t₀ + T)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := t₀ - T) (b := t₀ + T)).exists_bound_of_continuousOn
    hL.continuousOn
  have hnhds : ∀ t ∈ Ioo (t₀ - T) (t₀ + T), Icc (t₀ - T) (t₀ + T) ∈ 𝓝 t :=
    fun t ht => Icc_mem_nhds ht.1 ht.2
  refine ODE_solution_unique_of_mem_Icc (K := C.toNNReal) (s := fun _ => univ)
    (v := fun t => L t) (fun t ht => ?_) ⟨by linarith, by linarith⟩
    (HasDerivWithinAt.continuousOn hx)
    (fun t ht => (hx t (Ioo_subset_Icc_self ht)).hasDerivAt (hnhds t ht)) (fun _ _ => trivial)
    (HasDerivWithinAt.continuousOn hy)
    (fun t ht => (hy t (Ioo_subset_Icc_self ht)).hasDerivAt (hnhds t ht)) (fun _ _ => trivial) h
  refine ((L t).lipschitzWith.weaken ?_).lipschitzOnWith
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact le_max_of_le_left (hC t (Ioo_subset_Icc_self ht))

/-- **Linear ODE, global existence**: for a continuous family of operators `L t`, the equation
`x' = L(t) x` has a solution on all of `ℝ` with any initial value. -/
theorem exists_hasDerivAt_clm_apply [CompleteSpace E] (hL : Continuous L) (t₀ : ℝ) (x₀ : E) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t, HasDerivAt x (L t (x t)) t := by
  choose! α hα₀ hα using fun T (hT : 0 ≤ T) => exists_hasDerivWithinAt_clm_apply_Icc hL t₀ hT x₀
  have hagree : ∀ T T' : ℝ, 0 < T → 0 < T' → ∀ t, |t - t₀| ≤ min T T' → α T t = α T' t := by
    intro T T' hT hT' t ht
    have hsub : ∀ S, min T T' ≤ S →
        Icc (t₀ - min T T') (t₀ + min T T') ⊆ Icc (t₀ - S) (t₀ + S) := fun S hS =>
      Icc_subset_Icc (by linarith) (by linarith)
    refine eqOn_Icc_of_hasDerivWithinAt_clm_apply hL (lt_min hT hT')
      (fun s hs => (hα T hT.le s (hsub T (min_le_left _ _) hs)).mono
        (hsub T (min_le_left _ _)))
      (fun s hs => (hα T' hT'.le s (hsub T' (min_le_right _ _) hs)).mono
        (hsub T' (min_le_right _ _)))
      ((hα₀ T hT.le).trans (hα₀ T' hT'.le).symm) ?_
    rw [abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨fun t => α (|t - t₀| + 1) t, by simpa using hα₀ 1 zero_le_one, fun t => ?_⟩
  have hT : 0 < |t - t₀| + 1 := by positivity
  have hmem : t ∈ Ioo (t₀ - (|t - t₀| + 1)) (t₀ + (|t - t₀| + 1)) :=
    ⟨by linarith [neg_abs_le (t - t₀)], by linarith [le_abs_self (t - t₀)]⟩
  refine ((hα _ hT.le t (Ioo_subset_Icc_self hmem)).hasDerivAt
    (Icc_mem_nhds hmem.1 hmem.2)).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds (show t - 1 / 2 < t by linarith)
    (show t < t + 1 / 2 by linarith)] with s hs
  refine hagree _ _ (by positivity) hT s (le_min (by linarith) ?_)
  have h1 := abs_sub_le s t t₀
  have h2 : |s - t| < 1 / 2 := abs_sub_lt_iff.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  linarith

/-- **Linear ODE, global uniqueness.** -/
theorem eq_of_hasDerivAt_clm_apply (hL : Continuous L) {x y : ℝ → E} {t₀ : ℝ}
    (hx : ∀ t, HasDerivAt x (L t (x t)) t) (hy : ∀ t, HasDerivAt y (L t (y t)) t)
    (h : x t₀ = y t₀) : x = y := by
  funext t
  exact eqOn_Icc_of_hasDerivWithinAt_clm_apply hL (T := |t - t₀| + 1) (by positivity)
    (fun s _ => (hx s).hasDerivWithinAt) (fun s _ => (hy s).hasDerivWithinAt) h
    ⟨by linarith [neg_abs_le (t - t₀)], by linarith [le_abs_self (t - t₀)]⟩

/-! ### Linear equations in a Banach algebra -/

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {A : ℝ → 𝔸}

/-- **Propagator, existence**: for continuous `A`, the equation `U' = A(t) U` has a solution on
all of `ℝ` with any initial value. -/
theorem exists_hasDerivAt_mul [CompleteSpace 𝔸] (hA : Continuous A) (t₀ : ℝ) (U₀ : 𝔸) :
    ∃ U : ℝ → 𝔸, U t₀ = U₀ ∧ ∀ t, HasDerivAt U (A t * U t) t :=
  exists_hasDerivAt_clm_apply ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp hA) t₀ U₀

/-- **Propagator, uniqueness.** -/
theorem eq_of_hasDerivAt_mul (hA : Continuous A) {U V : ℝ → 𝔸} {t₀ : ℝ}
    (hU : ∀ t, HasDerivAt U (A t * U t) t) (hV : ∀ t, HasDerivAt V (A t * V t) t)
    (h : U t₀ = V t₀) : U = V :=
  eq_of_hasDerivAt_clm_apply ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp hA) hU hV h

variable [StarRing 𝔸] [StarModule ℝ 𝔸] [ContinuousStar 𝔸]

/-- If `U' = X U` with continuous skew-adjoint `X`, then `U U† = 1` holds at all times once it
holds at one: `D = U U† - 1` solves the linear equation `D' = X D - D X` with `D t₀ = 0`. -/
theorem mul_star_self_eq_one_of_hasDerivAt {U X : ℝ → 𝔸} (hXc : Continuous X)
    (hX : ∀ t, star (X t) = -X t) (hU : ∀ t, HasDerivAt U (X t * U t) t) {t₀ : ℝ}
    (h₀ : U t₀ * star (U t₀) = 1) (t : ℝ) : U t * star (U t) = 1 := by
  set L : ℝ → 𝔸 →L[ℝ] 𝔸 := fun s =>
    ContinuousLinearMap.mul ℝ 𝔸 (X s) - (ContinuousLinearMap.mul ℝ 𝔸).flip (X s)
  have hL : Continuous L := ((ContinuousLinearMap.mul ℝ 𝔸).continuous.comp hXc).sub
    ((ContinuousLinearMap.mul ℝ 𝔸).flip.continuous.comp hXc)
  have hD : ∀ s, HasDerivAt (fun s => U s * star (U s) - 1)
      (L s (U s * star (U s) - 1)) s := fun s => by
    convert ((hU s).mul (hU s).star).sub_const 1 using 1
    simp only [L, sub_apply, ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.flip_apply, star_mul, hX, mul_neg]
    noncomm_ring
  have h0 : ∀ s, HasDerivAt (fun _ => (0 : 𝔸)) (L s 0) s := fun s => by
    rw [map_zero]
    exact hasDerivAt_const s 0
  have := congrFun (eq_of_hasDerivAt_clm_apply hL hD h0 (by rw [h₀, sub_self])) t
  exact sub_eq_zero.mp this

/-- **Unitary propagator**: for continuous skew-adjoint `X`, the solution of `U' = X(t) U` with
`U t₀ = 1` is unitary at all times. -/
theorem exists_hasDerivAt_mul_mem_unitary [CompleteSpace 𝔸] {X : ℝ → 𝔸} (hXc : Continuous X)
    (hX : ∀ t, star (X t) = -X t) (t₀ : ℝ) :
    ∃ U : ℝ → 𝔸, U t₀ = 1 ∧ (∀ t, HasDerivAt U (X t * U t) t) ∧ ∀ t, U t ∈ unitary 𝔸 := by
  obtain ⟨U, hU₀, hU⟩ := exists_hasDerivAt_mul hXc t₀ 1
  refine ⟨U, hU₀, hU, fun t => Unitary.mem_iff.mpr ⟨?_, ?_⟩⟩
  · rw [star_mul_self_eq_of_hasDerivAt hX hU t₀ t, hU₀, star_one, one_mul]
  · exact mul_star_self_eq_one_of_hasDerivAt hXc hX hU (by rw [hU₀, star_one, one_mul]) t

end Algebra
