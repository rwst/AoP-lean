/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.KolmogorovWidth

/-!
# Power series spaces

For `r : EReal` and an exponent sequence `a : ℕ → ℝ`, the power series space `Λ_r(a)` is the
space of sequences `x : ℕ → 𝕜` with `∑ j, ‖x j‖ ^ 2 * exp (2 * t * a j) < ∞` for every real
`t < r`, with the seminorms `|x|_t = (∑ j, ‖x j‖ ^ 2 * exp (2 * t * a j)) ^ (1 / 2)`. The cases of
interest are `r = 0` (finite type) and `r = ⊤` (infinite type). For `a j = log (j + 1)` and
`r = ⊤` this is the space `s` of rapidly decreasing sequences.

We prove the isomorphic classification: for monotone nonnegative `a` and `b`, `Λ_r(a)` and
`Λ_r(b)` are isomorphic as topological vector spaces if and only if `a` and `b` are equivalent,
in the sense that each is bounded by a positive multiple of the other plus a constant.

The proof of the hard direction compares Kolmogorov widths. The `k`-th width of the unit ball of
`|·|_t` relative to that of `|·|_s`, `s < t`, is `exp (-(t - s) * a k)`. An isomorphism `T` and its
inverse are continuous, which gives `T '' U ⊆ c₁ • V` and `V' ⊆ c₂ • T '' U'` for suitable unit
balls, and `kolmogorovWidth_le_mul_of_subset` turns these into an inequality between widths.

## Main definitions

* `PowerSeriesSpace 𝕜 r a`: the space `Λ_r(a)` with the topology of its seminorms.
* `PowerSeriesSpace.seminorm 𝕜 r a t`: the seminorm `|·|_t`.

## Main statements

* `PowerSeriesSpace.withSeminorms`: the topology is that of the seminorms `|·|_t`, `t < r`.
* `PowerSeriesSpace.kolmogorovWidth_closedBall`: the `k`-th width of the unit ball of `|·|_t`
  relative to that of `|·|_s` is `exp (-(t - s) * a k)`.
* `PowerSeriesSpace.exists_le_mul_add_of_continuousLinearEquiv`: if `Λ_r(a) ≅ Λ_r(b)`, then
  `a k ≤ C * b k + D` for some `C > 0` and `D`.
* `PowerSeriesSpace.nonempty_continuousLinearEquiv_iff_top`,
  `PowerSeriesSpace.nonempty_continuousLinearEquiv_iff_zero`: the classification for infinite
  and for finite type.

## References

* B. S. Mityagin, *Approximative dimension and bases in nuclear spaces*, Russian Math. Surveys
  16 (1961) 59–127.
* R. Meise, D. Vogt, *Introduction to Functional Analysis*, Oxford University Press, 1997,
  Chapter 29.
* D. Vogt, *Lectures on Fréchet spaces*, Bergische Universität Wuppertal, 2000, Theorem 5.12.
-/

@[expose] public section

open Set Submodule Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace PowerSeriesSpace

variable (𝕜 : Type*) [RCLike 𝕜] (r : EReal) (a : ℕ → ℝ)

/-- The weighted sequence `j ↦ exp (t * a j) * x j`. -/
def weight (t : ℝ) (x : ℕ → 𝕜) : ℕ → 𝕜 := fun j => (Real.exp (t * a j) : 𝕜) * x j

variable {𝕜 a} in
theorem weight_add (t : ℝ) (x y : ℕ → 𝕜) : weight 𝕜 a t (x + y) = weight 𝕜 a t x + weight 𝕜 a t y :=
  funext fun _ => mul_add _ _ _

variable {𝕜 a} in
theorem weight_smul (t : ℝ) (c : 𝕜) (x : ℕ → 𝕜) : weight 𝕜 a t (c • x) = c • weight 𝕜 a t x :=
  funext fun _ => mul_left_comm _ _ _

/-- The sequences `x` with `j ↦ exp (t * a j) * x j` in `ℓ²` for every real `t < r`. -/
def submodule : Submodule 𝕜 (ℕ → 𝕜) where
  carrier := {x | ∀ t : ℝ, (t : EReal) < r → Memℓp (weight 𝕜 a t x) 2}
  add_mem' hx hy t ht := by rw [weight_add]; exact (hx t ht).add (hy t ht)
  zero_mem' t _ := by
    rw [show weight 𝕜 a t 0 = 0 from funext fun _ => mul_zero _]
    exact zero_memℓp
  smul_mem' c x hx t ht := by rw [weight_smul]; exact (hx t ht).const_smul c

/-- The admissible levels `t < r` of the seminorms. -/
abbrev Level := {t : ℝ // (t : EReal) < r}

instance [Fact (⊥ < r)] : Nonempty (Level r) :=
  let ⟨t, _, ht⟩ := EReal.lt_iff_exists_real_btwn.mp (Fact.out : ⊥ < r)
  ⟨⟨t, ht⟩⟩

instance : Fact ((⊥ : EReal) < ⊤) := ⟨bot_lt_top⟩

instance : Fact ((⊥ : EReal) < 0) := ⟨EReal.bot_lt_zero⟩

end PowerSeriesSpace

/-- The power series space `Λ_r(a)`. Its topology is defined by the seminorms
`PowerSeriesSpace.seminorm`. -/
def PowerSeriesSpace (𝕜 : Type*) [RCLike 𝕜] (r : EReal) (a : ℕ → ℝ) : Type _ :=
  PowerSeriesSpace.submodule 𝕜 r a

namespace PowerSeriesSpace

variable {𝕜 : Type*} [RCLike 𝕜] {r : EReal} {a b : ℕ → ℝ}

instance : AddCommGroup (PowerSeriesSpace 𝕜 r a) :=
  inferInstanceAs (AddCommGroup (submodule 𝕜 r a))

instance : Module 𝕜 (PowerSeriesSpace 𝕜 r a) :=
  inferInstanceAs (Module 𝕜 (submodule 𝕜 r a))

instance : CoeFun (PowerSeriesSpace 𝕜 r a) fun _ => ℕ → 𝕜 :=
  ⟨fun x => (x : submodule 𝕜 r a).1⟩

/-- Build an element of `Λ_r(a)` from a sequence. -/
def mk (x : ℕ → 𝕜) (hx : x ∈ submodule 𝕜 r a) : PowerSeriesSpace 𝕜 r a :=
  (⟨x, hx⟩ : submodule 𝕜 r a)

@[simp] theorem coe_mk (x : ℕ → 𝕜) (hx : x ∈ submodule 𝕜 r a) : ⇑(mk x hx) = x := rfl

theorem mem_submodule (x : PowerSeriesSpace 𝕜 r a) : ⇑x ∈ submodule 𝕜 r a :=
  (x : submodule 𝕜 r a).2

@[ext] theorem ext {x y : PowerSeriesSpace 𝕜 r a} (h : ⇑x = ⇑y) : x = y :=
  Subtype.ext h

@[simp] theorem coe_add (x y : PowerSeriesSpace 𝕜 r a) : ⇑(x + y) = ⇑x + ⇑y := rfl

@[simp] theorem coe_sub (x y : PowerSeriesSpace 𝕜 r a) : ⇑(x - y) = ⇑x - ⇑y := rfl

@[simp] theorem coe_smul (c : 𝕜) (x : PowerSeriesSpace 𝕜 r a) : ⇑(c • x) = c • ⇑x := rfl

@[simp] theorem coe_zero : ⇑(0 : PowerSeriesSpace 𝕜 r a) = 0 := rfl

/-- A sequence with finite support lies in every power series space. -/
theorem mem_submodule_of_finite {x : ℕ → 𝕜} (hx : {j | x j ≠ 0}.Finite) :
    x ∈ submodule 𝕜 r a := by
  intro t _
  exact (memℓp_zero (hx.subset fun j hj h => hj (by simp [weight, h]))).of_exponent_ge bot_le

variable (𝕜 r a) in
/-- The map `x ↦ (exp (t * a j) * x j)_j` into `ℓ²`. -/
def toL2 (t : Level r) : PowerSeriesSpace 𝕜 r a →ₗ[𝕜] lp (fun _ : ℕ => 𝕜) 2 where
  toFun x := ⟨weight 𝕜 a t x, (mem_submodule x) t t.2⟩
  map_add' _ _ := lp.ext (weight_add _ _ _)
  map_smul' _ _ := lp.ext (weight_smul _ _ _)

@[simp] theorem toL2_apply (t : Level r) (x : PowerSeriesSpace 𝕜 r a) (j : ℕ) :
    toL2 𝕜 r a t x j = (Real.exp (t * a j) : 𝕜) * x j := rfl

theorem norm_toL2_apply (t : Level r) (x : PowerSeriesSpace 𝕜 r a) (j : ℕ) :
    ‖toL2 𝕜 r a t x j‖ = Real.exp (t * a j) * ‖x j‖ := by
  rw [toL2_apply, norm_mul, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]

variable (𝕜 r a) in
/-- The seminorm `|x|_t = (∑ j, ‖exp (t * a j) * x j‖ ^ 2) ^ (1 / 2)`. -/
def seminorm (t : Level r) : Seminorm 𝕜 (PowerSeriesSpace 𝕜 r a) :=
  (normSeminorm 𝕜 ↥(lp (fun _ : ℕ => 𝕜) 2)).comp (toL2 𝕜 r a t)

theorem seminorm_apply (t : Level r) (x : PowerSeriesSpace 𝕜 r a) :
    seminorm 𝕜 r a t x = ‖toL2 𝕜 r a t x‖ := rfl

instance : TopologicalSpace (PowerSeriesSpace 𝕜 r a) :=
  (show SeminormFamily 𝕜 (PowerSeriesSpace 𝕜 r a) (Level r) from
    seminorm 𝕜 r a).moduleFilterBasis.topology

variable (𝕜 r a) in
theorem withSeminorms : WithSeminorms (seminorm 𝕜 r a) := ⟨rfl⟩

/-- For nonnegative exponents the seminorms increase with the level. -/
theorem seminorm_mono (ha0 : 0 ≤ a) {s t : Level r} (hst : s ≤ t) (x : PowerSeriesSpace 𝕜 r a) :
    seminorm 𝕜 r a s x ≤ seminorm 𝕜 r a t x := by
  refine lp.norm_mono two_ne_zero fun j => ?_
  rw [norm_toL2_apply, norm_toL2_apply]
  gcongr
  exact ha0 j

/-- A continuous seminorm on `Λ_r(a)` is bounded by a multiple of a single `|·|_t`. -/
theorem exists_le_mul_seminorm [Fact (⊥ < r)] (ha0 : 0 ≤ a)
    {q : Seminorm 𝕜 (PowerSeriesSpace 𝕜 r a)}
    (hq : Continuous q) :
    ∃ t : Level r, ∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * seminorm 𝕜 r a t x := by
  obtain ⟨s, C, hC, hle⟩ := Seminorm.bound_of_continuous (withSeminorms 𝕜 r a) q hq
  obtain ⟨t, ht⟩ := s.exists_le
  refine ⟨t, C, by positivity, fun x => (hle x).trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ C.2
  exact Seminorm.finset_sup_apply_le (apply_nonneg _ _) fun i hi =>
    seminorm_mono ha0 (ht i hi) x

/-! ### Widths of the unit balls -/

variable (𝕜 a) in
/-- The unit ball of `|·|_t`. -/
def unitBall (t : Level r) : Set (PowerSeriesSpace 𝕜 r a) := (seminorm 𝕜 r a t).closedBall 0 1

theorem mem_unitBall {t : Level r} {x : PowerSeriesSpace 𝕜 r a} :
    x ∈ unitBall 𝕜 a t ↔ seminorm 𝕜 r a t x ≤ 1 :=
  Seminorm.mem_closedBall_zero _

/-- The unit vectors of `ℓ²` are orthonormal. -/
theorem _root_.lp.orthonormal_single :
    Orthonormal 𝕜 fun i : ℕ => lp.single 2 i (1 : 𝕜) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left, lp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The unit vector `e i` of `Λ_r(a)`. -/
def single (i : ℕ) : PowerSeriesSpace 𝕜 r a :=
  mk (Pi.single i 1) (mem_submodule_of_finite <| (Set.finite_singleton i).subset fun j hj => by
    by_contra h; exact hj (Pi.single_eq_of_ne h _))

/-- The truncation of `x` to its first `k` coordinates lies in the span of the first `k` unit
vectors. -/
theorem exists_mem_span_single (k : ℕ) (x : PowerSeriesSpace 𝕜 r a) :
    ∃ l ∈ span 𝕜 (range fun i : Fin k => (single i : PowerSeriesSpace 𝕜 r a)),
      ∀ j, (x - l) j = if j < k then 0 else x j := by
  refine ⟨∑ i : Fin k, x i • single i, sum_mem fun i _ => smul_mem _ _
    (subset_span (mem_range_self i)), fun j => ?_⟩
  have : (∑ i : Fin k, x i • (single i : PowerSeriesSpace 𝕜 r a)) j =
      ∑ i ∈ Finset.range k, if j = i then x i else 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => if j = i then x i else 0) k]
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, coe_add, Pi.add_apply, ih]
      simp [single, Pi.single_apply]
  rw [coe_sub, Pi.sub_apply, this, Finset.sum_ite_eq]
  split_ifs with h1 h2 h2 <;> simp_all

/-- **Upper bound.** The first `k` unit vectors approximate the unit ball of `|·|_t` within
`exp (-(t - s) * a k)` in `|·|_s`. -/
theorem kolmogorovWidth_closedBall_le (ha : Monotone a) {s t : Level r} (hst : (s : ℝ) < t)
    (k : ℕ) :
    kolmogorovWidth 𝕜 (unitBall 𝕜 a t) (unitBall 𝕜 a s) k ≤
      ENNReal.ofReal (Real.exp (-((t - s) * a k))) := by
  set c : ℝ := Real.exp (-((t - s) * a k)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  refine (kolmogorovWidth_le (c := (c : 𝕜)) (fun i : Fin k => single i) ?_).trans_eq ?_
  · intro x hx
    rw [mem_unitBall] at hx
    obtain ⟨l, hl, hxl⟩ := exists_mem_span_single (r := r) (a := a) k x
    have hz : seminorm 𝕜 r a s (x - l) ≤ c := by
      rw [seminorm_apply]
      calc ‖toL2 𝕜 r a s (x - l)‖ ≤ ‖(c : 𝕜) • toL2 𝕜 r a t x‖ := by
            refine lp.norm_mono two_ne_zero fun j => ?_
            rw [norm_toL2_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul, norm_toL2_apply,
              RCLike.norm_ofReal, abs_of_pos hc0, hxl j]
            split_ifs with hj
            · simp only [norm_zero, mul_zero]; positivity
            · rw [hc, ← mul_assoc, ← Real.exp_add]
              gcongr
              nlinarith [ha (not_lt.mp hj), sub_pos.mpr hst]
        _ = c * ‖toL2 𝕜 r a t x‖ := by
            rw [lp.norm_const_smul two_ne_zero, RCLike.norm_ofReal, abs_of_pos hc0]
        _ ≤ c := mul_le_of_le_one_right hc0.le (by rwa [seminorm_apply] at hx)
    refine ⟨(c : 𝕜) • ((c : 𝕜)⁻¹ • (x - l)), ⟨(c : 𝕜)⁻¹ • (x - l), ?_, rfl⟩, l, hl, ?_⟩
    · rw [mem_unitBall, map_smul_eq_mul, norm_inv, RCLike.norm_ofReal,
        abs_of_pos hc0]
      exact inv_mul_le_one_of_le₀ hz hc0.le
    · simp [smul_smul, (RCLike.ofReal_ne_zero.mpr hc0.ne')]
  · rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm, RCLike.norm_ofReal, abs_of_pos hc0]

/-- **Lower bound.** No `k` vectors approximate the unit ball of `|·|_t` better than
`exp (-(t - s) * a k)` in `|·|_s`. -/
theorem ofReal_le_kolmogorovWidth_closedBall (ha : Monotone a) {s t : Level r}
    (hst : (s : ℝ) < t) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-((t - s) * a k))) ≤
      kolmogorovWidth 𝕜 (unitBall 𝕜 a t) (unitBall 𝕜 a s) k := by
  set c : ℝ := Real.exp (-((t - s) * a k)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  refine le_trans ?_ ((kolmogorovWidth_anti_right (A := toL2 𝕜 r a s '' unitBall 𝕜 a t)
    (B' := closedBall 0 1) ?_ k).trans
    (kolmogorovWidth_image_le (toL2 𝕜 r a s) _ _ k))
  · refine ofReal_le_kolmogorovWidth_of_orthonormal
      (u := fun i : Fin (k + 1) => lp.single 2 (i : ℕ) (1 : 𝕜))
      ((lp.orthonormal_single (𝕜 := 𝕜)).comp _ Fin.val_injective) fun y hy hy1 => ?_
    have hy0 : ∀ j, k < j → y j = 0 := fun j hj => by
      clear hy1
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        rw [lp.single_apply, Pi.single_eq_of_ne (by omega)]
      | zero => rfl
      | add z w _ _ hz hw => rw [lp.coeFn_add, Pi.add_apply, hz, hw, add_zero]
      | smul d z _ hz => rw [lp.coeFn_smul, Pi.smul_apply, hz, smul_zero]
    let x : PowerSeriesSpace 𝕜 r a :=
      mk (fun j => (c * Real.exp (-(s * a j)) : ℝ) * y j) (mem_submodule_of_finite <|
        (Set.finite_Iic k).subset fun j hj => by
          by_contra h; exact hj (by rw [hy0 j (not_le.mp h), mul_zero]))
    refine ⟨x, ?_, lp.ext (funext fun j => ?_)⟩
    · rw [mem_unitBall, seminorm_apply]
      refine (lp.norm_mono two_ne_zero fun j => ?_).trans hy1
      rw [norm_toL2_apply, coe_mk, norm_mul, RCLike.norm_ofReal, abs_of_pos (by positivity),
        ← mul_assoc]
      rcases le_or_gt j k with hj | hj
      · refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [hc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
        nlinarith [ha hj, sub_pos.mpr hst]
      · simp [hy0 j hj]
    · rw [toL2_apply, coe_mk, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, ← mul_assoc,
        ← RCLike.ofReal_mul, mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
        mul_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_unitBall] at hx
    rw [mem_closedBall_zero_iff, ← seminorm_apply]
    exact hx

/-- **Kolmogorov widths of the unit balls.** For `s < t < r`, the `k`-th width of the unit ball
of `|·|_t` relative to that of `|·|_s` is `exp (-(t - s) * a k)`. -/
theorem kolmogorovWidth_closedBall (ha : Monotone a) {s t : Level r} (hst : (s : ℝ) < t)
    (k : ℕ) :
    kolmogorovWidth 𝕜 (unitBall 𝕜 a t) (unitBall 𝕜 a s) k =
      ENNReal.ofReal (Real.exp (-((t - s) * a k))) :=
  (kolmogorovWidth_closedBall_le ha hst k).antisymm (ofReal_le_kolmogorovWidth_closedBall ha hst k)

/-! ### Classification -/

theorem enorm_ofReal_eq {C : ℝ} (hC : 0 < C) : (‖(C : 𝕜)‖₊ : ℝ≥0∞) = ENNReal.ofReal C := by
  rw [← ENNReal.ofReal_coe_nnreal, coe_nnNorm, RCLike.norm_ofReal, abs_of_pos hC]

/-- **Isomorphic power series spaces have equivalent exponents**, one half: if
`Λ_r(a) ≅ Λ_r(b)` then `a k ≤ C * b k + D` for some `C > 0` and `D`. -/
theorem exists_le_mul_add_of_continuousLinearEquiv [Fact (⊥ < r)] (ha : Monotone a) (ha0 : 0 ≤ a)
    (hb : Monotone b) (hb0 : 0 ≤ b)
    (T : PowerSeriesSpace 𝕜 r a ≃L[𝕜] PowerSeriesSpace 𝕜 r b) :
    ∃ C > 0, ∃ D, ∀ k, a k ≤ C * b k + D := by
  obtain ⟨γ⟩ : Nonempty (Level r) := inferInstance
  -- continuity of `T` at the level `γ`
  obtain ⟨y, C₁, hC₁, h₁⟩ := exists_le_mul_seminorm (q := (seminorm 𝕜 r b γ).comp
    (T : PowerSeriesSpace 𝕜 r a →ₗ[𝕜] PowerSeriesSpace 𝕜 r b)) ha0
    (((withSeminorms 𝕜 r b).continuous_seminorm γ).comp T.continuous)
  obtain ⟨x, hyx, hxr⟩ := EReal.lt_iff_exists_real_btwn.mp y.2
  let xL : Level r := ⟨x, hxr⟩
  have hyx' : (y : ℝ) < x := EReal.coe_lt_coe_iff.mp hyx
  -- continuity of `T⁻¹` at the level `x`
  obtain ⟨β, C₂, hC₂, h₂⟩ := exists_le_mul_seminorm (q := (seminorm 𝕜 r a xL).comp
    (T.symm : PowerSeriesSpace 𝕜 r b →ₗ[𝕜] PowerSeriesSpace 𝕜 r a)) hb0
    (((withSeminorms 𝕜 r a).continuous_seminorm xL).comp T.symm.continuous)
  obtain ⟨β', hβ'1, hβ'r⟩ := EReal.lt_iff_exists_real_btwn.mp
    (show ((max (β : ℝ) γ : ℝ) : EReal) < r from by
      rcases max_choice (β : ℝ) γ with h | h <;> rw [h]; exacts [β.2, γ.2])
  let βL : Level r := ⟨β', hβ'r⟩
  have hβγ : (γ : ℝ) < β' := (le_max_right _ _).trans_lt (EReal.coe_lt_coe_iff.mp hβ'1)
  have hββ : β ≤ βL := Subtype.coe_le_coe.mp
    ((le_max_left _ _).trans (EReal.coe_lt_coe_iff.mp hβ'1).le)
  -- the two inclusions
  have i₁ : T '' unitBall 𝕜 a y ⊆ (C₁ : 𝕜) • unitBall 𝕜 b γ := by
    rintro _ ⟨u, hu, rfl⟩
    rw [mem_unitBall] at hu
    refine ⟨(C₁ : 𝕜)⁻¹ • T u, ?_, by simp [smul_smul, RCLike.ofReal_ne_zero.mpr hC₁.ne']⟩
    rw [mem_unitBall, map_smul_eq_mul, norm_inv, RCLike.norm_ofReal,
      abs_of_pos hC₁]
    exact inv_mul_le_one_of_le₀ ((h₁ u).trans (mul_le_of_le_one_right hC₁.le hu)) hC₁.le
  have i₂ : unitBall 𝕜 b βL ⊆ (C₂ : 𝕜) • T '' unitBall 𝕜 a xL := by
    intro z hz
    rw [mem_unitBall] at hz
    refine ⟨T ((C₂ : 𝕜)⁻¹ • T.symm z), ⟨(C₂ : 𝕜)⁻¹ • T.symm z, ?_, rfl⟩, ?_⟩
    · rw [mem_unitBall, map_smul_eq_mul, norm_inv, RCLike.norm_ofReal,
        abs_of_pos hC₂]
      exact inv_mul_le_one_of_le₀ ((h₂ z).trans (mul_le_of_le_one_right hC₂.le
        ((seminorm_mono hb0 hββ z).trans hz))) hC₂.le
    · simp [smul_smul, RCLike.ofReal_ne_zero.mpr hC₂.ne']
  -- compare widths
  refine ⟨(β' - γ) / (x - y), div_pos (sub_pos.mpr hβγ) (sub_pos.mpr hyx'),
    Real.log (C₁ * C₂) / (x - y), fun k => ?_⟩
  have hw := (ofReal_le_kolmogorovWidth_closedBall (𝕜 := 𝕜) hb (s := γ) (t := βL) hβγ k).trans
    ((kolmogorovWidth_le_mul_of_subset (T : PowerSeriesSpace 𝕜 r a →ₗ[𝕜] _)
      (RCLike.ofReal_ne_zero.mpr hC₁.ne') (RCLike.ofReal_ne_zero.mpr hC₂.ne') i₁ i₂ k).trans
      (mul_le_mul_of_nonneg_left
        (kolmogorovWidth_closedBall_le ha (s := y) (t := xL) hyx' k) (by positivity)))
  rw [enorm_ofReal_eq hC₁, enorm_ofReal_eq hC₂, ← ENNReal.ofReal_mul hC₁.le,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity),
    ← Real.exp_log (mul_pos hC₁ hC₂), ← Real.exp_add, Real.exp_le_exp] at hw
  have hxy : 0 < x - y := sub_pos.mpr hyx'
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hxy]
  change -((β' - γ) * b k) ≤ Real.log (C₁ * C₂) + -((x - y) * a k) at hw
  linarith

/-! ### The converse: equivalent exponents give the same space -/

/-- If every weight of `b` is dominated by a weight of `a`, then `Λ_r(a) ⊆ Λ_r(b)`. -/
theorem submodule_le (h : ∀ t : Level r, ∃ t' : Level r, ∃ K : ℝ, ∀ j,
    Real.exp (t * b j) ≤ K * Real.exp (t' * a j)) :
    submodule 𝕜 r a ≤ submodule 𝕜 r b := fun x hx t ht => by
  obtain ⟨t', K, hK⟩ := h ⟨t, ht⟩
  refine ((hx t' t'.2).const_smul (K : 𝕜)).mono' fun j => ?_
  simp only [weight, Pi.smul_apply, smul_eq_mul, norm_mul, RCLike.norm_ofReal,
    abs_of_pos (Real.exp_pos _)]
  have hK0 : 0 ≤ K := nonneg_of_mul_nonneg_left ((Real.exp_pos _).le.trans (hK 0))
    (Real.exp_pos _)
  rw [abs_of_nonneg hK0, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hK j) (norm_nonneg _)

/-- The inclusion `Λ_r(a) → Λ_r(b)` as a linear map, when every weight of `b` is dominated by a
weight of `a`. -/
def inclusionₗ (h : ∀ t : Level r, ∃ t' : Level r, ∃ K : ℝ, ∀ j,
    Real.exp (t * b j) ≤ K * Real.exp (t' * a j)) :
    PowerSeriesSpace 𝕜 r a →ₗ[𝕜] PowerSeriesSpace 𝕜 r b where
  toFun x := mk x (submodule_le h (mem_submodule x))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion `Λ_r(a) → Λ_r(b)` when every weight of `b` is dominated by a weight of `a`. -/
def inclusion (h : ∀ t : Level r, ∃ t' : Level r, ∃ K : ℝ, ∀ j,
    Real.exp (t * b j) ≤ K * Real.exp (t' * a j)) :
    PowerSeriesSpace 𝕜 r a →L[𝕜] PowerSeriesSpace 𝕜 r b :=
  { inclusionₗ h with
    cont := by
      refine WithSeminorms.continuous_of_isBounded (withSeminorms 𝕜 r a) (withSeminorms 𝕜 r b)
        (inclusionₗ h) (Seminorm.IsBounded.of_real fun t => ?_)
      obtain ⟨t', K, hK⟩ := h t
      have hK0 : 0 ≤ K :=
        nonneg_of_mul_nonneg_left ((Real.exp_pos _).le.trans (hK 0)) (Real.exp_pos _)
      refine ⟨{t'}, K, fun x => ?_⟩
      rw [Finset.sup_singleton, seminorm_apply, seminorm_apply]
      calc ‖toL2 𝕜 r b t (inclusionₗ h x)‖ ≤ ‖(K : 𝕜) • toL2 𝕜 r a t' x‖ :=
            lp.norm_mono two_ne_zero fun j => by
              rw [norm_toL2_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul, norm_toL2_apply,
                RCLike.norm_ofReal, abs_of_nonneg hK0, ← mul_assoc]
              exact mul_le_mul_of_nonneg_right (hK j) (norm_nonneg _)
        _ = K * ‖toL2 𝕜 r a t' x‖ := by
            rw [lp.norm_const_smul two_ne_zero, RCLike.norm_ofReal, abs_of_nonneg hK0] }

@[simp] theorem coe_inclusion (h : ∀ t : Level r, ∃ t' : Level r, ∃ K : ℝ, ∀ j,
    Real.exp (t * b j) ≤ K * Real.exp (t' * a j)) (x : PowerSeriesSpace 𝕜 r a) :
    ⇑(inclusion h x) = ⇑x := rfl

/-- Mutually dominated weights give isomorphic spaces, by the identity on sequences. -/
def continuousLinearEquivOfDominated
    (hab : ∀ t : Level r, ∃ t' : Level r, ∃ K : ℝ, ∀ j,
      Real.exp (t * b j) ≤ K * Real.exp (t' * a j))
    (hba : ∀ t : Level r, ∃ t' : Level r, ∃ K : ℝ, ∀ j,
      Real.exp (t * a j) ≤ K * Real.exp (t' * b j)) :
    PowerSeriesSpace 𝕜 r a ≃L[𝕜] PowerSeriesSpace 𝕜 r b :=
  ContinuousLinearEquiv.ofContinuousLinearMap (inclusion hab) (inclusion hba)
    (ContinuousLinearMap.ext fun _ => ext rfl) (ContinuousLinearMap.ext fun _ => ext rfl)

/-- Infinite type: `b ≤ C * a + D` dominates every weight `exp (t * b)` by one of `a`. -/
theorem dominated_top (hb0 : 0 ≤ b) {C D : ℝ} (h : ∀ k, b k ≤ C * a k + D)
    (t : Level ⊤) : ∃ t' : Level ⊤, ∃ K : ℝ, ∀ j,
      Real.exp (t * b j) ≤ K * Real.exp (t' * a j) := by
  rcases le_or_gt (t : ℝ) 0 with ht | ht
  · refine ⟨⟨0, EReal.coe_lt_top 0⟩, 1, fun j => ?_⟩
    simp only [zero_mul, Real.exp_zero, mul_one, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg ht (hb0 j)
  · refine ⟨⟨t * C, EReal.coe_lt_top _⟩, Real.exp (t * D), fun j => ?_⟩
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [h j]

/-- Finite type: `a ≤ C * b + D` with `C > 0` dominates every weight `exp (t * b)`, `t < 0`, by
one of `a`. -/
theorem dominated_zero {C D : ℝ} (hC : 0 < C) (h : ∀ k, a k ≤ C * b k + D)
    (t : Level 0) : ∃ t' : Level 0, ∃ K : ℝ, ∀ j,
      Real.exp (t * b j) ≤ K * Real.exp (t' * a j) := by
  have ht : (t : ℝ) < 0 := by exact_mod_cast t.2
  refine ⟨⟨t / C, by exact_mod_cast div_neg_of_neg_of_pos ht hC⟩, Real.exp (-(t / C * D)),
    fun j => ?_⟩
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : t / C * a j ≥ t / C * (C * b j + D) :=
    mul_le_mul_of_nonpos_left (h j) (div_nonpos_of_nonpos_of_nonneg ht.le hC.le)
  have h2 : t / C * (C * b j + D) = t * b j + t / C * D := by field_simp
  linarith

/-- **Classification of power series spaces of infinite type.** For monotone nonnegative
exponents, `Λ_∞(a) ≅ Λ_∞(b)` if and only if each of `a`, `b` is bounded by a positive multiple
of the other plus a constant. -/
theorem nonempty_continuousLinearEquiv_iff_top (ha : Monotone a) (ha0 : 0 ≤ a)
    (hb : Monotone b) (hb0 : 0 ≤ b) :
    Nonempty (PowerSeriesSpace 𝕜 ⊤ a ≃L[𝕜] PowerSeriesSpace 𝕜 ⊤ b) ↔
      (∃ C > 0, ∃ D, ∀ k, a k ≤ C * b k + D) ∧ ∃ C > 0, ∃ D, ∀ k, b k ≤ C * a k + D := by
  refine ⟨fun ⟨T⟩ => ⟨exists_le_mul_add_of_continuousLinearEquiv ha ha0 hb hb0 T,
    exists_le_mul_add_of_continuousLinearEquiv hb hb0 ha ha0 T.symm⟩, ?_⟩
  rintro ⟨⟨C, -, D, h⟩, ⟨C', -, D', h'⟩⟩
  exact ⟨continuousLinearEquivOfDominated (dominated_top hb0 h')
    (dominated_top ha0 h)⟩

/-- **Classification of power series spaces of finite type.** For monotone nonnegative
exponents, `Λ_0(a) ≅ Λ_0(b)` if and only if each of `a`, `b` is bounded by a positive multiple
of the other plus a constant. -/
theorem nonempty_continuousLinearEquiv_iff_zero (ha : Monotone a) (ha0 : 0 ≤ a)
    (hb : Monotone b) (hb0 : 0 ≤ b) :
    Nonempty (PowerSeriesSpace 𝕜 0 a ≃L[𝕜] PowerSeriesSpace 𝕜 0 b) ↔
      (∃ C > 0, ∃ D, ∀ k, a k ≤ C * b k + D) ∧ ∃ C > 0, ∃ D, ∀ k, b k ≤ C * a k + D := by
  refine ⟨fun ⟨T⟩ => ⟨exists_le_mul_add_of_continuousLinearEquiv ha ha0 hb hb0 T,
    exists_le_mul_add_of_continuousLinearEquiv hb hb0 ha ha0 T.symm⟩, ?_⟩
  rintro ⟨⟨C, hC, D, h⟩, ⟨C', hC', D', h'⟩⟩
  exact ⟨continuousLinearEquivOfDominated (dominated_zero hC h) (dominated_zero hC' h')⟩

end PowerSeriesSpace

end
