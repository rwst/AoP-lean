/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Normed.Module.KolmogorovWidth
public import Mathlib.Analysis.Normed.Lp.lpSpace

import ForMathlib.Analysis.LocallyConvex.PowerSeriesSpace

/-!
# Unions of weighted `ℓ²` steps

For a weight `α : ι → ℝ` and `t > 0`, the step `H_t` is the space of families `x : ι → 𝕜` with
`(exp (t * α i) * x i)_i ∈ ℓ²`, and its unit ball `B_t` is given by
`∑ i, ‖exp (t * α i) * x i‖ ^ 2 ≤ 1`. The union `E(α) = ⋃_{t > 0} H_t` is, for an increasing
exponent sequence `a : ℕ → ℝ`, the strong dual `Λ_0(a)'` of the power series space of finite type
under the pairing `∑ j, x j * y j`, as a vector space together with its steps. This duality is
not formalized, and `E(α)` is not given a topology.

Instead we classify the linear bijections that, together with their inverses, map every step
ball `B_t` into a multiple of some step ball `B_s` (`IsStepBounded`). In the strong dual
`Λ_0(a)'` every bounded set is equicontinuous (Banach–Steinhaus), so it lies in the polar of a
neighbourhood of zero, which is a multiple of a step ball. Hence every isomorphism of these locally
convex spaces has this property. For monotone nonnegative exponents we prove: such a
bijection `E(a) → E(b)` exists if and only if each of `a`, `b` is bounded by a positive multiple
of the other plus a constant. The hard direction holds between any two subspaces of `ℕ → 𝕜` that
contain the unit vectors, and compares Kolmogorov widths of the step balls, as for
`PowerSeriesSpace`.

## Main definitions

* `DualPowerSeriesSpace.ball 𝕜 α t`: the unit ball `B_t`.
* `DualPowerSeriesSpace.step 𝕜 α t`, `DualPowerSeriesSpace.union 𝕜 α`: `H_t` and `⋃_{t > 0} H_t`.
* `DualPowerSeriesSpace.IsStepBounded α β T`: `T` maps every `B_t` into a multiple of some `B_s`.
* `DualPowerSeriesSpace.relabel e`: the relabelling `x ↦ x ∘ e` along `e : κ ≃ ι`.

## Main statements

* `DualPowerSeriesSpace.mem_union_iff`: for `α ≥ 0`, `x ∈ E(α)` iff `x ∈ H_t` for some `t > 0`.
* `DualPowerSeriesSpace.kolmogorovWidth_ballIn_le`,
  `DualPowerSeriesSpace.ofReal_le_kolmogorovWidth_ballIn`: in any subspace containing the unit
  vectors, the `k`-th width of `B_t` relative to `B_s` is `exp (-(t - s) * a k)`.
* `DualPowerSeriesSpace.exists_le_mul_add_of_isStepBounded`: the hard direction.
* `DualPowerSeriesSpace.exists_isStepBounded_equiv_iff`: the classification.
-/

@[expose] public section

open Set Submodule Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace DualPowerSeriesSpace

variable (𝕜 : Type*) [RCLike 𝕜] {ι κ : Type*} (α : ι → ℝ)

/-- The weighted family `i ↦ exp (t * α i) * x i`. -/
def weight (t : ℝ) (x : ι → 𝕜) : ι → 𝕜 := fun i => (Real.exp (t * α i) : 𝕜) * x i

/-- The unit ball `B_t`: `∑ i, ‖exp (t * α i) * x i‖ ^ 2 ≤ 1`, stated with finite partial
sums. -/
def ball (t : ℝ) : Set (ι → 𝕜) :=
  {x | ∀ s : Finset ι, ∑ i ∈ s, ‖weight 𝕜 α t x i‖ ^ 2 ≤ 1}

variable {𝕜 α} in
theorem weight_add (t : ℝ) (x y : ι → 𝕜) :
    weight 𝕜 α t (x + y) = weight 𝕜 α t x + weight 𝕜 α t y :=
  funext fun _ => mul_add _ _ _

variable {𝕜 α} in
theorem weight_smul (t : ℝ) (c : 𝕜) (x : ι → 𝕜) :
    weight 𝕜 α t (c • x) = c • weight 𝕜 α t x :=
  funext fun _ => mul_left_comm _ _ _

/-- The step `H_t`: the families with `i ↦ exp (t * α i) * x i` in `ℓ²`. -/
def step (t : ℝ) : Submodule 𝕜 (ι → 𝕜) where
  carrier := {x | Memℓp (weight 𝕜 α t x) 2}
  add_mem' hx hy := by
    rw [mem_ofPred_eq, weight_add]; exact hx.add hy
  zero_mem' := by
    rw [mem_ofPred_eq, show weight 𝕜 α t 0 = 0 from funext fun _ => mul_zero _]
    exact zero_memℓp
  smul_mem' c x hx := by
    rw [mem_ofPred_eq, weight_smul]; exact hx.const_smul c

/-- The union `E(α) = ⋃_{t > 0} H_t`, as the supremum of the steps. -/
def union : Submodule 𝕜 (ι → 𝕜) := ⨆ t : Ioi (0 : ℝ), step 𝕜 α t

variable {𝕜 α}

variable (α) in
/-- The unit ball `B_t`, inside a subspace `W`. -/
def ballIn (W : Submodule 𝕜 (ι → 𝕜)) (t : ℝ) : Set W := (↑) ⁻¹' ball 𝕜 α t

theorem norm_weight (t : ℝ) (x : ι → 𝕜) (i : ι) :
    ‖weight 𝕜 α t x i‖ = Real.exp (t * α i) * ‖x i‖ := by
  rw [weight, norm_mul, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]

/-- For nonnegative weights the steps decrease with `t`. -/
theorem step_mono (hα : 0 ≤ α) {s t : ℝ} (hst : s ≤ t) : step 𝕜 α t ≤ step 𝕜 α s :=
  fun x (hx : Memℓp _ 2) => show Memℓp _ 2 from hx.mono' fun i => by
    rw [norm_weight, norm_weight]
    gcongr
    exact hα i

/-- For nonnegative weights the step balls decrease with `t`. -/
theorem ball_anti (hα : 0 ≤ α) {s t : ℝ} (hst : s ≤ t) : ball 𝕜 α t ⊆ ball 𝕜 α s :=
  fun x hx u => (Finset.sum_le_sum fun i _ => by
    rw [norm_weight, norm_weight]
    gcongr
    exact hα i).trans (hx u)

/-- **The union is the set of families in some step**, for nonnegative weights. -/
theorem mem_union_iff (hα : 0 ≤ α) {x : ι → 𝕜} :
    x ∈ union 𝕜 α ↔ ∃ t > 0, Memℓp (weight 𝕜 α t x) 2 := by
  have : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, one_pos⟩⟩
  rw [union, mem_iSup_of_directed]
  · exact ⟨fun ⟨t, ht⟩ => ⟨t, t.2, ht⟩, fun ⟨t, ht, hx⟩ => ⟨⟨t, ht⟩, hx⟩⟩
  · exact fun s t => ⟨⟨min s t, lt_min s.2 t.2⟩, step_mono hα (min_le_left _ _),
      step_mono hα (min_le_right _ _)⟩

theorem step_le_step {β : ι → ℝ} {s t K : ℝ}
    (h : ∀ i, Real.exp (s * β i) ≤ K * Real.exp (t * α i)) : step 𝕜 α t ≤ step 𝕜 β s :=
  fun x (hx : Memℓp _ 2) => show Memℓp _ 2 from (hx.const_smul (K : 𝕜)).mono' fun i => by
    rw [Pi.smul_apply, norm_smul, norm_weight, norm_weight, RCLike.norm_ofReal, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right ((h i).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le)) (norm_nonneg _)

theorem smul_mem_ball {β : ι → ℝ} {s t K : ℝ} (hK : 0 < K)
    (h : ∀ i, Real.exp (s * β i) ≤ K * Real.exp (t * α i)) {x : ι → 𝕜} (hx : x ∈ ball 𝕜 α t) :
    (K⁻¹ : 𝕜) • x ∈ ball 𝕜 β s := fun u => (Finset.sum_le_sum fun i _ => by
    rw [norm_weight, norm_weight, Pi.smul_apply, norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_pos hK, ← mul_assoc]
    gcongr
    rw [mul_comm, inv_mul_le_iff₀ hK]
    exact h i).trans (hx u)

/-! ### Step-bounded maps -/

/-- `T` maps every step ball `B_t`, `t > 0`, into a multiple of some step ball `B_s`, `s > 0`. -/
def IsStepBounded {W : Submodule 𝕜 (ι → 𝕜)} {W' : Submodule 𝕜 (κ → 𝕜)} (α : ι → ℝ)
    (β : κ → ℝ) (T : W →ₗ[𝕜] W') : Prop :=
  ∀ t > 0, ∃ s > 0, ∃ C > (0 : ℝ), T '' ballIn α W t ⊆ (C : 𝕜) • ballIn β W' s

theorem IsStepBounded.comp {ι' : Type*} {W : Submodule 𝕜 (ι → 𝕜)} {W' : Submodule 𝕜 (κ → 𝕜)}
    {W'' : Submodule 𝕜 (ι' → 𝕜)} {β : κ → ℝ} {γ : ι' → ℝ} {T : W →ₗ[𝕜] W'}
    {S : W' →ₗ[𝕜] W''} (hT : IsStepBounded α β T) (hS : IsStepBounded β γ S) :
    IsStepBounded α γ (S ∘ₗ T) := fun t ht => by
  obtain ⟨s, hs, C₁, hC₁, h₁⟩ := hT t ht
  obtain ⟨u, hu, C₂, hC₂, h₂⟩ := hS s hs
  refine ⟨u, hu, C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  rw [LinearMap.coe_comp, Set.image_comp, RCLike.ofReal_mul, mul_smul]
  calc S '' (T '' ballIn α W t) ⊆ S '' ((C₁ : 𝕜) • ballIn β W' s) := image_mono h₁
    _ = (C₁ : 𝕜) • S '' ballIn β W' s := image_smul_set _ _ _
    _ ⊆ (C₁ : 𝕜) • (C₂ : 𝕜) • ballIn γ W'' u := smul_set_mono h₂

/-- A linear map that is the identity on families is step bounded when `β` is dominated by
`α`. -/
theorem isStepBounded_of_coe_eq {W W' : Submodule 𝕜 (ι → 𝕜)} {β : ι → ℝ} {C D : ℝ}
    (hC : 0 < C) (h : ∀ i, β i ≤ C * α i + D) (L : W →ₗ[𝕜] W')
    (hL : ∀ x, (L x : ι → 𝕜) = x) : IsStepBounded α β L := fun t ht => by
  have hK : 0 < Real.exp (t / C * D) := Real.exp_pos _
  have hexp : ∀ i, Real.exp (t / C * β i) ≤ Real.exp (t / C * D) * Real.exp (t * α i) :=
    fun i => by
      rw [← Real.exp_add, Real.exp_le_exp]
      have h1 : t / C * β i ≤ t / C * (C * α i + D) :=
        mul_le_mul_of_nonneg_left (h i) (div_pos ht hC).le
      have h2 : t / C * (C * α i + D) = t / C * D + t * α i := by field_simp; ring
      linarith
  refine ⟨t / C, div_pos ht hC, _, hK, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨((Real.exp (t / C * D))⁻¹ : 𝕜) • L x, ?_, ?_⟩
  · change ((((Real.exp (t / C * D))⁻¹ : 𝕜) • L x : W') : ι → 𝕜) ∈ ball 𝕜 β (t / C)
    rw [Submodule.coe_smul, hL]
    exact_mod_cast smul_mem_ball hK hexp hx
  · simp [smul_smul, RCLike.ofReal_ne_zero.mpr hK.ne']

/-- If `β ≤ C α + D` with `C > 0`, then `E(α) ⊆ E(β)`. -/
theorem union_le_union {β : ι → ℝ} {C D : ℝ} (hC : 0 < C) (h : ∀ i, β i ≤ C * α i + D) :
    union 𝕜 α ≤ union 𝕜 β :=
  iSup_le fun t => (step_le_step (K := Real.exp (t / C * D)) (s := t / C) fun i => by
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : t / C * β i ≤ t / C * (C * α i + D) :=
      mul_le_mul_of_nonneg_left (h i) (div_pos t.2 hC).le
    have h2 : t / C * (C * α i + D) = t / C * D + t * α i := by field_simp; ring
    linarith).trans
    (le_iSup (fun t : Ioi (0 : ℝ) => step 𝕜 β t) ⟨t / C, div_pos t.2 hC⟩)

/-! ### Widths of the step balls -/

section Widths

variable {a : ℕ → ℝ} {W : Submodule 𝕜 (ℕ → 𝕜)}

theorem sum_smul_single_apply (s : Finset ℕ) (c : ℕ → 𝕜) (j : ℕ) :
    (∑ i ∈ s, c i • Pi.single i (1 : 𝕜)) j = if j ∈ s then c j else 0 := by
  simp [Finset.sum_apply, Pi.single_apply]

/-- A subspace that contains the unit vectors contains every finitely supported family. -/
theorem mem_of_forall_lt_eq_zero (hW : ∀ i, Pi.single i (1 : 𝕜) ∈ W) {k : ℕ} {x : ℕ → 𝕜}
    (hx : ∀ j, k < j → x j = 0) : x ∈ W := by
  have : x = ∑ i ∈ Finset.range (k + 1), x i • Pi.single i (1 : 𝕜) := funext fun j => by
    rw [sum_smul_single_apply]
    split_ifs with h
    · rfl
    · exact hx j (by simp only [Finset.mem_range] at h; omega)
  rw [this]
  exact sum_mem fun i _ => smul_mem _ _ (hW i)

theorem two_toReal_pos : 0 < (2 : ℝ≥0∞).toReal := by norm_num

/-- **Upper bound.** The first `k` unit vectors approximate `B_t` within `exp (-(t - s) * a k)`
in `B_s`. -/
theorem kolmogorovWidth_ballIn_le (hW : ∀ i, Pi.single i (1 : 𝕜) ∈ W) (ha : Monotone a)
    {s t : ℝ} (hst : s < t) (k : ℕ) :
    kolmogorovWidth 𝕜 (ballIn a W t) (ballIn a W s) k ≤
      ENNReal.ofReal (Real.exp (-((t - s) * a k))) := by
  set c : ℝ := Real.exp (-((t - s) * a k)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  let v : Fin k → W := fun i => ⟨Pi.single (i : ℕ) 1, hW i⟩
  refine (kolmogorovWidth_le (c := (c : 𝕜)) v ?_).trans_eq
    (PowerSeriesSpace.enorm_ofReal_eq hc0)
  intro x hx
  let l : W := ∑ i ∈ Finset.range k, (x : ℕ → 𝕜) i • (⟨Pi.single i 1, hW i⟩ : W)
  have hl : l ∈ span 𝕜 (range v) := sum_mem fun i hi =>
    smul_mem _ _ (subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)
  have hxl : ∀ j, ((x - l : W) : ℕ → 𝕜) j = if j < k then 0 else (x : ℕ → 𝕜) j := fun j => by
    have : (l : ℕ → 𝕜) = ∑ i ∈ Finset.range k, (x : ℕ → 𝕜) i • Pi.single i (1 : 𝕜) := by
      simp [l]
    rw [Submodule.coe_sub, Pi.sub_apply, this, sum_smul_single_apply]
    simp only [Finset.mem_range]
    split_ifs <;> simp
  refine ⟨(c : 𝕜) • ((c : 𝕜)⁻¹ • (x - l)), ⟨(c : 𝕜)⁻¹ • (x - l), ?_, rfl⟩, l, hl, ?_⟩
  · intro u
    refine (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2).trans (hx u)
    rw [norm_weight, norm_weight, Submodule.coe_smul, Pi.smul_apply, norm_smul, norm_inv,
      RCLike.norm_ofReal, abs_of_pos hc0, hxl j]
    split_ifs with hj
    · simp only [norm_zero, mul_zero]
      positivity
    · rw [← mul_assoc]
      gcongr
      rw [hc, ← Real.exp_neg, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [ha (not_lt.mp hj), sub_pos.mpr hst]
  · simp [smul_smul, RCLike.ofReal_ne_zero.mpr hc0.ne']

/-- **Lower bound.** No `k` vectors approximate `B_t` better than `exp (-(t - s) * a k)` in
`B_s`. -/
theorem ofReal_le_kolmogorovWidth_ballIn (hW : ∀ i, Pi.single i (1 : 𝕜) ∈ W) (ha : Monotone a)
    {s t : ℝ} (hst : s < t) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-((t - s) * a k))) ≤
      kolmogorovWidth 𝕜 (ballIn a W t) (ballIn a W s) k := by
  set c : ℝ := Real.exp (-((t - s) * a k)) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hsq : ∀ r : ℝ, r ^ (2 : ℝ≥0∞).toReal = r ^ 2 := fun r => by
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
  -- the weighted coordinates `0, …, k`, as a vector of `ℓ²`
  let trunc : (ℕ → 𝕜) → ℕ → 𝕜 := fun x j => if j ≤ k then weight 𝕜 a s x j else 0
  have htrunc : ∀ x, Memℓp (trunc x) 2 := fun x =>
    (memℓp_zero ((Set.finite_Iic k).subset fun j hj => by
      by_contra h
      rw [Set.mem_Iic] at h
      exact hj (by simp [trunc, h]))).of_exponent_ge bot_le
  let P : W →ₗ[𝕜] lp (fun _ : ℕ => 𝕜) 2 :=
    { toFun := fun x => ⟨trunc x, htrunc x⟩
      map_add' := fun x y => lp.ext (funext fun j => by
        simp only [trunc, Submodule.coe_add, weight_add, lp.coeFn_add, Pi.add_apply]
        split_ifs <;> simp)
      map_smul' := fun c x => lp.ext (funext fun j => by
        simp only [trunc, Submodule.coe_smul, weight_smul, lp.coeFn_smul, Pi.smul_apply,
          RingHom.id_apply]
        split_ifs <;> simp) }
  have hP : ∀ x j, (P x : ℕ → 𝕜) j = trunc x j := fun _ _ => rfl
  refine le_trans ?_ ((kolmogorovWidth_anti_right (A := P '' ballIn a W t)
    (B' := closedBall 0 1) ?_ k).trans (kolmogorovWidth_image_le P _ _ k))
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
    let x : ℕ → 𝕜 := fun j => (c * Real.exp (-(s * a j)) : ℝ) * y j
    have hxW : x ∈ W := mem_of_forall_lt_eq_zero hW (k := k) fun j hj => by
      simp [x, hy0 j hj]
    refine ⟨⟨x, hxW⟩, fun u => ?_, lp.ext (funext fun j => ?_)⟩
    · have hy2 := lp.sum_rpow_le_norm_rpow two_toReal_pos y u
      simp only [hsq] at hy2
      refine (Finset.sum_le_sum fun j _ => ?_).trans (hy2.trans ?_)
      · rw [norm_weight]
        simp only [x, norm_mul, RCLike.norm_ofReal, abs_of_pos (by positivity : 0 < c *
          Real.exp (-(s * a j)))]
        rcases le_or_gt j k with hj | hj
        · rw [← mul_assoc, ← mul_assoc]
          gcongr
          refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (le_refl _)
          rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
          nlinarith [ha hj, sub_pos.mpr hst]
        · simp [hy0 j hj]
      · nlinarith [norm_nonneg y]
    · rw [hP, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      simp only [trunc]
      split_ifs with hj
      · simp only [weight, x]
        rw [← mul_assoc, ← RCLike.ofReal_mul, mul_left_comm, ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]
      · simp [hy0 j (not_le.mp hj)]
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_closedBall_zero_iff]
    refine lp.norm_le_of_forall_sum_le two_toReal_pos zero_le_one fun u => ?_
    simp only [hsq, one_pow]
    refine (Finset.sum_le_sum fun j _ => ?_).trans (hx u)
    rw [hP]
    simp only [trunc]
    split_ifs
    · exact le_rfl
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity

end Widths

/-! ### Classification -/

variable {a b : ℕ → ℝ}

/-- **Step-bounded bijections have equivalent exponents**, one half: if a linear bijection
`T : W → W'` between subspaces of `ℕ → 𝕜` containing the unit vectors maps, with its inverse,
every step ball into a multiple of some step ball, then `a k ≤ C * b k + D` for some `C > 0` and
`D`. -/
theorem exists_le_mul_add_of_isStepBounded (ha : Monotone a) (hb : Monotone b)
    (hb0 : 0 ≤ b) {W W' : Submodule 𝕜 (ℕ → 𝕜)} (hW : ∀ i, Pi.single i (1 : 𝕜) ∈ W)
    (hW' : ∀ i, Pi.single i (1 : 𝕜) ∈ W') (T : W ≃ₗ[𝕜] W')
    (hT : IsStepBounded a b T.toLinearMap) (hT' : IsStepBounded b a T.symm.toLinearMap) :
    ∃ C > 0, ∃ D, ∀ k, a k ≤ C * b k + D := by
  -- `T⁻¹` maps `B_1` into a multiple of some `B_σ`
  obtain ⟨σ, hσ, C₂, hC₂, h₂⟩ := hT' 1 one_pos
  -- `T` maps `B_{σ/2}` into a multiple of some `B_γ`
  obtain ⟨γ, -, C₁, hC₁, h₁⟩ := hT (σ / 2) (by positivity)
  set γ' := min γ (1 / 2)
  have hγ' : γ' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have i₁ : T.toLinearMap '' ballIn a W (σ / 2) ⊆ (C₁ : 𝕜) • ballIn b W' γ' :=
    h₁.trans (smul_set_mono fun _ hx => ball_anti hb0 (min_le_left _ _) hx)
  have i₂ : ballIn b W' 1 ⊆ (C₂ : 𝕜) • T.toLinearMap '' ballIn a W σ := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := h₂ ⟨z, hz, rfl⟩
    refine ⟨T w, ⟨w, hw, rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_coe] at hwz ⊢
    rw [← map_smul, hwz, LinearEquiv.apply_symm_apply]
  have hσ2 : σ / 2 < σ := by linarith
  refine ⟨(1 - γ') / (σ - σ / 2), div_pos (sub_pos.mpr hγ') (sub_pos.mpr hσ2),
    Real.log (C₁ * C₂) / (σ - σ / 2), fun k => ?_⟩
  have hw := (ofReal_le_kolmogorovWidth_ballIn (𝕜 := 𝕜) hW' hb hγ' k).trans
    ((kolmogorovWidth_le_mul_of_subset T.toLinearMap (RCLike.ofReal_ne_zero.mpr hC₁.ne')
      (RCLike.ofReal_ne_zero.mpr hC₂.ne') i₁ i₂ k).trans
      (mul_le_mul_of_nonneg_left (kolmogorovWidth_ballIn_le hW ha hσ2 k) (by positivity)))
  rw [PowerSeriesSpace.enorm_ofReal_eq hC₁, PowerSeriesSpace.enorm_ofReal_eq hC₂,
    ← ENNReal.ofReal_mul hC₁.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity), ← Real.exp_log (mul_pos hC₁ hC₂),
    ← Real.exp_add, Real.exp_le_exp] at hw
  have hxy : 0 < σ - σ / 2 := sub_pos.mpr hσ2
  rw [div_mul_eq_mul_div, ← add_div, le_div_iff₀ hxy]
  linarith

/-- The unit vectors lie in `E(a)`. -/
theorem single_mem_union (i : ℕ) : Pi.single i (1 : 𝕜) ∈ union 𝕜 a :=
  le_iSup (fun t : Ioi (0 : ℝ) => step 𝕜 a t) ⟨1, one_pos⟩ <|
    show Memℓp _ 2 from (memℓp_zero ((Set.finite_singleton i).subset fun j hj => by
      by_contra h
      exact hj (by simp [weight, Pi.single_eq_of_ne h]))).of_exponent_ge bot_le

/-- **Classification of the unions of steps.** For monotone nonnegative exponents there is a
linear bijection `E(a) → E(b)` that, with its inverse, maps every step ball into a multiple of
some step ball, if and only if each of `a`, `b` is bounded by a positive multiple of the other
plus a constant. -/
theorem exists_isStepBounded_equiv_iff (ha : Monotone a) (ha0 : 0 ≤ a) (hb : Monotone b)
    (hb0 : 0 ≤ b) :
    (∃ T : union 𝕜 a ≃ₗ[𝕜] union 𝕜 b,
      IsStepBounded a b T.toLinearMap ∧ IsStepBounded b a T.symm.toLinearMap) ↔
      (∃ C > 0, ∃ D, ∀ k, a k ≤ C * b k + D) ∧ ∃ C > 0, ∃ D, ∀ k, b k ≤ C * a k + D := by
  constructor
  · rintro ⟨T, hT, hT'⟩
    refine ⟨exists_le_mul_add_of_isStepBounded ha hb hb0 single_mem_union single_mem_union
      T hT hT', exists_le_mul_add_of_isStepBounded hb ha ha0 single_mem_union
      single_mem_union T.symm hT' ?_⟩
    rwa [LinearEquiv.symm_symm]
  · rintro ⟨⟨C, hC, D, h⟩, ⟨C', hC', D', h'⟩⟩
    have heq : union 𝕜 a = union 𝕜 b := le_antisymm (union_le_union hC' h') (union_le_union hC h)
    refine ⟨LinearEquiv.ofEq _ _ heq,
      isStepBounded_of_coe_eq hC' h' _ (LinearEquiv.coe_ofEq_apply heq), ?_⟩
    rw [LinearEquiv.ofEq_symm]
    exact isStepBounded_of_coe_eq hC h _ (LinearEquiv.coe_ofEq_apply heq.symm)

/-! ### Relabelling -/

variable (α) in
theorem comp_mem_ball_iff (e : κ ≃ ι) {t : ℝ} {x : ι → 𝕜} :
    x ∘ e ∈ ball 𝕜 (α ∘ e) t ↔ x ∈ ball 𝕜 α t := by
  constructor
  · intro hx u
    have := hx (u.map e.symm.toEmbedding)
    simpa only [Finset.sum_map, Equiv.coe_toEmbedding, weight, Function.comp_apply,
      Equiv.apply_symm_apply] using this
  · intro hx u
    have := hx (u.map e.toEmbedding)
    rw [Finset.sum_map] at this
    exact this

theorem memℓp_comp_equiv_iff (e : κ ≃ ι) {x : ι → 𝕜} : Memℓp (x ∘ e) 2 ↔ Memℓp x 2 := by
  simp only [memℓp_gen_iff two_toReal_pos]
  exact e.summable_iff (f := fun i => ‖x i‖ ^ (2 : ℝ≥0∞).toReal)

variable (α) in
theorem map_union (e : κ ≃ ι) :
    (union 𝕜 α).map (LinearEquiv.funCongrLeft 𝕜 𝕜 e : (ι → 𝕜) →ₗ[𝕜] κ → 𝕜) =
      union 𝕜 (α ∘ e) := by
  change (⨆ t : Ioi (0 : ℝ), step 𝕜 α t).map _ = ⨆ t : Ioi (0 : ℝ), step 𝕜 (α ∘ e) t
  rw [Submodule.map_iSup]
  refine iSup_congr fun t => ?_
  ext x
  rw [mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change Memℓp (weight 𝕜 α t y ∘ e) 2
    exact (memℓp_comp_equiv_iff e).mpr hy
  · intro hx
    refine ⟨x ∘ e.symm, ?_, funext fun j => ?_⟩
    · change Memℓp (weight 𝕜 α t (x ∘ e.symm)) 2
      rw [← memℓp_comp_equiv_iff e]
      have : weight 𝕜 α t (x ∘ e.symm) ∘ e = weight 𝕜 (α ∘ e) t x := funext fun j => by
        simp only [Function.comp_apply, weight, Equiv.symm_apply_apply]
      rw [this]
      exact hx
    · rw [LinearEquiv.coe_coe, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      exact congrArg x (e.symm_apply_apply j)

variable (𝕜 α) in
/-- The relabelling `x ↦ x ∘ e` from `E(α)` onto `E(α ∘ e)`. -/
def relabel (e : κ ≃ ι) : union 𝕜 α ≃ₗ[𝕜] union 𝕜 (α ∘ e) :=
  ((LinearEquiv.funCongrLeft 𝕜 𝕜 e).submoduleMap (union 𝕜 α)).trans
    (LinearEquiv.ofEq _ _ (map_union α e))

theorem coe_relabel (e : κ ≃ ι) (x : union 𝕜 α) : (relabel 𝕜 α e x : κ → 𝕜) = x ∘ e := rfl

/-- The relabelling maps `B_t` into `B_t`. -/
theorem isStepBounded_relabel (e : κ ≃ ι) :
    IsStepBounded α (α ∘ e) (relabel 𝕜 α e).toLinearMap := fun t ht => by
  refine ⟨t, ht, 1, one_pos, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨relabel 𝕜 α e x, ?_, by simp⟩
  change (relabel 𝕜 α e x : κ → 𝕜) ∈ ball 𝕜 (α ∘ e) t
  rw [coe_relabel]
  exact (comp_mem_ball_iff α e).mpr hx

/-- The inverse relabelling maps `B_t` into `B_t`. -/
theorem isStepBounded_relabel_symm (e : κ ≃ ι) :
    IsStepBounded (α ∘ e) α (relabel 𝕜 α e).symm.toLinearMap := fun t ht => by
  refine ⟨t, ht, 1, one_pos, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨(relabel 𝕜 α e).symm y, ?_, by simp⟩
  have : (((relabel 𝕜 α e).symm y : union 𝕜 α) : ι → 𝕜) ∘ e = y := by
    rw [← coe_relabel, LinearEquiv.apply_symm_apply]
  change (((relabel 𝕜 α e).symm y : union 𝕜 α) : ι → 𝕜) ∈ ball 𝕜 α t
  rw [← comp_mem_ball_iff α e, this]
  exact hy

end DualPowerSeriesSpace

end
