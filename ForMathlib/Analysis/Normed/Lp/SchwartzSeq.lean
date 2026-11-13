/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.l2Diagonal
public import Mathlib.Analysis.PSeries

/-!
# The space of Schwartz sequences

The Schwartz sequence space `S(ℕ, 𝕜)` consists of the rapidly decreasing sequences: those
`x ∈ ℓ²(ℕ, 𝕜)` with `((n + 1)ᵏ xₙ)ₙ ∈ ℓ²` for every `k`. Its topology is given by the seminorms
`p k x = ‖((n + 1)ᵏ xₙ)ₙ‖`, the `ℓ²` norms of the weighted sequences. Under the Hermite basis it
is the Schwartz space of the real line.

The sup-type seminorms `supₙ (n + 1)ᵏ |xₙ|` define the same space and the same topology:
`(n + 1)ᵏ |xₙ| ≤ p k x`, and `p k x ≤ √S · supₙ (n + 1)ᵏ⁺¹ |xₙ|` with `S = ∑ₙ (n + 1)⁻²`.

## Main definitions

* `SchwartzSeq.submodule 𝕜`: the rapidly decreasing sequences, as a submodule of `ℓ²(ℕ, 𝕜)`;
* `SchwartzSeq 𝕜`: the same sequences, as a type with the topology of the seminorms;
* `SchwartzSeq.toLp`: the inclusion into `ℓ²(ℕ, 𝕜)`;
* `SchwartzSeq.seminormFamily 𝕜`: the seminorms `p k`;
* `SchwartzSeq.mkCLM`: a linear map into `ℓ²` whose weighted values are bounded by seminorms, as
  a continuous linear endomorphism of `S(ℕ, 𝕜)`.

## Main results

* `SchwartzSeq.withSeminorms`: the topology is that of the seminorms;
* `SchwartzSeq.continuous_toLp`: the inclusion into `ℓ²` is continuous;
* `SchwartzSeq.mem_submodule_iff`: a sequence is rapidly decreasing iff every
  `(n + 1)ᵏ |xₙ|` is bounded;
* `SchwartzSeq.tendsto_iff`: convergence in `S(ℕ, 𝕜)` is uniform convergence of every
  `(n + 1)ᵏ xₙ`;
* `SchwartzSeq.not_tendsto_of_tendsto_atTop`: a sequence along which a seminorm diverges has no
  limit;
* `SchwartzSeq.continuous_inner_apply`: for a continuous linear endomorphism `T`, the expectation
  `x ↦ ⟪x, T x⟫` is continuous.
-/

open Filter Topology
open scoped lp NNReal InnerProductSpace

@[expose] public noncomputable section

namespace SchwartzSeq

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The weight `(n + 1)ᵏ`. -/
abbrev weightSeq (k : ℕ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ k

/-- The rapidly decreasing sequences, `((n + 1)ᵏ xₙ)ₙ ∈ ℓ²` for every `k`, as a submodule of
`ℓ²(ℕ, 𝕜)`. -/
def submodule : Submodule 𝕜 ℓ²(ℕ, 𝕜) := ⨅ k : ℕ, lp.diagonalDomain (weightSeq k)

/-- The Schwartz sequence space `S(ℕ, 𝕜)`, with the topology of the seminorms
`‖((n + 1)ᵏ xₙ)ₙ‖`. -/
def _root_.SchwartzSeq : Type _ := submodule 𝕜

instance : AddCommGroup (SchwartzSeq 𝕜) := inferInstanceAs (AddCommGroup (submodule 𝕜))

instance : Module 𝕜 (SchwartzSeq 𝕜) := inferInstanceAs (Module 𝕜 (submodule 𝕜))

variable {𝕜}

/-- The inclusion `S(ℕ, 𝕜) → ℓ²(ℕ, 𝕜)`. -/
def toLp : SchwartzSeq 𝕜 →ₗ[𝕜] ℓ²(ℕ, 𝕜) := (submodule 𝕜).subtype

/-- The element of `S(ℕ, 𝕜)` given by a rapidly decreasing sequence. -/
def mk (x : ℓ²(ℕ, 𝕜)) (hx : x ∈ submodule 𝕜) : SchwartzSeq 𝕜 := ⟨x, hx⟩

@[simp]
lemma toLp_mk (x : ℓ²(ℕ, 𝕜)) (hx : x ∈ submodule 𝕜) : toLp (mk x hx) = x :=
  rfl

lemma toLp_mem (x : SchwartzSeq 𝕜) : toLp x ∈ submodule 𝕜 :=
  Subtype.prop (p := (· ∈ submodule 𝕜)) x

lemma toLp_injective : Function.Injective (toLp : SchwartzSeq 𝕜 → ℓ²(ℕ, 𝕜)) :=
  Subtype.val_injective (p := (· ∈ submodule 𝕜))

@[ext]
lemma ext {x y : SchwartzSeq 𝕜} (h : ∀ n, toLp x n = toLp y n) : x = y :=
  toLp_injective (lp.ext (funext h))

lemma mem_diagonalDomain {x : ℓ²(ℕ, 𝕜)} (hx : x ∈ submodule 𝕜) (k : ℕ) :
    x ∈ lp.diagonalDomain (weightSeq k) :=
  Submodule.mem_iInf _ |>.1 hx k

/-- The weighted sequence `((n + 1)ᵏ xₙ)ₙ ∈ ℓ²`. -/
def weight (k : ℕ) : SchwartzSeq 𝕜 →ₗ[𝕜] ℓ²(ℕ, 𝕜) :=
  (lp.diagonal (𝕜 := 𝕜) (weightSeq k)).toFun ∘ₗ
    (Submodule.inclusion (iInf_le (fun k => lp.diagonalDomain (𝕜 := 𝕜) (weightSeq k)) k) :
      submodule 𝕜 →ₗ[𝕜] lp.diagonalDomain (𝕜 := 𝕜) (weightSeq k))

lemma norm_weight_apply (k : ℕ) (x : SchwartzSeq 𝕜) (n : ℕ) :
    ‖weight k x n‖ = ((n : ℝ) + 1) ^ k * ‖toLp x n‖ := by
  change ‖((weightSeq k n : ℝ) : 𝕜) * toLp x n‖ = _
  rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]

lemma weight_zero (x : SchwartzSeq 𝕜) : weight 0 x = toLp x :=
  lp.ext <| funext fun n => by
    change ((weightSeq 0 n : ℝ) : 𝕜) * toLp x n = toLp x n
    simp

variable (𝕜) in
/-- The seminorms `p k x = ‖((n + 1)ᵏ xₙ)ₙ‖` of `S(ℕ, 𝕜)`. -/
def seminormFamily : SeminormFamily 𝕜 (SchwartzSeq 𝕜) ℕ :=
  fun k => (normSeminorm 𝕜 ℓ²(ℕ, 𝕜)).comp (weight k)

lemma seminormFamily_apply (k : ℕ) (x : SchwartzSeq 𝕜) :
    seminormFamily 𝕜 k x = ‖weight k x‖ :=
  rfl

lemma seminormFamily_zero (x : SchwartzSeq 𝕜) : seminormFamily 𝕜 0 x = ‖toLp x‖ := by
  rw [seminormFamily_apply, weight_zero]

instance : TopologicalSpace (SchwartzSeq 𝕜) := (seminormFamily 𝕜).moduleFilterBasis.topology'

variable (𝕜) in
theorem withSeminorms : WithSeminorms (seminormFamily 𝕜) := ⟨rfl⟩

instance : IsTopologicalAddGroup (SchwartzSeq 𝕜) :=
  (seminormFamily 𝕜).addGroupFilterBasis.isTopologicalAddGroup

instance : ContinuousSMul 𝕜 (SchwartzSeq 𝕜) := (withSeminorms 𝕜).continuousSMul

/-- The inclusion `S(ℕ, 𝕜) → ℓ²(ℕ, 𝕜)` is continuous. -/
theorem continuous_toLp : Continuous (toLp : SchwartzSeq 𝕜 → ℓ²(ℕ, 𝕜)) := by
  refine WithSeminorms.continuous_normedSpace_rng _ (withSeminorms 𝕜) toLp ⟨{0}, 1, fun x => ?_⟩
  simp [seminormFamily_zero]

/-- `(n + 1)ᵏ |xₙ| ≤ p k x`. -/
theorem mul_norm_le_seminorm (k : ℕ) (x : SchwartzSeq 𝕜) (n : ℕ) :
    ((n : ℝ) + 1) ^ k * ‖toLp x n‖ ≤ seminormFamily 𝕜 k x := by
  rw [← norm_weight_apply, seminormFamily_apply]
  exact lp.norm_apply_le_norm (by norm_num) _ n

/-- `S = ∑ₙ (n + 1)⁻²` is finite. -/
lemma summable_inv_sq : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff (G := ℝ) (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).2
    (Real.summable_one_div_nat_pow.2 one_lt_two)
  simpa only [Nat.cast_add, Nat.cast_one] using this

/-- The constant `√S`, `S = ∑ₙ (n + 1)⁻²`, comparing the `ℓ²` and the sup seminorms. -/
def sqrtSum : ℝ := √(∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2)

lemma sqrtSum_nonneg : 0 ≤ sqrtSum := Real.sqrt_nonneg _

/-- If `(n + 1)ᵏ⁺¹ |xₙ| ≤ M` for all `n`, then `‖((n + 1)ᵏ xₙ)ₙ‖ ≤ M √S`. -/
theorem norm_le_of_bound {k : ℕ} {x : ℓ²(ℕ, 𝕜)} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ n : ℕ, ((n : ℝ) + 1) ^ (k + 1) * ‖x n‖ ≤ M) (w : ℓ²(ℕ, 𝕜))
    (hw : ∀ n, ‖w n‖ = ((n : ℝ) + 1) ^ k * ‖x n‖) :
    ‖w‖ ≤ M * sqrtSum := by
  have hterm (n : ℕ) : ‖w n‖ ^ 2 ≤ M ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : ‖w n‖ * ((n : ℝ) + 1) ≤ M := by
      rw [hw, mul_assoc, mul_comm ‖x n‖, ← mul_assoc, ← pow_succ]
      exact h n
    have h2 : ‖w n‖ ≤ M / ((n : ℝ) + 1) := (le_div_iff₀ hn).2 h1
    calc ‖w n‖ ^ 2 ≤ (M / ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = M ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by rw [div_pow, mul_one_div]
  have hsw : Summable fun n => ‖w n‖ ^ 2 := by
    simpa [Real.rpow_two] using (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp w)
  refine lp.norm_le_of_tsum_le (by norm_num) (by unfold sqrtSum; positivity) ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  calc ∑' n, ‖w n‖ ^ 2 ≤ ∑' n : ℕ, M ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) :=
        hsw.tsum_le_tsum hterm (summable_inv_sq.mul_left _)
    _ = (M * sqrtSum) ^ 2 := by
        rw [tsum_mul_left, mul_pow, sqrtSum, Real.sq_sqrt (tsum_nonneg fun n => by positivity)]

/-- A sequence is rapidly decreasing iff every `(n + 1)ᵏ |xₙ|` is bounded. -/
theorem mem_submodule_iff (x : ℓ²(ℕ, 𝕜)) :
    x ∈ submodule 𝕜 ↔ ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) ^ k * ‖x n‖ ≤ C := by
  constructor
  · intro hx k
    exact ⟨seminormFamily 𝕜 k (mk x hx), mul_norm_le_seminorm k (mk x hx)⟩
  · intro h
    refine Submodule.mem_iInf _ |>.2 fun k => ?_
    obtain ⟨C, hC⟩ := h (k + 1)
    have hC0 : 0 ≤ C := (by positivity : (0 : ℝ) ≤ ((0 : ℕ) + 1) ^ (k + 1) * ‖x 0‖).trans (hC 0)
    -- `‖(n + 1)ᵏ xₙ‖ ≤ C / (n + 1)`, and `(C / (n + 1))ₙ ∈ ℓ²`.
    have hg : Memℓp (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) 2 := by
      rw [memℓp_gen_iff (by norm_num)]
      simpa [Real.rpow_two, mul_pow, abs_of_nonneg hC0, div_pow] using
        summable_inv_sq.mul_left (C ^ 2)
    refine hg.mono' fun n => ?_
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    change ‖((weightSeq k n : ℝ) : 𝕜) * x n‖ ≤ _
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_nonneg (by positivity), mul_one_div, le_div_iff₀ hn, mul_right_comm, ← pow_succ]
    exact hC n

/-- **Convergence in `S(ℕ, 𝕜)`** is uniform convergence of every `(n + 1)ᵏ xₙ`. -/
theorem tendsto_iff {α : Type*} {l : Filter α} {u : α → SchwartzSeq 𝕜} {y : SchwartzSeq 𝕜} :
    Tendsto u l (𝓝 y) ↔ ∀ k : ℕ, ∀ ε > 0, ∀ᶠ j in l, ∀ n : ℕ,
      ((n : ℝ) + 1) ^ k * ‖toLp (u j - y) n‖ ≤ ε := by
  rw [(withSeminorms 𝕜).tendsto_nhds]
  constructor
  · intro h k ε hε
    filter_upwards [h k ε hε] with j hj n
    exact (mul_norm_le_seminorm k _ n).trans hj.le
  · intro h k ε hε
    have hδ : 0 < ε / (sqrtSum + 1) := div_pos hε (by linarith [sqrtSum_nonneg])
    filter_upwards [h (k + 1) _ hδ] with j hj
    calc seminormFamily 𝕜 k (u j - y)
        ≤ ε / (sqrtSum + 1) * sqrtSum :=
          norm_le_of_bound hδ.le hj _ (norm_weight_apply k (u j - y))
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith [sqrtSum_nonneg])]
          nlinarith

/-- A sequence along which a seminorm of `S(ℕ, 𝕜)` diverges has no limit in `S(ℕ, 𝕜)`. -/
theorem not_tendsto_of_tendsto_atTop {α : Type*} {l : Filter α} [l.NeBot]
    {u : α → SchwartzSeq 𝕜} {k : ℕ} (hu : Tendsto (fun j => seminormFamily 𝕜 k (u j)) l atTop)
    (y : SchwartzSeq 𝕜) : ¬ Tendsto u l (𝓝 y) := fun h =>
  not_tendsto_nhds_of_tendsto_atTop hu _ (((withSeminorms 𝕜).continuous_seminorm k).tendsto y
    |>.comp h)

/-- The finitely supported sequences are rapidly decreasing. -/
lemma single_mem_submodule (i : ℕ) (c : 𝕜) : lp.single 2 i c ∈ submodule 𝕜 :=
  Submodule.mem_iInf _ |>.2 fun _ => lp.single_mem_diagonalDomain _ i c

/-- A sequence dominated by a weighted Schwartz sequence `((n + 1)ᵏ xₙ)ₙ` lies in `ℓ²`. -/
theorem memℓp_of_norm_le {f : ℕ → 𝕜} (k : ℕ) (x : SchwartzSeq 𝕜)
    (h : ∀ n, ‖f n‖ ≤ ((n : ℝ) + 1) ^ k * ‖toLp x n‖) : Memℓp f 2 :=
  (lp.memℓp (weight k x)).mono' fun n => (h n).trans (norm_weight_apply k x n).ge

/-! ### Continuous linear endomorphisms -/

section mkCLM

variable (f : SchwartzSeq 𝕜 →ₗ[𝕜] ℓ²(ℕ, 𝕜))
  (hf : ∀ k : ℕ, ∃ m : ℕ, ∃ C : ℝ, ∀ x : SchwartzSeq 𝕜, ∀ n : ℕ,
    ((n : ℝ) + 1) ^ k * ‖f x n‖ ≤ C * seminormFamily 𝕜 m x)

include hf in
lemma mem_submodule_of_bound (x : SchwartzSeq 𝕜) : f x ∈ submodule 𝕜 :=
  (mem_submodule_iff _).2 fun k => by
    obtain ⟨m, C, hC⟩ := hf k
    exact ⟨C * seminormFamily 𝕜 m x, hC x⟩

/-- The linear map underlying `mkCLM`. -/
def mkLM : SchwartzSeq 𝕜 →ₗ[𝕜] SchwartzSeq 𝕜 :=
  f.codRestrict (submodule 𝕜) (mem_submodule_of_bound f hf)

theorem continuous_mkLM : Continuous (mkLM f hf) := by
  refine continuous_iff_continuousAt.2 fun g => tendsto_iff.2 fun k ε hε => ?_
  obtain ⟨m, C, hC⟩ := hf k
  have hC1 : 0 < |C| + 1 := by positivity
  filter_upwards [((withSeminorms 𝕜).tendsto_nhds id g).1 tendsto_id m _
    (div_pos hε hC1)] with y hy n
  rw [← map_sub]
  change ((n : ℝ) + 1) ^ k * ‖f (y - g) n‖ ≤ ε
  have hp := apply_nonneg (seminormFamily 𝕜 m) (y - g)
  calc ((n : ℝ) + 1) ^ k * ‖f (y - g) n‖ ≤ C * seminormFamily 𝕜 m (y - g) := hC _ n
    _ ≤ (|C| + 1) * seminormFamily 𝕜 m (y - g) :=
        mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) hp
    _ ≤ (|C| + 1) * (ε / (|C| + 1)) := mul_le_mul_of_nonneg_left hy.le hC1.le
    _ = ε := mul_div_cancel₀ ε hC1.ne'

/-- A linear map `f : S(ℕ, 𝕜) → ℓ²(ℕ, 𝕜)` whose weighted values are bounded by seminorms,
`(n + 1)ᵏ |(f x)ₙ| ≤ C p m x`, as a continuous linear endomorphism of `S(ℕ, 𝕜)`. -/
def mkCLM : SchwartzSeq 𝕜 →L[𝕜] SchwartzSeq 𝕜 := ⟨mkLM f hf, continuous_mkLM f hf⟩

@[simp]
theorem toLp_mkCLM (x : SchwartzSeq 𝕜) : toLp (mkCLM f hf x) = f x :=
  rfl

end mkCLM

/-- **Continuous expectations.** For a continuous linear endomorphism `T` of `S(ℕ, 𝕜)`, the
expectation `x ↦ ⟪x, T x⟫` is continuous on `S(ℕ, 𝕜)`. -/
theorem continuous_inner_apply (T : SchwartzSeq 𝕜 →L[𝕜] SchwartzSeq 𝕜) :
    Continuous fun x => ⟪toLp x, toLp (T x)⟫_𝕜 :=
  continuous_toLp.inner (continuous_toLp.comp T.continuous)

end SchwartzSeq
