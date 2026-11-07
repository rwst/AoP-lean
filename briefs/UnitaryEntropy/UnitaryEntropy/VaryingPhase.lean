/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import UnitaryEntropy.MomentumPropagator

/-!
# A continuously varying boundary phase: the forward Hamiltonian at the Hölder-½ threshold

This continues `UnitaryEntropy.MomentumPropagator`, with `ħ = 1`. The switched example of
`UnitaryEntropy.MomentumExtensions` differentiates `U(t)` from both sides at `t₀`; each one-sided
derivative alone has a self-adjoint generator. The evolution only runs forward, so the
Hamiltonian at `t₀` can be defined from the right derivative alone. Here the boundary phase
varies continuously, `H(t) = H_{α(t)}`, and the forward Hamiltonian is still not self-adjoint
when `α` is only Hölder-½ continuous.

## The propagator

A point that wraps around at the time `s` picks up the phase `e^{-iα(s)}`. So `U(t₁, t₀)`,
`t₀ ≤ t₁`, translates by `t₁ - t₀`, times `e^{-i Σⱼ α(sⱼ)}` over the wrap-around times `sⱼ` of
the point (`phasePropagator`, `crossPhase`). It is unitary, `U(t, t) = 1` and
`U(t₂, t₁) U(t₁, t₀) = U(t₂, t₀)`; for constant `α = γ` it is `e^{-i(t₁ - t₀)H_γ}`.

## The forward Hamiltonian

Let `D` be the set of `ψ` for which `τ ↦ U(t₀ + τ, t₀) ψ` has a right derivative at `0`, and
`H₀ ψ = i ∂₊U(t₀ + τ, t₀) ψ` (`forwardHamiltonian`). For `τ < 1`, `U(t₀ + τ, t₀)` differs from
`e^{-iτH_γ}`, `γ = α(t₀)`, only on the strip `x < τ` of points that have wrapped around, where
the phase is `e^{-iα(t₀ + τ - x)}` instead of `e^{-iγ}`, applied to `ψ(x - τ + 1)`. The
difference against `eₙ = e^{i(γ + 2πn)x}` is at most `sup |α - γ| · √τ · ‖ψ‖_{L²(1 - τ, 1)}`.

* If `|α(t₀ + s) - α(t₀)| = O(√s)`, this is `o(τ)`: the coordinates `⟨eₙ, ψ⟩` obey the eigenvalue
  relation of `H_γ`, and `H₀ ⊆ H_γ`.
* If `|α(t₀ + s) - α(t₀)| = o(√s)`, every `ψ` in the domain of `H_γ` is bounded, and the whole
  difference is `o(τ)`: `H₀ = H_γ`, which is self-adjoint.
* For every `α`, `H¹₀(0, 1) ⊆ D`: on `H¹₀` the tail `‖ψ‖_{L²(1 - τ, 1)}` is `o(τ)`, as it is half
  of `e^{-iτH_{γ+π}} ψ - e^{-iτH_γ} ψ`, and both have the derivative `-ψ'`.

## The example `α(t) = α₀ + √t`

At `t₀ ≠ 0`, `α` is `o(√s)` from the right, and `H₀ = H_{α(t₀)}`. At `t₀ = 0`, `ψ ∈ D` is in the
domain of `H_{α₀}`, so continuous with `ψ(1) = e^{iα₀} ψ(0)`. On the strip,
`|e^{-i√(τ - x)} - 1| ≥ (2/π) √(τ - x)`, so `U(τ, 0) ψ - e^{-iτH_{α₀}} ψ` has norm `≳ |ψ(1)| τ`,
while it must be `o(τ)`. So `ψ(1) = ψ(0) = 0`: `D = H¹₀(0, 1)`, and `H₀` is the minimal momentum
`-i d/dx`, the non-self-adjoint operator of the switched example. A continuous family of
self-adjoint `H(t)`, with a unitary propagator differentiable on a dense set, does not give a
self-adjoint `H(t₀)`, even from the forward derivative alone.

## Main results

* `phasePropagator_mem_unitary`, `phasePropagator_self`, `phasePropagator_comp`,
  `phasePropagator_const`: the propagator.
* `forwardHamiltonian_le_momentum` (`O(√s)`), `forwardHamiltonian_eq_momentum` (`o(√s)`).
* `hasDerivWithinAt_phasePropagator_primitive`: `H¹₀ ⊆ D` for every `α`.
* `forwardDomain_sqrtPhase`, `forwardHamiltonian_sqrtPhase`,
  `not_isSelfAdjoint_forwardHamiltonian_sqrtPhase`: at `t₀ = 0`, `D = H¹₀` and `H₀` is the minimal
  momentum, not self-adjoint.
* `sqrtPhase_counterexample`: everything together.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy

open MeasureTheory Filter Topology Set AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate Real LinearPMap

/-- The circle `ℝ/ℤ`. -/
local notation "𝕋" => AddCircle (1 : ℝ)

/-- Haar probability measure on `ℝ/ℤ`, which is Lebesgue measure on `[0, 1)`. -/
local notation "μc" => (haarAddCircle : Measure 𝕋)

/-- `L²(0, 1)`, as `L²` of the circle. -/
local notation "L²" => Lp ℂ 2 μc

/-! ### Unitaries from phases and shifts -/

lemma memLp_top_of_norm_eq_one {w : 𝕋 → ℂ} (hw : Measurable w) (h1 : ∀ x, ‖w x‖ = 1) :
    MemLp w ∞ μc :=
  memLp_top_of_bound hw.aestronglyMeasurable 1 (.of_forall fun x => (h1 x).le)

lemma norm_mulL_of_norm_eq_one {w : 𝕋 → ℂ} (hw : Measurable w) (h1 : ∀ x, ‖w x‖ = 1)
    (f : L²) : ‖Lp.mulL w f‖ = ‖f‖ := by
  have h := Lp.coeFn_mulL (memLp_top_of_norm_eq_one hw h1) f
  refine le_antisymm (Lp.norm_le_norm_of_ae_le ?_) (Lp.norm_le_norm_of_ae_le ?_) <;>
    filter_upwards [h] with x hx <;>
    simp [hx, h1]

lemma mulL_mulL_conj {w : 𝕋 → ℂ} (hw : Measurable w) (h1 : ∀ x, ‖w x‖ = 1) (f : L²) :
    Lp.mulL w (Lp.mulL (fun x => conj (w x)) f) = f := by
  have hc : Measurable fun x => conj (w x) := Complex.continuous_conj.measurable.comp hw
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_mulL (memLp_top_of_norm_eq_one hw h1) (Lp.mulL _ f),
    Lp.coeFn_mulL (memLp_top_of_norm_eq_one hc fun x => by rw [Complex.norm_conj, h1]) f]
    with x h₁ h₂
  rw [h₁, h₂, ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  simp

lemma circleShift_circleShift_neg (s : ℝ) (f : L²) : circleShift s (circleShift (-s) f) = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_circleShift s (circleShift (-s) f),
    (measurePreserving_sub s).quasiMeasurePreserving.ae_eq_comp (coeFn_circleShift (-s) f)]
    with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₂, AddCircle.coe_neg, sub_neg_eq_add, sub_add_cancel]

/-- A norm-preserving operator with a right inverse is unitary. -/
lemma mem_unitary_of_norm_map {T S : L² →L[ℂ] L²} (hT : ∀ f, ‖T f‖ = ‖f‖) (hS : T * S = 1) :
    T ∈ unitary (L² →L[ℂ] L²) := by
  have h₁ : star T * T = 1 := (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp
    (LinearIsometry.inner_map_map { toLinearMap := T.toLinearMap, norm_map' := hT })
  have h₂ : star T = S := by rw [← mul_one (star T), ← hS, ← mul_assoc, h₁, one_mul]
  exact ⟨h₁, by rw [h₂, hS]⟩

/-! ### The propagator -/

/-- The boundary phase collected during the time `τ` before `t` by the point `y` of the universal
cover `ℝ`: it crosses the integers `m ∈ (y - τ, y]`, at the times `t - y + m`. -/
def crossPhase (α : ℝ → ℝ) (t τ y : ℝ) : ℝ := ∑ m ∈ Finset.Ioc ⌊y - τ⌋ ⌊y⌋, α (t - y + m)

lemma measurable_crossPhase {α : ℝ → ℝ} (hα : Measurable α) (t τ : ℝ) :
    Measurable (crossPhase α t τ) := by
  have hq : ∀ q : ℤ × ℤ, Measurable fun y : ℝ => ∑ m ∈ Finset.Ioc q.1 q.2, α (t - y + m) :=
    fun q => Finset.measurable_fun_sum _ fun _ _ =>
      hα.comp ((measurable_const.sub measurable_id).add_const _)
  have h : Measurable fun p : ℝ × (ℤ × ℤ) => ∑ m ∈ Finset.Ioc p.2.1 p.2.2, α (t - p.1 + m) :=
    measurable_from_prod_countable_left hq
  have hg : Measurable fun y : ℝ => (y, (⌊y - τ⌋, ⌊y⌋)) :=
    measurable_id.prodMk ((Int.measurable_floor.comp (measurable_id.sub_const τ)).prodMk
      Int.measurable_floor)
  have := h.comp hg
  unfold crossPhase
  exact this

lemma crossPhase_add_intCast (α : ℝ → ℝ) (t τ y : ℝ) (k : ℤ) :
    crossPhase α t τ (y + k) = crossPhase α t τ y := by
  rw [crossPhase, crossPhase, show y + k - τ = y - τ + k by ring, Int.floor_add_intCast,
    Int.floor_add_intCast, ← Finset.map_add_right_Ioc, Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [addRightEmbedding_apply]
  congr 1
  push_cast
  ring

/-- The crossings in `(t - τ₁ - τ₂, t]` are those in `(t - τ₂, t]` and in
`(t - τ₁ - τ₂, t - τ₂]`. -/
lemma crossPhase_add (α : ℝ → ℝ) (t y : ℝ) {τ₁ τ₂ : ℝ} (h₁ : 0 ≤ τ₁) (h₂ : 0 ≤ τ₂) :
    crossPhase α t τ₂ y + crossPhase α (t - τ₂) τ₁ (y - τ₂) = crossPhase α t (τ₁ + τ₂) y := by
  have e : ∀ m ∈ Finset.Ioc ⌊y - τ₂ - τ₁⌋ ⌊y - τ₂⌋,
      α (t - τ₂ - (y - τ₂) + m) = α (t - y + m) := fun m _ => by
    congr 1
    ring
  rw [crossPhase, crossPhase, crossPhase, Finset.sum_congr rfl e, add_comm,
    show y - (τ₁ + τ₂) = y - τ₂ - τ₁ by ring,
    ← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),
    Finset.Ioc_union_Ioc_eq_Ioc (Int.floor_mono (by linarith)) (Int.floor_mono (by linarith))]

/-- The phase `e^{-i Σⱼ α(sⱼ)}` of `U(t, t - τ)` at `x`, over the wrap-around times `sⱼ`. -/
def wrapPhase (α : ℝ → ℝ) (t τ : ℝ) (x : 𝕋) : ℂ :=
  Complex.exp (-(Complex.I * (crossPhase α t τ (circleRep x) : ℂ)))

lemma measurable_wrapPhase {α : ℝ → ℝ} (hα : Measurable α) (t τ : ℝ) :
    Measurable (wrapPhase α t τ) := by
  have h := (measurable_crossPhase hα t τ).comp measurable_circleRep
  unfold wrapPhase
  fun_prop

lemma norm_exp_neg_I_mul (a : ℝ) : ‖Complex.exp (-(Complex.I * a))‖ = 1 := by
  rw [← mul_neg, ← Complex.ofReal_neg, Complex.norm_exp_I_mul_ofReal]

lemma norm_wrapPhase (α : ℝ → ℝ) (t τ : ℝ) (x : 𝕋) : ‖wrapPhase α t τ x‖ = 1 :=
  norm_exp_neg_I_mul _

/-- **The propagator `U(t₁, t₀)` of `H(t) = H_{α(t)}`**, for `t₀ ≤ t₁` and `ħ = 1`: translation
by `t₁ - t₀`, where a point that wraps around at the time `s` picks up the phase `e^{-iα(s)}`. -/
def phasePropagator (α : ℝ → ℝ) (t₁ t₀ : ℝ) : L² →L[ℂ] L² :=
  Lp.mulL (wrapPhase α t₁ (t₁ - t₀)) ∘L circleShift (t₁ - t₀)

local notation "V" => phasePropagator

variable {α : ℝ → ℝ}

lemma coeFn_phasePropagator (hα : Measurable α) (t₁ t₀ : ℝ) (f : L²) :
    V α t₁ t₀ f =ᵐ[μc] fun x => wrapPhase α t₁ (t₁ - t₀) x * f (x - (t₁ - t₀ : ℝ)) := by
  filter_upwards [Lp.coeFn_mulL (memLp_top_of_norm_eq_one (measurable_wrapPhase hα t₁ (t₁ - t₀))
      (norm_wrapPhase α t₁ (t₁ - t₀))) (circleShift (t₁ - t₀) f),
    coeFn_circleShift (t₁ - t₀) f] with x h₁ h₂
  rw [phasePropagator, ContinuousLinearMap.comp_apply, h₁, h₂]

/-- `U(t₁, t₀)` is unitary. -/
theorem phasePropagator_mem_unitary (hα : Measurable α) (t₁ t₀ : ℝ) :
    V α t₁ t₀ ∈ unitary (L² →L[ℂ] L²) := by
  have hw := measurable_wrapPhase hα t₁ (t₁ - t₀)
  refine mem_unitary_of_norm_map
    (S := circleShift (-(t₁ - t₀)) ∘L Lp.mulL fun x => conj (wrapPhase α t₁ (t₁ - t₀) x))
    (fun f => ?_) (ContinuousLinearMap.ext fun f => ?_)
  · rw [phasePropagator, ContinuousLinearMap.comp_apply,
      norm_mulL_of_norm_eq_one hw (norm_wrapPhase α t₁ _), norm_circleShift]
  · simp only [ContinuousLinearMap.mul_def, phasePropagator, ContinuousLinearMap.comp_apply]
    rw [circleShift_circleShift_neg, mulL_mulL_conj hw (norm_wrapPhase α t₁ _),
      one_apply_eq_self]

/-- `U(t, t) = 1`. -/
theorem phasePropagator_self (hα : Measurable α) (t : ℝ) : V α t t = 1 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  change V α t t f =ᵐ[μc] f
  filter_upwards [coeFn_phasePropagator hα t t f] with x hx
  simp [hx, wrapPhase, crossPhase]

/-- **The propagator law** `U(t₂, t₁) U(t₁, t₀) = U(t₂, t₀)` for `t₀ ≤ t₁ ≤ t₂`. -/
theorem phasePropagator_comp (hα : Measurable α) {t₀ t₁ t₂ : ℝ} (h₀₁ : t₀ ≤ t₁)
    (h₁₂ : t₁ ≤ t₂) : V α t₂ t₁ ∘L V α t₁ t₀ = V α t₂ t₀ := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  change V α t₂ t₁ (V α t₁ t₀ f) =ᵐ[μc] V α t₂ t₀ f
  filter_upwards [coeFn_phasePropagator hα t₂ t₁ (V α t₁ t₀ f),
    (measurePreserving_sub (t₂ - t₁)).quasiMeasurePreserving.ae_eq_comp
      (coeFn_phasePropagator hα t₁ t₀ f), coeFn_phasePropagator hα t₂ t₀ f] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₂
  have hx : x - ((t₂ - t₁ : ℝ) : 𝕋) - ((t₁ - t₀ : ℝ) : 𝕋) = x - ((t₂ - t₀ : ℝ) : 𝕋) := by
    rw [sub_sub, ← AddCircle.coe_add, show t₂ - t₁ + (t₁ - t₀) = t₂ - t₀ by ring]
  have hr : circleRep (x - ((t₂ - t₁ : ℝ) : 𝕋)) = Int.fract (circleRep x - (t₂ - t₁)) := by
    conv_lhs => rw [← coe_circleRep x]
    rw [← AddCircle.coe_sub, circleRep_coe]
  have key := crossPhase_add α t₂ (circleRep x) (sub_nonneg.mpr h₀₁) (sub_nonneg.mpr h₁₂)
  rw [show t₂ - (t₂ - t₁) = t₁ by ring, show t₁ - t₀ + (t₂ - t₁) = t₂ - t₀ by ring,
    ← crossPhase_add_intCast α t₁ (t₁ - t₀) _ (-⌊circleRep x - (t₂ - t₁)⌋), Int.cast_neg,
    ← sub_eq_add_neg] at key
  rw [h₁, h₂, h₃, ← mul_assoc, hx, wrapPhase, wrapPhase, wrapPhase, hr, ← Int.self_sub_floor,
    ← key, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The number of wrap-arounds: for constant `α = γ`, the collected phase is `γ` times it. -/
lemma crossPhase_const (γ t : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (y : ℝ) :
    crossPhase (fun _ => γ) t τ y = γ * (⌊y⌋ - ⌊y - τ⌋ : ℤ) := by
  rw [crossPhase, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  exact_mod_cast Int.card_Ioc_of_le _ _ (Int.floor_mono (by linarith))

lemma twistPhase_eq_wrapPhase (γ t : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (x : 𝕋) :
    twistPhase γ τ x = wrapPhase (fun _ => γ) t τ x := by
  have hr : circleRep (x - (τ : 𝕋)) = Int.fract (circleRep x - τ) := by
    conv_lhs => rw [← coe_circleRep x]
    rw [← AddCircle.coe_sub, circleRep_coe]
  rw [wrapPhase, twistPhase, crossPhase_const γ t hτ, hr, ← Int.self_sub_floor,
    Int.floor_eq_zero_iff.mpr (circleRep_mem x)]
  congr 1
  push_cast
  ring

/-- **For constant `α = γ`, the propagator is `U(t₁, t₀) = e^{-i(t₁ - t₀)H_γ}`.** -/
theorem phasePropagator_const (γ : ℝ) {t₁ t₀ : ℝ} (h : t₀ ≤ t₁) :
    V (fun _ => γ) t₁ t₀ = twistedTranslation γ (t₁ - t₀) := by
  rw [phasePropagator, twistedTranslation]
  congr 2
  funext x
  exact (twistPhase_eq_wrapPhase γ t₁ (sub_nonneg.mpr h) x).symm

/-! ### Short times: one wrap-around -/

lemma circleRep_sub_of_lt {τ : ℝ} (hτ : τ < 1) {x : 𝕋} (h : circleRep x < τ) :
    circleRep (x - (τ : 𝕋)) = circleRep x - τ + 1 := by
  have hx := circleRep_mem x
  conv_lhs => rw [← coe_circleRep x]
  rw [← AddCircle.coe_sub, circleRep_coe, Int.fract_eq_iff]
  exact ⟨by linarith [hx.1], by linarith, -1, by push_cast; ring⟩

lemma circleRep_sub_of_le {τ : ℝ} (hτ : 0 ≤ τ) {x : 𝕋} (h : τ ≤ circleRep x) :
    circleRep (x - (τ : 𝕋)) = circleRep x - τ := by
  have hx := circleRep_mem x
  conv_lhs => rw [← coe_circleRep x]
  rw [← AddCircle.coe_sub, circleRep_coe, Int.fract_eq_iff]
  exact ⟨by linarith, by linarith [hx.2], 0, by push_cast; ring⟩

/-- Within the time `τ < 1`, the points `x - τ ∈ [1 - τ, 1)` wrap around, to `x ∈ [0, τ)`. -/
lemma one_sub_le_circleRep_sub_iff {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) (x : 𝕋) :
    1 - τ ≤ circleRep (x - (τ : 𝕋)) ↔ circleRep x < τ := by
  have hx := circleRep_mem x
  rcases lt_or_ge (circleRep x) τ with h | h
  · rw [circleRep_sub_of_lt h1 h]
    exact ⟨fun _ => h, fun _ => by linarith [hx.1]⟩
  · rw [circleRep_sub_of_le h0 h]
    exact ⟨fun h' => by linarith [hx.2], fun h' => absurd h' (not_lt.mpr h)⟩

lemma crossPhase_of_lt (α : ℝ → ℝ) (t : ℝ) {τ r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (hτ : τ < 1)
    (h : r < τ) : crossPhase α t τ r = α (t - r) := by
  have h1 : ⌊r - τ⌋ = -1 :=
    Int.floor_eq_iff.mpr ⟨by push_cast; linarith [hr.1], by push_cast; linarith⟩
  rw [crossPhase, h1, Int.floor_eq_zero_iff.mpr hr, show Finset.Ioc (-1 : ℤ) 0 = {0} by decide,
    Finset.sum_singleton, Int.cast_zero, add_zero]

lemma crossPhase_of_le (α : ℝ → ℝ) (t : ℝ) {τ r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (hτ : 0 ≤ τ)
    (h : τ ≤ r) : crossPhase α t τ r = 0 := by
  have h1 : ⌊r - τ⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith [hr.2]⟩
  rw [crossPhase, h1, Int.floor_eq_zero_iff.mpr hr, Finset.Ioc_self, Finset.sum_empty]

lemma wrapPhase_of_lt (α : ℝ → ℝ) (t : ℝ) {τ : ℝ} (hτ : τ < 1) {x : 𝕋} (h : circleRep x < τ) :
    wrapPhase α t τ x = Complex.exp (-(Complex.I * α (t - circleRep x))) := by
  rw [wrapPhase, crossPhase_of_lt α t (circleRep_mem x) hτ h]

lemma wrapPhase_of_le (α : ℝ → ℝ) (t : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) {x : 𝕋} (h : τ ≤ circleRep x) :
    wrapPhase α t τ x = 1 := by
  rw [wrapPhase, crossPhase_of_le α t (circleRep_mem x) hτ h]
  simp

/-- The difference of the phases of `U(t₀ + τ, t₀)` and of `e^{-iτH_γ}`, on the strip `x < τ` of
the points that have wrapped around. -/
def stripPhase (α : ℝ → ℝ) (t₀ γ τ : ℝ) (x : 𝕋) : ℂ :=
  if circleRep x < τ then
    Complex.exp (-(Complex.I * α (t₀ + τ - circleRep x))) - Complex.exp (-(Complex.I * γ))
  else 0

lemma measurable_stripPhase (hα : Measurable α) (t₀ γ τ : ℝ) :
    Measurable (stripPhase α t₀ γ τ) := by
  have h1 := measurable_circleRep
  have h2 : Measurable fun x : 𝕋 => α (t₀ + τ - circleRep x) := hα.comp (by fun_prop)
  exact Measurable.ite (measurableSet_lt measurable_circleRep measurable_const) (by fun_prop)
    measurable_const

lemma norm_exp_neg_I_sub_le (a b : ℝ) :
    ‖Complex.exp (-(Complex.I * a)) - Complex.exp (-(Complex.I * b))‖ ≤ |a - b| := by
  have h := norm_exp_I_sub_exp_I_le (-a) (-b)
  rwa [Complex.ofReal_neg, Complex.ofReal_neg, mul_neg, mul_neg,
    show -a - -b = -(a - b) by ring, abs_neg] at h

lemma norm_stripPhase_le (α : ℝ → ℝ) (t₀ γ τ : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ x : 𝕋, circleRep x < τ → |α (t₀ + τ - circleRep x) - γ| ≤ B) (x : 𝕋) :
    ‖stripPhase α t₀ γ τ x‖ ≤ B := by
  unfold stripPhase
  split_ifs with hx
  · exact (norm_exp_neg_I_sub_le _ _).trans (h x hx)
  · simpa using hB

lemma norm_stripPhase_le_two (α : ℝ → ℝ) (t₀ γ τ : ℝ) (x : 𝕋) : ‖stripPhase α t₀ γ τ x‖ ≤ 2 := by
  unfold stripPhase
  split_ifs
  · refine (norm_sub_le _ _).trans ?_
    rw [norm_exp_neg_I_mul, norm_exp_neg_I_mul]
    norm_num
  · simp

lemma memLp_stripPhase (hα : Measurable α) (t₀ γ τ : ℝ) : MemLp (stripPhase α t₀ γ τ) ∞ μc :=
  memLp_top_of_bound (measurable_stripPhase hα t₀ γ τ).aestronglyMeasurable 2
    (.of_forall (norm_stripPhase_le_two α t₀ γ τ))

lemma measurableSet_tail (τ : ℝ) : MeasurableSet {x : 𝕋 | 1 - τ ≤ circleRep x} :=
  measurableSet_le measurable_const measurable_circleRep

lemma norm_indicator_one_le (S : Set 𝕋) (x : 𝕋) : ‖S.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
  by_cases hx : x ∈ S <;> simp [hx]

lemma memLp_tail (τ : ℝ) :
    MemLp ({x : 𝕋 | 1 - τ ≤ circleRep x}.indicator fun _ => (1 : ℂ)) ∞ μc :=
  memLp_top_of_bound ((measurable_const.indicator (measurableSet_tail τ)).aestronglyMeasurable) 1
    (.of_forall (norm_indicator_one_le _))

/-- The part `1_{[1 - τ, 1)} ψ` of `ψ` that wraps around within the time `τ`. -/
def tailPart (τ : ℝ) : L² →L[ℂ] L² := Lp.mulL ({x : 𝕋 | 1 - τ ≤ circleRep x}.indicator fun _ => 1)

lemma coeFn_tailPart (τ : ℝ) (ψ : L²) :
    tailPart τ ψ =ᵐ[μc] fun x => {x : 𝕋 | 1 - τ ≤ circleRep x}.indicator (fun _ => 1) x * ψ x :=
  Lp.coeFn_mulL (memLp_tail τ) ψ

/-- **Short times**: for `0 ≤ τ < 1`, `U(t₀ + τ, t₀) ψ - e^{-iτH_γ} ψ` is `ψ(x - τ)` times the
difference of the phases on the strip `x < τ`. -/
lemma phasePropagator_sub_twistedTranslation (hα : Measurable α) (t₀ γ : ℝ) {τ : ℝ} (h0 : 0 ≤ τ)
    (h1 : τ < 1) (ψ : L²) :
    V α (t₀ + τ) t₀ ψ - twistedTranslation γ τ ψ =ᵐ[μc]
      fun x => stripPhase α t₀ γ τ x * ψ (x - τ) := by
  filter_upwards [Lp.coeFn_sub (V α (t₀ + τ) t₀ ψ) (twistedTranslation γ τ ψ),
    coeFn_phasePropagator hα (t₀ + τ) t₀ ψ, coeFn_twistedTranslation γ τ ψ] with x h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, h₃, add_sub_cancel_left, ← sub_mul, stripPhase,
    twistPhase_eq_wrapPhase γ (t₀ + τ) h0]
  split_ifs with h
  · rw [wrapPhase_of_lt α _ h1 h, wrapPhase_of_lt (fun _ => γ) _ h1 h]
  · rw [wrapPhase_of_le α _ h0 (not_lt.mp h), wrapPhase_of_le _ _ h0 (not_lt.mp h), sub_self]

/-- The same, as an operator identity: only the tail `1_{[1 - τ, 1)} ψ` enters. -/
lemma phasePropagator_sub_twistedTranslation_eq (hα : Measurable α) (t₀ γ : ℝ) {τ : ℝ}
    (h0 : 0 ≤ τ) (h1 : τ < 1) (ψ : L²) :
    V α (t₀ + τ) t₀ ψ - twistedTranslation γ τ ψ =
      Lp.mulL (stripPhase α t₀ γ τ) (circleShift τ (tailPart τ ψ)) := by
  refine Lp.ext ((phasePropagator_sub_twistedTranslation hα t₀ γ h0 h1 ψ).trans ?_)
  filter_upwards [Lp.coeFn_mulL (memLp_stripPhase hα t₀ γ τ) (circleShift τ (tailPart τ ψ)),
    coeFn_circleShift τ (tailPart τ ψ),
    (measurePreserving_sub τ).quasiMeasurePreserving.ae_eq_comp (coeFn_tailPart τ ψ)]
    with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃]
  by_cases h : circleRep x < τ
  · rw [Set.indicator_of_mem (show x - (τ : 𝕋) ∈ {x : 𝕋 | 1 - τ ≤ circleRep x} from
      (one_sub_le_circleRep_sub_iff h0 h1 x).mpr h), one_mul]
  · simp [stripPhase, h]

lemma mulL_zero_apply (ψ : L²) : Lp.mulL (0 : 𝕋 → ℂ) ψ = 0 := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_mulL (p := 2) (μ := μc) (MemLp.zero : MemLp (0 : 𝕋 → ℂ) ∞ μc) ψ,
    Lp.coeFn_zero ℂ 2 μc] with x h₁ h₂
  rw [h₁, h₂]
  simp

/-- The tail `1_{[1 - τ, 1)} ψ` tends to `0`. -/
lemma tendsto_tailPart (ψ : L²) : Tendsto (fun τ => tailPart τ ψ) (𝓝[≥] 0) (𝓝 0) := by
  have h := Lp.tendsto_mulL_apply (p := 2) ENNReal.ofNat_ne_top (l := 𝓝[≥] (0 : ℝ))
    (g := fun τ => {x : 𝕋 | 1 - τ ≤ circleRep x}.indicator fun _ => (1 : ℂ)) (g₀ := 0) (C := 1)
    (.of_forall fun τ => (memLp_tail τ).aestronglyMeasurable) aestronglyMeasurable_zero
    (.of_forall fun τ => .of_forall (norm_indicator_one_le _))
    (.of_forall fun x => by simp) (.of_forall fun x => ?_) ψ
  · rwa [mulL_zero_apply] at h
  · have hr := (circleRep_mem x).2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ico_mem_nhdsGE (show (0 : ℝ) < 1 - circleRep x by linarith)] with τ hτ
    rw [Set.indicator_of_notMem (show x ∉ {x : 𝕋 | 1 - τ ≤ circleRep x} from fun h => by
      have : 1 - τ ≤ circleRep x := h
      linarith [hτ.2]), Pi.zero_apply]

/-! ### Norms on strips -/

lemma integral_comp_circleRep_real (F : ℝ → ℝ) :
    ∫ x, F (circleRep x) ∂μc = ∫ u in (0 : ℝ)..1, F u := by
  rw [← volume_eq_haarAddCircle, ← UnitAddCircle.intervalIntegral_preimage 0, zero_add]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(by simp [ae_iff] : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ 1)] with a ha hmem
  rw [uIoc_of_le zero_le_one] at hmem
  rw [circleRep_coe, Int.fract_eq_self.mpr ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ha⟩]

lemma measureReal_circleRep_preimage {I : Set ℝ} (hI : MeasurableSet I) :
    (μc).real (circleRep ⁻¹' I) = volume.real (Ioc 0 1 ∩ I) := by
  rw [← integral_indicator_one (measurable_circleRep hI)]
  have h : (circleRep ⁻¹' I).indicator (1 : 𝕋 → ℝ) = fun x => I.indicator 1 (circleRep x) := by
    funext x
    by_cases hx : circleRep x ∈ I <;> simp [hx]
  rw [h, integral_comp_circleRep_real, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator hI]
  simp

lemma measureReal_strip {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (μc).real {x : 𝕋 | circleRep x < a} = a := by
  rw [show {x : 𝕋 | circleRep x < a} = circleRep ⁻¹' Iio a from rfl,
    measureReal_circleRep_preimage measurableSet_Iio,
    show Ioc (0 : ℝ) 1 ∩ Iio a = Ioo 0 a by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by linarith [h.2]⟩, h.2⟩⟩,
    Real.volume_real_Ioo_of_le h0, sub_zero]

lemma measureReal_tail {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ < 1) :
    (μc).real {x : 𝕋 | 1 - τ ≤ circleRep x} = τ := by
  rw [show {x : 𝕋 | 1 - τ ≤ circleRep x} = circleRep ⁻¹' Ici (1 - τ) from rfl,
    measureReal_circleRep_preimage measurableSet_Ici,
    show Ioc (0 : ℝ) 1 ∩ Ici (1 - τ) = Icc (1 - τ) 1 by
      ext u
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨by linarith [h.1], h.2⟩, h.1⟩⟩,
    Real.volume_real_Icc_of_le (by linarith)]
  ring

lemma measurableSet_strip (a : ℝ) : MeasurableSet {x : 𝕋 | circleRep x < a} :=
  measurableSet_lt measurable_circleRep measurable_const

/-- A vector bounded by `B` and supported on `S` has norm at most `B √|S|`. -/
lemma norm_le_of_ae_le_indicator {f : L²} {S : Set 𝕋} (hS : MeasurableSet S) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂μc, ‖f x‖ ≤ S.indicator (fun _ => B) x) : ‖f‖ ≤ B * √((μc).real S) := by
  calc ‖f‖ ≤ ‖indicatorConstLp 2 hS (measure_ne_top μc S) (B : ℂ)‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [h, indicatorConstLp_coeFn (p := 2) (hs := hS)
          (hμs := measure_ne_top μc S) (c := (B : ℂ))] with x hx hc
        rw [hc, norm_indicator_eq_indicator_norm]
        simpa [Complex.norm_real, abs_of_nonneg hB] using hx
    _ = B * √((μc).real S) := by
        rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, Complex.norm_real,
          Real.norm_of_nonneg hB, Real.sqrt_eq_rpow]
        norm_num

/-- A vector at least `B` on `S` has norm at least `B √|S|`. -/
lemma le_norm_of_ae_le {f : L²} {S : Set 𝕋} (hS : MeasurableSet S) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ᵐ x ∂μc, x ∈ S → B ≤ ‖f x‖) : B * √((μc).real S) ≤ ‖f‖ := by
  calc B * √((μc).real S) = ‖indicatorConstLp 2 hS (measure_ne_top μc S) (B : ℂ)‖ := by
        rw [norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, Complex.norm_real,
          Real.norm_of_nonneg hB, Real.sqrt_eq_rpow]
        norm_num
    _ ≤ ‖f‖ := by
        refine Lp.norm_le_norm_of_ae_le ?_
        filter_upwards [h, indicatorConstLp_coeFn (p := 2) (hs := hS)
          (hμs := measure_ne_top μc S) (c := (B : ℂ))] with x hx hc
        rw [hc, norm_indicator_eq_indicator_norm]
        by_cases hxS : x ∈ S
        · simpa [hxS, Complex.norm_real, abs_of_nonneg hB] using hx hxS
        · simp [hxS]

/-! ### One-sided derivatives at `0` -/

lemma hasDerivWithinAt_Ici_zero_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (h0 : g 0 = 0) :
    HasDerivWithinAt g 0 (Ici 0) 0 ↔ ∀ ε > 0, ∀ᶠ τ in 𝓝[≥] (0 : ℝ), ‖g τ‖ ≤ ε * τ := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  simp only [h0, sub_zero, smul_zero]
  refine forall₂_congr fun ε _ => ⟨fun h => ?_, fun h => ?_⟩ <;>
    filter_upwards [h, self_mem_nhdsWithin] with τ hτ (hτ0 : 0 ≤ τ)
  · rwa [Real.norm_of_nonneg hτ0] at hτ
  · rwa [Real.norm_of_nonneg hτ0]

/-- `t ↦ ⟨e^{iδx}, w⟩` against a phase difference on the strip `x < τ`: at most
`B √τ ‖w‖`. -/
lemma norm_inner_planeWave_mulL_stripPhase_le (hα : Measurable α) (t₀ γ δ : ℝ) {τ : ℝ}
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1) {B : ℝ} (hB : 0 ≤ B) (hle : ∀ x, ‖stripPhase α t₀ γ τ x‖ ≤ B)
    (w : L²) : ‖⟪planeWave δ, Lp.mulL (stripPhase α t₀ γ τ) w⟫_ℂ‖ ≤ B * √τ * ‖w‖ := by
  have hD := measurable_stripPhase hα t₀ γ τ
  have hDc : Measurable fun x => conj (stripPhase α t₀ γ τ x) :=
    Complex.continuous_conj.measurable.comp hD
  have hm : MemLp (fun x => conj (stripPhase α t₀ γ τ x)) ∞ μc :=
    memLp_top_of_bound hDc.aestronglyMeasurable B
      (.of_forall fun x => by rw [Complex.norm_conj]; exact hle x)
  have hinner : ⟪planeWave δ, Lp.mulL (stripPhase α t₀ γ τ) w⟫_ℂ =
      ⟪Lp.mulL (fun x => conj (stripPhase α t₀ γ τ x)) (planeWave δ), w⟫_ℂ := by
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_mulL (memLp_stripPhase hα t₀ γ τ) w,
      Lp.coeFn_mulL hm (planeWave δ)] with x h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_conj]
    ring
  rw [hinner]
  refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg w))
  refine (norm_le_of_ae_le_indicator (measurableSet_strip τ) hB ?_).trans_eq
    (by rw [measureReal_strip h0 h1])
  filter_upwards [Lp.coeFn_mulL hm (planeWave δ), (memLp_planeWaveFun δ).coeFn_toLp]
    with x h₁ h₂
  rw [h₁, norm_mul, Complex.norm_conj, planeWave, h₂, norm_planeWaveFun, mul_one]
  by_cases hx : circleRep x < τ
  · rw [Set.indicator_of_mem (show x ∈ {x : 𝕋 | circleRep x < τ} from hx)]
    exact hle x
  · rw [Set.indicator_of_notMem (show x ∉ {x : 𝕋 | circleRep x < τ} from hx)]
    simp [stripPhase, hx]

/-! ### The forward generator -/

/-- **Right Hölder-½ at `t₀` ⇒ the forward generator at `t₀` is a restriction of `H_{α(t₀)}`**: if
`|α(t₀ + s) - α(t₀)| ≤ C √s` for small `s ≥ 0` and `τ ↦ U(t₀ + τ, t₀) ψ` has the right derivative
`v` at `0`, then `ψ` is in the domain of `H_{α(t₀)}` and `H_{α(t₀)} ψ = i v`. -/
theorem momentum_of_hasDerivWithinAt_phasePropagator (hα : Measurable α) {t₀ : ℝ}
    (hO : ∃ C δ, 0 < δ ∧ ∀ s ∈ Icc (0 : ℝ) δ, |α (t₀ + s) - α t₀| ≤ C * √s) {ψ v : L²}
    (h : HasDerivWithinAt (fun τ => V α (t₀ + τ) t₀ ψ) v (Ici 0) 0) :
    ∃ hψ : ψ ∈ (momentum (α t₀)).domain, momentum (α t₀) ⟨ψ, hψ⟩ = Complex.I • v := by
  obtain ⟨C, δ, hδ, hC⟩ := hO
  set γ := α t₀
  refine momentum_of_inner fun n => ?_
  set e := twistedBasis γ n with he
  set c := ⟪e, ψ⟫_ℂ
  have hf : HasDerivWithinAt (fun τ => ⟪e, V α (t₀ + τ) t₀ ψ⟫_ℂ) ⟪e, v⟫_ℂ (Ici 0) 0 := by
    simpa using (hasDerivWithinAt_const (0 : ℝ) (Ici 0) e).inner ℂ h
  have hφ : HasDerivAt (fun τ : ℝ => ⟪e, twistedTranslation γ τ ψ⟫_ℂ)
      (-(Complex.I * ((γ + 2 * π * n : ℝ) : ℂ)) * c) 0 := by
    have := hasDerivAt_phase (ħ := 1) (γ + 2 * π * n) c
    simp only [div_one] at this
    exact this.congr_of_eventuallyEq
      (.of_forall fun τ => inner_twistedBasis_twistedTranslation γ τ n ψ)
  have hR : HasDerivWithinAt
      (fun τ => ⟪e, V α (t₀ + τ) t₀ ψ⟫_ℂ - ⟪e, twistedTranslation γ τ ψ⟫_ℂ) 0 (Ici 0) 0 := by
    refine (hasDerivWithinAt_Ici_zero_iff (by
      simp [phasePropagator_self hα, twistedTranslation_zero])).mpr fun ε hε => ?_
    set C' := |C|
    have ht := (tendsto_tailPart ψ).norm
    rw [norm_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (C' + 1) by positivity)),
      Icc_mem_nhdsGE (show (0 : ℝ) < min δ (1 / 2) by positivity)] with τ hτ hτδ
    have h0 := hτδ.1
    have h1 : τ < 1 := by linarith [hτδ.2, min_le_right δ (1 / 2)]
    have hB : ∀ x, ‖stripPhase α t₀ γ τ x‖ ≤ C' * √τ := norm_stripPhase_le α t₀ γ τ
      (by positivity) fun x hx => by
        have hs : τ - circleRep x ∈ Icc (0 : ℝ) δ :=
          ⟨by linarith, by linarith [(circleRep_mem x).1, hτδ.2, min_le_left δ (1 / 2)]⟩
        have := hC _ hs
        rw [show t₀ + (τ - circleRep x) = t₀ + τ - circleRep x by ring] at this
        calc |α (t₀ + τ - circleRep x) - γ| ≤ C * √(τ - circleRep x) := this
          _ ≤ C' * √(τ - circleRep x) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
          _ ≤ C' * √τ := mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (by linarith [(circleRep_mem x).1])) (abs_nonneg C)
    rw [← inner_sub_right, phasePropagator_sub_twistedTranslation_eq hα t₀ γ h0 h1, he,
      twistedBasis_apply]
    refine (norm_inner_planeWave_mulL_stripPhase_le hα t₀ γ _ h0 h1.le (by positivity) hB
      _).trans ?_
    rw [norm_circleShift, show C' * √τ * √τ * ‖tailPart τ ψ‖ = C' * (√τ * √τ * ‖tailPart τ ψ‖)
      by ring, Real.mul_self_sqrt h0]
    calc C' * (τ * ‖tailPart τ ψ‖) ≤ C' * (τ * (ε / (C' + 1))) := by gcongr
      _ ≤ ε * τ := by
        rw [show C' * (τ * (ε / (C' + 1))) = (C' / (C' + 1)) * (ε * τ) by ring]
        exact mul_le_of_le_one_left (by positivity)
          ((div_le_one (by positivity)).mpr (by linarith))
  have heq := (uniqueDiffWithinAt_Ici 0).eq_deriv _ (hf.sub hφ.hasDerivWithinAt) hR
  rw [inner_smul_right]
  linear_combination Complex.I * heq - (((γ + 2 * π * n : ℝ) : ℂ) * c) * Complex.I_sq

/-- A vector in the domain of `H_γ` is bounded: `|ψ(x)| = |c + ∫₀ˣ g| ≤ M`. -/
lemma exists_bound_of_mem_domain {γ : ℝ} (ψ : (momentum γ).domain) :
    ∃ M, 0 ≤ M ∧ ∀ᵐ x ∂μc, ‖(ψ : L²) x‖ ≤ M := by
  obtain ⟨c, g, -, hψ, -⟩ := mem_graph_momentum.mp ((momentum γ).mem_graph ψ)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_primitive_lift g).continuousOn
  refine ⟨‖c‖ + max C 0, by positivity, ?_⟩
  rw [hψ]
  filter_upwards [Lp.coeFn_add (c • planeWave 0) (primitive g), Lp.coeFn_smul c (planeWave 0),
    (memLp_planeWaveFun 0).coeFn_toLp, (memLp_primitiveFun g).coeFn_toLp] with x h₁ h₂ h₃ h₄
  rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, planeWave, h₃, primitive, h₄, smul_eq_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ((hC _ (Ico_subset_Icc_self
    (circleRep_mem x))).trans (le_max_left _ _)))
  rw [norm_mul, norm_planeWaveFun, mul_one]

/-- **Right `o(√s)` at `t₀` ⇒ the domain of `H_{α(t₀)}` is in the forward domain at `t₀`**, with
the right derivative `-i H_{α(t₀)} ψ`. -/
theorem hasDerivWithinAt_phasePropagator_of_mem (hα : Measurable α) {t₀ : ℝ}
    (ho : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) δ, |α (t₀ + s) - α t₀| ≤ ε * √s)
    (ψ : (momentum (α t₀)).domain) :
    HasDerivWithinAt (fun τ => V α (t₀ + τ) t₀ ψ) ((-Complex.I) • momentum (α t₀) ψ)
      (Ici 0) 0 := by
  have hU : HasDerivAt (fun τ => twistedTranslation (α t₀) τ ψ)
      ((-Complex.I) • momentum (α t₀) ψ) 0 := by
    have := hasDerivAt_twistedTranslation_momentum (ħ := 1) ψ
    simp only [div_one, Complex.ofReal_one, mul_one, Complex.inv_I] at this
    exact this
  obtain ⟨M, hM0, hM⟩ := exists_bound_of_mem_domain ψ
  have hR : HasDerivWithinAt (fun τ => V α (t₀ + τ) t₀ ψ - twistedTranslation (α t₀) τ ψ) 0
      (Ici 0) 0 := by
    refine (hasDerivWithinAt_Ici_zero_iff (by
      simp [phasePropagator_self hα, twistedTranslation_zero])).mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hε'⟩ := ho (ε / (M + 1)) (by positivity)
    filter_upwards [Icc_mem_nhdsGE (show (0 : ℝ) < min δ (1 / 2) by positivity)] with τ hτδ
    have h0 := hτδ.1
    have h1 : τ < 1 := by linarith [hτδ.2, min_le_right δ (1 / 2)]
    have hB : ∀ x, ‖stripPhase α t₀ (α t₀) τ x‖ ≤ ε / (M + 1) * √τ :=
      norm_stripPhase_le α t₀ (α t₀) τ (by positivity) fun x hx => by
        have hs : τ - circleRep x ∈ Icc (0 : ℝ) δ :=
          ⟨by linarith, by linarith [(circleRep_mem x).1, hτδ.2, min_le_left δ (1 / 2)]⟩
        have := hε' _ hs
        rw [show t₀ + (τ - circleRep x) = t₀ + τ - circleRep x by ring] at this
        exact this.trans (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by linarith [(circleRep_mem x).1])) (by positivity))
    have htail : ‖tailPart τ (ψ : L²)‖ ≤ M * √τ := by
      refine (norm_le_of_ae_le_indicator (measurableSet_tail τ) hM0 ?_).trans_eq
        (by rw [measureReal_tail h0 h1])
      filter_upwards [coeFn_tailPart τ (ψ : L²), hM] with x h₁ h₂
      rw [h₁]
      by_cases hx : x ∈ {x : 𝕋 | 1 - τ ≤ circleRep x}
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
        exact h₂
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, norm_zero]
    rw [phasePropagator_sub_twistedTranslation_eq hα t₀ (α t₀) h0 h1]
    calc ‖Lp.mulL (stripPhase α t₀ (α t₀) τ) (circleShift τ (tailPart τ (ψ : L²)))‖
        ≤ ε / (M + 1) * √τ * ‖circleShift τ (tailPart τ (ψ : L²))‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (Lp.norm_mulL_le (measurable_stripPhase hα t₀ (α t₀) τ).aestronglyMeasurable
              (by positivity) (.of_forall hB)) (norm_nonneg _))
      _ ≤ ε / (M + 1) * √τ * (M * √τ) := by
          rw [norm_circleShift]
          gcongr
      _ = M / (M + 1) * (ε * τ) := by
          rw [show ε / (M + 1) * √τ * (M * √τ) = M / (M + 1) * ε * (√τ * √τ) by ring,
            Real.mul_self_sqrt h0]
          ring
      _ ≤ ε * τ := mul_le_of_le_one_left (by positivity)
          ((div_le_one (by positivity)).mpr (by linarith))
  have := hR.add hU.hasDerivWithinAt
  rw [zero_add] at this
  exact this.congr (fun τ _ => (sub_add_cancel _ _).symm) (sub_add_cancel _ _).symm

/-- **`H¹₀` is in the forward domain at every `t₀`, for every `α`**: for `ψ(x) = ∫₀ˣ g` with
`∫₀¹ g = 0`, `τ ↦ U(t₀ + τ, t₀) ψ` has the right derivative `-ψ' = -g` at `0`. -/
theorem hasDerivWithinAt_phasePropagator_primitive (hα : Measurable α) (t₀ : ℝ) {g : L²}
    (hg : ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0) :
    HasDerivWithinAt (fun τ => V α (t₀ + τ) t₀ (primitive g)) ((-Complex.I) • (-Complex.I) • g)
      (Ici 0) 0 := by
  set γ := α t₀
  set β := γ + π
  have hU : ∀ γ' : ℝ, HasDerivAt (fun τ => twistedTranslation γ' τ (primitive g))
      ((-Complex.I) • (-Complex.I) • g) 0 := fun γ' => by
    have := hasDerivAt_twistedTranslation_primitive (ħ := 1) γ' hg
    simp only [div_one, inv_one, Complex.ofReal_one, mul_one] at this
    exact this
  -- the tail of `ψ` is `o(τ)`, since `U_β(τ) ψ - U_γ(τ) ψ = o(τ)` is twice the shifted tail
  have hβγ := (hasDerivWithinAt_Ici_zero_iff (g := fun τ =>
    twistedTranslation β τ (primitive g) - twistedTranslation γ τ (primitive g))
    (by simp [twistedTranslation_zero])).mp (by
      have := ((hU β).sub (hU γ)).hasDerivWithinAt (s := Ici 0)
      rwa [sub_self] at this)
  have hR : HasDerivWithinAt
      (fun τ => V α (t₀ + τ) t₀ (primitive g) - twistedTranslation γ τ (primitive g)) 0
      (Ici 0) 0 := by
    refine (hasDerivWithinAt_Ici_zero_iff (by
      simp [phasePropagator_self hα, twistedTranslation_zero])).mpr fun ε hε => ?_
    filter_upwards [hβγ ε hε, Ico_mem_nhdsGE (show (0 : ℝ) < 1 by norm_num)] with τ hτ hτ1
    have h0 := hτ1.1
    have h1 := hτ1.2
    have hconst := phasePropagator_sub_twistedTranslation_eq (α := fun _ => β) measurable_const
      t₀ γ h0 h1 (primitive g)
    rw [phasePropagator_const β (by linarith), add_sub_cancel_left] at hconst
    have hπ : Complex.exp (-(Complex.I * π)) = -1 := by
      rw [show -(Complex.I * π) = -(π * Complex.I) by ring, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have hβexp : Complex.exp (-(Complex.I * β)) = -Complex.exp (-(Complex.I * γ)) := by
      rw [show -(Complex.I * ((γ + π : ℝ) : ℂ)) = -(Complex.I * γ) + -(Complex.I * π) by
        push_cast; ring, Complex.exp_add, hπ, mul_neg_one]
    have hβ2 : ∀ x : 𝕋, circleRep x < τ → ‖stripPhase (fun _ => β) t₀ γ τ x‖ = 2 := fun x hx => by
      simp only [stripPhase, hx, ↓reduceIte]
      rw [hβexp]
      rw [show -Complex.exp (-(Complex.I * γ)) - Complex.exp (-(Complex.I * γ)) =
        -2 * Complex.exp (-(Complex.I * γ)) by ring, norm_mul, norm_exp_neg_I_mul]
      norm_num
    have htail : ‖tailPart τ (primitive g)‖ ≤ 1 / 2 * (ε * τ) := by
      rw [← norm_circleShift τ]
      refine (Lp.norm_le_mul_norm_of_ae_le_mul ?_).trans
        (mul_le_mul_of_nonneg_left (hconst ▸ hτ) (by norm_num))
      filter_upwards [Lp.coeFn_mulL (memLp_stripPhase measurable_const t₀ γ τ)
          (circleShift τ (tailPart τ (primitive g))),
        coeFn_circleShift τ (tailPart τ (primitive g)),
        (measurePreserving_sub τ).quasiMeasurePreserving.ae_eq_comp
          (coeFn_tailPart τ (primitive g))] with x h₁ h₂ h₃
      simp only [Function.comp_apply] at h₃
      rw [h₁, norm_mul]
      by_cases hx : circleRep x < τ
      · rw [hβ2 x hx]
        linarith
      · rw [h₂, h₃, Set.indicator_of_notMem (show x - (τ : 𝕋) ∉
          {x : 𝕋 | 1 - τ ≤ circleRep x} from fun h => hx
            ((one_sub_le_circleRep_sub_iff h0 h1 x).mp h)), zero_mul, norm_zero]
        positivity
    rw [phasePropagator_sub_twistedTranslation_eq hα t₀ γ h0 h1]
    calc ‖Lp.mulL (stripPhase α t₀ γ τ) (circleShift τ (tailPart τ (primitive g)))‖
        ≤ 2 * ‖circleShift τ (tailPart τ (primitive g))‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
            (Lp.norm_mulL_le (measurable_stripPhase hα t₀ γ τ).aestronglyMeasurable
              (by norm_num) (.of_forall (norm_stripPhase_le_two α t₀ γ τ))) (norm_nonneg _))
      _ ≤ ε * τ := by
          rw [norm_circleShift]
          linarith
  have := hR.add (hU γ).hasDerivWithinAt
  rw [zero_add] at this
  exact this.congr (fun τ _ => (sub_add_cancel _ _).symm) (sub_add_cancel _ _).symm

/-! ### The forward Hamiltonian -/

variable (α) in
/-- The forward domain at `t₀`: the `ψ` for which `τ ↦ U(t₀ + τ, t₀) ψ` has a right derivative
at `0`. -/
def forwardDomain (t₀ : ℝ) : Submodule ℂ L² where
  carrier := {ψ | DifferentiableWithinAt ℝ (fun τ => V α (t₀ + τ) t₀ ψ) (Ici 0) 0}
  add_mem' {ψ φ} hψ hφ := by
    change DifferentiableWithinAt ℝ (fun τ => V α (t₀ + τ) t₀ (ψ + φ)) (Ici 0) 0
    simp only [map_add]
    exact hψ.add hφ
  zero_mem' := by
    change DifferentiableWithinAt ℝ (fun τ => V α (t₀ + τ) t₀ 0) (Ici 0) 0
    simp only [map_zero]
    exact differentiableWithinAt_const _
  smul_mem' c ψ hψ := by
    change DifferentiableWithinAt ℝ (fun τ => V α (t₀ + τ) t₀ (c • ψ)) (Ici 0) 0
    simp only [map_smul]
    exact hψ.const_smul c

lemma mem_forwardDomain {t₀ : ℝ} {ψ : L²} :
    ψ ∈ forwardDomain α t₀ ↔ DifferentiableWithinAt ℝ (fun τ => V α (t₀ + τ) t₀ ψ) (Ici 0) 0 :=
  Iff.rfl

variable (α) in
/-- **The forward Hamiltonian** `H₀ ψ = i ∂₊U(t₀ + τ, t₀) ψ` at `τ = 0`, from the right derivative
only, as the evolution runs forward. -/
def forwardHamiltonian (t₀ : ℝ) : L² →ₗ.[ℂ] L² where
  domain := forwardDomain α t₀
  toFun :=
    { toFun := fun ψ => Complex.I • derivWithin (fun τ => V α (t₀ + τ) t₀ ψ) (Ici 0) 0
      map_add' := fun ψ φ => by
        simp only [Submodule.coe_add, map_add]
        rw [derivWithin_fun_add (mem_forwardDomain.mp ψ.2) (mem_forwardDomain.mp φ.2), smul_add]
      map_smul' := fun c ψ => by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        rw [derivWithin_fun_const_smul c (mem_forwardDomain.mp ψ.2), smul_comm] }

lemma forwardHamiltonian_apply {t₀ : ℝ} (ψ : (forwardHamiltonian α t₀).domain) :
    forwardHamiltonian α t₀ ψ = Complex.I • derivWithin (fun τ => V α (t₀ + τ) t₀ ψ) (Ici 0) 0 :=
  rfl

lemma forwardHamiltonian_of_hasDerivWithinAt {t₀ : ℝ} {ψ v : L²}
    (h : HasDerivWithinAt (fun τ => V α (t₀ + τ) t₀ ψ) v (Ici 0) 0) :
    ∃ hψ : ψ ∈ forwardDomain α t₀, forwardHamiltonian α t₀ ⟨ψ, hψ⟩ = Complex.I • v :=
  ⟨h.differentiableWithinAt, by
    rw [forwardHamiltonian_apply, h.derivWithin (uniqueDiffWithinAt_Ici 0)]⟩

/-- **Right Hölder-½ at `t₀`: the forward Hamiltonian is a restriction of `H_{α(t₀)}`.** -/
theorem forwardHamiltonian_le_momentum (hα : Measurable α) {t₀ : ℝ}
    (hO : ∃ C δ, 0 < δ ∧ ∀ s ∈ Icc (0 : ℝ) δ, |α (t₀ + s) - α t₀| ≤ C * √s) :
    forwardHamiltonian α t₀ ≤ momentum (α t₀) := by
  have key : ∀ ψ : (forwardHamiltonian α t₀).domain, ∃ h : (ψ : L²) ∈ (momentum (α t₀)).domain,
      momentum (α t₀) ⟨ψ, h⟩ = forwardHamiltonian α t₀ ψ := fun ψ => by
    rw [forwardHamiltonian_apply]
    exact momentum_of_hasDerivWithinAt_phasePropagator hα hO
      (mem_forwardDomain.mp ψ.2).hasDerivWithinAt
  refine ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, fun ψ φ hψφ => ?_⟩
  obtain ⟨h, hH⟩ := key ψ
  rw [← hH]
  exact congrArg _ (Subtype.ext hψφ)

/-- **Right `o(√s)` at `t₀`: `H_{α(t₀)}` is a restriction of the forward Hamiltonian.** -/
theorem momentum_le_forwardHamiltonian (hα : Measurable α) {t₀ : ℝ}
    (ho : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) δ, |α (t₀ + s) - α t₀| ≤ ε * √s) :
    momentum (α t₀) ≤ forwardHamiltonian α t₀ := by
  have key : ∀ ψ : (momentum (α t₀)).domain, ∃ h : (ψ : L²) ∈ forwardDomain α t₀,
      forwardHamiltonian α t₀ ⟨ψ, h⟩ = momentum (α t₀) ψ := fun ψ => by
    obtain ⟨h, hH⟩ :=
      forwardHamiltonian_of_hasDerivWithinAt (hasDerivWithinAt_phasePropagator_of_mem hα ho ψ)
    exact ⟨h, by rw [hH, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]⟩
  refine ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, fun ψ φ hψφ => ?_⟩
  obtain ⟨h, hH⟩ := key ψ
  rw [← hH]
  exact congrArg _ (Subtype.ext hψφ)

/-- **Right `o(√s)` at `t₀`: the forward Hamiltonian is `H_{α(t₀)}`**, hence self-adjoint. -/
theorem forwardHamiltonian_eq_momentum (hα : Measurable α) {t₀ : ℝ}
    (ho : ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) δ, |α (t₀ + s) - α t₀| ≤ ε * √s) :
    forwardHamiltonian α t₀ = momentum (α t₀) :=
  le_antisymm (forwardHamiltonian_le_momentum hα (by
      obtain ⟨δ, hδ, h⟩ := ho 1 one_pos
      exact ⟨1, δ, hδ, h⟩))
    (momentum_le_forwardHamiltonian hα ho)

/-! ### The example `α(t) = α₀ + √t` -/

/-- The boundary phase `α(t) = α₀ + √t` (`α₀` for `t ≤ 0`): continuous, but at `t = 0` only
Hölder with exponent `½`. -/
def sqrtPhase (α₀ t : ℝ) : ℝ := α₀ + √t

lemma continuous_sqrtPhase (α₀ : ℝ) : Continuous (sqrtPhase α₀) :=
  continuous_const.add Real.continuous_sqrt

lemma sqrtPhase_holder (α₀ : ℝ) :
    ∃ C δ, 0 < δ ∧ ∀ s ∈ Icc (0 : ℝ) δ, |sqrtPhase α₀ (0 + s) - sqrtPhase α₀ 0| ≤ C * √s :=
  ⟨1, 1, one_pos, fun s _ => by simp [sqrtPhase, abs_of_nonneg (Real.sqrt_nonneg s)]⟩

/-- Away from `0`, `α₀ + √t` is `o(√s)` from the right (it is locally Lipschitz, or constant). -/
lemma sqrtPhase_littleO (α₀ : ℝ) {t₀ : ℝ} (ht : t₀ ≠ 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) δ,
      |sqrtPhase α₀ (t₀ + s) - sqrtPhase α₀ t₀| ≤ ε * √s := by
  intro ε hε
  simp only [sqrtPhase, add_sub_add_left_eq_sub]
  rcases ht.lt_or_gt with ht | ht
  · refine ⟨-t₀, by linarith, fun s hs => ?_⟩
    rw [Real.sqrt_eq_zero'.mpr (by linarith [hs.2]), Real.sqrt_eq_zero'.mpr ht.le, sub_zero,
      abs_zero]
    positivity
  · refine ⟨ε ^ 2 * t₀, by positivity, fun s hs => ?_⟩
    have ha := Real.sq_sqrt (show 0 ≤ t₀ + s by linarith [hs.1])
    have hb := Real.sq_sqrt ht.le
    have hb0 : 0 < √t₀ := Real.sqrt_pos.mpr ht
    have hab : √t₀ ≤ √(t₀ + s) := Real.sqrt_le_sqrt (by linarith [hs.1])
    have hq : √s ^ 2 = s := Real.sq_sqrt hs.1
    have hq_le : √s ≤ ε * √t₀ := by
      rw [← Real.sqrt_sq hε.le, ← Real.sqrt_mul (sq_nonneg ε)]
      exact Real.sqrt_le_sqrt hs.2
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    have key : (√(t₀ + s) - √t₀) * √t₀ ≤ ε * √s * √t₀ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (Real.sqrt_nonneg (t₀ + s)),
        mul_le_mul_of_nonneg_left hq_le (Real.sqrt_nonneg s)]
    exact le_of_mul_le_mul_right key hb0

/-- `|e^{-i(a + θ)} - e^{-ia}| = 2 sin(θ/2) ≥ (2/π) θ` for `0 ≤ θ ≤ π`. -/
lemma two_div_pi_mul_le_norm_exp_sub (a θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ π) :
    2 / π * θ ≤
      ‖Complex.exp (-(Complex.I * ((a + θ : ℝ) : ℂ))) - Complex.exp (-(Complex.I * a))‖ := by
  have e : Complex.exp (-(Complex.I * ((a + θ : ℝ) : ℂ))) - Complex.exp (-(Complex.I * a)) =
      Complex.exp (-(Complex.I * a)) * (Complex.exp (Complex.I * ((-θ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, norm_exp_neg_I_mul, one_mul, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_two, neg_div, Real.sin_neg, abs_neg,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
  have := Real.mul_le_sin (show 0 ≤ θ / 2 by linarith) (show θ / 2 ≤ π / 2 by linarith)
  calc 2 / π * θ = 2 * (2 / π * (θ / 2)) := by ring
    _ ≤ 2 * Real.sin (θ / 2) := by linarith

/-- **At `t₀ = 0` the forward domain is in `H¹₀(0, 1)`**: if `τ ↦ U(τ, 0) ψ` has a right
derivative at `0`, then `ψ(x) = ∫₀ˣ g` with `∫₀¹ g = 0`. The right derivative gives `ψ` in the
domain of `H_{α₀}`, so `ψ` is continuous with `ψ(1) = e^{iα₀} ψ(0)`. On the strip `x < τ`,
`U(τ, 0) ψ - e^{-iτH_{α₀}} ψ` is `(e^{-i√(τ - x)} - 1) e^{-iα₀} ψ(x - τ + 1)`, of norm `≳ |ψ(1)| τ`;
it must be `o(τ)`, so `ψ(1) = ψ(0) = 0`. -/
theorem mem_sobolevZero_of_hasDerivWithinAt_sqrtPhase (α₀ : ℝ) {ψ v : L²}
    (h : HasDerivWithinAt (fun τ => V (sqrtPhase α₀) (0 + τ) 0 ψ) v (Ici 0) 0) :
    ψ ∈ sobolevZero := by
  have hα : Measurable (sqrtPhase α₀) := (continuous_sqrtPhase α₀).measurable
  have hγ : sqrtPhase α₀ 0 = α₀ := by simp [sqrtPhase]
  obtain ⟨hψ, hHψ⟩ := momentum_of_hasDerivWithinAt_phasePropagator hα (sqrtPhase_holder α₀) h
  have hpair : IsMomentumPair α₀ ψ (Complex.I • v) := by
    have hg := (momentum (sqrtPhase α₀ 0)).mem_graph ⟨ψ, hψ⟩
    rw [hHψ, mem_graph_momentum] at hg
    change IsMomentumPair (sqrtPhase α₀ 0) ψ (Complex.I • v) at hg
    rwa [hγ] at hg
  obtain ⟨hψ', hH'⟩ := momentum_of_inner (isMomentumPair_iff.mp hpair)
  obtain ⟨c, g, hbc, hψeq, -⟩ := hpair
  have hU : HasDerivAt (fun τ => twistedTranslation α₀ τ ψ) v 0 := by
    have := hasDerivAt_twistedTranslation_momentum (ħ := 1) ⟨ψ, hψ'⟩
    rw [hH'] at this
    simp only [div_one, Complex.ofReal_one, mul_one, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul] at this
    exact this
  have hR := (hasDerivWithinAt_Ici_zero_iff (g := fun τ =>
    V (sqrtPhase α₀) (0 + τ) 0 ψ - twistedTranslation α₀ τ ψ)
    (by simp [phasePropagator_self hα, twistedTranslation_zero])).mp (by
      have := h.sub hU.hasDerivWithinAt
      rwa [sub_self] at this)
  have hψfun : ψ =ᵐ[μc] fun y => c + primitiveFun g y := by
    rw [hψeq]
    filter_upwards [Lp.coeFn_add (c • planeWave 0) (primitive g), Lp.coeFn_smul c (planeWave 0),
      (memLp_planeWaveFun 0).coeFn_toLp, (memLp_primitiveFun g).coeFn_toLp] with y h₁ h₂ h₃ h₄
    rw [h₁, Pi.add_apply, h₂, Pi.smul_apply, planeWave, h₃, primitive, h₄, smul_eq_mul]
    simp [planeWaveFun]
  set b := c + ∫ u in (0 : ℝ)..1, g (u : 𝕋) with hbdef
  have hb : b = 0 := by
    by_contra hb
    have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
    have hπ := Real.pi_pos
    -- `c + ∫₀ᵘ g` is close to `b` for `u` near `1`
    obtain ⟨η, hη, hηb⟩ : ∃ η > 0, ∀ u : ℝ, |u - 1| < η →
        ‖b‖ / 2 ≤ ‖c + ∫ w in (0 : ℝ)..u, g (w : 𝕋)‖ := by
      obtain ⟨η, hη, hc⟩ := Metric.continuousAt_iff.mp
        ((continuous_primitive_lift g).continuousAt (x := 1)) (‖b‖ / 2) (by positivity)
      refine ⟨η, hη, fun u hu => ?_⟩
      have h1 := hc (show dist u 1 < η by rwa [Real.dist_eq])
      rw [dist_eq_norm] at h1
      have h2 : b = (c + ∫ w in (0 : ℝ)..u, g (w : 𝕋)) -
          ((∫ w in (0 : ℝ)..u, g (w : 𝕋)) - ∫ w in (0 : ℝ)..1, g (w : 𝕋)) := by
        rw [hbdef]
        ring
      have h3 := norm_sub_le (c + ∫ w in (0 : ℝ)..u, g (w : 𝕋))
        ((∫ w in (0 : ℝ)..u, g (w : 𝕋)) - ∫ w in (0 : ℝ)..1, g (w : 𝕋))
      rw [← h2] at h3
      linarith
    obtain ⟨τ, hτR, hτ⟩ := (((hR (‖b‖ / (4 * π)) (by positivity)).filter_mono
      (nhdsWithin_mono _ Ioi_subset_Ici_self)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < min η 1 by positivity))).exists
    have hτ0 := hτ.1
    have hτ1 : τ < 1 := lt_of_lt_of_le hτ.2 (min_le_right _ _)
    have hτη : τ < η := lt_of_lt_of_le hτ.2 (min_le_left _ _)
    -- the lower bound on the strip `x < τ / 2`
    set B := 2 / π * √(τ / 2) * (‖b‖ / 2)
    have hlow : B * √((μc).real {x : 𝕋 | circleRep x < τ / 2}) ≤
        ‖V (sqrtPhase α₀) (0 + τ) 0 ψ - twistedTranslation α₀ τ ψ‖ := by
      refine le_norm_of_ae_le (measurableSet_strip _) (by positivity) ?_
      filter_upwards [phasePropagator_sub_twistedTranslation hα 0 α₀ hτ0.le hτ1 ψ,
        (measurePreserving_sub τ).quasiMeasurePreserving.ae_eq_comp hψfun] with x h₁ h₂ hxS
      simp only [Function.comp_apply] at h₂
      have hxS' : circleRep x < τ / 2 := hxS
      have hx0 := (circleRep_mem x).1
      have hxτ : circleRep x < τ := by linarith
      rw [h₁, h₂, norm_mul]
      refine mul_le_mul ?_ ?_ (by positivity) (norm_nonneg _)
      · simp only [stripPhase, hxτ, ↓reduceIte, sqrtPhase]
        have hθ : √(τ / 2) ≤ √(0 + τ - circleRep x) := Real.sqrt_le_sqrt (by linarith)
        have hθπ : √(0 + τ - circleRep x) ≤ π := by
          refine (Real.sqrt_le_one.mpr (by linarith)).trans ?_
          linarith [Real.two_le_pi]
        refine le_trans ?_ (two_div_pi_mul_le_norm_exp_sub α₀ _ (Real.sqrt_nonneg _) hθπ)
        exact mul_le_mul_of_nonneg_left hθ (by positivity)
      · rw [primitiveFun, circleRep_sub_of_lt hτ1 hxτ]
        exact hηb _ (by rw [abs_lt]; constructor <;> linarith)
    rw [measureReal_strip (by linarith) (by linarith)] at hlow
    have hB : B * √(τ / 2) = ‖b‖ * τ / (2 * π) := by
      rw [show B * √(τ / 2) = 2 / π * (√(τ / 2) * √(τ / 2)) * (‖b‖ / 2) by ring,
        Real.mul_self_sqrt (by linarith)]
      field_simp
    have h1 : ‖b‖ * τ / (2 * π) ≤ ‖b‖ / (4 * π) * τ := hB ▸ hlow.trans hτR
    have h2 : ‖b‖ / (4 * π) * τ < ‖b‖ * τ / (2 * π) := by
      rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hbpos hτ0, mul_pos (mul_pos hbpos hτ0) hπ]
    linarith
  have hc : c = 0 := by
    have : Complex.exp (Complex.I * α₀) * c = 0 := hbc.symm.trans hb
    exact (mul_eq_zero.mp this).resolve_left (Complex.exp_ne_zero _)
  refine ⟨g, ?_, ?_⟩
  · rw [hbdef, hc, zero_add] at hb
    exact hb
  · rw [hψeq, hc, zero_smul, zero_add]

/-- **At `t₀ = 0` the forward domain is `H¹₀(0, 1)`.** -/
theorem forwardDomain_sqrtPhase (α₀ : ℝ) :
    (forwardDomain (sqrtPhase α₀) 0 : Set L²) = sobolevZero := by
  have hα : Measurable (sqrtPhase α₀) := (continuous_sqrtPhase α₀).measurable
  ext ψ
  constructor
  · intro hψ
    exact mem_sobolevZero_of_hasDerivWithinAt_sqrtPhase α₀
      (mem_forwardDomain.mp hψ).hasDerivWithinAt
  · rintro ⟨g, hg, rfl⟩
    exact (hasDerivWithinAt_phasePropagator_primitive hα 0 hg).differentiableWithinAt

lemma exp_ne_exp_add_pi (α₀ : ℝ) :
    Complex.exp (Complex.I * α₀) ≠ Complex.exp (Complex.I * ((α₀ + π : ℝ) : ℂ)) := by
  rw [Complex.ofReal_add, mul_add, Complex.exp_add, mul_comm Complex.I (π : ℂ),
    Complex.exp_pi_mul_I, mul_neg_one]
  intro h
  exact Complex.exp_ne_zero (Complex.I * α₀) (by linear_combination h / 2)

/-- **At `t₀ = 0` the forward Hamiltonian is the minimal momentum** `-i d/dx` on `H¹₀(0, 1)`: the
operator `H₀` of the switched example, for any two boundary phases. -/
theorem forwardHamiltonian_sqrtPhase (α₀ : ℝ) :
    forwardHamiltonian (sqrtPhase α₀) 0 = switchedHamiltonian 1 α₀ (α₀ + π) := by
  have hα : Measurable (sqrtPhase α₀) := (continuous_sqrtPhase α₀).measurable
  have hdom : forwardDomain (sqrtPhase α₀) 0 = switchedDomain 1 α₀ (α₀ + π) :=
    SetLike.coe_injective ((forwardDomain_sqrtPhase α₀).trans
      (switchedDomain_eq one_ne_zero (exp_ne_exp_add_pi α₀)).symm)
  refine LinearPMap.ext hdom fun ψ hf hs => ?_
  obtain ⟨g, hg, rfl⟩ : ψ ∈ sobolevZero := by
    rw [← forwardDomain_sqrtPhase α₀]
    exact hf
  obtain ⟨h, hH⟩ :=
    forwardHamiltonian_of_hasDerivWithinAt (hasDerivWithinAt_phasePropagator_primitive hα 0 hg)
  rw [hH, switchedHamiltonian_primitive one_ne_zero hg, smul_smul, smul_smul]
  congr 1
  linear_combination Complex.I * Complex.I_sq

/-- **The forward Hamiltonian at `0` is not self-adjoint.** -/
theorem not_isSelfAdjoint_forwardHamiltonian_sqrtPhase (α₀ : ℝ) :
    ¬ IsSelfAdjoint (forwardHamiltonian (sqrtPhase α₀) 0) := by
  rw [forwardHamiltonian_sqrtPhase]
  exact not_isSelfAdjoint_switchedHamiltonian one_ne_zero (exp_ne_exp_add_pi α₀)

/-- **Unbounded time-dependent Hamiltonians, forward derivative: a continuous `H(t) = H_{α(t)}`
whose forward Hamiltonian is not self-adjoint.** For `α(t) = α₀ + √t`, the propagator `U(t₁, t₀)`
of `H(t) = H_{α(t)}` is unitary, `U(t, t) = 1`, and `U(t₂, t₁) U(t₁, t₀) = U(t₂, t₀)`. At every
`t₀ ≠ 0` the forward Hamiltonian is `H_{α(t₀)}`, which is self-adjoint. At `t₀ = 0` it has a dense
domain, `H¹₀(0, 1)`, and is symmetric, but it is not self-adjoint. -/
theorem sqrtPhase_counterexample (α₀ : ℝ) :
    Continuous (sqrtPhase α₀) ∧
      (∀ t₁ t₀, V (sqrtPhase α₀) t₁ t₀ ∈ unitary (L² →L[ℂ] L²)) ∧
      (∀ t, V (sqrtPhase α₀) t t = 1) ∧
      (∀ t₀ t₁ t₂ : ℝ, t₀ ≤ t₁ → t₁ ≤ t₂ →
        V (sqrtPhase α₀) t₂ t₁ ∘L V (sqrtPhase α₀) t₁ t₀ = V (sqrtPhase α₀) t₂ t₀) ∧
      (∀ t₀ ≠ 0, forwardHamiltonian (sqrtPhase α₀) t₀ = momentum (sqrtPhase α₀ t₀) ∧
        IsSelfAdjoint (forwardHamiltonian (sqrtPhase α₀) t₀)) ∧
      Dense ((forwardHamiltonian (sqrtPhase α₀) 0).domain : Set L²) ∧
      (∀ ψ φ : (forwardHamiltonian (sqrtPhase α₀) 0).domain,
        ⟪forwardHamiltonian (sqrtPhase α₀) 0 ψ, φ⟫_ℂ =
          ⟪(ψ : L²), forwardHamiltonian (sqrtPhase α₀) 0 φ⟫_ℂ) ∧
      ¬ IsSelfAdjoint (forwardHamiltonian (sqrtPhase α₀) 0) := by
  have hα : Measurable (sqrtPhase α₀) := (continuous_sqrtPhase α₀).measurable
  refine ⟨continuous_sqrtPhase α₀, phasePropagator_mem_unitary hα, phasePropagator_self hα,
    fun _ _ _ => phasePropagator_comp hα, fun t₀ ht => ?_, ?_, ?_,
    not_isSelfAdjoint_forwardHamiltonian_sqrtPhase α₀⟩
  · have h := forwardHamiltonian_eq_momentum hα (sqrtPhase_littleO α₀ ht)
    exact ⟨h, h ▸ isSelfAdjoint_momentum⟩
  · rw [forwardHamiltonian_sqrtPhase]
    exact dense_switchedDomain
  · rw [forwardHamiltonian_sqrtPhase]
    exact switchedHamiltonian_symm

end UnitaryEntropy
