/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Strongly continuous families of operators

A family `A t` of bounded operators on a Banach space is strongly continuous if `t ↦ A t x` is
continuous for every `x`. By the Banach–Steinhaus theorem it is then bounded in operator norm on
compact sets, hence near every point of a locally compact parameter space. This gives the two
rules used for propagators: `t ↦ A t (u t)` is continuous along a continuous `u`, and for a real
parameter the product rule `d/dt A t (u t) = A t u' + (d/dt A t) (u t)` holds when `u` is
differentiable and `s ↦ A s (u t)` is differentiable at `t`. No norm continuity of `t ↦ A t` is
needed.

## Main results

* `ContinuousLinearMap.exists_norm_le_of_continuous_apply`: a bound on a compact set;
* `ContinuousLinearMap.eventually_norm_le_of_continuous_apply`: a bound near a point;
* `ContinuousLinearMap.tendsto_apply_apply`, `ContinuousLinearMap.continuous_apply_apply`:
  continuity of `t ↦ A t (u t)`;
* `ContinuousLinearMap.hasDerivAt_apply_apply`: the product rule.
-/

open Filter Topology

public section

namespace ContinuousLinearMap

variable {𝕜 E F X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace E] [TopologicalSpace X]
  {A : X → E →L[𝕜] F}

/-- **Banach–Steinhaus** for a strongly continuous family: it is bounded in operator norm on a
compact set. -/
theorem exists_norm_le_of_continuous_apply (hA : ∀ x, Continuous (A · x)) {K : Set X}
    (hK : IsCompact K) : ∃ C, ∀ t ∈ K, ‖A t‖ ≤ C := by
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : K => A t) fun x => by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hA x).continuousOn
    exact ⟨C, fun t => hC t t.2⟩
  exact ⟨C, fun t ht => hC ⟨t, ht⟩⟩

/-- A strongly continuous family on a locally compact space is bounded in operator norm near
every point. -/
theorem eventually_norm_le_of_continuous_apply [WeaklyLocallyCompactSpace X]
    (hA : ∀ x, Continuous (A · x)) (t₀ : X) : ∃ C, ∀ᶠ t in 𝓝 t₀, ‖A t‖ ≤ C := by
  obtain ⟨K, hK, hK₀⟩ := exists_compact_mem_nhds t₀
  obtain ⟨C, hC⟩ := exists_norm_le_of_continuous_apply hA hK
  exact ⟨C, Filter.mem_of_superset hK₀ hC⟩

/-- If `A` is strongly continuous and `u t → v` along a filter `l ≤ 𝓝 t₀`, then
`A t (u t) → A t₀ v`. -/
theorem tendsto_apply_apply [WeaklyLocallyCompactSpace X] (hA : ∀ x, Continuous (A · x))
    {l : Filter X} {t₀ : X} (hl : l ≤ 𝓝 t₀) {u : X → E} {v : E} (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun t => A t (u t)) l (𝓝 (A t₀ v)) := by
  obtain ⟨C, hC⟩ := eventually_norm_le_of_continuous_apply hA t₀
  have h₁ : Tendsto (fun t => A t (u t - v)) l (𝓝 0) := by
    have h : Tendsto (fun t => C * ‖u t - v‖) l (𝓝 0) := by
      simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hu).const_mul C
    refine squeeze_zero_norm' (Eventually.mono (hl hC) fun t ht => ?_) h
    exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  have h₂ : Tendsto (fun t => A t v) l (𝓝 (A t₀ v)) := ((hA v).tendsto t₀).mono_left hl
  simpa [map_sub] using h₁.add h₂

/-- A strongly continuous family applied along a continuous curve is continuous. -/
theorem continuous_apply_apply [WeaklyLocallyCompactSpace X] (hA : ∀ x, Continuous (A · x))
    {u : X → E} (hu : Continuous u) : Continuous fun t => A t (u t) :=
  continuous_iff_continuousAt.mpr fun t₀ => tendsto_apply_apply hA le_rfl (hu.tendsto t₀)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [CompleteSpace E] {A : ℝ → E →L[ℝ] F}

/-- **Product rule** for a strongly continuous family: if `u` is differentiable at `t` and
`s ↦ A s (u t)` has derivative `a'` at `t`, then `s ↦ A s (u s)` has derivative
`A t u' + a'` at `t`. -/
theorem hasDerivAt_apply_apply (hA : ∀ x, Continuous (A · x)) {u : ℝ → E} {u' : E} {a' : F}
    {t : ℝ} (hu : HasDerivAt u u' t) (ha : HasDerivAt (fun s => A s (u t)) a' t) :
    HasDerivAt (fun s => A s (u s)) (A t u' + a') t := by
  have hg : HasDerivAt (fun s => A s (u s - u t)) (A t u') t := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h := tendsto_apply_apply hA nhdsWithin_le_nhds (hasDerivAt_iff_tendsto_slope.mp hu)
    refine h.congr fun s => ?_
    simp [slope_def_module, map_smul]
  convert ha.add hg using 1
  · ext s
    simp [map_sub]
  · exact add_comm _ _

end ContinuousLinearMap
