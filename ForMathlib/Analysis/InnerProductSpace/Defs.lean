/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# The seminorm of a pre-inner product core

A `PreInnerProductSpace.Core 𝕜 F` is an inner product on a vector space `F` that carries no
norm or topology. Mathlib turns it into a `SeminormedAddCommGroup` structure, which fixes the
topology of `F`. This file packages `x ↦ √(re ⟪x, x⟫)` as a bare `Seminorm 𝕜 F` instead, so that
it can be compared with an arbitrary topology on `F`.

## Main results

* `PreInnerProductSpace.Core.toSeminorm`: the seminorm `x ↦ √(re ⟪x, x⟫)`;
* `PreInnerProductSpace.Core.norm_inner_le`: Cauchy–Schwarz for this seminorm;
* `PreInnerProductSpace.Core.continuous_inner`: for a topological additive group, the inner
  product is jointly continuous as soon as the seminorm is continuous;
* `PreInnerProductSpace.Core.continuous_toSeminorm`: conversely, the seminorm is continuous
  when the inner product is.
-/

open RCLike Filter Topology

@[expose] public noncomputable section

namespace PreInnerProductSpace.Core

variable {𝕜 F : Type*} [RCLike 𝕜] [AddCommGroup F] [Module 𝕜 F]
  (c : PreInnerProductSpace.Core 𝕜 F)

/-- The seminorm `x ↦ √(re ⟪x, x⟫)` of a pre-inner product core, as a bare seminorm. -/
def toSeminorm : Seminorm 𝕜 F :=
  letI : PreInnerProductSpace.Core 𝕜 F := c
  @normSeminorm 𝕜 F _ InnerProductSpace.Core.toSeminormedAddCommGroup
    InnerProductSpace.Core.toNormedSpace

theorem toSeminorm_apply (x : F) : c.toSeminorm x = √(re (c.inner x x)) := rfl

/-- Cauchy–Schwarz: `‖⟪x, y⟫‖ ≤ p x * p y`. -/
theorem norm_inner_le (x y : F) : ‖c.inner x y‖ ≤ c.toSeminorm x * c.toSeminorm y :=
  letI : PreInnerProductSpace.Core 𝕜 F := c
  InnerProductSpace.Core.norm_inner_le_norm x y

/-- `⟪v, w⟫ - ⟪v₀, w₀⟫ = ⟪v - v₀, w - w₀⟫ + ⟪v - v₀, w₀⟫ + ⟪v₀, w - w₀⟫`. -/
lemma inner_sub_inner (v w v₀ w₀ : F) :
    c.inner v w - c.inner v₀ w₀ =
      c.inner (v - v₀) (w - w₀) + c.inner (v - v₀) w₀ + c.inner v₀ (w - w₀) := by
  let : PreInnerProductSpace.Core 𝕜 F := c
  have h₁ := InnerProductSpace.Core.inner_sub_left (𝕜 := 𝕜) v v₀ (w - w₀)
  have h₂ := InnerProductSpace.Core.inner_sub_left (𝕜 := 𝕜) v v₀ w₀
  have h₃ := InnerProductSpace.Core.inner_sub_right (𝕜 := 𝕜) v w w₀
  have h₄ := InnerProductSpace.Core.inner_sub_right (𝕜 := 𝕜) v₀ w w₀
  change c.inner (v - v₀) (w - w₀) = _ at h₁
  change c.inner (v - v₀) w₀ = _ at h₂
  change c.inner v (w - w₀) = _ at h₃
  change c.inner v₀ (w - w₀) = _ at h₄
  rw [h₁, h₂, h₄, h₃]
  ring

/-- If the seminorm of a pre-inner product core is continuous for a group topology, then the
inner product is jointly continuous. -/
theorem continuous_inner [TopologicalSpace F] [IsTopologicalAddGroup F]
    (h : Continuous c.toSeminorm) : Continuous fun p : F × F => c.inner p.1 p.2 := by
  refine continuous_iff_continuousAt.mpr fun ⟨v₀, w₀⟩ => ?_
  have hv : Tendsto (fun p : F × F => c.toSeminorm (p.1 - v₀)) (𝓝 (v₀, w₀)) (𝓝 0) := by
    have : Continuous fun p : F × F => c.toSeminorm (p.1 - v₀) := by fun_prop
    simpa using this.tendsto (v₀, w₀)
  have hw : Tendsto (fun p : F × F => c.toSeminorm (p.2 - w₀)) (𝓝 (v₀, w₀)) (𝓝 0) := by
    have : Continuous fun p : F × F => c.toSeminorm (p.2 - w₀) := by fun_prop
    simpa using this.tendsto (v₀, w₀)
  have hlim : Tendsto (fun p : F × F => c.toSeminorm (p.1 - v₀) * c.toSeminorm (p.2 - w₀) +
      c.toSeminorm (p.1 - v₀) * c.toSeminorm w₀ + c.toSeminorm v₀ * c.toSeminorm (p.2 - w₀))
      (𝓝 (v₀, w₀)) (𝓝 0) := by
    simpa using ((hv.mul hw).add (hv.mul_const _)).add (hw.const_mul _)
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _)
    (fun p => ?_) hlim)
  rw [inner_sub_inner]
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_) <;> exact c.norm_inner_le _ _

/-- If the inner product of a pre-inner product core is jointly continuous, then so is its
seminorm. -/
theorem continuous_toSeminorm [TopologicalSpace F]
    (h : Continuous fun p : F × F => c.inner p.1 p.2) : Continuous c.toSeminorm := by
  have : Continuous fun x : F => c.inner x x := h.comp (continuous_id.prodMk continuous_id)
  exact (continuous_re.comp this).sqrt

end PreInnerProductSpace.Core
