/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# The Leibniz rule for multiplication by a temperate growth function

For a function `g` of temperate growth whose directional derivative `∂_m g` has temperate
growth too, the product rule `∂_m (g • f) = (∂_m g) • f + g • ∂_m f` holds for Schwartz maps
and, by duality, for tempered distributions.

## Main results

* `SchwartzMap.lineDerivOp_smulLeftCLM`: the product rule on `𝓢(E, F)`;
* `TemperedDistribution.lineDerivOp_smulLeftCLM`: the product rule on `𝓢'(E, F)`.
-/

@[expose] public noncomputable section

open LineDeriv
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SchwartzMap

variable [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The product rule for a Schwartz map times a function of temperate growth. -/
theorem lineDerivOp_smulLeftCLM {g : E → ℂ} {m : E} (hg : g.HasTemperateGrowth)
    (hg' : (fun x => fderiv ℝ g x m).HasTemperateGrowth) (f : 𝓢(E, F)) :
    ∂_{m} (smulLeftCLM F g f) =
      smulLeftCLM F (fun x => fderiv ℝ g x m) f + smulLeftCLM F g (∂_{m} f) := by
  ext x
  have hgd : DifferentiableAt ℝ g x := (hg.1.differentiable (by simp)).differentiableAt
  have hfd : DifferentiableAt ℝ f x := f.differentiableAt
  rw [lineDerivOp_apply_eq_fderiv, smulLeftCLM_apply hg, fderiv_fun_smul hgd hfd]
  simp [smulLeftCLM_apply_apply hg', smulLeftCLM_apply_apply hg, lineDerivOp_apply_eq_fderiv,
    add_comm]

end SchwartzMap

namespace TemperedDistribution

variable [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℂ F]

/-- The product rule for a tempered distribution times a function of temperate growth. -/
theorem lineDerivOp_smulLeftCLM {g : E → ℂ} {m : E} (hg : g.HasTemperateGrowth)
    (hg' : (fun x => fderiv ℝ g x m).HasTemperateGrowth) (u : 𝓢'(E, F)) :
    ∂_{m} (smulLeftCLM F g u) =
      smulLeftCLM F (fun x => fderiv ℝ g x m) u + smulLeftCLM F g (∂_{m} u) := by
  ext φ
  simp [SchwartzMap.lineDerivOp_smulLeftCLM hg hg']

end TemperedDistribution
