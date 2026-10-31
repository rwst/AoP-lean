/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivatives of operator-valued functions evaluated at a fixed vector

If `f : 𝕜 → F →L[𝕜'] G` has derivative `f'` at `t`, then `s ↦ f s x` has derivative `f' x` at `t`,
for every fixed `x`. Mathlib's `HasDerivAt.clm_apply` needs the operators to be linear over the
field `𝕜` of the variable. Here they may be linear over a larger normed algebra `𝕜'`, as for a
complex operator depending on a real time.

## Main results

* `HasDerivAt.clm_apply_const`
-/

@[expose] public section

variable {𝕜 𝕜' F G : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [NormedAddCommGroup F] [NormedSpace 𝕜' F] [NormedAddCommGroup G]
  [NormedSpace 𝕜' G] [NormedSpace 𝕜 G] [IsScalarTower 𝕜 𝕜' G]

/-- Evaluation at a fixed vector preserves derivatives of operator-valued functions, also when
the operators are linear over a larger field than the variable. -/
theorem HasDerivAt.clm_apply_const {f : 𝕜 → F →L[𝕜'] G} {f' : F →L[𝕜'] G} {t : 𝕜}
    (h : HasDerivAt f f' t) (x : F) : HasDerivAt (fun s => f s x) (f' x) t :=
  ((ContinuousLinearMap.apply 𝕜' G x).restrictScalars 𝕜).hasFDerivAt.comp_hasDerivAt t h
