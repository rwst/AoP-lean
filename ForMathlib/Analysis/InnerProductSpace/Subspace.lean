/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Summable combinations of an orthonormal family

## Main results

* `Orthonormal.summable_smul_iff`: for an orthonormal family `v` in a Hilbert space, `∑ aᵢ vᵢ`
  converges iff `∑ |aᵢ|²` does.
-/

@[expose] public section

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For an orthonormal family `v` in a Hilbert space, `∑ aᵢ vᵢ` converges iff `∑ |aᵢ|²` does. -/
theorem Orthonormal.summable_smul_iff [CompleteSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal 𝕜 v) {a : ι → 𝕜} :
    Summable (fun i => a i • v i) ↔ Summable fun i => ‖a i‖ ^ 2 := by
  simpa using hv.orthogonalFamily.summable_iff_norm_sq_summable a
