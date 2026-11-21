/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Determinant

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A global inverse function theorem

An injective `C^n` map `f : E → F`, `n ≠ 0`, whose derivative is invertible at every point is
an open embedding, and its inverse on the open set `range f` is `C^n`: `f` is a `C^n`
diffeomorphism of `E` onto an open subset of `F`. Conversely, a map with a left inverse that is
differentiable on the range has injective derivatives; in finite dimension, a nonzero
determinant.

## Main results

* `ContDiff.isOpenEmbedding_of_injective`: `f` is an open embedding.
* `ContDiff.contDiffOn_symm_of_injective`: the inverse is `C^n` on `range f`.
* `ContDiff.exists_contDiffOn_leftInverse_of_injective`,
  `ContDiff.exists_contDiffOn_leftInverse_of_det_ne_zero`: the same, with an inverse given as a
  left inverse of `f`.
* `det_fderiv_ne_zero_of_leftInverse`: the converse, in finite dimension.
-/

@[expose] public section

open Function Set Topology

namespace ContDiff

variable {𝕂 : Type*} [RCLike 𝕂] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F}
  {f' : E → E ≃L[𝕂] F} {n : WithTop ℕ∞}

/-- **Global inverse function theorem.** An injective `C^n` map, `n ≠ 0`, with an invertible
derivative at every point is an open embedding. -/
theorem isOpenEmbedding_of_injective (hf : ContDiff 𝕂 n f) (hn : n ≠ 0)
    (hf' : ∀ x, HasFDerivAt f (f' x : E →L[𝕂] F) x) (hinj : Injective f) :
    IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap hf.continuous hinj <|
    isOpenMap_of_hasStrictFDerivAt_equiv fun x => hf.contDiffAt.hasStrictFDerivAt (hf' x) hn

/-- **Global inverse function theorem.** The inverse of an injective `C^n` map, `n ≠ 0`, with an
invertible derivative at every point is `C^n` on its range. -/
theorem contDiffOn_symm_of_injective (hf : ContDiff 𝕂 n f) (hn : n ≠ 0)
    (hf' : ∀ x, HasFDerivAt f (f' x : E →L[𝕂] F) x) (hinj : Injective f) :
    ContDiffOn 𝕂 n
      ((hf.isOpenEmbedding_of_injective hn hf' hinj).toOpenPartialHomeomorph f).symm
      (range f) := by
  intro y hy
  set e := (hf.isOpenEmbedding_of_injective hn hf' hinj).toOpenPartialHomeomorph f
  have hye : y ∈ e.target := by
    rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  have he : (e : E → F) = f := Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply _ _
  refine (e.contDiffAt_symm hye (f₀' := f' (e.symm y)) ?_ ?_).contDiffWithinAt
  · rw [he]
    exact hf' _
  · rw [he]
    exact hf.contDiffAt

/-- **Global inverse function theorem.** An injective `C^n` map, `n ≠ 0`, with an invertible
derivative at every point has an open range and a left inverse that is `C^n` on it. -/
theorem exists_contDiffOn_leftInverse_of_injective (hf : ContDiff 𝕂 n f) (hn : n ≠ 0)
    (hf' : ∀ x, HasFDerivAt f (f' x : E →L[𝕂] F) x) (hinj : Injective f) :
    IsOpen (range f) ∧ ∃ g : F → E, ContDiffOn 𝕂 n g (range f) ∧ LeftInverse g f :=
  ⟨(hf.isOpenEmbedding_of_injective hn hf' hinj).isOpen_range, _,
    hf.contDiffOn_symm_of_injective hn hf' hinj, fun _ =>
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv _ _⟩

/-- **Global inverse function theorem**, in finite dimension. An injective `C^n` self-map,
`n ≠ 0`, whose derivative has nonzero determinant at every point has an open range and a left
inverse that is `C^n` on it. -/
theorem exists_contDiffOn_leftInverse_of_det_ne_zero [FiniteDimensional 𝕂 E] {f : E → E}
    (hf : ContDiff 𝕂 n f) (hn : n ≠ 0) (hdet : ∀ x, (fderiv 𝕂 f x).det ≠ 0)
    (hinj : Injective f) :
    IsOpen (range f) ∧ ∃ g : E → E, ContDiffOn 𝕂 n g (range f) ∧ LeftInverse g f :=
  hf.exists_contDiffOn_leftInverse_of_injective hn
    (f' := fun x => (fderiv 𝕂 f x).toContinuousLinearEquivOfDetNeZero (hdet x))
    (fun x => by
      rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
      exact (hf.differentiable hn x).hasFDerivAt) hinj

end ContDiff

/-- A self-map of a finite-dimensional space with a left inverse that is differentiable at
`f x` has a derivative of nonzero determinant at `x`. -/
theorem det_fderiv_ne_zero_of_leftInverse {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {f g : E → E} {x : E}
    (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g (f x)) (hgf : LeftInverse g f) :
    (fderiv 𝕜 f x).det ≠ 0 := by
  have hid : (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) = ContinuousLinearMap.id 𝕜 E := by
    have h := hg.hasFDerivAt.comp x hf.hasFDerivAt
    rw [show g ∘ f = id from funext hgf] at h
    exact h.unique (hasFDerivAt_id x)
  intro h0
  have h1 := congrArg ContinuousLinearMap.det hid
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id] at h0 h1
  simp [h0] at h1
