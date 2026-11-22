/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
import ForMathlib.Geometry.Manifold.DifferentialForm.Integration.Measure
import ForMathlib.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Area-preserving isotopies of a surface

On a surface, the symplectic volume form `σ¹ / 1!` of a two-form `σ` is `σ` itself
(`TauCeti.SmoothTwoForm.volumeForm_one_val`), so the Liouville measure is the area `|σ|`. A map
preserving `σ` preserves the area (`Homeomorph.measurePreserving_liouvilleMeasure`). The converse
fails for single maps, since a reflection reverses `σ`, but it holds along an isotopy from the
identity: a map preserving the area pulls `σ` back to `± σ` at each point
(`TauCeti.RoughForm.eq_or_eq_neg_of_measure_eq`), and along an isotopy the sign cannot jump
(`TauCeti.mpullback_eq_of_forall_eq_or_eq_neg`).

## Main results

* `TauCeti.SmoothTwoForm.volumeForm_one_val`: on a surface the volume form is the two-form.
* `TauCeti.SmoothTwoForm.forall_measurePreserving_isotopy_iff`: a smooth isotopy of a surface from
  the identity preserves the Liouville measure at all times exactly when it preserves the
  two-form.
-/

public section

open Module MeasureTheory
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

namespace TauCeti.SmoothTwoForm

/-- **On a surface the symplectic volume form is the two-form**: `σ¹ / 1! = σ`. -/
theorem volumeForm_one_val (σ : SmoothTwoForm I M) : (σ.volumeForm 1).val = σ.val := by
  funext x
  ext v
  rw [volumeForm_apply, Nat.factorial_one, Nat.cast_one, inv_one, one_smul,
    ContinuousAlternatingMap.wedgePow_succ (σ.val x) 0,
    ContinuousAlternatingMap.pairedWedge_apply_zero_left]
  simp [ContinuousAlternatingMap.wedgePow_zero_apply]

variable [FiniteDimensional ℝ E] [Fact (finrank ℝ E = 2 * 1)] [I.Boundaryless]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]

/-- **Area-preserving isotopies of a surface preserve the area form.** Let `φ t` be a smooth
isotopy of a surface from the identity, with jointly smooth inverses `ψ t`. Every `φ t` preserves
the Liouville measure of a two-form `σ`, the area `|σ|`, exactly when every `φ t` preserves `σ`.
For a single map this fails: a reflection preserves the area and reverses `σ`. -/
theorem forall_measurePreserving_isotopy_iff {σ : SmoothTwoForm I M} {φ ψ : ℝ → M → M}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2))
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2))
    (hφψ : ∀ t y, φ t (ψ t y) = y) (hψφ : ∀ t x, ψ t (φ t x) = x) (hφ0 : ∀ x, φ 0 x = x) :
    (∀ t, MeasurePreserving (φ t) (σ.liouvilleMeasure 1) (σ.liouvilleMeasure 1)) ↔
      ∀ t, mpullback I I (φ t) σ.val = σ.val := by
  have hφt (t : ℝ) : ContMDiff I I ∞ (φ t) :=
    hφ.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)
  have hψt (t : ℝ) : ContMDiff I I ∞ (ψ t) :=
    hψ.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)
  -- Each `φ t` is a homeomorphism.
  let Φ (t : ℝ) : M ≃ₜ M :=
    { toFun := φ t
      invFun := ψ t
      left_inv := hψφ t
      right_inv := hφψ t
      continuous_toFun := (hφt t).continuous
      continuous_invFun := (hψt t).continuous }
  have hΦ (t : ℝ) : MDifferentiable I I (Φ t) := (hφt t).mdifferentiable (by simp)
  refine ⟨fun h ↦ ?_, fun h t ↦ (Φ t).measurePreserving_liouvilleMeasure (hΦ t) (h t)⟩
  -- Preserving the area, `φ t` pulls `σ` back to `± σ` at each point.
  have hpm (t : ℝ) (x : M) : mpullback I I (φ t) σ.val x = σ.val x ∨
      mpullback I I (φ t) σ.val x = -σ.val x := by
    set vol := σ.volumeForm 1
    set σt : SmoothTwoForm I M := SmoothForm.mpullback (φ t) (hφt t) σ
    have hmeas : RoughForm.measure (mpullback I I (φ t) vol.val) = RoughForm.measure vol.val :=
      (Φ t).measure_mpullback_eq_of_measurePreserving (hΦ t) vol.val
        (by rw [← liouvilleMeasure_def]; exact h t)
    have hvol : mpullback I I (φ t) vol.val = (σt.volumeForm 1).val :=
      mpullback_volumeForm (SmoothForm.coe_mpullback _ _ _).symm
    have hsm : IsSmoothForm I 0 (σt.volumeForm 1).val :=
      (σt.volumeForm 1).isSmoothForm.of_le (by simp)
    rw [hvol] at hmeas
    have := RoughForm.eq_or_eq_neg_of_measure_eq (vol.isSmoothForm.of_le (by simp)) hsm
      hmeas.symm x
    rwa [volumeForm_one_val, volumeForm_one_val, SmoothForm.coe_mpullback] at this
  -- Along the isotopy the sign cannot jump.
  exact fun t ↦ mpullback_eq_of_forall_eq_or_eq_neg hφ hφ0 σ hpm t

end TauCeti.SmoothTwoForm
