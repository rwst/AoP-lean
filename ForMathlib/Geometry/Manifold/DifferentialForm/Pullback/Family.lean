/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# The sign of a pulled-back form along an isotopy

Let `φ t` be a jointly smooth family of maps of a manifold `M` with `φ 0 = id`, and `σ` a smooth
form on `M`. If at every time and point the pulled-back form is `± σ`, the sign cannot jump: at a
fixed point `x`, the value `(φ_t^* σ)_x` depends continuously on `t`
(`TauCeti.SmoothForm.contMDiff_mpullback_prodMk`, applied to the pullback of `σ` along
`(t, x) ↦ φ t x`), the times with sign `+` and those with sign `-` form two disjoint closed sets
where `σ_x ≠ 0`, and the sign at time `0` is `+`. So `φ_t^* σ = σ` for all `t`.

This is how preserving the area and preserving the area form agree along an evolution of a
surface: a map preserving the measure `|σ|` of a top form pulls `σ` back to `± σ` at each point
(`TauCeti.RoughForm.eq_or_eq_neg_of_measure_eq`).

## Main results

* `TauCeti.mpullback_eq_of_forall_eq_or_eq_neg`: along a smooth isotopy from the identity, a form
  pulled back to `± σ` at every point is pulled back to `σ`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace TauCeti

/-- **The sign of a pulled-back form cannot jump along an isotopy.** Let `φ t` be a jointly smooth
family of maps with `φ 0 = id`. If every `φ t` pulls the smooth form `σ` back to `σ` or to `-σ` at
each point, then every `φ t` pulls `σ` back to `σ`. -/
theorem mpullback_eq_of_forall_eq_or_eq_neg {φ : ℝ → M → M}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2)) (hφ0 : ∀ x, φ 0 x = x)
    (σ : SmoothForm I M F k)
    (h : ∀ t x, mpullback (F := F) I I (φ t) σ.val x = σ.val x ∨
      mpullback (F := F) I I (φ t) σ.val x = -σ.val x)
    (t : ℝ) : mpullback (F := F) I I (φ t) σ.val = σ.val := by
  funext x
  -- The slices of the pullback of `σ` along `(t, x) ↦ φ t x` are the forms `φ_t^* σ`.
  set Ω := SmoothForm.mpullback (fun p : ℝ × M ↦ φ p.1 p.2) hφ σ
  have hslice (s : ℝ) :
      (SmoothForm.mpullback (Prod.mk s) (contMDiff_const.prodMk contMDiff_id) Ω).val x =
        mpullback (F := F) I I (φ s) σ.val x := by
    rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, ← mpullback_comp]
    · rfl
    · exact mdifferentiable_const.prodMk mdifferentiable_id
    · exact hφ.mdifferentiable (by simp)
  -- So the value at `x` depends continuously on the time.
  have hc : Continuous fun s : ℝ ↦ mpullback (F := F) I I (φ s) σ.val x := by
    have h1 := (SmoothForm.contMDiff_mpullback_prodMk Ω).continuous.comp
      (continuous_id.prodMk continuous_const : Continuous fun s : ℝ ↦ (s, x))
    simp only [Function.comp_def, hslice] at h1
    exact (FiberBundle.totalSpaceMk_isInducing _ _ x).continuous_iff.2 h1
  by_cases h0 : σ.val x = 0
  · rcases h t x with h' | h' <;> simp [h', h0]
  -- Where `σ_x ≠ 0`, the signs `+` and `-` exclude each other.
  have hne (s : ℝ) : mpullback (F := F) I I (φ s) σ.val x = -σ.val x ↔
      mpullback (F := F) I I (φ s) σ.val x ≠ σ.val x := by
    refine ⟨fun h' h'' ↦ h0 ?_, fun h' ↦ (h s x).resolve_left h'⟩
    rw [h''] at h'
    have h2 : (2 : ℝ) • σ.val x = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h']
      exact add_neg_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have hS : IsClopen {s : ℝ | mpullback (F := F) I I (φ s) σ.val x = σ.val x} := by
    refine ⟨isClosed_eq hc continuous_const, ?_⟩
    rw [← isClosed_compl_iff]
    convert isClosed_eq hc (continuous_const (y := -σ.val x)) using 1
    ext s
    exact (hne s).symm
  have h0' : φ 0 = id := funext hφ0
  have := hS.eq_univ ⟨0, by simp [h0', mpullback_id]⟩
  exact (this ▸ mem_univ t : t ∈ {s : ℝ | mpullback (F := F) I I (φ s) σ.val x = σ.val x})

end TauCeti
