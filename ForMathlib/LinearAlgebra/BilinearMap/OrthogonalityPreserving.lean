/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.LinearAlgebra.BilinearMap

import Mathlib.Tactic.Ring

/-!
# Bilinear forms with the same orthogonality

Let `B` be a bilinear form over a field that is nondegenerate on the left: `B u ≠ 0` for `u ≠ 0`.
If a second bilinear form `B'` vanishes on every pair on which `B` vanishes, then `B'` is a
scalar multiple of `B`. Applied to `B' u v = B (A u) (A v)`, a linear map that preserves
`B`-orthogonality multiplies `B` by a constant; for a symplectic form, it is conformally
symplectic.

## Main results

* `LinearMap.exists_eq_smul_of_forall_eq_zero_imp`: a linear functional that vanishes on the
  kernel of a nonzero functional `f` is a multiple of `f`;
* `LinearMap.exists_eq_smul_of_forall_isOrtho_imp`: the statement for bilinear forms.
-/

public section

namespace LinearMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A linear functional that vanishes wherever the nonzero functional `f` vanishes is a multiple
of `f`. -/
theorem exists_eq_smul_of_forall_eq_zero_imp {f g : V →ₗ[K] K} (hf : f ≠ 0)
    (h : ∀ x, f x = 0 → g x = 0) : ∃ c : K, g = c • f := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra! H
    exact hf (LinearMap.ext H)
  refine ⟨g w / f w, LinearMap.ext fun x => ?_⟩
  have := h (x - (f x / f w) • w) (by simp [hw])
  simp only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at this
  rw [LinearMap.smul_apply, smul_eq_mul, this]
  ring

/-- If the bilinear form `B` is nondegenerate on the left and `B'` vanishes on every pair on which
`B` vanishes, then `B' = c • B` for a scalar `c`. -/
theorem exists_eq_smul_of_forall_isOrtho_imp {B B' : V →ₗ[K] V →ₗ[K] K}
    (hB : ∀ u, u ≠ 0 → B u ≠ 0) (h : ∀ u v, B u v = 0 → B' u v = 0) :
    ∃ c : K, B' = c • B := by
  -- On the left, `B' u = c u • B u` for every `u ≠ 0`; on the right, `B'.flip v = d v • B.flip v`
  -- for every `v` with `B.flip v ≠ 0`.
  have hl : ∀ u, ∃ c : K, B' u = c • B u := fun u => by
    rcases eq_or_ne u 0 with rfl | hu
    · exact ⟨0, by simp⟩
    · exact exists_eq_smul_of_forall_eq_zero_imp (hB u hu) (h u)
  choose c hc using hl
  have hr : ∀ v, ∃ d : K, B'.flip v = d • B.flip v := fun v => by
    by_cases hv : B.flip v = 0
    · refine ⟨0, LinearMap.ext fun u => ?_⟩
      have : B u v = 0 := LinearMap.congr_fun hv u
      simp [h u v this]
    · exact exists_eq_smul_of_forall_eq_zero_imp hv fun u => h u v
  choose d hd using hr
  -- `c u = d v` whenever `B u v ≠ 0`.
  have hcd : ∀ u v, B u v ≠ 0 → c u = d v := fun u v huv => by
    have h1 : B' u v = c u * B u v := by rw [hc u]; rfl
    have h2 : B' u v = d v * B u v := by
      rw [← flip_apply (f := B'), hd v]
      rfl
    exact mul_right_cancel₀ huv (h1.symm.trans h2)
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, LinearMap.ext fun u => LinearMap.ext fun v => by
      simp [Subsingleton.elim u 0]⟩
  obtain ⟨u₀, hu₀⟩ := exists_ne (0 : V)
  refine ⟨c u₀, LinearMap.ext fun u => ?_⟩
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  rw [hc u]
  congr 1
  -- Find `v` with `B u v ≠ 0` and `B u₀ v ≠ 0`.
  obtain ⟨v₁, hv₁⟩ : ∃ v, B u v ≠ 0 := by
    by_contra! H
    exact hB u hu (LinearMap.ext H)
  obtain ⟨v₂, hv₂⟩ : ∃ v, B u₀ v ≠ 0 := by
    by_contra! H
    exact hB u₀ hu₀ (LinearMap.ext H)
  obtain ⟨v, hv, hv₀⟩ : ∃ v, B u v ≠ 0 ∧ B u₀ v ≠ 0 := by
    by_cases h₁ : B u₀ v₁ = 0
    · by_cases h₂ : B u v₂ = 0
      · exact ⟨v₁ + v₂, by simp [h₂, hv₁], by simp [h₁, hv₂]⟩
      · exact ⟨v₂, h₂, hv₂⟩
    · exact ⟨v₁, hv₁, h₁⟩
  rw [hcd u v hv, hcd u₀ v hv₀]

end LinearMap
