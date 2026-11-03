/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Convex.Midpoint
public import ForMathlib.Analysis.InnerProductSpace.Trace
public import ForPhyslib.QuantumMechanics.Wigner.Density

/-!
# Maps that preserve equal mixtures

## i. Overview

A map of the density operators that preserves equal mixtures, `T (½ ρ + ½ σ) = ½ T ρ + ½ T σ`, is
affine on them. No continuity is needed: density operators have operator norm at most one, so
`T` is bounded on them, and a bounded map that preserves midpoints preserves all convex
combinations of two points (`Convex.map_add_of_map_midpoint`).

## ii. Key results

- `QuantumMechanics.Wigner.IsDensity.norm_le_one`: density operators have norm at most one.
- `QuantumMechanics.Wigner.affineOnDensities_of_map_mix`: preserving equal mixtures implies
  `AffineOnDensities`.

## iii. Table of contents

- A. Equal mixtures suffice
-/

public section

namespace QuantumMechanics.Wigner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-!
## A. Equal mixtures suffice
-/

/-- A density operator has operator norm at most one. -/
lemma IsDensity.norm_le_one {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) : ‖ρ‖ ≤ 1 := by
  simpa [hρ.trace_eq_one] using ContinuousLinearMap.norm_le_re_trace hρ.isPositive

/-- A map of the density operators that preserves equal mixtures is affine on them. -/
theorem affineOnDensities_of_map_mix {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hD : ∀ ρ, IsDensity ρ → IsDensity (T ρ))
    (hmix : ∀ ρ σ, IsDensity ρ → IsDensity σ → T (mix ρ σ) = mix (T ρ) (T σ)) :
    AffineOnDensities T := by
  have hc : ∀ (r : ℝ) (x : E →L[ℂ] E), (r : ℂ) • x = r • x := fun _ _ => Complex.coe_smul _ _
  have h2 : ∀ x : E →L[ℂ] E, (2⁻¹ : ℂ) • x = (2⁻¹ : ℝ) • x := fun x => by
    rw [← hc]
    norm_num
  have hs : Convex ℝ {ρ : E →L[ℂ] E | IsDensity ρ} := fun ρ hρ σ hσ a b ha hb hab => by
    obtain rfl : b = 1 - a := by linarith
    have h := IsDensity.smul_add_smul hρ hσ ha (by linarith : a ≤ 1)
    rwa [hc, hc] at h
  intro ρ σ hρ hσ t ht₀ ht₁
  have h := hs.map_add_of_map_midpoint (f := T) (fun ρ hρ => (hD ρ hρ).norm_le_one)
    (fun ρ hρ σ hσ => by simpa only [mix, h2] using hmix ρ σ hρ hσ) hρ hσ ht₀
    (sub_nonneg.2 ht₁) (add_sub_cancel t 1)
  simpa only [hc] using h

end QuantumMechanics.Wigner
