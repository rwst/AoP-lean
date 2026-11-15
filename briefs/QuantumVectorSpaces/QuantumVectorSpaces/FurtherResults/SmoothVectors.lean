/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces
public import ForMathlib.Analysis.Distribution.SchwartzSpace.SmoothVectors

/-!
# Further results: Example 3 as the smooth vectors of the Schrödinger representation

Not part of the brief. This file checks the Heisenberg-group instance of the group form in Sec. 2
of `further-results.tex` in the brief's directory. The Schrödinger representation
`ρ(a, b, t) g (x) = e^{i(t + ⟪x, b⟫)} g(x + a)` of the (polarized) Heisenberg group `H_n` acts on
`L²(ℝⁿ)` by unitaries (`Heisenberg.schrodinger`). Its smooth vectors, the `g` whose orbit
`p ↦ ρ(p) g` is a smooth map into `L²`, are exactly the vectors of `V = 𝓢(ℝⁿ)`, and on `V` the
infinitesimal generators of `ρ` are `i` times the defining observables `Pᵢ`, `Xⁱ`, `I` at `ħ = 1`.

## Main results

* `contDiff_schrodinger_iff_schwartzN`: for `n ≥ 1`, `g ∈ L²(ℝⁿ)` is a smooth vector of the
  Schrödinger representation iff it is in `V`;
* `fderiv_schrodinger_obsDir`: the derivative at the identity of the orbit of `f ∈ V` in the
  direction of a defining observable `A` is `i A f`.
-/

open SchwartzMap MeasureTheory Complex Heisenberg
open scoped ContDiff

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

variable {n : ℕ}

set_option hygiene false in
local notation "𝓢ₙ" => 𝓢(EuclideanSpace ℝ (Fin n), ℂ)

set_option hygiene false in
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- The direction in `H_n` that belongs to a defining observable: the translations `(eᵢ, 0, 0)` for
`Pᵢ`, the modulations `(0, eᵢ, 0)` for `Xⁱ`, and the centre `(0, 0, 1)` for `I`. -/
def obsDir : ObsN n → Eₙ × Eₙ × ℝ
  | .pos i => (0, EuclideanSpace.single i 1, 0)
  | .mom i => (EuclideanSpace.single i 1, 0, 0)
  | .one => (0, 0, 1)

/-- **The generators of the Schrödinger representation are the defining observables.** For
`f ∈ V`, the derivative at the identity of `p ↦ ρ(p) f` in the direction of a defining observable
`A` is `i A f`, with `ħ = 1`. -/
theorem fderiv_schrodinger_obsDir (f : 𝓢ₙ) (k : ObsN n) :
    fderiv ℝ (fun p => schrodinger p (f.toLp 2)) 0 (obsDir k) =
      (I • obsN n 1 k f).toLp 2 := by
  rw [fderiv_schrodinger_toLp_zero]
  congr 1
  cases k with
  | pos i =>
    ext x
    simp [obsDir, obsN, posOpN_apply, EuclideanSpace.inner_single_left]
  | mom i =>
    ext x
    simp [obsDir, obsN, momOpN_eq, derivN_apply, ← mul_assoc]
  | one =>
    ext x
    simp [obsDir, obsN]

/-- **Example 3 is the space of smooth vectors of the Schrödinger representation.** For `n ≥ 1`, a
vector `g ∈ L²(ℝⁿ)` has a smooth orbit `p ↦ ρ(p) g` under the Schrödinger representation of the
Heisenberg group iff it lies in `V = 𝓢(ℝⁿ)`. -/
theorem contDiff_schrodinger_iff_schwartzN (hn : n ≠ 0)
    (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (ContDiff ℝ ∞ fun p => schrodinger p g) ↔ ∃ f : 𝓢ₙ, f.toLp 2 = g := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  exact contDiff_schrodinger_iff g

end QuantumVectorSpaces.FurtherResults
