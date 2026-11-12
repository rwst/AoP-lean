/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import HilbertUnphysicality
public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteEquiv

/-!
# Unphysicality of Hilbert spaces: Schwartz spaces

The last sentence of the proof of Theorem 5, "This third failure is not related to the problems
of continuity, as Schwartz spaces present the same problem", read as: refining QSTO:H by the
Schwartz space `𝓢(ℝⁿ) ⊆ L²(ℝⁿ)`, on which position and momentum are continuous, does not make
systems with different numbers of degrees of freedom distinguishable. For all `n + 1` and
`m + 1` there is a unitary `U : L²(ℝⁿ⁺¹) → L²(ℝᵐ⁺¹)` that carries the whole QSTO:H model (as in
`exists_carriesQSTO`) and restricts to an isomorphism of topological vector spaces
`𝓢(ℝⁿ⁺¹) ≃ 𝓢(ℝᵐ⁺¹)`, so the rigged Hilbert spaces `𝓢 ⊆ L²` are isomorphic as well.

The isomorphism relabels Hermite functions (`SchwartzMap.exists_unitary_schwartzEquiv`, in
`ForMathlib`): Schwartz functions are exactly the `L²` functions with rapidly decreasing Hermite
coefficients, and a bijection of multi-indices with polynomial bounds preserves rapid decrease.
It does not carry the positions `Xᵢ` and momenta `Pᵢ`, which are not part of the QSTO:H model.

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.

## Main results

* `schwartz_stdist`: the unitary `U` above, with `CarriesQSTO U`, and the isomorphism of
  Schwartz spaces it restricts to;
* `nonempty_schwartzEquiv`: `𝓢(ℝⁿ⁺¹)` and `𝓢(ℝᵐ⁺¹)` are isomorphic as topological vector
  spaces.
-/

open MeasureTheory
open scoped SchwartzMap

public section

namespace HilbertUnphysicality

/-- **[B]STDIST for Schwartz spaces.** For any numbers `n + 1`, `m + 1` of degrees of freedom
there is a unitary `L²(ℝⁿ⁺¹) → L²(ℝᵐ⁺¹)` that carries the whole QSTO:H model and restricts to an
isomorphism of topological vector spaces `𝓢(ℝⁿ⁺¹) ≃ 𝓢(ℝᵐ⁺¹)`. -/
theorem schwartz_stdist (n m : ℕ) :
    ∃ (U : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))))
      (T : 𝓢(EuclideanSpace ℝ (Fin (n + 1)), ℂ) ≃L[ℂ] 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)),
      CarriesQSTO U ∧ ∀ f, (T f).toLp 2 = U (f.toLp 2) :=
  let ⟨U, T, h⟩ := SchwartzMap.exists_unitary_schwartzEquiv n m
  ⟨U, T, carriesQSTO U, h⟩

/-- "Schwartz spaces present the same problem": `𝓢(ℝⁿ⁺¹)` and `𝓢(ℝᵐ⁺¹)` are isomorphic as
topological vector spaces. -/
theorem nonempty_schwartzEquiv (n m : ℕ) :
    Nonempty (𝓢(EuclideanSpace ℝ (Fin (n + 1)), ℂ) ≃L[ℂ] 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) :=
  SchwartzMap.nonempty_schwartzEquiv n m

end HilbertUnphysicality
