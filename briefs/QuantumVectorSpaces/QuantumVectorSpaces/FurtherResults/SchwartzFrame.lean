/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces
public import HilbertUnphysicality
public import TauCeti.Analysis.SpecialFunctions.Gaussian.Schwartz

/-!
# Further results: the Hilbert brief's change of frame on `𝓢(ℝ)`

Not part of the brief. This file formalizes Sec. 1 of `further-results.tex` in the brief's
directory (R. Stephan, *Further results on the brief "Physical vector spaces for quantum
mechanics"*).

In the proof of Theorem 5, [B]WDQ, the brief assumes that "the defining observables of A must be
observables in B and vice-versa" (see `QuantumVectorSpaces.Frames`). This fails for Example 3,
`V = 𝓢(ℝ)`, with the change of frame `y = tan(π/2 · erf x)` that the brief Unphysicality of
Hilbert spaces for quantum mechanics uses against [B]WDQ (its Proposition 3, in the module
`HilbertUnphysicality`). Its unitary `U` sends the Gaussian packet `ψ`, a Schwartz function, to
`ϕ(y) = (π(1 + y²))^{-1/2}`, which is not one. So the second observer cannot express the first
observer's `ψ` in `𝓢(ℝ)`, and the second observer's position, carried back to the first frame,
is not defined at `ψ`. QSTO:V gives [B]WDQ only for changes of frame that map `V` onto itself.

## Main results

* `toLp_gaussSchwartz`  the Gaussian packet `ψ` of the Hilbert brief is a Schwartz function;
* `toLp_mem_positionDomain`  every Schwartz function lies in the domain of the position operator
  on `L²(ℝ)`;
* `frameUnitary_gaussState_not_mem_range`  `Uψ = ϕ` is not a Schwartz function;
* `not_forall_frameUnitary_mem_range`  so `U` does not map `𝓢(ℝ)` into itself;
* `toLp_gaussSchwartz_not_mem_domain`  and `U⁻¹YU`, the position `Y` of the second frame carried
  back to the first, is not defined at the Schwartz function `ψ`.

## References

* G. Carcassi, F. Calderón, C. A. Aidala, The unphysicality of Hilbert spaces,
  arXiv:2308.06669v3, Appendix, Sec. VIII: on the Schwartz space "the only unitary
  transformations we are interested in are those that map Schwartz functions to Schwartz
  functions", so the change of coordinate `y(x)` "is automatically ruled out".
* A. Galbis, E. Jordá, Composition operators on the Schwartz space, Rev. Mat. Iberoam. 34
  (2018) 397–412, Theorem 2.3: the changes of variable that map `𝓢(ℝ)` into itself.
-/

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

open HilbertUnphysicality MeasureTheory SchwartzMap QuantumMechanics

/-- The Gaussian packet `ψ(x) = (e^{-x²}/√π)^{1/2} = π^{-1/4} e^{-x²/2}` as a Schwartz
function. -/
def gaussSchwartz : 𝓢(ℝ, ℂ) :=
  ((√(√Real.pi) : ℝ) : ℂ)⁻¹ • TauCeti.gaussianSchwartzMap (b := (1 / 2 : ℂ)) (by norm_num)

lemma gaussSchwartz_apply (x : ℝ) : gaussSchwartz x = gaussFun x := by
  have h : √(Real.exp (-x ^ 2) / √Real.pi) = (√(√Real.pi))⁻¹ * Real.exp (-(1 / 2) * x ^ 2) := by
    rw [Real.sqrt_div (Real.exp_pos _).le, div_eq_inv_mul, ← Real.exp_half]
    ring_nf
  simp only [gaussSchwartz, smul_apply, TauCeti.gaussianSchwartzMap_apply, smul_eq_mul, gaussFun,
    gaussDensity, h, Real.norm_eq_abs]
  rw [← Complex.ofReal_pow, sq_abs]
  push_cast
  ring_nf

/-- The Gaussian packet `ψ` of the Hilbert brief is a Schwartz function. -/
theorem toLp_gaussSchwartz : gaussSchwartz.toLp 2 volume = gaussState :=
  MemLp.toLp_congr _ _ (ae_of_all _ gaussSchwartz_apply)

/-- Every Schwartz function lies in the domain of the position operator on `L²(ℝ)`. -/
theorem toLp_mem_positionDomain (f : 𝓢(ℝ, ℂ)) : f.toLp 2 volume ∈ positionDomain := by
  refine (memLp (posOp f) 2).ae_eq ?_
  filter_upwards [coeFn_toLp f 2 volume] with x hx
  rw [posOp_apply, hx]

/-- The change of frame takes `ψ` out of `𝓢(ℝ)`: `Uψ = ϕ` is not a Schwartz function. -/
theorem frameUnitary_gaussState_not_mem_range :
    frameUnitary gaussState ∉ Set.range fun f : 𝓢(ℝ, ℂ) => f.toLp 2 volume := by
  rintro ⟨f, hf⟩
  exact frameUnitary_gaussState_not_mem (hf ▸ toLp_mem_positionDomain f)

/-- [B]WDQ on `𝓢(ℝ)` fails for this change of frame: `U` does not map `𝓢(ℝ)` into itself. -/
theorem not_forall_frameUnitary_mem_range :
    ¬ ∀ f : 𝓢(ℝ, ℂ), ∃ g : 𝓢(ℝ, ℂ), frameUnitary (f.toLp 2 volume) = g.toLp 2 volume := by
  intro h
  obtain ⟨g, hg⟩ := h gaussSchwartz
  rw [toLp_gaussSchwartz] at hg
  exact frameUnitary_gaussState_not_mem_range ⟨g, hg.symm⟩

/-- The premise of the proof of Theorem 5 fails for this change of frame: the position `Y` of
the second frame, carried back to the first as `U⁻¹YU`, is not defined at the Schwartz function
`ψ`, so it is not an operator on `𝓢(ℝ)`. -/
theorem toLp_gaussSchwartz_not_mem_domain :
    gaussSchwartz.toLp 2 volume ∉ (conjLinearPMap frameUnitary.symm positionOp).domain := by
  rw [mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_symm, toLp_gaussSchwartz]
  exact frameUnitary_gaussState_not_mem

end QuantumVectorSpaces.FurtherResults
