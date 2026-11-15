/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces
public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteOscillator

/-!
# Further results: Example 3 as the joint domain of the powers of the oscillator

Not part of the brief. Example 3 in `n` dimensions defines `V = 𝓢(ℝⁿ)` by the Cartesian
seminorms, or equivalently by the defining observables `Xⁱ`, `Pᵢ`. The space can also be given
by a single operator of `L²(ℝⁿ)`: with `N` the closure of the harmonic oscillator
`H = ½ ∑ᵢ (Xᵢ² + Pᵢ²)` (at `ħ = 1`), `𝓢(ℝⁿ) = ⋂_k D(Nᵏ)` (B. Simon 1971; the general result is
`SchwartzMap.forall_mem_powDomain_iff`). Here `H` is the restriction of `N` to `V`, and it lies in
the algebra of the defining observables.

## Main results

* `oscillatorCLM_eq`: on `𝓢(ℝⁿ)` the oscillator is `½ ∑ᵢ (Xᵢ² + Pᵢ²)` with `ħ = 1`;
* `oscillatorCLM_mem_algebra`: it lies in the algebra of the defining observables, for `ħ ≠ 0`;
* `forall_mem_powDomain_iff_schwartzN`: for `n ≥ 1`, `g ∈ L²(ℝⁿ)` lies in every `D(Nᵏ)` iff it
  is in `V`.
-/

open SchwartzMap MeasureTheory Complex

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

variable (n : ℕ)

set_option hygiene false in
local notation "𝓢ₙ" => 𝓢(EuclideanSpace ℝ (Fin n), ℂ)

/-- On `𝓢(ℝⁿ)` the oscillator is `½ ∑ᵢ (Xᵢ² + Pᵢ²)`, with the momenta of Example 3 at `ħ = 1`. -/
theorem oscillatorCLM_eq :
    ((oscillatorCLM : 𝓢ₙ →L[ℂ] 𝓢ₙ) : Module.End ℂ 𝓢ₙ) =
      (2⁻¹ : ℂ) • ∑ i, (posOpN n i * posOpN n i + momOpN n 1 i * momOpN n 1 i) := by
  have hm : ∀ i, momOpN n 1 i * momOpN n 1 i = -(derivN n i * derivN n i) := by
    intro i
    rw [momOpN_eq, smul_mul_smul_comm, ofReal_one, mul_one, ← sq, neg_sq, I_sq,
      neg_one_smul]
  simp only [hm, ← sub_eq_add_neg]
  ext f : 1
  simp only [oscillatorCLM, ContinuousLinearMap.coe_coe, _root_.smul_apply, _root_.sum_apply,
    _root_.sub_apply, ContinuousLinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, mul_apply_eq_comp]
  rfl

/-- The oscillator lies in the algebra of the defining observables of Example 3. -/
theorem oscillatorCLM_mem_algebra {ħ : ℝ} (hħ : ħ ≠ 0) :
    ((oscillatorCLM : 𝓢ₙ →L[ℂ] 𝓢ₙ) : Module.End ℂ 𝓢ₙ) ∈ algebra (obsN n ħ) := by
  have hx : ∀ i, posOpN n i ∈ algebra (obsN n ħ) := fun i =>
    Algebra.subset_adjoin ⟨ObsN.pos i, rfl⟩
  rw [oscillatorCLM_eq]
  refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun i _ => ?_) _
  have hd := derivN_mem n hħ i
  have hp : momOpN n 1 i ∈ algebra (obsN n ħ) := by
    rw [momOpN_eq]
    exact Subalgebra.smul_mem _ hd _
  exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hx i) (hx i)) (Subalgebra.mul_mem _ hp hp)

/-- **Example 3 as the joint domain of the powers of the oscillator.** For `n ≥ 1`, a vector
`g ∈ L²(ℝⁿ)` lies in `D(Nᵏ)` for every `k`, where `N` is the closure of the oscillator on `V`, iff
`g ∈ V = 𝓢(ℝⁿ)`. -/
theorem forall_mem_powDomain_iff_schwartzN (hn : n ≠ 0)
    (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ k, g ∈ (oscillator (Fin n)).closure.powDomain k) ↔ ∃ f : 𝓢ₙ, f.toLp 2 = g := by
  have : NeZero n := ⟨hn⟩
  exact forall_mem_powDomain_iff g

end QuantumVectorSpaces.FurtherResults
