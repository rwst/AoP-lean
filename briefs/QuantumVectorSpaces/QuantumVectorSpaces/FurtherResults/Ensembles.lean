/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.EntropyContinuity
public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteReal
public import Mathlib.Analysis.PSeries

/-!
# Further results: ensembles over Example 3 and the continuity of entropy

Not part of the brief. This file formalizes Sec. 4 of `further-results.tex` in the brief's
directory (R. Stephan, *Further results on the brief "Physical vector spaces for quantum
mechanics"*).

The brief leaves open which space of ensembles goes with a quantum vector space ("Ensembles",
Sec. 5). For Example 3, `V = 𝓢(ℝ)`, the natural candidate is the set of positive trace-one
Schwartz operators of Keyl, Kiukas and Werner. A positive trace-class operator `ρ` on `L²(ℝ)` is a
Schwartz operator exactly when all its moments `tr ρNʲ` of the number operator are finite, where
`N ψₙ = n ψₙ` on the Hermite functions. That is the definition used here.

On this space the von Neumann entropy is finite, and it is continuous: convergence in the topology
of Schwartz operators implies convergence in the trace norm and of `tr ρN`, and then the entropy
converges by Wehrl's theorem (`QuantumMechanics.tendsto_vonNeumannEntropy`), since
`tr e^{-βN} = (1 - e^{-β})⁻¹` is finite for every `β > 0`. Every pure state of `V` is such an
ensemble.

## Main definitions

* `numberBasis`: the Hermite functions as a Hilbert basis of `L²(ℝ)`;
* `numberMoment j ρ`: the moment `tr ρNʲ = ∑ₙ nʲ ⟨ψₙ, ρ ψₙ⟩ ∈ [0, ∞]`;
* `IsSchwartzDensity ρ`: a density operator with all moments finite.

## Main results

* `isSchwartzDensity_proj`  every unit vector of `𝓢(ℝ)` gives a Schwartz density operator;
* `IsSchwartzDensity.vonNeumannEntropy_ne_top`  the entropy is finite on Schwartz density
  operators;
* `tendsto_vonNeumannEntropy_of_tendsto_numberMoment`  if `‖ρₘ - σ‖₁ → 0` and
  `tr ρₘN → tr σN < ∞`, then `S(ρₘ) → S(σ)`.

## References

* M. Keyl, J. Kiukas, R. F. Werner, Schwartz operators, Rev. Math. Phys. 28 (2016) 1630001,
  arXiv:1503.04086, Sec. 3.2: the seminorms `‖Q^α P^β T P^β' Q^α'‖₁` induce the topology of
  Schwartz operators.
* A. Wehrl, General properties of entropy, Rev. Mod. Phys. 50 (1978) 221–260, Sec. II.D.
-/

open MeasureTheory Filter Topology Real QuantumMechanics TauCeti
open scoped ENNReal NNReal InnerProductSpace SchwartzMap

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

/-- `L²(ℝ)`, the Hilbert completion of Example 3. -/
abbrev L2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The number basis: the Hermite functions `ψₙ`, with `N ψₙ = n ψₙ`. -/
abbrev numberBasis : HilbertBasis ℕ ℂ L2 := hermiteHilbertBasis ℂ

/-- The moment `tr ρNʲ = ∑ₙ nʲ ⟨ψₙ, ρ ψₙ⟩ ∈ [0, ∞]` of the number operator. -/
def numberMoment (j : ℕ) (ρ : L2 →L[ℂ] L2) : ℝ≥0∞ :=
  energy numberBasis (fun n => (n : ℝ) ^ j) ρ

/-- A Schwartz density operator: a density operator on `L²(ℝ)` all of whose moments of the
number operator are finite. -/
def IsSchwartzDensity (ρ : L2 →L[ℂ] L2) : Prop :=
  IsDensityOperator ρ ∧ ∀ j, numberMoment j ρ ≠ ⊤

lemma summable_exp_neg_mul_pow_one {β : ℝ} (hβ : 0 < β) :
    Summable fun n : ℕ => exp (-(β * (n : ℝ) ^ 1)) := by
  have h : ∀ n : ℕ, exp (-(β * (n : ℝ) ^ 1)) = exp (-β) ^ n := fun n => by
    rw [← Real.exp_nat_mul]; ring_nf
  simp_rw [h]
  exact summable_geometric_of_lt_one (exp_pos _).le ((Real.exp_lt_exp.2 (by linarith : -β < 0)).trans_eq Real.exp_zero)

/-- **The entropy is finite on Schwartz density operators.** -/
theorem IsSchwartzDensity.vonNeumannEntropy_ne_top {ρ : L2 →L[ℂ] L2} (hρ : IsSchwartzDensity ρ) :
    vonNeumannEntropy ρ ≠ ⊤ :=
  QuantumMechanics.vonNeumannEntropy_ne_top hρ.1 (fun n => by positivity) zero_le_one
    (summable_exp_neg_mul_pow_one one_pos) (hρ.2 1)

/-- **The entropy is continuous on the ensembles of Example 3.** If density operators `ρₘ`
converge to `σ` in the trace norm and `tr ρₘN → tr σN < ∞`, then `S(ρₘ) → S(σ)`. Convergence of
Schwartz density operators in the topology of Keyl, Kiukas and Werner gives both hypotheses. -/
theorem tendsto_vonNeumannEntropy_of_tendsto_numberMoment {α : Type*} {l : Filter α}
    {ρ : α → L2 →L[ℂ] L2} {σ : L2 →L[ℂ] L2} (hρ : ∀ a, IsDensityOperator (ρ a))
    (hσ : IsDensityOperator σ) (h : Tendsto (fun a => traceENorm (ρ a - σ)) l (𝓝 0))
    (hE : Tendsto (fun a => numberMoment 1 (ρ a)) l (𝓝 (numberMoment 1 σ)))
    (hσE : numberMoment 1 σ ≠ ⊤) :
    Tendsto (fun a => vonNeumannEntropy (ρ a)) l (𝓝 (vonNeumannEntropy σ)) := by
  set h₀ : ℝ≥0 := (numberMoment 1 σ).toNNReal + 1
  have hlt : numberMoment 1 σ < h₀ := by
    rw [← ENNReal.coe_toNNReal hσE, ENNReal.coe_lt_coe]
    exact lt_add_one _
  have hev : ∀ᶠ a in l, energy numberBasis (fun n => (n : ℝ) ^ 1) (ρ a) ≤ h₀ :=
    (hE.eventually (gt_mem_nhds hlt)).mono fun a ha => ha.le
  exact tendsto_vonNeumannEntropy (fun n => by positivity)
    (fun β hβ => summable_exp_neg_mul_pow_one hβ) hρ hσ h hev

/-- `⟨φ, |ψ⟩⟨ψ| φ⟩ = |⟨φ, ψ⟩|²`. -/
lemma re_inner_proj_apply (ψ φ : L2) :
    (⟪φ, Wigner.proj ψ φ⟫_ℂ).re = ‖⟪φ, ψ⟫_ℂ‖ ^ 2 := by
  rw [Wigner.proj, InnerProductSpace.rankOne_apply, inner_smul_right, ← inner_conj_symm φ ψ,
    Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re, Complex.norm_conj]

/-- **Every pure state of `V = 𝓢(ℝ)` is an ensemble**: for a Schwartz function `f` of norm one,
`|f⟩⟨f|` is a Schwartz density operator. Its moments are finite because the Hermite coefficients
of `f` decrease rapidly. -/
theorem isSchwartzDensity_proj (f : 𝓢(ℝ, ℂ)) (hf : ‖f.toLp 2 volume‖ = 1) :
    IsSchwartzDensity (Wigner.proj (f.toLp 2 volume)) := by
  refine ⟨isDensityOperator_proj hf, fun j => ?_⟩
  obtain ⟨C, hC⟩ := (SchwartzMap.exists_toLp_eq_iff (f.toLp 2)).1 ⟨f, rfl⟩ (j + 1)
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)
  -- `nʲ |cₙ|² ≤ C² / (n + 1)²`
  have hterm : ∀ n : ℕ, (n : ℝ) ^ j * ‖⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ‖ ^ 2 ≤
      C ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := fun n => by
    set c := ‖⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ‖
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h1 : ((n : ℝ) + 1) ^ (j + 1) * c ≤ C := hC n
    have h2 : ((n : ℝ) + 1) ^ (2 * j + 2) * c ^ 2 ≤ C ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) h1 2
      rwa [mul_pow, ← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring] at this
    have h3 : (n : ℝ) ^ j ≤ ((n : ℝ) + 1) ^ j := pow_le_pow_left₀ (by positivity) (by linarith) j
    rw [le_mul_inv_iff₀ (by positivity)]
    calc (n : ℝ) ^ j * c ^ 2 * ((n : ℝ) + 1) ^ 2
        ≤ ((n : ℝ) + 1) ^ j * c ^ 2 * ((n : ℝ) + 1) ^ 2 := by gcongr
      _ ≤ ((n : ℝ) + 1) ^ (2 * j + 2) * c ^ 2 := by
          rw [show ((n : ℝ) + 1) ^ j * c ^ 2 * ((n : ℝ) + 1) ^ 2 =
            ((n : ℝ) + 1) ^ (j + 2) * c ^ 2 by ring]
          gcongr
          · linarith
          · omega
      _ ≤ C ^ 2 := h2
  have hsum : Summable fun n : ℕ => C ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    simpa using this
  have hnn : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ j * ‖⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ‖ ^ 2 :=
    fun n => by positivity
  have hs : Summable fun n : ℕ => (n : ℝ) ^ j * ‖⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ‖ ^ 2 :=
    hsum.of_nonneg_of_le hnn hterm
  rw [numberMoment, energy]
  have heq : ∀ n : ℕ, ENNReal.ofReal ((n : ℝ) ^ j) *
      ENNReal.ofReal (⟪numberBasis n, Wigner.proj (f.toLp 2 volume) (numberBasis n)⟫_ℂ).re =
      ENNReal.ofReal ((n : ℝ) ^ j * ‖⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ‖ ^ 2) := fun n => by
    rw [re_inner_proj_apply, ← ENNReal.ofReal_mul (by positivity), numberBasis,
      coe_hermiteHilbertBasis]
  simp_rw [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs]
  exact ENNReal.ofReal_ne_top

end QuantumVectorSpaces.FurtherResults
