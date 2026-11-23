/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.LocallyConvex.DualPowerSeriesSpace
public import QuantumVectorSpaces.FurtherResults.HermiteSpaces

/-!
# Further results: `S^{1/2}_{1/2}(ℝⁿ)` remembers `n`, in step form

Not part of the brief. This file formalizes the headline case of Sec. 5 of `further-results.tex`
in the brief's directory (R. Stephan, *Further results on the brief "Physical vector spaces for
quantum mechanics"*), without inductive limit topologies.

By Gramchev–Pilipović–Rodino, `S^μ_μ(ℝⁿ)` is the space of functions whose Hermite coefficients
satisfy `∑ k, |c_k|² exp (2t |k| ^ (1 / (2μ))) < ∞` for some `t > 0`, and its topology is the
inductive limit of the corresponding weighted `ℓ²` steps (Lozanov-Crvenković–Perišić). For
`μ = 1/2` the weight is `exp (2t |k|)`: the analytic vectors of the number operator. Here
`stepSpace 𝕜 f n` is this coefficient space, for a weight `f : ℕ → ℝ`, with its steps, and no
topology.

The theorem is stated for linear bijections that, together with their inverses, map every step
ball into a multiple of some step ball (`DualPowerSeriesSpace.IsStepBounded`). Every isomorphism of
the locally convex spaces `S^μ_μ(ℝⁿ) → S^ν_ν(ℝᵐ)` is of this kind: it maps bounded sets to
bounded sets, and these spaces are strong duals of Fréchet spaces, in which every bounded set is
equicontinuous and so lies in a multiple of a step ball. That passage stays cited, as does the
coefficient description itself.

## Main definitions

* `HermiteSpace.stepSpace 𝕜 f n`: the families `c` on `ℕⁿ` with
  `∑ k, |c_k|² exp (2t f(|k|)) < ∞` for some `t > 0`.

## Main statements

* `HermiteSpace.exists_isStepBounded_equiv_iff`: the general criterion, for monotone
  nonnegative `f` and `g`: a step-bounded bijection exists if and only if `f ∘ level n` and
  `g ∘ level m` dominate each other.
* `HermiteSpace.exists_isStepBounded_equiv_rpow_iff`: for `f = (· ^ s)`, `g = (· ^ s')`, if and
  only if `s / n = s' / m`.
* `HermiteSpace.exists_isStepBounded_equiv_gelfandShilov_iff`: for the Gelfand–Shilov exponents
  `1 / (2μ)`, if and only if `μ n = ν m`.
* `HermiteSpace.exists_isStepBounded_equiv_iff_eq`: **for `S^{1/2}_{1/2}`, if and only if
  `n = m`.**
-/

@[expose] public section

open Set
open DualPowerSeriesSpace (IsStepBounded)

noncomputable section

namespace QuantumVectorSpaces.FurtherResults

namespace HermiteSpace

variable (𝕜 : Type*) [RCLike 𝕜] (f : ℕ → ℝ) (n : ℕ)

/-- The weight `k ↦ f |k|` on multi-indices. -/
def degreeWeight : (Fin n → ℕ) → ℝ := fun k => f (degree k)

/-- The coefficient families `c` on `ℕⁿ` with `∑ k, |c_k|² exp (2t f(|k|)) < ∞` for some `t > 0`
(`mem_stepSpace_iff`), as the union of the steps of `DualPowerSeriesSpace`. -/
def stepSpace : Submodule 𝕜 ((Fin n → ℕ) → 𝕜) := DualPowerSeriesSpace.union 𝕜 (degreeWeight f n)

variable {𝕜 f n} {g : ℕ → ℝ} {m : ℕ}

theorem mem_stepSpace_iff (hf0 : 0 ≤ f) {c : (Fin n → ℕ) → 𝕜} :
    c ∈ stepSpace 𝕜 f n ↔
      ∃ t > 0, Memℓp (fun k => (Real.exp (t * f (degree k)) : 𝕜) * c k) 2 :=
  DualPowerSeriesSpace.mem_union_iff (α := degreeWeight f n) fun k => hf0 (degree k)

variable (𝕜 f n) in
/-- Relabelling the multi-indices in order of degree. It maps step balls onto step balls. -/
def stepRelabel [NeZero n] :
    stepSpace 𝕜 f n ≃ₗ[𝕜] DualPowerSeriesSpace.union 𝕜 (degreeWeight f n ∘ enum n) :=
  DualPowerSeriesSpace.relabel 𝕜 (degreeWeight f n) (enum n)

theorem exponent_eq [NeZero n] : exponent f n = degreeWeight f n ∘ enum n := rfl

theorem isStepBounded_stepRelabel [NeZero n] :
    IsStepBounded (degreeWeight f n) (degreeWeight f n ∘ enum n)
      (stepRelabel 𝕜 f n).toLinearMap :=
  DualPowerSeriesSpace.isStepBounded_relabel (enum n)

theorem isStepBounded_stepRelabel_symm [NeZero n] :
    IsStepBounded (degreeWeight f n ∘ enum n) (degreeWeight f n)
      (stepRelabel 𝕜 f n).symm.toLinearMap :=
  DualPowerSeriesSpace.isStepBounded_relabel_symm (enum n)

/-- **The general criterion.** For monotone nonnegative `f` and `g` there is a linear bijection
`stepSpace 𝕜 f n → stepSpace 𝕜 g m` that, with its inverse, maps every step ball into a multiple
of some step ball, if and only if `f ∘ level n` and `g ∘ level m` dominate each other. -/
theorem exists_isStepBounded_equiv_iff [NeZero n] [NeZero m] (hf : Monotone f) (hf0 : 0 ≤ f)
    (hg : Monotone g) (hg0 : 0 ≤ g) :
    (∃ T : stepSpace 𝕜 f n ≃ₗ[𝕜] stepSpace 𝕜 g m,
      IsStepBounded (degreeWeight f n) (degreeWeight g m) T.toLinearMap ∧
        IsStepBounded (degreeWeight g m) (degreeWeight f n) T.symm.toLinearMap) ↔
      Dominated (exponent f n) (exponent g m) ∧ Dominated (exponent g m) (exponent f n) := by
  have ha : Monotone (degreeWeight f n ∘ enum n) := hf.comp (monotone_level n)
  have hb : Monotone (degreeWeight g m ∘ enum m) := hg.comp (monotone_level m)
  rw [exponent_eq, exponent_eq]
  refine Iff.trans ?_ (DualPowerSeriesSpace.exists_isStepBounded_equiv_iff (𝕜 := 𝕜)
    ha (fun j => hf0 (degree (enum n j))) hb (fun j => hg0 (degree (enum m j))))
  have hRn := isStepBounded_stepRelabel (𝕜 := 𝕜) (f := f) (n := n)
  have hRn' := isStepBounded_stepRelabel_symm (𝕜 := 𝕜) (f := f) (n := n)
  have hRm := isStepBounded_stepRelabel (𝕜 := 𝕜) (f := g) (n := m)
  have hRm' := isStepBounded_stepRelabel_symm (𝕜 := 𝕜) (f := g) (n := m)
  constructor
  · rintro ⟨T, hT, hT'⟩
    refine ⟨((stepRelabel 𝕜 f n).symm.trans T).trans (stepRelabel 𝕜 g m), ?_, ?_⟩
    · rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans]
      exact (hRn'.comp hT).comp hRm
    · rw [LinearEquiv.trans_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
        LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.comp_assoc]
      exact (hRm'.comp hT').comp hRn
  · rintro ⟨T, hT, hT'⟩
    refine ⟨((stepRelabel 𝕜 f n).trans T).trans (stepRelabel 𝕜 g m).symm, ?_, ?_⟩
    · rw [LinearEquiv.coe_trans, LinearEquiv.coe_trans]
      exact (hRn.comp hT).comp hRm'
    · rw [LinearEquiv.trans_symm, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
        LinearEquiv.coe_trans, LinearEquiv.coe_trans, LinearMap.comp_assoc]
      exact (hRm.comp hT').comp hRn'

theorem dominated_and_dominated_rpow_iff [NeZero n] [NeZero m] {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') :
    Dominated (exponent (fun d => (d : ℝ) ^ s) n) (exponent (fun d => (d : ℝ) ^ s') m) ∧
      Dominated (exponent (fun d => (d : ℝ) ^ s') m) (exponent (fun d => (d : ℝ) ^ s) n) ↔
      s / n = s' / m :=
  ⟨fun ⟨h, h'⟩ => (div_le_div_of_dominated_exponent hs.le hs'.le h).antisymm
    (div_le_div_of_dominated_exponent hs'.le hs.le h'), fun h =>
    ⟨(dominated_exponent_rpow n hs.le).trans (h ▸ dominated_rpow_exponent m hs'.le),
      (dominated_exponent_rpow m hs'.le).trans (h ▸ dominated_rpow_exponent n hs.le)⟩⟩

theorem monotone_rpow {s : ℝ} (hs : 0 ≤ s) : Monotone fun d : ℕ => (d : ℝ) ^ s :=
  fun _ _ h => Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) hs

/-- **Power exponents.** For `s, s' > 0`, a step-bounded bijection
`stepSpace 𝕜 (· ^ s) n → stepSpace 𝕜 (· ^ s') m` exists if and only if `s / n = s' / m`. -/
theorem exists_isStepBounded_equiv_rpow_iff [NeZero n] [NeZero m] {s s' : ℝ} (hs : 0 < s)
    (hs' : 0 < s') :
    (∃ T : stepSpace 𝕜 (fun d => (d : ℝ) ^ s) n ≃ₗ[𝕜] stepSpace 𝕜 (fun d => (d : ℝ) ^ s') m,
      IsStepBounded (degreeWeight (fun d => (d : ℝ) ^ s) n)
          (degreeWeight (fun d => (d : ℝ) ^ s') m) T.toLinearMap ∧
        IsStepBounded (degreeWeight (fun d => (d : ℝ) ^ s') m)
          (degreeWeight (fun d => (d : ℝ) ^ s) n) T.symm.toLinearMap) ↔
      s / n = s' / m :=
  (exists_isStepBounded_equiv_iff (monotone_rpow hs.le) (fun _ => by positivity)
    (monotone_rpow hs'.le) (fun _ => by positivity)).trans
    (dominated_and_dominated_rpow_iff hs hs')

/-- **Gelfand–Shilov exponents.** With `f d = d ^ (1 / (2μ))`, the coefficient spaces of
`S^μ_μ(ℝⁿ)` and `S^ν_ν(ℝᵐ)` admit a step-bounded bijection if and only if `μ n = ν m`. -/
theorem exists_isStepBounded_equiv_gelfandShilov_iff [NeZero n] [NeZero m] {μ ν : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) :
    (∃ T : stepSpace 𝕜 (fun d => (d : ℝ) ^ (1 / (2 * μ))) n ≃ₗ[𝕜]
        stepSpace 𝕜 (fun d => (d : ℝ) ^ (1 / (2 * ν))) m,
      IsStepBounded (degreeWeight (fun d => (d : ℝ) ^ (1 / (2 * μ))) n)
          (degreeWeight (fun d => (d : ℝ) ^ (1 / (2 * ν))) m) T.toLinearMap ∧
        IsStepBounded (degreeWeight (fun d => (d : ℝ) ^ (1 / (2 * ν))) m)
          (degreeWeight (fun d => (d : ℝ) ^ (1 / (2 * μ))) n) T.symm.toLinearMap) ↔
      μ * n = ν * m := by
  rw [exists_isStepBounded_equiv_rpow_iff (by positivity) (by positivity)]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
  constructor <;> intro h <;> linarith

/-- **`S^{1/2}_{1/2}(ℝⁿ)` remembers `n`.** The coefficient spaces with weights `exp (t |k|)`,
`t > 0`, on `ℕⁿ` and `ℕᵐ` admit a linear bijection that, with its inverse, maps every step ball
into a multiple of some step ball, if and only if `n = m`. -/
theorem exists_isStepBounded_equiv_iff_eq [NeZero n] [NeZero m] :
    (∃ T : stepSpace 𝕜 (fun d => (d : ℝ)) n ≃ₗ[𝕜] stepSpace 𝕜 (fun d => (d : ℝ)) m,
      IsStepBounded (degreeWeight (fun d => (d : ℝ)) n) (degreeWeight (fun d => (d : ℝ)) m)
          T.toLinearMap ∧
        IsStepBounded (degreeWeight (fun d => (d : ℝ)) m) (degreeWeight (fun d => (d : ℝ)) n)
          T.symm.toLinearMap) ↔
      n = m := by
  have h1 : (fun d : ℕ => (d : ℝ)) = fun d : ℕ => (d : ℝ) ^ (1 : ℝ) :=
    funext fun d => (Real.rpow_one _).symm
  rw [h1, exists_isStepBounded_equiv_rpow_iff one_pos one_pos]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [div_eq_div_iff hn hm, one_mul, one_mul, eq_comm]
  exact Nat.cast_inj

end HermiteSpace

end QuantumVectorSpaces.FurtherResults

end
