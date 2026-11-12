/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.MeasureTheory.Function.L2Multiplication

/-!
# Complex conjugation on `L²`

Complex conjugation `f ↦ f̄` is an antilinear isometric involution of `L²(μ)` with
`⟪f̄, ḡ⟫ = ⟪g, f⟫`: a *conjugation* in the sense of von Neumann. It commutes with multiplication
by a real function `a`, and so does composition with a measure-preserving map `σ` if `a ∘ σ = a`.

## Main results

* `MeasureTheory.L2.conjugate`: complex conjugation on `L²`;
* `MeasureTheory.L2.inner_conjugate_conjugate`, `MeasureTheory.L2.conjugate_conjugate`: it is a
  conjugation;
* `MeasureTheory.L2.mulOp_conjugate`: `a f̄ = (a f)‾` for real `a`;
* `MeasureTheory.L2.mulOp_compMeasurePreserving`: `a (f ∘ σ) = (a f) ∘ σ` if `a ∘ σ = a`.
-/

@[expose] public noncomputable section

namespace MeasureTheory.L2

open scoped InnerProductSpace ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Complex conjugation on `L²`, an antilinear isometry. -/
def conjugate : Lp ℂ 2 μ →ₗ⋆[ℂ] Lp ℂ 2 μ where
  toFun f := star f
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add f g, Lp.coeFn_add (star f) (star g),
      Lp.coeFn_star f, Lp.coeFn_star g] with x h1 h2 h3 h4 h5
    simp only [h1, h3, Pi.star_apply, h2, Pi.add_apply, h4, h5, star_add]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f,
      Lp.coeFn_smul ((starRingEnd ℂ) c) (star f), Lp.coeFn_star f] with x h1 h2 h3 h4
    rw [h1, h3, Pi.star_apply, h2, Pi.smul_apply, Pi.smul_apply, h4, Pi.star_apply, smul_eq_mul,
      smul_eq_mul, star_mul', starRingEnd_apply]

lemma coeFn_conjugate (f : Lp ℂ 2 μ) : conjugate f =ᵐ[μ] fun x => (starRingEnd ℂ) (f x) :=
  Lp.coeFn_star f

@[simp]
lemma conjugate_conjugate (f : Lp ℂ 2 μ) : conjugate (conjugate f) = f :=
  star_star f

lemma inner_conjugate_conjugate (f g : Lp ℂ 2 μ) : ⟪conjugate f, conjugate g⟫_ℂ = ⟪g, f⟫_ℂ := by
  rw [inner_def, inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_conjugate f, coeFn_conjugate g] with x hf hg
  rw [hf, hg]
  simp [mul_comm]

@[simp]
lemma norm_conjugate (f : Lp ℂ 2 μ) : ‖conjugate f‖ = ‖f‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_conjugate_conjugate]

lemma continuous_conjugate : Continuous (conjugate : Lp ℂ 2 μ → Lp ℂ 2 μ) :=
  (AddMonoidHomClass.isometry_of_norm conjugate norm_conjugate).continuous

variable (a : α → ℝ)

lemma conjugate_mem_mulDomain {f : Lp ℂ 2 μ} (hf : f ∈ mulDomain a) :
    conjugate f ∈ mulDomain a := by
  rw [mem_mulDomain] at hf ⊢
  refine (Lp.memLp (conjugate (hf.toLp _))).ae_eq ?_
  filter_upwards [coeFn_conjugate (hf.toLp _), hf.coeFn_toLp, coeFn_conjugate f] with x h1 h2 h3
  rw [h1, h2, h3, map_mul, Complex.conj_ofReal]

/-- Multiplication by a real function commutes with conjugation. -/
lemma mulOp_conjugate (f : (mulOp a : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ).domain) :
    mulOp a ⟨conjugate (f : Lp ℂ 2 μ), conjugate_mem_mulDomain a f.2⟩ = conjugate (mulOp a f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulOp a ⟨conjugate (f : Lp ℂ 2 μ), conjugate_mem_mulDomain a f.2⟩,
    coeFn_conjugate (f : Lp ℂ 2 μ), coeFn_conjugate (mulOp a f), coeFn_mulOp a f] with x h1 h2 h3 h4
  rw [h1, h3, h2, h4, map_mul, Complex.conj_ofReal]

variable {a} {σ : α → α} (hσ : MeasurePreserving σ μ μ) (ha : ∀ x, a (σ x) = a x)
include hσ ha

lemma compMeasurePreserving_mem_mulDomain {f : Lp ℂ 2 μ} (hf : f ∈ mulDomain a) :
    Lp.compMeasurePreserving σ hσ f ∈ mulDomain a := by
  rw [mem_mulDomain] at hf ⊢
  refine (hf.comp_measurePreserving hσ).ae_eq ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving f hσ] with x hx
  rw [hx, Function.comp_apply, Function.comp_apply, ha]

/-- Composition with a measure-preserving map that leaves `a` invariant commutes with
multiplication by `a`. -/
lemma mulOp_compMeasurePreserving (f : (mulOp a : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ).domain) :
    mulOp a ⟨Lp.compMeasurePreserving σ hσ (f : Lp ℂ 2 μ),
      compMeasurePreserving_mem_mulDomain hσ ha f.2⟩ =
      Lp.compMeasurePreserving σ hσ (mulOp a f) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_mulOp a ⟨Lp.compMeasurePreserving σ hσ (f : Lp ℂ 2 μ),
      compMeasurePreserving_mem_mulDomain hσ ha f.2⟩,
    Lp.coeFn_compMeasurePreserving (f : Lp ℂ 2 μ) hσ,
    Lp.coeFn_compMeasurePreserving (mulOp a f) hσ,
    hσ.quasiMeasurePreserving.ae (coeFn_mulOp a f)] with x h1 h2 h3 h4
  rw [h1, h3, h2, Function.comp_apply, Function.comp_apply, h4, ha]

end MeasureTheory.L2
