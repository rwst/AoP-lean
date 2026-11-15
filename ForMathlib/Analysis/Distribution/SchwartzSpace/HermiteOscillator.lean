/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteSeries
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# The Schwartz space is the joint domain of the powers of the oscillator

On `ℝ^ι`, `ι` nonempty, let `N` be the closure in `L²(ℝ^ι)` of the harmonic oscillator
`H = ½ ∑ᵢ (xᵢ² - ∂ᵢ²)` defined on `𝓢(ℝ^ι)`. Then `𝓢(ℝ^ι) = ⋂_k D(Nᵏ)` (B. Simon 1971).

`H` multiplies the Hermite coefficient `c_α` by `λ_α = |α| + dim/2`. The relation
`⟪h_α, w⟫ = λ_α ⟪h_α, g⟫` is closed in `(g, w)`, so it holds on the closure of the graph of `H`.
Hence that closure is a graph, `H` is closable, and for `g ∈ D(Nᵏ)` the vector `Nᵏ g` has the
coefficients `λ_αᵏ c_α(g)`, which are bounded by `‖Nᵏ g‖`. So the coefficients of a vector in every
`D(Nᵏ)` are rapidly decreasing, and the vector is the Hermite series of a Schwartz function.

## Main definitions

* `LinearPMap.powDomain T k`: the domain `D(Tᵏ)` of the `k`-th power of an unbounded operator;
* `SchwartzMap.oscillatorCLM`: the harmonic oscillator `½ ∑ᵢ (xᵢ² - ∂ᵢ²)` on `𝓢(ℝ^ι)`;
* `SchwartzMap.oscillator`: the same as an unbounded operator on `L²(ℝ^ι)` with domain `𝓢(ℝ^ι)`.

## Main results

* `SchwartzMap.hermiteCoeff_oscillatorCLM`: `c_α(H f) = (|α| + dim/2) c_α(f)`;
* `SchwartzMap.isClosable_oscillator`: `H` is closable;
* `SchwartzMap.forall_mem_powDomain_iff`: `g ∈ L²(ℝ^ι)` lies in `D(Nᵏ)` for every `k` iff it
  is a Schwartz function.

## References

* B. Simon, Distributions and their Hermite expansions, J. Math. Phys. 12 (1971) 140–148.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap InnerProductSpace ENNReal LineDeriv

@[expose] public noncomputable section

/-- The domain `D(Tᵏ)` of the `k`-th power of an unbounded operator: `D(T⁰)` is everything, and
`x ∈ D(Tᵏ⁺¹)` when `x ∈ D(T)` and `T x ∈ D(Tᵏ)`. -/
def LinearPMap.powDomain {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]
    (T : E →ₗ.[R] E) : ℕ → Set E
  | 0 => Set.univ
  | k + 1 => {x | ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T.powDomain k}

namespace SchwartzMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The oscillator on `𝓢(ℝ^ι)` -/

/-- The product rule `∂ᵢ (xᵢ f) = f + xᵢ ∂ᵢ f`. -/
lemma coordDerivCLM_coordMulCLM (i : ι) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    coordDerivCLM i (coordMulCLM i f) = f + coordMulCLM i (coordDerivCLM i f) := by
  ext x
  set L : EuclideanSpace ℝ ι →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj i)
  have hL : ∀ y, L y = ((y i : ℝ) : ℂ) := fun y => rfl
  have he : ⇑(coordMulCLM i f) = ⇑L * ⇑f := funext fun y => by
    rw [coordMulCLM_apply, Pi.mul_apply, hL]
  have hd := (L.hasFDerivAt (x := x)).mul (f.differentiableAt (x := x)).hasFDerivAt
  rw [coordDerivCLM_apply, add_apply, coordMulCLM_apply, coordDerivCLM_apply,
    lineDerivOp_apply_eq_fderiv, lineDerivOp_apply_eq_fderiv, he, hd.fderiv]
  simp [hL]
  ring

lemma ladderCLM_apply (i : ι) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ladderCLM i f =
      coordMulCLM i (coordMulCLM i f) - coordDerivCLM i (coordDerivCLM i f) + f := by
  rw [ladderCLM, ContinuousLinearMap.comp_apply, _root_.sub_apply,
    _root_.add_apply, map_sub, map_sub, coordDerivCLM_coordMulCLM]
  abel

/-- The harmonic oscillator `H = ½ ∑ᵢ (xᵢ² - ∂ᵢ²)`, with `m = ω = ħ = 1`. -/
def oscillatorCLM : 𝓢(EuclideanSpace ℝ ι, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
  (2⁻¹ : ℂ) • ∑ i, ((coordMulCLM i).comp (coordMulCLM i) - (coordDerivCLM i).comp (coordDerivCLM i))

variable (ι) in
/-- The eigenvalue `|α| + dim/2` of the oscillator at the Hermite function `h_α`. -/
def oscillatorEigenvalue (α : ι → ℕ) : ℝ := ∑ i, (α i : ℝ) + Fintype.card ι / 2

omit [DecidableEq ι] in
lemma oscillatorEigenvalue_nonneg (α : ι → ℕ) : 0 ≤ oscillatorEigenvalue ι α := by
  unfold oscillatorEigenvalue
  positivity

/-- **The oscillator is diagonal in the Hermite basis:** `c_α(H f) = (|α| + dim/2) c_α(f)`. -/
theorem hermiteCoeff_oscillatorCLM (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α (oscillatorCLM f) = oscillatorEigenvalue ι α * hermiteCoeff α f := by
  have h : ∀ i, hermiteCoeff α (coordMulCLM i (coordMulCLM i f) -
      coordDerivCLM i (coordDerivCLM i f)) = (2 * (α i : ℂ) + 1) * hermiteCoeff α f := by
    intro i
    have := hermiteCoeff_ladderCLM α i f
    rw [ladderCLM_apply, map_add] at this
    linear_combination this
  simp only [oscillatorCLM, _root_.smul_apply, _root_.sum_apply,
    _root_.sub_apply, ContinuousLinearMap.comp_apply, map_smul, map_sum, h,
    oscillatorEigenvalue, smul_eq_mul]
  rw [← Finset.sum_mul]
  push_cast
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  ring

/-! ### The oscillator as an unbounded operator on `L²(ℝ^ι)` -/

set_option hygiene false in
local notation "𝓗" => Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))

variable (ι) in
/-- The graph `{(f, H f) | f ∈ 𝓢(ℝ^ι)}` of the oscillator in `L²(ℝ^ι) × L²(ℝ^ι)`. -/
def oscillatorGraph : Submodule ℂ (𝓗 × 𝓗) :=
  LinearMap.range ((toLpCLM ℂ ℂ 2 volume).toLinearMap.prod
    ((toLpCLM ℂ ℂ 2 volume).comp oscillatorCLM).toLinearMap)

/-- On the closure of the graph, `⟪h_α, w⟫ = λ_α ⟪h_α, g⟫`. -/
lemma inner_snd_of_mem_closure {p : 𝓗 × 𝓗} (hp : p ∈ (oscillatorGraph ι).topologicalClosure)
    (α : ι → ℕ) :
    ⟪hermitePiBasis α, p.2⟫_ℂ = oscillatorEigenvalue ι α * ⟪hermitePiBasis α, p.1⟫_ℂ := by
  have hS : IsClosed {p : 𝓗 × 𝓗 |
      ⟪hermitePiBasis α, p.2⟫_ℂ = oscillatorEigenvalue ι α * ⟪hermitePiBasis α, p.1⟫_ℂ} :=
    isClosed_eq (continuous_const.inner continuous_snd)
      (continuous_const.mul (continuous_const.inner continuous_fst))
  refine closure_minimal (fun q hq => ?_) hS
    ((Submodule.topologicalClosure_coe _).subst (motive := fun s => p ∈ s) hp)
  obtain ⟨f, rfl⟩ := hq
  exact hermiteCoeff_oscillatorCLM α f

omit [DecidableEq ι] in
lemma eq_of_inner_hermitePiBasis_eq {v w : 𝓗}
    (h : ∀ α, ⟪hermitePiBasis α, v⟫_ℂ = ⟪hermitePiBasis α, w⟫_ℂ) : v = w :=
  hermitePiBasis.repr.injective <| lp.ext <| funext fun α => by
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, h]

lemma snd_eq_zero_of_mem_closure {p : 𝓗 × 𝓗} (hp : p ∈ (oscillatorGraph ι).topologicalClosure)
    (h0 : p.1 = 0) : p.2 = 0 :=
  eq_of_inner_hermitePiBasis_eq fun α => by simp [inner_snd_of_mem_closure hp, h0]

variable (ι) in
/-- The harmonic oscillator as an unbounded operator on `L²(ℝ^ι)` with domain `𝓢(ℝ^ι)`. -/
def oscillator : 𝓗 →ₗ.[ℂ] 𝓗 := (oscillatorGraph ι).toLinearPMap

lemma graph_oscillator : (oscillator ι).graph = oscillatorGraph ι :=
  Submodule.toLinearPMap_graph_eq _ fun _ hp h0 =>
    snd_eq_zero_of_mem_closure ((oscillatorGraph ι).le_topologicalClosure hp) h0

/-- The oscillator is closable. -/
theorem isClosable_oscillator : (oscillator ι).IsClosable :=
  ⟨(oscillatorGraph ι).topologicalClosure.toLinearPMap, by
    rw [graph_oscillator, Submodule.toLinearPMap_graph_eq _ fun _ hp h0 =>
      snd_eq_zero_of_mem_closure hp h0]⟩

lemma graph_closure_oscillator :
    (oscillator ι).closure.graph = (oscillatorGraph ι).topologicalClosure := by
  rw [← isClosable_oscillator.graph_closure_eq_closure_graph, graph_oscillator]

/-- The closure `N` of the oscillator is diagonal in the Hermite basis. -/
theorem inner_closure_oscillator (g : (oscillator ι).closure.domain) (α : ι → ℕ) :
    ⟪hermitePiBasis α, (oscillator ι).closure g⟫_ℂ =
      oscillatorEigenvalue ι α * ⟪hermitePiBasis α, (g : 𝓗)⟫_ℂ := by
  have hg : ((g : 𝓗), (oscillator ι).closure g) ∈ (oscillatorGraph ι).topologicalClosure := by
    rw [← graph_closure_oscillator]
    exact ((oscillator ι).closure.mem_graph_iff).2 ⟨g, rfl, rfl⟩
  exact inner_snd_of_mem_closure hg α

/-- On a Schwartz function, the closure `N` is the oscillator `H`. -/
theorem exists_mem_domain_closure (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ∃ h : f.toLp 2 volume ∈ (oscillator ι).closure.domain,
      (oscillator ι).closure ⟨_, h⟩ = (oscillatorCLM f).toLp 2 volume := by
  have hf : (f.toLp 2 volume, (oscillatorCLM f).toLp 2 volume) ∈
      (oscillator ι).closure.graph := by
    rw [graph_closure_oscillator]
    exact (oscillatorGraph ι).le_topologicalClosure ⟨f, rfl⟩
  obtain ⟨y, h1, h2⟩ := ((oscillator ι).closure.mem_graph_iff).1 hf
  have h1' : (y : 𝓗) = f.toLp 2 volume := h1
  refine ⟨h1' ▸ y.2, ?_⟩
  refine Eq.trans ?_ h2
  congr 1
  exact Subtype.ext h1'.symm

/-! ### `𝓢(ℝ^ι) = ⋂_k D(Nᵏ)` -/

lemma exists_inner_eq_pow_mul {k : ℕ} {g : 𝓗} (hg : g ∈ (oscillator ι).closure.powDomain k) :
    ∃ w : 𝓗, ∀ α, ⟪hermitePiBasis α, w⟫_ℂ =
      (oscillatorEigenvalue ι α : ℂ) ^ k * ⟪hermitePiBasis α, g⟫_ℂ := by
  induction k generalizing g with
  | zero => exact ⟨g, fun α => by simp⟩
  | succ k ih =>
    obtain ⟨hgd, hk⟩ := hg
    obtain ⟨w, hw⟩ := ih hk
    refine ⟨w, fun α => ?_⟩
    rw [hw, inner_closure_oscillator ⟨g, hgd⟩, pow_succ, mul_assoc]

omit [DecidableEq ι] in
lemma hermiteWeight_le_two_mul [Nonempty ι] (α : ι → ℕ) :
    (hermiteWeight α : ℝ) ≤ 2 * oscillatorEigenvalue ι α := by
  have h1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h2 : (0 : ℝ) ≤ ∑ i, (α i : ℝ) := by positivity
  simp only [hermiteWeight, oscillatorEigenvalue]
  push_cast
  linarith

/-- **The Schwartz space is the joint domain of the powers of the oscillator** (B. Simon).
A vector `g ∈ L²(ℝ^ι)` lies in `D(Nᵏ)` for every `k`, where `N` is the closure of the harmonic
oscillator on `𝓢(ℝ^ι)`, iff it is a Schwartz function. -/
theorem forall_mem_powDomain_iff [Nonempty ι] (g : 𝓗) :
    (∀ k, g ∈ (oscillator ι).closure.powDomain k) ↔
      ∃ f : 𝓢(EuclideanSpace ℝ ι, ℂ), f.toLp 2 = g := by
  constructor
  · intro hg
    set c : (ι → ℕ) → ℂ := fun α => ⟪hermitePiBasis α, g⟫_ℂ
    have hc : ∀ K, coeffNorm K c ≠ ⊤ := by
      intro K
      obtain ⟨w, hw⟩ := exists_inner_eq_pow_mul (hg K)
      refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 2 ^ K * ‖w‖)) (iSup_le fun α => ?_)
      have hb : ‖⟪hermitePiBasis α, w⟫_ℂ‖ ≤ ‖w‖ := by
        simpa [hermitePiBasis.orthonormal.1 α] using norm_inner_le_norm (hermitePiBasis α) w
      rw [hw, norm_mul, norm_pow, Complex.norm_of_nonneg (oscillatorEigenvalue_nonneg α)] at hb
      rw [← ofReal_norm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (hermiteWeight α : ℝ) ^ K * ‖c α‖
          ≤ (2 * oscillatorEigenvalue ι α) ^ K * ‖c α‖ := by
            gcongr
            exact hermiteWeight_le_two_mul α
        _ = 2 ^ K * (oscillatorEigenvalue ι α ^ K * ‖c α‖) := by ring
        _ ≤ 2 ^ K * ‖w‖ := by gcongr
    refine ⟨hermiteSeries c hc, eq_of_inner_hermitePiBasis_eq fun α => ?_⟩
    rw [← hermiteCoeff_apply, hermiteCoeff_hermiteSeries]
  · rintro ⟨f, rfl⟩ k
    induction k generalizing f with
    | zero => trivial
    | succ k ih =>
      obtain ⟨h, hN⟩ := exists_mem_domain_closure f
      exact ⟨h, hN ▸ ih (oscillatorCLM f)⟩

end SchwartzMap
