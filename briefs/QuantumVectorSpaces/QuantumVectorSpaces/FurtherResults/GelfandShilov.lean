/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.FurtherResults.Irreducibility
public import Mathlib.Analysis.PSeries

/-!
# Further results: the Gelfand–Shilov space `S^{1/2}_{1/2}` and Definition 1

Not part of the brief. This file formalizes part of Sec. 5 of `further-results.tex` in the
brief's directory (R. Stephan, *Further results on the brief "Physical vector spaces for quantum
mechanics"*).

The Schwartz spaces `𝓢(ℝⁿ)` are isomorphic for all `n` (`SchwartzMap.nonempty_schwartzEquiv`), so
as bare topological vector spaces they do not remember the number of degrees of freedom. The
Gelfand–Shilov spaces `S^{1/2}_{1/2}(ℝⁿ)` do: they are pairwise non-isomorphic (Sec. 5 of the
note, not formalized). In one dimension, `S^{1/2}_{1/2}(ℝ)` is the space of functions whose
Hermite coefficients decrease exponentially (Gramchev–Pilipović–Rodino), and that is the
definition used here.

This file shows that `S^{1/2}_{1/2}(ℝ)` does not fit Definition 1 with the observables of
Example 3: `X` and `P` map it into itself, but in the topology of Corollary 2 it is not complete,
because it is a dense proper subspace of `𝓢(ℝ)`.

## Main definitions

* `ExpDecay a`: `|aₙ| ≤ C e^{-εn}` for some `C` and some `ε > 0`;
* `gelfandShilov`: the Schwartz functions with exponentially decreasing Hermite coefficients;
* `coreRestrict`, `obsRestrict`: the inner product and the defining observables restricted to an
  invariant subspace.

## Main results

* `topology_restrict`: on a subspace invariant under the defining observables, the topology of
  Corollary 2 is the subspace topology;
* `lowerOp_apply_mem`, `raiseOp_apply_mem`, `obs_apply_mem`: the ladder operators, and so `X` and `P`, map
  `S^{1/2}_{1/2}(ℝ)` into itself;
* `dense_gelfandShilov`, `exists_not_mem_gelfandShilov`: it is dense in `𝓢(ℝ)` and not all of it;
* `not_completeSpace_gelfandShilov`, `not_isQuantumVectorSpace_gelfandShilov`: with `X`, `P`, `I`
  it is not complete, so it is not a quantum vector space.

## References

* T. Gramchev, S. Pilipović, L. Rodino, Eigenfunction expansions in `ℝⁿ`, Proc. Amer. Math. Soc.
  139 (2011) 4361–4368, Thm. 1.2 and Remark 1.3: `u ∈ S^{1/2}_{1/2}(ℝⁿ)` iff its Hermite
  coefficients satisfy `|a_α| ≤ C e^{-ε|α|}`.
* Z. Lozanov-Crvenković, D. Perišić, Hermite expansions of elements of generalized Gelfand-Shilov
  spaces in quasianalytic and non quasianalytic case, arXiv:quant-ph/0701041, Thm. 2.3: the
  Hermite representation is a topological isomorphism onto the space of coefficient sequences.
-/

open Topology Filter SchwartzMap MeasureTheory Complex
open scoped NNReal ENNReal InnerProductSpace

@[expose] public noncomputable section

namespace QuantumVectorSpaces.FurtherResults

/-! ### Defining observables on an invariant subspace -/

section Restrict

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : PreInnerProductSpace.Core ℂ V)
  {ι : Type*} (X : ι → Module.End ℂ V) (W : Submodule ℂ V) (hW : ∀ i, ∀ v ∈ W, X i v ∈ W)

/-- The inner product, restricted to a subspace. -/
@[instance_reducible]
def coreRestrict : PreInnerProductSpace.Core ℂ W where
  inner v w := c.inner v w
  conj_inner_symm v w := c.conj_inner_symm v w
  re_inner_nonneg v := c.re_inner_nonneg v
  add_left u v w := c.add_left u v w
  smul_left u v r := c.smul_left u v r

lemma coreRestrict_toSeminorm (w : W) :
    (coreRestrict c W).toSeminorm w = c.toSeminorm (w : V) := by
  rw [PreInnerProductSpace.Core.toSeminorm_apply, PreInnerProductSpace.Core.toSeminorm_apply]
  rfl

/-- The defining observables, restricted to an invariant subspace. -/
def obsRestrict (i : ι) : Module.End ℂ W := (X i).restrict (hW i)

/-- Every element of the algebra of the observables maps `W` into itself and restricts to an
element of the algebra of the restricted observables. -/
lemma exists_restrict {A : Module.End ℂ V} (hA : A ∈ algebra X) :
    (∀ v ∈ W, A v ∈ W) ∧
      ∃ A' ∈ algebra (obsRestrict X W hW), ∀ w : W, ((A' w : W) : V) = A w := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    obtain ⟨i, rfl⟩ := hA
    exact ⟨hW i, obsRestrict X W hW i, Algebra.subset_adjoin ⟨i, rfl⟩, fun _ => rfl⟩
  | algebraMap r =>
    refine ⟨fun v hv => ?_, algebraMap ℂ _ r, Subalgebra.algebraMap_mem _ r, fun w => ?_⟩
    · simpa [Module.algebraMap_end_apply] using W.smul_mem r hv
    · simp [Module.algebraMap_end_apply]
  | add A B _ _ hA hB =>
    obtain ⟨hA, A', hA', hAe⟩ := hA
    obtain ⟨hB, B', hB', hBe⟩ := hB
    exact ⟨fun v hv => W.add_mem (hA v hv) (hB v hv), A' + B', Subalgebra.add_mem _ hA' hB',
      fun w => by simp [hAe, hBe]⟩
  | mul A B _ _ hA hB =>
    obtain ⟨hA, A', hA', hAe⟩ := hA
    obtain ⟨hB, B', hB', hBe⟩ := hB
    exact ⟨fun v hv => hA _ (hB v hv), A' * B', Subalgebra.mul_mem _ hA' hB',
      fun w => by simp [hAe, hBe]⟩

/-- **On an invariant subspace, the topology of Corollary 2 is the subspace topology.** -/
theorem topology_restrict :
    topology (coreRestrict c W) (obsRestrict X W hW) = (topology c X).induced W.subtype := by
  refine le_antisymm ?_ ((isGreatest_topology _ _).2 ?_)
  · -- the inclusion is continuous for the topology of the restricted observables
    let tW := topology (coreRestrict c W) (obsRestrict X W hW)
    let tV := topology c X
    have hpW := withSeminorms (coreRestrict c W) (obsRestrict X W hW)
    have := hpW.isTopologicalAddGroup
    rw [← continuous_id_iff_le, continuous_induced_rng]
    refine WithSeminorms.continuous_of_continuous_comp (withSeminorms c X) W.subtype
      fun A => ?_
    obtain ⟨-, A', hA', hAe⟩ := exists_restrict X W hW A.2
    have h : ⇑((seminormFamily c X A).comp W.subtype) =
        seminormFamily (coreRestrict c W) (obsRestrict X W hW) ⟨A', hA'⟩ := by
      ext w
      simp only [seminormFamily, Seminorm.comp_apply, Submodule.subtype_apply]
      rw [coreRestrict_toSeminorm, hAe]
    rw [h]
    exact hpW.continuous_seminorm _
  · -- the subspace topology is admissible
    let tV := topology c X
    have hV := isAdmissible_topology c X
    have := hV.isTopologicalAddGroup
    have := hV.continuousSMul
    let tW : TopologicalSpace W := tV.induced W.subtype
    have hs : Continuous[tW, tV] W.subtype := continuous_induced_dom
    refine ⟨isTopologicalAddGroup_induced W.subtype, continuousSMul_induced W.subtype,
      fun i => ?_, ?_⟩
    · exact continuous_induced_rng.2 ((hV.continuous_obs i).comp hs)
    · exact hV.continuous_inner.comp ((hs.comp continuous_fst).prodMk (hs.comp continuous_snd))

end Restrict

/-! ### Exponentially decreasing sequences -/

section ExpDecay

/-- `|aₙ| ≤ C e^{-εn}` for some `C` and some `ε > 0`. -/
def ExpDecay (a : ℕ → ℂ) : Prop :=
  ∃ C ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ‖a n‖ ≤ C * Real.exp (-(ε * n))

lemma expDecay_zero : ExpDecay 0 := ⟨0, 1, one_pos, fun n => by simp⟩

lemma ExpDecay.add {a b : ℕ → ℂ} (ha : ExpDecay a) (hb : ExpDecay b) : ExpDecay (a + b) := by
  obtain ⟨C, ε, hε, hC⟩ := ha
  obtain ⟨D, δ, hδ, hD⟩ := hb
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  have hD0 : 0 ≤ D := by simpa using (norm_nonneg _).trans (hD 0)
  refine ⟨C + D, min ε δ, lt_min hε hδ, fun n => ?_⟩
  have h1 : Real.exp (-(ε * n)) ≤ Real.exp (-(min ε δ * n)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left _ _) n.cast_nonneg))
  have h2 : Real.exp (-(δ * n)) ≤ Real.exp (-(min ε δ * n)) :=
    Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right _ _) n.cast_nonneg))
  calc ‖(a + b) n‖ ≤ ‖a n‖ + ‖b n‖ := norm_add_le _ _
    _ ≤ C * Real.exp (-(ε * n)) + D * Real.exp (-(δ * n)) := add_le_add (hC n) (hD n)
    _ ≤ C * Real.exp (-(min ε δ * n)) + D * Real.exp (-(min ε δ * n)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC0) (mul_le_mul_of_nonneg_left h2 hD0)
    _ = (C + D) * Real.exp (-(min ε δ * n)) := by ring

lemma ExpDecay.smul {a : ℕ → ℂ} (ha : ExpDecay a) (r : ℂ) : ExpDecay (r • a) := by
  obtain ⟨C, ε, hε, hC⟩ := ha
  refine ⟨‖r‖ * C, ε, hε, fun n => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC n) (norm_nonneg r)

/-- `√(2(x + 1)) ≤ (4/ε) e^{ε(x+1)/2}`. -/
lemma sqrt_le_exp {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) :
    √(2 * (x + 1)) ≤ 4 / ε * Real.exp (ε / 2 * (x + 1)) := by
  have h1 : √(2 * (x + 1)) ≤ 2 * (x + 1) :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  have h2 : ε / 2 * (x + 1) ≤ Real.exp (ε / 2 * (x + 1)) := by
    linarith [Real.add_one_le_exp (ε / 2 * (x + 1))]
  calc √(2 * (x + 1)) ≤ 2 * (x + 1) := h1
    _ = 4 / ε * (ε / 2 * (x + 1)) := by field_simp; norm_num
    _ ≤ 4 / ε * Real.exp (ε / 2 * (x + 1)) := by gcongr

/-- If `a` decreases exponentially, so does `n ↦ √(2(n+1)) aₙ₊₁`. -/
lemma ExpDecay.lower {a : ℕ → ℂ} (ha : ExpDecay a) :
    ExpDecay fun n => (√(2 * ((n : ℝ) + 1)) : ℂ) * a (n + 1) := by
  obtain ⟨C, ε, hε, hC⟩ := ha
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine ⟨C * (4 / ε), ε / 2, by positivity, fun n => ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h := hC (n + 1)
  push_cast at h
  have hs := sqrt_le_exp hε (Nat.cast_nonneg n)
  have he : Real.exp (ε / 2 * ((n : ℝ) + 1)) * Real.exp (-(ε * ((n : ℝ) + 1))) ≤
      Real.exp (-(ε / 2 * n)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  calc √(2 * ((n : ℝ) + 1)) * ‖a (n + 1)‖
      ≤ (4 / ε * Real.exp (ε / 2 * ((n : ℝ) + 1))) * (C * Real.exp (-(ε * ((n : ℝ) + 1)))) :=
        mul_le_mul hs h (norm_nonneg _) (by positivity)
    _ = C * (4 / ε) * (Real.exp (ε / 2 * ((n : ℝ) + 1)) * Real.exp (-(ε * ((n : ℝ) + 1)))) := by
        ring
    _ ≤ C * (4 / ε) * Real.exp (-(ε / 2 * n)) := by gcongr

/-- If `a` decreases exponentially, so does `n ↦ √(2n) aₙ₋₁`. -/
lemma ExpDecay.raise {a : ℕ → ℂ} (ha : ExpDecay a) :
    ExpDecay fun n => (√(2 * (n : ℝ)) : ℂ) * a (n - 1) := by
  obtain ⟨C, ε, hε, hC⟩ := ha
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine ⟨C * (4 / ε) * Real.exp ε, ε / 2, by positivity, fun n => ?_⟩
  rcases n with _ | m
  · simp only [CharP.cast_eq_zero, mul_zero, Real.sqrt_zero, ofReal_zero, zero_mul, norm_zero]
    positivity
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Nat.add_sub_cancel]
  push_cast
  have hs := sqrt_le_exp hε (Nat.cast_nonneg m)
  have he : Real.exp (ε / 2 * ((m : ℝ) + 1)) * Real.exp (-(ε * m)) =
      Real.exp ε * Real.exp (-(ε / 2 * ((m : ℝ) + 1))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  calc √(2 * ((m : ℝ) + 1)) * ‖a m‖
      ≤ (4 / ε * Real.exp (ε / 2 * ((m : ℝ) + 1))) * (C * Real.exp (-(ε * m))) :=
        mul_le_mul hs (hC m) (norm_nonneg _) (by positivity)
    _ = C * (4 / ε) * (Real.exp (ε / 2 * ((m : ℝ) + 1)) * Real.exp (-(ε * m))) := by ring
    _ = C * (4 / ε) * Real.exp ε * Real.exp (-(ε / 2 * ((m : ℝ) + 1))) := by rw [he]; ring

end ExpDecay

/-! ### The space `S^{1/2}_{1/2}(ℝ)` -/

section GelfandShilov

lemma coef_add (n : ℕ) (f g : 𝓢(ℝ, ℂ)) : coef n (f + g) = coef n f + coef n g := by
  simp only [coef, ← toLpCLM_apply (𝕜 := ℂ), map_add, inner_add_right]

lemma coef_smul (n : ℕ) (r : ℂ) (f : 𝓢(ℝ, ℂ)) : coef n (r • f) = r * coef n f := by
  simp only [coef, ← toLpCLM_apply (𝕜 := ℂ), map_smul, inner_smul_right]

/-- **The Gelfand–Shilov space `S^{1/2}_{1/2}(ℝ)`**: the Schwartz functions whose Hermite
coefficients decrease exponentially. -/
def gelfandShilov : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := {f | ExpDecay fun n => coef n f}
  zero_mem' := by
    have : (fun n => coef n (0 : 𝓢(ℝ, ℂ))) = 0 := by
      ext n
      simpa using coef_smul n 0 0
    simp only [Set.mem_ofPred_eq, this]
    exact expDecay_zero
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, coef_add]
    exact hf.add hg
  smul_mem' r f hf := by
    simp only [Set.mem_ofPred_eq, coef_smul]
    exact hf.smul r

lemma mem_gelfandShilov {f : 𝓢(ℝ, ℂ)} : f ∈ gelfandShilov ↔ ExpDecay fun n => coef n f :=
  Iff.rfl

/-- `cₙ(a₊ f) = √(2n) cₙ₋₁(f)`. -/
lemma coef_raiseOp (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    coef n (raiseOp f) = √(2 * (n : ℝ)) * coef (n - 1) f := by
  have hsym : l2Core.inner (hermite n) (posOp f) = l2Core.inner (posOp (hermite n)) f :=
    (isSymmetric_posOp _ _).symm
  have hD : l2Core.inner (hermite n) (derivOp f) = -l2Core.inner (derivOp (hermite n)) f := by
    rw [l2Core_inner_derivOp, neg_neg]
  rw [coef_eq, coef_eq, raiseOp, LinearMap.sub_apply, l2Core_inner_eq, map_sub, inner_sub_right,
    ← l2Core_inner_eq, ← l2Core_inner_eq, hsym, hD, sub_neg_eq_add, l2Core_inner_eq,
    l2Core_inner_eq, ← inner_add_left, ← map_add, ← LinearMap.add_apply, ← lowerOp,
    lowerOp_hermite, map_smul, inner_smul_left, conj_ofReal]
  rfl

lemma lowerOp_apply_mem {f : 𝓢(ℝ, ℂ)} (hf : f ∈ gelfandShilov) : lowerOp f ∈ gelfandShilov := by
  rw [mem_gelfandShilov]
  simp_rw [coef_lowerOp]
  exact ExpDecay.lower hf

lemma raiseOp_apply_mem {f : 𝓢(ℝ, ℂ)} (hf : f ∈ gelfandShilov) : raiseOp f ∈ gelfandShilov := by
  rw [mem_gelfandShilov]
  simp_rw [coef_raiseOp]
  exact ExpDecay.raise hf

lemma posOp_eq : posOp = (2 : ℂ)⁻¹ • (lowerOp + raiseOp) := by
  rw [lowerOp, raiseOp]
  module

lemma derivOp_eq_ladder : derivOp = (2 : ℂ)⁻¹ • (lowerOp - raiseOp) := by
  rw [lowerOp, raiseOp]
  module

/-- **`X`, `P` and `I` map `S^{1/2}_{1/2}(ℝ)` into itself.** -/
lemma obs_apply_mem (ħ : ℝ) (i : Fin 3) {f : 𝓢(ℝ, ℂ)} (hf : f ∈ gelfandShilov) :
    obs ħ i f ∈ gelfandShilov := by
  fin_cases i
  · change posOp f ∈ gelfandShilov
    rw [posOp_eq, LinearMap.smul_apply, LinearMap.add_apply]
    exact gelfandShilov.smul_mem _ (gelfandShilov.add_mem (lowerOp_apply_mem hf) (raiseOp_apply_mem hf))
  · change momOp ħ f ∈ gelfandShilov
    rw [momOp_eq, derivOp_eq_ladder, smul_smul, LinearMap.smul_apply, LinearMap.sub_apply]
    exact gelfandShilov.smul_mem _ (gelfandShilov.sub_mem (lowerOp_apply_mem hf) (raiseOp_apply_mem hf))
  · exact hf

/-- The inner product of `L²`, restricted to `S^{1/2}_{1/2}(ℝ)`. -/
abbrev gsCore : PreInnerProductSpace.Core ℂ gelfandShilov := coreRestrict l2Core gelfandShilov

/-- `X`, `P`, `I` on `S^{1/2}_{1/2}(ℝ)`. -/
abbrev gsObs (ħ : ℝ) : Fin 3 → Module.End ℂ gelfandShilov :=
  obsRestrict (obs ħ) gelfandShilov fun i _ hf => obs_apply_mem ħ i hf

/-- With `X`, `P`, `I`, the topology of Corollary 2 on `S^{1/2}_{1/2}(ℝ)` is the topology of
`𝓢(ℝ)`. -/
theorem topology_gelfandShilov {ħ : ℝ} (hħ : ħ ≠ 0) :
    topology gsCore (gsObs ħ) = (inferInstance : TopologicalSpace gelfandShilov) := by
  rw [topology_restrict, topology_schwartz ħ hħ]
  rfl

lemma coef_hermite (k n : ℕ) : coef k (hermite n) = if k = n then 1 else 0 := by
  have ho := (TauCeti.hermiteHilbertBasis ℂ).orthonormal
  rw [TauCeti.coe_hermiteHilbertBasis] at ho
  rw [coef, toLp_hermite, orthonormal_iff_ite.1 ho]

lemma hermite_mem (n : ℕ) : hermite n ∈ gelfandShilov := by
  refine ⟨Real.exp n, 1, one_pos, fun k => ?_⟩
  dsimp only
  rw [coef_hermite]
  split_ifs with h
  · subst h
    simp [← Real.exp_add]
  · simp only [norm_zero]
    positivity

lemma hermiteSum_mem (m : ℕ) (f : 𝓢(ℝ, ℂ)) : hermiteSum m f ∈ gelfandShilov :=
  Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (hermite_mem n)

/-- **`S^{1/2}_{1/2}(ℝ)` is dense in `𝓢(ℝ)`**, since it contains the Hermite partial sums. -/
theorem dense_gelfandShilov : Dense (gelfandShilov : Set 𝓢(ℝ, ℂ)) := fun f =>
  mem_closure_of_tendsto (tendsto_hermiteSum f) (Eventually.of_forall fun m => hermiteSum_mem m f)

/-- The sequence `e^{-√(n+1)}`. -/
def slowSeq (n : ℕ) : ℂ := (Real.exp (-√((n : ℝ) + 1)) : ℂ)

lemma norm_slowSeq (n : ℕ) : ‖slowSeq n‖ = Real.exp (-√((n : ℝ) + 1)) := by
  rw [slowSeq, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

/-- `(n + 1)^K e^{-√(n+1)} ≤ (2K)!`. -/
lemma pow_mul_norm_slowSeq_le (K n : ℕ) :
    ((n : ℝ) + 1) ^ K * ‖slowSeq n‖ ≤ (2 * K).factorial := by
  rw [norm_slowSeq]
  have hx : 0 ≤ √((n : ℝ) + 1) := Real.sqrt_nonneg _
  have h := Real.pow_div_factorial_le_exp _ hx (2 * K)
  rw [pow_mul, Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)] at h
  calc ((n : ℝ) + 1) ^ K * Real.exp (-√((n : ℝ) + 1))
      ≤ Real.exp √((n : ℝ) + 1) * (2 * K).factorial * Real.exp (-√((n : ℝ) + 1)) := by gcongr
    _ = (2 * K).factorial := by
        rw [mul_comm, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

lemma memℓp_slowSeq : Memℓp slowSeq 2 := by
  refine memℓp_gen ?_
  have hb (n : ℕ) : ‖slowSeq n‖ ^ (2 : ℝ≥0∞).toReal ≤ 24 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    rw [ENNReal.toReal_ofNat, Real.rpow_two]
    have h1 := pow_mul_norm_slowSeq_le 2 n
    have h2 : ‖slowSeq n‖ ≤ 1 := by
      rw [norm_slowSeq, Real.exp_le_one_iff]
      exact neg_nonpos.2 (Real.sqrt_nonneg _)
    norm_num at h1
    rw [le_mul_inv_iff₀ (by positivity)]
    nlinarith [norm_nonneg (slowSeq n), sq_nonneg ((n : ℝ) + 1)]
  have hs : Summable fun n : ℕ => 24 * (((n : ℝ) + 1) ^ 2)⁻¹ := by
    refine Summable.mul_left _ ?_
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
    simpa using this
  exact hs.of_nonneg_of_le (fun n => by positivity) hb

/-- `e^{-√(n+1)}` does not decrease exponentially. -/
lemma not_expDecay_slowSeq : ¬ ExpDecay slowSeq := by
  rintro ⟨C, ε, hε, hC⟩
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0)
    simpa using h
  -- `√(n+1) ≤ (ε(n+1) + 1/ε)/2`, so `e^{εn/2} ≤ C e^{ε/2 + 1/(2ε)}` for all `n`
  have hb (n : ℕ) : Real.exp (ε / 2 * n) ≤ C * Real.exp (ε / 2 + 1 / (2 * ε)) := by
    have h := hC n
    rw [norm_slowSeq] at h
    set s := √((n : ℝ) + 1)
    have hsq : s ≤ (ε * ((n : ℝ) + 1) + 1 / ε) / 2 := by
      have hx : s ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hsq' : (ε * s - 1) ^ 2 = ε * ((n : ℝ) + 1) * ε + 1 - 2 * s * ε := by
        rw [← hx]; ring
      have key : 2 * s * ε ≤ ε * ((n : ℝ) + 1) * ε + 1 := by
        linarith [sq_nonneg (ε * s - 1)]
      have he : (ε * ((n : ℝ) + 1) + 1 / ε) / 2 * ε = (ε * ((n : ℝ) + 1) * ε + 1) / 2 := by
        rw [div_mul_eq_mul_div, add_mul, one_div, inv_mul_cancel₀ hε.ne']
      refine le_of_mul_le_mul_right ?_ hε
      rw [he]
      linarith
    have h3 : s - ε / 2 * n ≤ ε / 2 + 1 / (2 * ε) := by
      have h2 : 1 / (2 * ε) = 1 / ε / 2 := by rw [div_div, mul_comm]
      rw [h2]
      linarith
    calc Real.exp (ε / 2 * n) = Real.exp (-s) * Real.exp (s + ε / 2 * n) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ C * Real.exp (-(ε * n)) * Real.exp (s + ε / 2 * n) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = C * Real.exp (s - ε / 2 * n) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ C * Real.exp (ε / 2 + 1 / (2 * ε)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h3) hC0
  obtain ⟨n, hn⟩ := exists_nat_gt ((C * Real.exp (ε / 2 + 1 / (2 * ε))) / (ε / 2))
  have h1 := hb n
  have h2 : ε / 2 * n + 1 ≤ Real.exp (ε / 2 * n) := by
    linarith [Real.add_one_le_exp (ε / 2 * n)]
  rw [div_lt_iff₀ (by positivity)] at hn
  linarith

/-- **`S^{1/2}_{1/2}(ℝ)` is a proper subspace of `𝓢(ℝ)`**: the Schwartz function with Hermite
coefficients `e^{-√(n+1)}` is not in it. -/
theorem exists_not_mem_gelfandShilov : ∃ f : 𝓢(ℝ, ℂ), f ∉ gelfandShilov := by
  set g : Lp ℂ 2 (volume : Measure ℝ) :=
    (TauCeti.hermiteHilbertBasis ℂ).repr.symm ⟨slowSeq, memℓp_slowSeq⟩
  have hg (n : ℕ) : ⟪TauCeti.hermiteFunctionLp ℂ n, g⟫_ℂ = slowSeq n := by
    rw [← TauCeti.coe_hermiteHilbertBasis, ← HilbertBasis.repr_apply_apply,
      LinearIsometryEquiv.apply_symm_apply]
  obtain ⟨f, hf⟩ := (exists_toLp_eq_iff g).2 fun K =>
    ⟨(2 * K).factorial, fun n => by rw [hg]; exact pow_mul_norm_slowSeq_le K n⟩
  refine ⟨f, fun hmem => not_expDecay_slowSeq ?_⟩
  have : (fun n => coef n f) = slowSeq := by
    ext n
    rw [coef, hf, hg]
  rw [mem_gelfandShilov, this] at hmem
  exact hmem

/-- **`S^{1/2}_{1/2}(ℝ)` with `X`, `P`, `I` is not complete** in the topology of Corollary 2. -/
theorem not_completeSpace_gelfandShilov {ħ : ℝ} (hħ : ħ ≠ 0) :
    ¬ @CompleteSpace gelfandShilov (uniformSpace gsCore (gsObs ħ)) := by
  intro hc
  have : IsUniformAddGroup gelfandShilov := IsUniformAddGroup.comap gelfandShilov.subtype
  rw [uniformSpace_eq _ _ (topology_gelfandShilov hħ)] at hc
  have hcl : IsClosed (gelfandShilov : Set 𝓢(ℝ, ℂ)) :=
    (completeSpace_coe_iff_isComplete.1 hc).isClosed
  obtain ⟨f, hf⟩ := exists_not_mem_gelfandShilov
  have h := dense_gelfandShilov f
  rw [hcl.closure_eq] at h
  exact hf h

/-- **`S^{1/2}_{1/2}(ℝ)` with `X`, `P`, `I` is not a quantum vector space**, whatever the
structure constants. -/
theorem not_isQuantumVectorSpace_gelfandShilov {ħ : ℝ} (hħ : ħ ≠ 0)
    (C : Fin 3 → Fin 3 → Fin 3 →₀ ℂ) : ¬ IsQuantumVectorSpace gsCore (gsObs ħ) ħ C :=
  fun h => not_completeSpace_gelfandShilov hħ h.completeSpace

end GelfandShilov

end QuantumVectorSpaces.FurtherResults
