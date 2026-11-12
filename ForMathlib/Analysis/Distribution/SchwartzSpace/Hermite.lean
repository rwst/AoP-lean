/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Pi.Basis
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Ladder
import TauCeti.Analysis.SpecialFunctions.Gaussian.Schwartz

/-!
# Multi-index Hermite functions as Schwartz functions

On `ℝ^ι = EuclideanSpace ℝ ι`, the multi-index Hermite functions
`h_α(x) = ∏ᵢ ψ_{αᵢ}(xᵢ)`, `α : ι → ℕ`, are Schwartz functions, and they form a Hilbert basis of
`L²(ℝ^ι)` (TauCeti's `hermiteFunctionPiBasis`, moved from `ι → ℝ` to the Euclidean space). The
Hermite coefficient `c_α(f) = ⟪h_α, f⟫` of a Schwartz function transforms under multiplication by
a coordinate and under a partial derivative by the ladder relations
`c_α(xᵢ f) = √((αᵢ+1)/2) c_{α+eᵢ}(f) + √(αᵢ/2) c_{α-eᵢ}(f)` and
`c_α(∂ᵢ f) = √((αᵢ+1)/2) c_{α+eᵢ}(f) - √(αᵢ/2) c_{α-eᵢ}(f)`.

## Main definitions

* `SchwartzMap.hermitePi α`: the Hermite function `h_α` as a Schwartz function;
* `SchwartzMap.hermitePiBasis`: the Hilbert basis `(h_α)` of `L²(ℝ^ι)`;
* `SchwartzMap.coordMulCLM i`, `SchwartzMap.coordDerivCLM i`: multiplication by `xᵢ` and `∂ᵢ`;
* `SchwartzMap.hermiteCoeff α`: the coefficient functional `f ↦ ⟪h_α, f⟫`.

## Main results

* `SchwartzMap.toLp_hermitePi`: `h_α` is the `α`-th basis vector;
* `SchwartzMap.hermiteCoeff_coordMulCLM`, `SchwartzMap.hermiteCoeff_coordDerivCLM`: the ladder
  relations for coefficients.
-/

open MeasureTheory TauCeti Finset
open scoped SchwartzMap LineDeriv InnerProductSpace

@[expose] public noncomputable section

namespace SchwartzMap

variable {ι : Type*} [Fintype ι]

/-- The multi-index Hermite function `x ↦ ∏ᵢ ψ_{αᵢ}(xᵢ)`. -/
def hermitePiFun (α : ι → ℕ) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∏ i, (hermiteFunction (α i) (x i) : ℂ)

/-- Splitting off the `i`-th factor, with the `i`-th index replaced by `k`. -/
lemma hermitePiFun_update [DecidableEq ι] (α : ι → ℕ) (i : ι) (k : ℕ)
    (x : EuclideanSpace ℝ ι) :
    hermitePiFun (Function.update α i k) x =
      (hermiteFunction k (x i) : ℂ) * ∏ j ∈ univ.erase i, (hermiteFunction (α j) (x j) : ℂ) := by
  rw [hermitePiFun, ← Finset.mul_prod_erase _ _ (mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma hermitePiFun_eq_mul [DecidableEq ι] (α : ι → ℕ) (i : ι) (x : EuclideanSpace ℝ ι) :
    hermitePiFun α x =
      (hermiteFunction (α i) (x i) : ℂ) * ∏ j ∈ univ.erase i, (hermiteFunction (α j) (x j) : ℂ) :=
  by rw [← hermitePiFun_update, Function.update_eq_self]

lemma continuous_hermitePiFun (α : ι → ℕ) : Continuous (hermitePiFun α) :=
  continuous_finsetProd _ fun i _ => Complex.continuous_ofReal.comp
    ((continuous_hermiteFunction (α i)).comp (EuclideanSpace.proj i).continuous)

/-- The partial derivative of a multi-index Hermite function in the direction `eᵢ`. -/
lemma hasLineDerivAt_hermitePiFun [DecidableEq ι] (α : ι → ℕ) (i : ι) (x : EuclideanSpace ℝ ι) :
    HasLineDerivAt ℝ (hermitePiFun α)
      (((deriv (hermiteFunction (α i)) (x i) : ℝ) : ℂ) *
        ∏ j ∈ univ.erase i, (hermiteFunction (α j) (x j) : ℂ)) x (EuclideanSpace.single i 1) := by
  have hfun : (fun t : ℝ => hermitePiFun α (x + t • EuclideanSpace.single i 1)) =
      fun t => (hermiteFunction (α i) (x i + t) : ℂ) *
        ∏ j ∈ univ.erase i, (hermiteFunction (α j) (x j) : ℂ) := by
    funext t
    rw [hermitePiFun_eq_mul α i]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Finset.ne_of_mem_erase hj]
  unfold HasLineDerivAt
  rw [hfun]
  have h1 : HasDerivAt (hermiteFunction (α i)) (deriv (hermiteFunction (α i)) (x i + 0))
      (x i + 0) :=
    ((contDiff_hermiteFunction (α i)).differentiable (by simp)).differentiableAt.hasDerivAt
  have h2 := (h1.comp_const_add (x i) 0 |>.ofReal_comp).mul_const
    (∏ j ∈ univ.erase i, (hermiteFunction (α j) (x j) : ℂ))
  rw [add_zero] at h2
  exact h2

/-- The multi-index ladder relation for multiplication by a coordinate. -/
lemma coord_mul_hermitePiFun [DecidableEq ι] (α : ι → ℕ) (i : ι) (x : EuclideanSpace ℝ ι) :
    (x i : ℂ) * hermitePiFun α x =
      (√(((α i : ℝ) + 1) / 2) : ℂ) * hermitePiFun (Function.update α i (α i + 1)) x +
        (√((α i : ℝ) / 2) : ℂ) * hermitePiFun (Function.update α i (α i - 1)) x := by
  rw [hermitePiFun_eq_mul α i, hermitePiFun_update, hermitePiFun_update]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (mul_hermiteFunction (α i) (x i))
  push_cast at h
  linear_combination (∏ j ∈ univ.erase i, (hermiteFunction (α j) (x j) : ℂ)) * h

/-- The multi-index ladder relation for a partial derivative. -/
lemma deriv_mul_hermitePiFun [DecidableEq ι] (α : ι → ℕ) (i : ι) (x : EuclideanSpace ℝ ι) :
    ((deriv (hermiteFunction (α i)) (x i) : ℝ) : ℂ) *
        ∏ j ∈ univ.erase i, (hermiteFunction (α j) (x j) : ℂ) =
      (√((α i : ℝ) / 2) : ℂ) * hermitePiFun (Function.update α i (α i - 1)) x -
        (√(((α i : ℝ) + 1) / 2) : ℂ) * hermitePiFun (Function.update α i (α i + 1)) x := by
  rw [hermitePiFun_update, hermitePiFun_update, deriv_hermiteFunction]
  push_cast
  ring

/-! ### Coordinate operators -/

lemma hasTemperateGrowth_coord (i : ι) :
    Function.HasTemperateGrowth fun x : EuclideanSpace ℝ ι => ((x i : ℝ) : ℂ) :=
  (Complex.ofRealCLM.comp (EuclideanSpace.proj i)).hasTemperateGrowth

/-- Multiplication by the coordinate `xᵢ`. -/
def coordMulCLM (i : ι) : 𝓢(EuclideanSpace ℝ ι, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
  smulLeftCLM ℂ fun x : EuclideanSpace ℝ ι => ((x i : ℝ) : ℂ)

@[simp]
lemma coordMulCLM_apply (i : ι) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    coordMulCLM i f x = (x i : ℂ) * f x := by
  rw [coordMulCLM, smulLeftCLM_apply_apply (hasTemperateGrowth_coord i), smul_eq_mul]

/-- The partial derivative `∂ᵢ` in the direction of the `i`-th coordinate. -/
def coordDerivCLM [DecidableEq ι] (i : ι) :
    𝓢(EuclideanSpace ℝ ι, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclideanSpace ℝ ι, ℂ) (EuclideanSpace.single i (1 : ℝ))

lemma coordDerivCLM_apply [DecidableEq ι] (i : ι) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    coordDerivCLM i f = ∂_{EuclideanSpace.single i (1 : ℝ)} f :=
  LineDeriv.lineDerivOpCLM_apply _ _

/-! ### Hermite functions as Schwartz functions -/

/-- The Gaussian `∏ᵢ ψ₀(xᵢ)`. -/
lemma hermitePiFun_zero (x : EuclideanSpace ℝ ι) :
    hermitePiFun 0 x = ((√√Real.pi : ℂ)⁻¹) ^ Fintype.card ι *
      Complex.exp (-(1 / 2 : ℂ) * ((‖x‖ : ℝ) : ℂ) ^ 2) := by
  have hn : ((‖x‖ : ℝ) : ℂ) ^ 2 = ∑ i, ((x i : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    push_cast
    rfl
  rw [hn, Finset.mul_sum, Complex.exp_sum, ← Finset.card_univ, ← Finset.prod_const,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.zero_apply, hermiteFunction_zero]
  push_cast
  rw [div_eq_inv_mul]
  congr 2
  ring

theorem exists_hermitePi (α : ι → ℕ) :
    ∃ S : 𝓢(EuclideanSpace ℝ ι, ℂ), ∀ x, S x = hermitePiFun α x := by
  classical
  induction h : ∑ i, α i using Nat.strong_induction_on generalizing α with
  | _ n ih =>
    by_cases h0 : ∀ i, α i = 0
    · obtain rfl : α = 0 := funext h0
      refine ⟨((√√Real.pi : ℂ)⁻¹) ^ Fintype.card ι •
        gaussianSchwartzMap (E := EuclideanSpace ℝ ι) (b := 1 / 2) (by norm_num), fun x => ?_⟩
      rw [smul_apply, gaussianSchwartzMap_apply, hermitePiFun_zero, smul_eq_mul]
    push Not at h0
    obtain ⟨i, hi⟩ := h0
    set β := Function.update α i (α i - 1) with hβ
    have hβi : β i = α i - 1 := by simp [hβ]
    have hlt : ∑ j, β j < n := by
      rw [← h]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, mem_univ i, by omega⟩
      rcases eq_or_ne j i with rfl | hj
      · omega
      · rw [hβ, Function.update_of_ne hj]
    obtain ⟨S, hS⟩ := ih _ hlt β rfl
    have hα : Function.update β i (β i + 1) = α := by
      rw [hβi, Nat.sub_add_cancel (Nat.pos_of_ne_zero hi), hβ, Function.update_idem,
        Function.update_eq_self]
    have hsq : (√(2 * ((β i : ℝ) + 1)) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * ((β i : ℝ) + 1) := by positivity
      exact_mod_cast (Real.sqrt_pos.2 this).ne'
    refine ⟨(√(2 * ((β i : ℝ) + 1)) : ℂ)⁻¹ • (coordMulCLM i S - coordDerivCLM i S),
      fun x => ?_⟩
    have hd : coordDerivCLM i S x = ((deriv (hermiteFunction (β i)) (x i) : ℝ) : ℂ) *
        ∏ j ∈ univ.erase i, (hermiteFunction (β j) (x j) : ℂ) := by
      rw [coordDerivCLM_apply, lineDerivOp_apply]
      have hSf : (S : EuclideanSpace ℝ ι → ℂ) = hermitePiFun β := funext hS
      rw [hSf]
      exact (hasLineDerivAt_hermitePiFun β i x).lineDeriv
    rw [smul_apply, sub_apply, coordMulCLM_apply, hd, hS, hermitePiFun_eq_mul β i,
      ← hα, hermitePiFun_update, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hsq]
    have h1 := congrArg (fun r : ℝ => (r : ℂ)) (mul_sub_deriv_hermiteFunction (β i) (x i))
    push_cast at h1
    linear_combination (∏ j ∈ univ.erase i, (hermiteFunction (β j) (x j) : ℂ)) * h1

/-- The multi-index Hermite function `h_α` as a Schwartz function. -/
def hermitePi (α : ι → ℕ) : 𝓢(EuclideanSpace ℝ ι, ℂ) :=
  (exists_hermitePi α).choose

@[simp]
lemma hermitePi_apply (α : ι → ℕ) (x : EuclideanSpace ℝ ι) :
    hermitePi α x = hermitePiFun α x :=
  (exists_hermitePi α).choose_spec x

/-- Ladder relation: `xᵢ h_α = √((αᵢ+1)/2) h_{α+eᵢ} + √(αᵢ/2) h_{α-eᵢ}`. -/
lemma coordMulCLM_hermitePi [DecidableEq ι] (α : ι → ℕ) (i : ι) :
    coordMulCLM i (hermitePi α) =
      (√(((α i : ℝ) + 1) / 2) : ℂ) • hermitePi (Function.update α i (α i + 1)) +
        (√((α i : ℝ) / 2) : ℂ) • hermitePi (Function.update α i (α i - 1)) := by
  ext x
  simp only [coordMulCLM_apply, hermitePi_apply, add_apply, smul_apply, smul_eq_mul]
  exact coord_mul_hermitePiFun α i x

/-- Ladder relation: `∂ᵢ h_α = √(αᵢ/2) h_{α-eᵢ} - √((αᵢ+1)/2) h_{α+eᵢ}`. -/
lemma coordDerivCLM_hermitePi [DecidableEq ι] (α : ι → ℕ) (i : ι) :
    coordDerivCLM i (hermitePi α) =
      (√((α i : ℝ) / 2) : ℂ) • hermitePi (Function.update α i (α i - 1)) -
        (√(((α i : ℝ) + 1) / 2) : ℂ) • hermitePi (Function.update α i (α i + 1)) := by
  ext x
  rw [coordDerivCLM_apply, lineDerivOp_apply]
  have hSf : (hermitePi α : EuclideanSpace ℝ ι → ℂ) = hermitePiFun α :=
    funext (hermitePi_apply α)
  rw [hSf, (hasLineDerivAt_hermitePiFun α i x).lineDeriv, deriv_mul_hermitePiFun]
  simp only [sub_apply, smul_apply, hermitePi_apply, smul_eq_mul]

/-! ### The Hilbert basis of `L²(ℝ^ι)` -/

/-- `L²(ι → ℝ) ≃ L²(ℝ^ι)`, by composition with `ofLp`. -/
def lpEuclidean :
    Lp ℂ 2 (volume : Measure (ι → ℝ)) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) :=
  LinearIsometryEquiv.ofSurjective
    (Lp.compMeasurePreservingₗᵢ ℂ _ (PiLp.volume_preserving_ofLp ι)) fun g =>
      ⟨Lp.compMeasurePreserving _ (PiLp.volume_preserving_toLp ι) g, by
        change Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ g) = g
        rw [← Lp.compMeasurePreserving_comp_apply]
        exact Lp.compMeasurePreserving_id_apply g⟩

lemma lpEuclidean_apply (g : Lp ℂ 2 (volume : Measure (ι → ℝ))) :
    lpEuclidean g = Lp.compMeasurePreserving _ (PiLp.volume_preserving_ofLp ι) g :=
  rfl

/-- The Hilbert basis `(h_α)` of `L²(ℝ^ι)`. -/
def hermitePiBasis :
    HilbertBasis (ι → ℕ) ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) :=
  HilbertBasis.ofRepr (lpEuclidean.symm.trans (hermiteFunctionPiBasis ℂ ι).repr)

lemma hermitePiBasis_apply (α : ι → ℕ) :
    hermitePiBasis α = lpEuclidean (hermiteFunctionPiBasis ℂ ι α) := by
  classical
  rw [← (hermitePiBasis (ι := ι)).repr_symm_single α,
    ← (hermiteFunctionPiBasis ℂ ι).repr_symm_single α]
  rfl

/-- The Schwartz function `h_α` is the `α`-th basis vector of `L²(ℝ^ι)`. -/
theorem toLp_hermitePi (α : ι → ℕ) : (hermitePi α).toLp 2 = hermitePiBasis α := by
  rw [hermitePiBasis_apply]
  refine Lp.ext ?_
  filter_upwards [coeFn_toLp (hermitePi α) 2,
    Lp.coeFn_compMeasurePreserving (hermiteFunctionPiBasis ℂ ι α)
      (PiLp.volume_preserving_ofLp ι),
    (PiLp.volume_preserving_ofLp ι).quasiMeasurePreserving.ae
      (coeFn_hermiteFunctionPiBasis ℂ ι α)] with x h1 h2 h3
  rw [h1, hermitePi_apply, lpEuclidean_apply, h2, Function.comp_apply, h3]
  simp [hermitePiFun]

/-! ### Hermite coefficients -/

/-- The Hermite coefficient `c_α(f) = ⟪h_α, f⟫` of a Schwartz function. -/
def hermiteCoeff (α : ι → ℕ) : 𝓢(EuclideanSpace ℝ ι, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ (hermitePiBasis α)).comp (toLpCLM ℂ ℂ 2 volume)

lemma hermiteCoeff_apply (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α f = ⟪hermitePiBasis α, f.toLp 2⟫_ℂ :=
  rfl

lemma hermiteCoeff_eq_integral (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α f = ∫ x, hermitePiFun α x * f x := by
  rw [hermiteCoeff_apply, ← toLp_hermitePi, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toLp (hermitePi α) 2, coeFn_toLp f 2] with x h1 h2
  rw [h1, h2, hermitePi_apply]
  simp [hermitePiFun, map_prod, Complex.conj_ofReal, mul_comm]

lemma integrable_hermitePiFun_mul (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    Integrable fun x => hermitePiFun α x * f x := by
  have h := (f.integrable (μ := volume)).bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 (hermitePi α))
    (hermitePi α).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => norm_le_seminorm ℝ _ x)
  simpa using h

/-- The coefficients of `h_β` are those of a basis vector. -/
lemma hermiteCoeff_hermitePi (α β : ι → ℕ) :
    hermiteCoeff α (hermitePi β) = if α = β then 1 else 0 := by
  rw [hermiteCoeff_apply, toLp_hermitePi]
  exact orthonormal_iff_ite.1 hermitePiBasis.orthonormal α β

/-- Ladder relation for coefficients: `c_α(xᵢ f) = √((αᵢ+1)/2) c_{α+eᵢ}(f) + √(αᵢ/2) c_{α-eᵢ}(f)`.
-/
theorem hermiteCoeff_coordMulCLM [DecidableEq ι] (α : ι → ℕ) (i : ι)
    (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α (coordMulCLM i f) =
      (√(((α i : ℝ) + 1) / 2) : ℂ) * hermiteCoeff (Function.update α i (α i + 1)) f +
        (√((α i : ℝ) / 2) : ℂ) * hermiteCoeff (Function.update α i (α i - 1)) f := by
  simp only [hermiteCoeff_eq_integral, coordMulCLM_apply]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((integrable_hermitePiFun_mul _ f).const_mul _) ((integrable_hermitePiFun_mul _ f).const_mul _)]
  congr 1
  funext x
  linear_combination (f x) * coord_mul_hermitePiFun α i x

/-- Ladder relation for coefficients: `c_α(∂ᵢ f) = √((αᵢ+1)/2) c_{α+eᵢ}(f) - √(αᵢ/2) c_{α-eᵢ}(f)`.
-/
theorem hermiteCoeff_coordDerivCLM [DecidableEq ι] (α : ι → ℕ) (i : ι)
    (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α (coordDerivCLM i f) =
      (√(((α i : ℝ) + 1) / 2) : ℂ) * hermiteCoeff (Function.update α i (α i + 1)) f -
        (√((α i : ℝ) / 2) : ℂ) * hermiteCoeff (Function.update α i (α i - 1)) f := by
  have hibp := integral_mul_lineDerivOp_right_eq_neg_left (μ := volume) (hermitePi α) f
    (EuclideanSpace.single i (1 : ℝ))
  simp only [hermitePi_apply] at hibp
  rw [hermiteCoeff_eq_integral, coordDerivCLM_apply, hibp, ← coordDerivCLM_apply,
    coordDerivCLM_hermitePi]
  simp only [sub_apply, smul_apply, smul_eq_mul, hermitePi_apply, hermiteCoeff_eq_integral]
  rw [← integral_neg, ← integral_const_mul, ← integral_const_mul, ← integral_sub
    ((integrable_hermitePiFun_mul _ f).const_mul _) ((integrable_hermitePiFun_mul _ f).const_mul _)]
  congr 1
  funext x
  ring

end SchwartzMap
