/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.HilbertBasisMaps
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The trace of a positive operator in `[0, ∞]`

For a bounded operator `T` on a complex Hilbert space and a Hilbert basis `{eᵢ}`, the diagonal
sum `∑ᵢ ⟪eᵢ, T eᵢ⟫` need not converge. For positive `T` its terms are nonnegative, so the sum
always exists in `[0, ∞]`, and it does not depend on the basis. The proof writes
`⟪eᵢ, R R† eᵢ⟫ = ‖R† eᵢ‖²`, expands each square in a second basis by Parseval, and exchanges the
two sums of nonnegative terms.

## Main results

* `HilbertBasis.tsum_ofReal_norm_inner_sq`: Parseval's identity in `[0, ∞]`.
* `ContinuousLinearMap.tsum_ofReal_norm_apply_sq_eq_adjoint`: `∑ᵢ ‖R eᵢ‖² = ∑ⱼ ‖R† fⱼ‖²`.
* `ContinuousLinearMap.posTrace`: the trace in `[0, ∞]`.
* `ContinuousLinearMap.posTrace_eq_tsum`: it can be computed in any Hilbert basis.
* `ContinuousLinearMap.posTrace_mul_star`: `tr (R R†) = ∑ⱼ ‖R fⱼ‖²`.
* `ContinuousLinearMap.posTrace_conj_of_star_mul_self`: conjugation by an isometry preserves it.
* `ContinuousLinearMap.posTrace_add`, `ContinuousLinearMap.posTrace_smul`: additivity and
  homogeneity on positive operators.
* `ContinuousLinearMap.posTrace_eq_zero_iff`: only `0` has trace zero.
* `ContinuousLinearMap.posTrace_rankOne_self`: `tr |x⟩⟨x| = ‖x‖²`.
* `ContinuousLinearMap.norm_le_toReal_posTrace`: `‖T‖ ≤ tr T`.
* `ContinuousLinearMap.posTrace_eq_ofReal_re_trace`: in finite dimension it is the usual trace.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

namespace HilbertBasis

variable {ι : Type*}

/-- Parseval's identity in `[0, ∞]`. -/
theorem tsum_ofReal_norm_inner_sq (b : HilbertBasis ι ℂ E) (x : E) :
    ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (b.hasSum_norm_inner_sq x).summable,
    (b.hasSum_norm_inner_sq x).tsum_eq]

end HilbertBasis

namespace ContinuousLinearMap

variable [CompleteSpace E] {ι κ : Type*}

/-- `∑ᵢ ‖R eᵢ‖² = ∑ⱼ ‖R† fⱼ‖²` in `[0, ∞]`, for any two Hilbert bases. -/
theorem tsum_ofReal_norm_apply_sq_eq_adjoint (R : E →L[ℂ] E) (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ E) :
    ∑' i, ENNReal.ofReal (‖R (b i)‖ ^ 2) = ∑' j, ENNReal.ofReal (‖adjoint R (c j)‖ ^ 2) := by
  calc ∑' i, ENNReal.ofReal (‖R (b i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, R (b i)⟫_ℂ‖ ^ 2) := by
        simp_rw [c.tsum_ofReal_norm_inner_sq]
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪b i, adjoint R (c j)⟫_ℂ‖ ^ 2) := by
        rw [ENNReal.tsum_comm]
        congr! 4 with j i
        rw [← adjoint_inner_left, norm_inner_symm]
    _ = _ := by simp_rw [b.tsum_ofReal_norm_inner_sq]

/-- The Hilbert basis used to define `posTrace`. -/
def posTraceBasis (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :
    HilbertBasis (exists_hilbertBasis ℂ E).choose ℂ E :=
  (exists_hilbertBasis ℂ E).choose_spec.choose

/-- The trace `∑ᵢ ⟪eᵢ, T eᵢ⟫ ∈ [0, ∞]` of an operator, meaningful for positive `T`. It does not
depend on the Hilbert basis (`posTrace_eq_tsum`). -/
def posTrace (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (⟪posTraceBasis E i, T (posTraceBasis E i)⟫_ℂ).re

lemma re_inner_mul_star_apply (R : E →L[ℂ] E) (x : E) :
    (⟪x, (R * star R) x⟫_ℂ).re = ‖star R x‖ ^ 2 := by
  rw [mul_def, comp_apply, ← adjoint_inner_left, star_eq_adjoint, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `tr (R R†) = ∑ⱼ ‖R fⱼ‖²` in any Hilbert basis. -/
theorem posTrace_mul_star (R : E →L[ℂ] E) (c : HilbertBasis κ ℂ E) :
    posTrace (R * star R) = ∑' j, ENNReal.ofReal (‖R (c j)‖ ^ 2) := by
  simp only [posTrace, re_inner_mul_star_apply]
  rw [star_eq_adjoint, tsum_ofReal_norm_apply_sq_eq_adjoint _ _ c, adjoint_adjoint]

variable {T : E →L[ℂ] E}

lemma sqrt_mul_star_sqrt (hT : 0 ≤ T) : CFC.sqrt T * star (CFC.sqrt T) = T := by
  rw [(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self T hT]

lemma re_inner_apply_eq_norm_sqrt_sq (hT : 0 ≤ T) (x : E) :
    (⟪x, T x⟫_ℂ).re = ‖CFC.sqrt T x‖ ^ 2 := by
  conv_lhs => rw [← sqrt_mul_star_sqrt hT]
  rw [re_inner_mul_star_apply, (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq]

lemma re_inner_apply_nonneg (hT : 0 ≤ T) (x : E) : 0 ≤ (⟪x, T x⟫_ℂ).re := by
  rw [re_inner_apply_eq_norm_sqrt_sq hT]
  positivity

/-- `tr T = ∑ᵢ ‖√T eᵢ‖²` in any Hilbert basis. -/
theorem posTrace_eq_tsum_norm_sqrt_sq (hT : 0 ≤ T) (b : HilbertBasis ι ℂ E) :
    posTrace T = ∑' i, ENNReal.ofReal (‖CFC.sqrt T (b i)‖ ^ 2) := by
  conv_lhs => rw [← sqrt_mul_star_sqrt hT]
  exact posTrace_mul_star _ b

/-- The trace of a positive operator can be computed in any Hilbert basis. -/
theorem posTrace_eq_tsum (hT : 0 ≤ T) (b : HilbertBasis ι ℂ E) :
    posTrace T = ∑' i, ENNReal.ofReal (⟪b i, T (b i)⟫_ℂ).re := by
  simp only [posTrace_eq_tsum_norm_sqrt_sq hT b, re_inner_apply_eq_norm_sqrt_sq hT]

/-- Conjugation by an isometry preserves the trace of a positive operator. -/
theorem posTrace_conj_of_star_mul_self (hT : 0 ≤ T) {U : E →L[ℂ] E} (hU : star U * U = 1) :
    posTrace (U * T * star U) = posTrace T := by
  have hiso : ∀ x, ‖U x‖ = ‖x‖ := fun x => by
    have h := congrArg (fun A => ⟪x, A x⟫_ℂ) hU
    simp only [mul_def, comp_apply, star_eq_adjoint, adjoint_inner_right, one_def, coe_id', id_eq,
      inner_self_eq_norm_sq_to_K] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by exact_mod_cast h)
  have h : U * T * star U = (U * CFC.sqrt T) * star (U * CFC.sqrt T) := by
    rw [star_mul, (CFC.sqrt_nonneg T).isSelfAdjoint.star_eq]
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self T hT]
    simp only [mul_assoc]
  rw [h, posTrace_mul_star _ (posTraceBasis E), posTrace_eq_tsum_norm_sqrt_sq hT (posTraceBasis E)]
  simp only [mul_def, comp_apply, hiso]

theorem posTrace_add {S : E →L[ℂ] E} (hS : 0 ≤ S) (hT : 0 ≤ T) :
    posTrace (S + T) = posTrace S + posTrace T := by
  simp only [posTrace, add_apply, inner_add_right, Complex.add_re]
  rw [← ENNReal.tsum_add]
  congr! 2 with i
  exact ENNReal.ofReal_add (re_inner_apply_nonneg hS _) (re_inner_apply_nonneg hT _)

theorem posTrace_smul {r : ℝ} (hr : 0 ≤ r) (T : E →L[ℂ] E) :
    posTrace ((r : ℂ) • T) = ENNReal.ofReal r * posTrace T := by
  simp only [posTrace, smul_apply, inner_smul_right, Complex.re_ofReal_mul]
  rw [← ENNReal.tsum_mul_left]
  congr! 2 with i
  exact ENNReal.ofReal_mul hr

@[simp]
theorem posTrace_zero : posTrace (0 : E →L[ℂ] E) = 0 := by
  simp [posTrace]

/-- Only the zero operator has trace zero. -/
theorem posTrace_eq_zero_iff (hT : 0 ≤ T) : posTrace T = 0 ↔ T = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ posTrace_zero⟩
  set b := posTraceBasis E
  rw [posTrace_eq_tsum_norm_sqrt_sq hT b, ENNReal.tsum_eq_zero] at h
  have hb : ∀ i, CFC.sqrt T (b i) = 0 := fun i => by
    have := h i
    rw [ENNReal.ofReal_eq_zero] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
      (le_antisymm this (by positivity)))
  have h0 : CFC.sqrt T = 0 :=
    ContinuousLinearMap.ext_on (s := Set.range b)
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
      (by rintro _ ⟨i, rfl⟩; simp [hb i])
  rw [← sqrt_mul_star_sqrt hT, h0, zero_mul]

/-- `tr |x⟩⟨x| = ‖x‖²`. -/
theorem posTrace_rankOne_self (x : E) : posTrace (rankOne ℂ x x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  simp only [posTrace, rankOne_apply, inner_smul_right]
  rw [← (posTraceBasis E).tsum_ofReal_norm_inner_sq x]
  congr! 2 with i
  rw [← inner_conj_symm x, Complex.conj_mul']
  norm_cast

/-- A diagonal entry of a positive operator is at most its trace. -/
theorem ofReal_re_inner_le_posTrace (hT : 0 ≤ T) {x : E} (hx : ‖x‖ = 1) :
    ENNReal.ofReal (⟪x, T x⟫_ℂ).re ≤ posTrace T := by
  classical
  have hs : Orthonormal ℂ ((↑) : ({x} : Set E) → E) := by
    rw [orthonormal_subtype_iff_ite]
    rintro v rfl w rfl
    simp [inner_self_eq_norm_sq_to_K, hx]
  obtain ⟨w, b, hxw, hb⟩ := hs.exists_hilbertBasis_extension
  rw [posTrace_eq_tsum hT b]
  have hx' : x ∈ w := hxw rfl
  have hbx : b ⟨x, hx'⟩ = x := by simp [hb]
  calc ENNReal.ofReal (⟪x, T x⟫_ℂ).re = ENNReal.ofReal (⟪b ⟨x, hx'⟩, T (b ⟨x, hx'⟩)⟫_ℂ).re := by
        rw [hbx]
    _ ≤ _ := ENNReal.le_tsum (f := fun i => ENNReal.ofReal (⟪b i, T (b i)⟫_ℂ).re) ⟨x, hx'⟩

/-- The operator norm of a positive operator is at most its trace. -/
theorem norm_le_toReal_posTrace (hT : 0 ≤ T) (hfin : posTrace T ≠ ⊤) :
    ‖T‖ ≤ (posTrace T).toReal := by
  set c := (posTrace T).toReal
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hle : ∀ x : E, ‖CFC.sqrt T x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    set u := (‖x‖⁻¹ : ℂ) • x
    have hu : ‖u‖ = 1 := by
      simp [u, norm_smul, hx]
    have h1 := ofReal_re_inner_le_posTrace hT hu
    rw [← ENNReal.ofReal_toReal hfin, ENNReal.ofReal_le_ofReal_iff hc,
      re_inner_apply_eq_norm_sqrt_sq hT, map_smul, norm_smul] at h1
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm] at h1
    rw [mul_pow, inv_pow, inv_mul_le_iff₀ (by positivity)] at h1
    linarith
  have hsq : ‖CFC.sqrt T‖ ≤ √c := by
    refine opNorm_le_bound _ (Real.sqrt_nonneg c) fun x => ?_
    rw [← Real.sqrt_sq (norm_nonneg (CFC.sqrt T x)), ← Real.sqrt_sq (norm_nonneg x),
      ← Real.sqrt_mul hc]
    exact Real.sqrt_le_sqrt (hle x)
  calc ‖T‖ = ‖star (CFC.sqrt T) * CFC.sqrt T‖ := by
        rw [(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self T hT]
    _ = ‖CFC.sqrt T‖ ^ 2 := by rw [CStarRing.norm_star_mul_self, sq]
    _ ≤ √c ^ 2 := by gcongr
    _ = c := Real.sq_sqrt hc

/-- In finite dimension the trace of a positive operator is the usual trace. -/
theorem posTrace_eq_ofReal_re_trace [FiniteDimensional ℂ E] (hT : 0 ≤ T) :
    posTrace T = ENNReal.ofReal (LinearMap.trace ℂ E T).re := by
  set b := stdOrthonormalBasis ℂ E
  rw [posTrace_eq_tsum hT b.toHilbertBasis, LinearMap.trace_eq_sum_inner _ b, tsum_fintype,
    Complex.re_sum, ENNReal.ofReal_sum_of_nonneg fun i _ => ?_]
  · simp
  · exact re_inner_apply_nonneg hT (b i)

end ContinuousLinearMap
