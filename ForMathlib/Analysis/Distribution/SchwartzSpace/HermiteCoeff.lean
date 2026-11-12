/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.Hermite

/-!
# Hermite coefficients of Schwartz functions decay rapidly

For a Schwartz function `f` on `ℝ^ι`, the weighted suprema
`‖f‖_K = sup_α (1 + |α|)^K |c_α(f)|` of its Hermite coefficients are finite, and bounded by
finitely many Schwartz seminorms. Conversely (in `HermiteSeminorm.lean`), every Schwartz seminorm
is bounded by one of these weighted suprema.

The weighted suprema behave well under the coordinate operators: by the ladder relations,
`‖xᵢ g‖_K` and `‖∂ᵢ g‖_K` are bounded by `2^(K+2) ‖g‖_{K+1}`. The operator
`N = ∑ᵢ (xᵢ + ∂ᵢ)(xᵢ - ∂ᵢ) + 2` multiplies `c_α` by `2 (|α| + 1 + dim)`, so
`(1 + |α|)^K |c_α(f)| ≤ |c_α(N^K f)| ≤ ‖N^K f‖_{L²}`, and `N^K` is continuous.

## Main definitions

* `SchwartzMap.hermiteWeight α = 1 + |α|`;
* `SchwartzMap.hermiteNorm K f = sup_α (1 + |α|)^K |c_α(f)|`, in `ℝ≥0∞`.

## Main results

* `SchwartzMap.hermiteNorm_coordMulCLM_le`, `SchwartzMap.hermiteNorm_coordDerivCLM_le`: the
  shift bounds;
* `SchwartzMap.exists_hermiteNorm_le_seminorm`: `‖f‖_K` is bounded by Schwartz seminorms.
-/

open MeasureTheory Finset
open scoped SchwartzMap LineDeriv InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace SchwartzMap

variable {ι : Type*} [Fintype ι]

/-- The weight `1 + |α|` of a multi-index. -/
def hermiteWeight (α : ι → ℕ) : ℕ := ∑ i, α i + 1

lemma one_le_hermiteWeight (α : ι → ℕ) : 1 ≤ hermiteWeight α := by
  simp [hermiteWeight]

lemma coord_add_one_le_hermiteWeight (α : ι → ℕ) (i : ι) : α i + 1 ≤ hermiteWeight α := by
  have := Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _) (mem_univ i)
  simp only [hermiteWeight]
  omega

lemma hermiteWeight_update [DecidableEq ι] (α : ι → ℕ) (i : ι) (k : ℕ) :
    hermiteWeight (Function.update α i k) + α i = hermiteWeight α + k := by
  simp only [hermiteWeight, Finset.sum_update_of_mem (mem_univ i)]
  rw [← Finset.add_sum_erase _ _ (mem_univ i), Finset.sdiff_singleton_eq_erase]
  omega

/-- The weighted supremum `sup_α (1 + |α|)^K |c_α(f)|` of the Hermite coefficients. -/
def hermiteNorm (K : ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) : ℝ≥0∞ :=
  ⨆ α, (hermiteWeight α : ℝ≥0∞) ^ K * ‖hermiteCoeff α f‖ₑ

lemma le_hermiteNorm (K : ℕ) (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    (hermiteWeight α : ℝ≥0∞) ^ K * ‖hermiteCoeff α f‖ₑ ≤ hermiteNorm K f :=
  le_iSup (fun α => (hermiteWeight α : ℝ≥0∞) ^ K * ‖hermiteCoeff α f‖ₑ) α

lemma hermiteNorm_mono {K L : ℕ} (h : K ≤ L) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteNorm K f ≤ hermiteNorm L f :=
  iSup_mono fun α => by
    gcongr
    · exact_mod_cast one_le_hermiteWeight α

lemma enorm_hermiteCoeff_le (K : ℕ) (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ‖hermiteCoeff α f‖ₑ ≤ hermiteNorm K f := by
  refine le_trans ?_ (le_hermiteNorm K α f)
  conv_lhs => rw [← one_mul ‖hermiteCoeff α f‖ₑ]
  gcongr
  exact one_le_pow₀ (by exact_mod_cast one_le_hermiteWeight α)

/-! ### Shift bounds -/

lemma enorm_sqrt_le {r : ℝ} {k : ℕ} (h : √r ≤ k) : ‖((√r : ℝ) : ℂ)‖ₑ ≤ (k : ℝ≥0∞) := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg r),
    ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal h

lemma sqrt_le_of_le {r : ℝ} {k : ℕ} (hr : r ≤ k) (hk : 1 ≤ k) : √r ≤ k := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, hr.trans ?_⟩
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

/-- The common estimate behind the shift bounds: a combination of the two neighbouring
coefficients with the ladder factors. -/
lemma mul_enorm_le_of_ladder [DecidableEq ι] (K : ℕ) (β : ι → ℕ) (i : ι)
    (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) (z : ℂ)
    (hz : ‖z‖ₑ ≤ ‖((√(((β i : ℝ) + 1) / 2) : ℝ) : ℂ)‖ₑ *
        ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ +
      ‖((√((β i : ℝ) / 2) : ℝ) : ℂ)‖ₑ * ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ) :
    (hermiteWeight β : ℝ≥0∞) ^ K * ‖z‖ₑ ≤ 2 ^ (K + 2) * hermiteNorm (K + 1) g := by
  set w := (hermiteWeight β : ℝ≥0∞)
  have hw1 : 1 ≤ hermiteWeight β := one_le_hermiteWeight β
  have hwi := coord_add_one_le_hermiteWeight β i
  -- the factor of the raised coefficient
  have hplus : w ^ K * (‖((√(((β i : ℝ) + 1) / 2) : ℝ) : ℂ)‖ₑ *
      ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ) ≤ 2 ^ (K + 1) * hermiteNorm (K + 1) g := by
    have ha : ‖((√(((β i : ℝ) + 1) / 2) : ℝ) : ℂ)‖ₑ ≤ w := by
      refine enorm_sqrt_le (sqrt_le_of_le ?_ hw1)
      have : ((β i : ℝ) + 1) ≤ hermiteWeight β := by exact_mod_cast hwi
      linarith
    have hup := hermiteWeight_update β i (β i + 1)
    have hww : w ≤ 2 * (hermiteWeight (Function.update β i (β i + 1)) : ℝ≥0∞) := by
      have : hermiteWeight β ≤ 2 * hermiteWeight (Function.update β i (β i + 1)) := by omega
      have h2 := (Nat.cast_le (α := ℝ≥0∞)).2 this
      push_cast at h2
      exact h2
    calc w ^ K * (‖((√(((β i : ℝ) + 1) / 2) : ℝ) : ℂ)‖ₑ *
          ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ)
        ≤ w ^ K * (w * ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ) := by gcongr
      _ = w ^ (K + 1) * ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ := by ring
      _ ≤ (2 * (hermiteWeight (Function.update β i (β i + 1)) : ℝ≥0∞)) ^ (K + 1) *
          ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ := by gcongr
      _ = 2 ^ (K + 1) * ((hermiteWeight (Function.update β i (β i + 1)) : ℝ≥0∞) ^ (K + 1) *
          ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ) := by ring
      _ ≤ 2 ^ (K + 1) * hermiteNorm (K + 1) g := by gcongr; exact le_hermiteNorm _ _ _
  -- the factor of the lowered coefficient
  have hminus : w ^ K * (‖((√((β i : ℝ) / 2) : ℝ) : ℂ)‖ₑ *
      ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ) ≤ 2 ^ (K + 1) * hermiteNorm (K + 1) g := by
    rcases Nat.eq_zero_or_pos (β i) with h0 | hpos
    · simp [h0]
    have hb : ‖((√((β i : ℝ) / 2) : ℝ) : ℂ)‖ₑ ≤ w := by
      refine enorm_sqrt_le (sqrt_le_of_le ?_ hw1)
      have : ((β i : ℝ) + 1) ≤ hermiteWeight β := by exact_mod_cast hwi
      have : (0 : ℝ) ≤ β i := by positivity
      linarith
    have hup := hermiteWeight_update β i (β i - 1)
    have hww : w ≤ 2 * (hermiteWeight (Function.update β i (β i - 1)) : ℝ≥0∞) := by
      have := one_le_hermiteWeight (Function.update β i (β i - 1))
      have : hermiteWeight β ≤ 2 * hermiteWeight (Function.update β i (β i - 1)) := by omega
      have h2 := (Nat.cast_le (α := ℝ≥0∞)).2 this
      push_cast at h2
      exact h2
    calc w ^ K * (‖((√((β i : ℝ) / 2) : ℝ) : ℂ)‖ₑ *
          ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ)
        ≤ w ^ K * (w * ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ) := by gcongr
      _ = w ^ (K + 1) * ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ := by ring
      _ ≤ (2 * (hermiteWeight (Function.update β i (β i - 1)) : ℝ≥0∞)) ^ (K + 1) *
          ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ := by gcongr
      _ = 2 ^ (K + 1) * ((hermiteWeight (Function.update β i (β i - 1)) : ℝ≥0∞) ^ (K + 1) *
          ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ) := by ring
      _ ≤ 2 ^ (K + 1) * hermiteNorm (K + 1) g := by gcongr; exact le_hermiteNorm _ _ _
  calc w ^ K * ‖z‖ₑ ≤ w ^ K * (‖((√(((β i : ℝ) + 1) / 2) : ℝ) : ℂ)‖ₑ *
          ‖hermiteCoeff (Function.update β i (β i + 1)) g‖ₑ +
        ‖((√((β i : ℝ) / 2) : ℝ) : ℂ)‖ₑ * ‖hermiteCoeff (Function.update β i (β i - 1)) g‖ₑ) := by
        gcongr
    _ ≤ 2 ^ (K + 1) * hermiteNorm (K + 1) g + 2 ^ (K + 1) * hermiteNorm (K + 1) g := by
        rw [mul_add]
        exact add_le_add hplus hminus
    _ = 2 ^ (K + 2) * hermiteNorm (K + 1) g := by ring

/-- Shift bound for multiplication by a coordinate. -/
theorem hermiteNorm_coordMulCLM_le [DecidableEq ι] (K : ℕ) (i : ι)
    (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteNorm K (coordMulCLM i g) ≤ 2 ^ (K + 2) * hermiteNorm (K + 1) g :=
  iSup_le fun β => mul_enorm_le_of_ladder K β i g _ (by
    rw [hermiteCoeff_coordMulCLM, ← enorm_mul, ← enorm_mul]
    exact enorm_add_le _ _)

/-- Shift bound for a partial derivative. -/
theorem hermiteNorm_coordDerivCLM_le [DecidableEq ι] (K : ℕ) (i : ι)
    (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteNorm K (coordDerivCLM i g) ≤ 2 ^ (K + 2) * hermiteNorm (K + 1) g :=
  iSup_le fun β => mul_enorm_le_of_ladder K β i g _ (by
    rw [hermiteCoeff_coordDerivCLM, ← enorm_mul, ← enorm_mul]
    exact enorm_sub_le)

/-! ### The number operator -/

lemma hermiteCoeff_add_coord [DecidableEq ι] (α : ι → ℕ) (i : ι)
    (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α ((coordMulCLM i + coordDerivCLM i) g) =
      2 * (√(((α i : ℝ) + 1) / 2) : ℂ) * hermiteCoeff (Function.update α i (α i + 1)) g := by
  rw [_root_.add_apply, map_add, hermiteCoeff_coordMulCLM,
    hermiteCoeff_coordDerivCLM]
  ring

lemma hermiteCoeff_sub_coord [DecidableEq ι] (α : ι → ℕ) (i : ι)
    (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α ((coordMulCLM i - coordDerivCLM i) g) =
      2 * (√((α i : ℝ) / 2) : ℂ) * hermiteCoeff (Function.update α i (α i - 1)) g := by
  rw [_root_.sub_apply, map_sub, hermiteCoeff_coordMulCLM,
    hermiteCoeff_coordDerivCLM]
  ring

/-- The operator `(xᵢ + ∂ᵢ)(xᵢ - ∂ᵢ)`, twice the `i`-th mode number plus `2`. -/
def ladderCLM [DecidableEq ι] (i : ι) : 𝓢(EuclideanSpace ℝ ι, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
  (coordMulCLM i + coordDerivCLM i).comp (coordMulCLM i - coordDerivCLM i)

lemma hermiteCoeff_ladderCLM [DecidableEq ι] (α : ι → ℕ) (i : ι)
    (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α (ladderCLM i f) = 2 * ((α i : ℂ) + 1) * hermiteCoeff α f := by
  rw [ladderCLM, ContinuousLinearMap.comp_apply, hermiteCoeff_add_coord, hermiteCoeff_sub_coord]
  simp only [Function.update_self, Nat.add_sub_cancel, Function.update_idem,
    Function.update_eq_self]
  have h : (√(((α i : ℝ) + 1) / 2) : ℂ) * (√(((α i + 1 : ℕ) : ℝ) / 2) : ℂ) =
      ((α i : ℂ) + 1) / 2 := by
    have e : ((α i + 1 : ℕ) : ℝ) = (α i : ℝ) + 1 := by push_cast; ring
    rw [e, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  linear_combination 4 * hermiteCoeff α f * h

/-- The number operator `∑ᵢ (xᵢ + ∂ᵢ)(xᵢ - ∂ᵢ) + 2`. -/
def numberCLM [DecidableEq ι] : 𝓢(EuclideanSpace ℝ ι, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ ι, ℂ) :=
  ∑ i, ladderCLM i + (2 : ℂ) • ContinuousLinearMap.id ℂ _

lemma hermiteCoeff_numberCLM [DecidableEq ι] (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α (numberCLM f) =
      2 * ((hermiteWeight α : ℂ) + Fintype.card ι) * hermiteCoeff α f := by
  rw [numberCLM, _root_.add_apply, _root_.sum_apply, map_add, map_sum]
  simp only [hermiteCoeff_ladderCLM, _root_.smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul, hermiteWeight]
  rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
  push_cast
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring

lemma hermiteCoeff_numberCLM_iterate [DecidableEq ι] (K : ℕ) (α : ι → ℕ)
    (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteCoeff α (numberCLM^[K] f) =
      (2 * ((hermiteWeight α : ℂ) + Fintype.card ι)) ^ K * hermiteCoeff α f := by
  induction K with
  | zero => simp
  | succ K ih => rw [Function.iterate_succ_apply', hermiteCoeff_numberCLM, ih]; ring

/-- Bessel's inequality for a single coefficient. -/
lemma enorm_hermiteCoeff_le_toLp (α : ι → ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ‖hermiteCoeff α f‖ₑ ≤ ‖f.toLp 2‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, hermiteCoeff_apply]
  refine ENNReal.ofReal_le_ofReal ((norm_inner_le_norm _ _).trans ?_)
  rw [hermitePiBasis.orthonormal.1 α, one_mul]

lemma hermiteNorm_le_toLp_numberCLM [DecidableEq ι] (K : ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteNorm K f ≤ ‖(numberCLM^[K] f).toLp 2‖ₑ := by
  refine iSup_le fun α => le_trans ?_ (enorm_hermiteCoeff_le_toLp α _)
  rw [hermiteCoeff_numberCLM_iterate, enorm_mul, enorm_pow]
  gcongr
  have h : (2 * ((hermiteWeight α : ℂ) + Fintype.card ι)) =
      ((2 * (hermiteWeight α + Fintype.card ι) : ℕ) : ℂ) := by push_cast; ring
  rw [h, ← ofReal_norm, Complex.norm_natCast, ENNReal.ofReal_natCast]
  exact_mod_cast (show hermiteWeight α ≤ 2 * (hermiteWeight α + Fintype.card ι) by omega)

/-- The weighted suprema of the Hermite coefficients are bounded by Schwartz seminorms. -/
theorem exists_hermiteNorm_le_seminorm (K : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ≥0), ∀ f : 𝓢(EuclideanSpace ℝ ι, ℂ),
      hermiteNorm K f ≤
        C * ENNReal.ofReal (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ ι) ℂ) f) := by
  classical
  set T := (toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))).comp (numberCLM ^ K)
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ _ ℂ)
    ((normSeminorm ℂ _).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  refine ⟨s, C, fun f => (hermiteNorm_le_toLp_numberCLM K f).trans ?_⟩
  have h := hC f
  simp only [Seminorm.comp_apply, coe_normSeminorm, FunLike.coe_smul, Pi.smul_apply,
    NNReal.smul_def, smul_eq_mul] at h
  have key : ∀ (L : ℕ) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)), (numberCLM ^ L) g = numberCLM^[L] g := by
    intro L
    induction L with
    | zero => intro g; rfl
    | succ L ih =>
      intro g
      rw [pow_succ', mul_apply_eq_comp, ih, Function.iterate_succ_apply']
  have hT : T f = (numberCLM^[K] f).toLp 2 := by
    simp [T, key]
  rw [← hT, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal h

lemma hermiteNorm_ne_top (K : ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) : hermiteNorm K f ≠ ⊤ := by
  obtain ⟨s, C, h⟩ := exists_hermiteNorm_le_seminorm (ι := ι) K
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (h f)

end SchwartzMap
