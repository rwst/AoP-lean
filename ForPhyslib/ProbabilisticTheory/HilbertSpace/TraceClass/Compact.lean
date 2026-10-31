/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.GeneralIdeal

/-!
# Hilbert–Schmidt and trace-class operators are compact

A Hilbert–Schmidt operator `S` is the operator-norm limit of its truncations
`x ↦ ∑_{i ∈ F} ⟪eᵢ, x⟫ S eᵢ` to finite sets `F` of a Hilbert basis, since by Cauchy–Schwarz
`‖S - S_F‖² ≤ ∑_{i ∉ F} ‖S eᵢ‖²`. The truncations have finite rank, so `S` is compact. A
trace-class operator is `T = W |T|^{1/2} |T|^{1/2}` with `|T|^{1/2}` Hilbert–Schmidt, so it is
compact too.

## Main results

* `ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt.isCompactOperator`
* `ProbabilisticTheory.IsTraceClass.isCompactOperator`

## References

* B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS (2005), Thm 2.7(b).
-/

@[expose] public section

open scoped InnerProductSpace Topology
open Filter

namespace ProbabilisticTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HilbertSchmidt

omit [CompleteSpace H] in
/-- The truncation `x ↦ ⟪e, x⟫ v` of an operator to one basis vector is compact. -/
lemma isCompactOperator_innerSL_smulRight (e v : H) :
    IsCompactOperator ((innerSL ℂ e).smulRight v) :=
  (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ e)).clm_comp
    ((1 : ℂ →L[ℂ] ℂ).smulRight v)

/-- **The truncation estimate.** For a Hilbert–Schmidt operator `S`, a Hilbert basis `b` and a
finite set `F` of indices, `‖S - S_F‖ ≤ (∑_{i ∉ F} ‖S bᵢ‖²)^{1/2}`. -/
lemma norm_sub_sum_smulRight_le {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S) {w : Set H}
    (b : HilbertBasis w ℂ H) (F : Finset w) :
    ‖S - ∑ i ∈ F, (innerSL ℂ (b i)).smulRight (S (b i))‖ ≤
      √(∑' i, ‖S (b i)‖ ^ 2 - ∑ i ∈ F, ‖S (b i)‖ ^ 2) := by
  classical
  have hsum := summable_norm_sq_apply_of_hilbertBasis w b hS
  -- `g` is the tail of `‖S bᵢ‖` outside `F`.
  set g : w → ℝ := fun i => if i ∈ F then 0 else ‖S (b i)‖
  have hg : HasSum (fun i => g i ^ 2) (∑' i, ‖S (b i)‖ ^ 2 - ∑ i ∈ F, ‖S (b i)‖ ^ 2) := by
    convert hsum.hasSum.sub (hasSum_sum_of_ne_finset_zero (s := F)
      (f := fun i => if i ∈ F then ‖S (b i)‖ ^ 2 else 0) (by intro i hi; simp [hi])) using 1
    · funext i; by_cases hi : i ∈ F <;> simp [g, hi]
    · exact congrArg _ (Finset.sum_congr rfl fun i hi => by simp [hi])
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  set t : w → H := fun i => ⟪b i, x⟫_ℂ • S (b i)
  have ht : HasSum t (S x) := by
    simpa [t, b.repr_apply_apply] using (b.hasSum_repr x).mapL S
  have htail : HasSum (fun i => if i ∈ F then 0 else t i) (S x - ∑ i ∈ F, t i) := by
    convert ht.sub (hasSum_sum_of_ne_finset_zero (s := F)
      (f := fun i => if i ∈ F then t i else 0) (by intro i hi; simp [hi])) using 1
    · funext i; by_cases hi : i ∈ F <;> simp [hi]
    · exact congrArg _ (Finset.sum_congr rfl fun i hi => by simp [hi])
  have hx : HasSum (fun i : w => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := hasSum_norm_sq_inner_basis b x
  have hprod : Summable fun i => ‖⟪b i, x⟫_ℂ‖ * g i :=
    summable_norm_mul_of_square_sums _ _ hx.summable hg.summable (fun _ => norm_nonneg _)
      fun i => by by_cases hi : i ∈ F <;> simp [g, hi]
  have hle := htail.norm_le_of_bounded hprod.hasSum fun i => by
    by_cases hi : i ∈ F <;> simp [g, t, hi, norm_smul]
  calc ‖(S - ∑ i ∈ F, (innerSL ℂ (b i)).smulRight (S (b i))) x‖
      = ‖S x - ∑ i ∈ F, t i‖ := by simp [t]
    _ ≤ ∑' i, ‖⟪b i, x⟫_ℂ‖ * g i := hle
    _ ≤ √(∑' i, ‖⟪b i, x⟫_ℂ‖ ^ 2) * √(∑' i, g i ^ 2) :=
      tsum_mul_le_sqrt_mul_sqrt hx.summable hg.summable (fun _ => norm_nonneg _)
        fun i => by by_cases hi : i ∈ F <;> simp [g, hi]
    _ = _ := by
      rw [hx.tsum_eq, hg.tsum_eq, Real.sqrt_sq (norm_nonneg x), mul_comm]

/-- **Hilbert–Schmidt operators are compact.** -/
theorem IsHilbertSchmidt.isCompactOperator {S : H →L[ℂ] H} (hS : IsHilbertSchmidt S) :
    IsCompactOperator S := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  have hsum := summable_norm_sq_apply_of_hilbertBasis w b hS
  have htail : Tendsto (fun F : Finset w => √(∑' i, ‖S (b i)‖ ^ 2 - ∑ i ∈ F, ‖S (b i)‖ ^ 2))
      atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto _).comp
      ((tendsto_const_nhds (x := ∑' i, ‖S (b i)‖ ^ 2)).sub hsum.hasSum)
    simpa [Function.comp_def] using this
  refine isCompactOperator_of_tendsto (l := atTop) (F := fun F : Finset w =>
    ∑ i ∈ F, (innerSL ℂ (b i)).smulRight (S (b i))) ?_ (Eventually.of_forall fun F => ?_)
  · rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun F => (norm_sub_rev _ _).trans_le (norm_sub_sum_smulRight_le hS b F)) htail
  · refine Finset.sum_induction _ (fun T : H →L[ℂ] H => IsCompactOperator T)
      (fun A B hA hB => ?_) ?_ fun i _ => isCompactOperator_innerSL_smulRight _ _
    · exact hA.add hB
    · exact isCompactOperator_zero

end HilbertSchmidt

open HilbertSchmidt Polar in
/-- **Trace-class operators are compact.** -/
theorem IsTraceClass.isCompactOperator {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsCompactOperator T := by
  have hS := (isHilbertSchmidt_sqrt_abs_of_isTraceClass hT).isCompactOperator
  have hT' : T = (polarFactor T * CFC.sqrt (CFC.abs T)) * CFC.sqrt (CFC.abs T) := by
    rw [mul_assoc, CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg T)]
    exact (polarFactor_mul_absOperator T).symm
  rw [hT']
  exact hS.clm_comp (polarFactor T * CFC.sqrt (CFC.abs T))

end ProbabilisticTheory
