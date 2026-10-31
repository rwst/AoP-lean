/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.Spectrum
public import ForPhyslib.ProbabilisticTheory.HilbertSpace.TraceClass.Compact
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Banach
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.RankOne

/-!
# Canonical expansion of a positive trace-class operator

A positive trace-class operator `T` is compact, so it has a Hilbert basis `(bᵢ)` of eigenvectors,
`T bᵢ = μᵢ bᵢ` with `μᵢ ≥ 0`. The eigenvalues sum to the trace, and
`T = ∑ᵢ μᵢ |bᵢ⟩⟨bᵢ|` with the series converging in the trace norm. The tail after a finite set `F`
of indices has trace norm at most `∑_{i ∉ F} μᵢ`.

## Main results

* `ProbabilisticTheory.IsTraceClass.exists_hasSum_rankOne`: the canonical expansion.
* `ProbabilisticTheory.TraceClass.norm_sub_sum_le_of_hasSum`: the tail estimate.

## References

* B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS (2005), Thm 1.4 and Thm 3.1.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer (2012), Cor A.9.
-/

@[expose] public section

open scoped InnerProductSpace ComplexOrder
open InnerProductSpace

namespace ProbabilisticTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

/-- The inclusion of the trace class into the bounded operators, a contraction since the operator
norm is at most the trace norm. -/
noncomputable def toOperator : TraceClass H →L[ℂ] H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun T => T.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    fun T => by
      simp only [one_mul, norm_eq_traceNorm]
      exact opNorm_le_traceNorm (isTraceClass_coe T)

@[simp] lemma toOperator_apply (T : TraceClass H) : toOperator T = T.1 := rfl

/-- Removing finitely many terms from a sum. -/
lemma hasSum_ite_not_mem {ι M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DecidableEq ι] {f : ι → M} {s : M} (hf : HasSum f s)
    (F : Finset ι) : HasSum (fun i => if i ∈ F then 0 else f i) (s - ∑ i ∈ F, f i) := by
  convert hf.sub (hasSum_sum_of_ne_finset_zero (s := F) (f := fun i => if i ∈ F then f i else 0)
    (by intro i hi; simp [hi])) using 1
  · funext i; by_cases hi : i ∈ F <;> simp [hi]
  · exact congrArg _ (Finset.sum_congr rfl fun i hi => by simp [hi])

/-- **Tail estimate.** If `∑ᵢ aᵢ = A` in a normed group and `‖aᵢ‖ ≤ μᵢ` with `∑ᵢ μᵢ = m`, then
`‖A - ∑_{i ∈ F} aᵢ‖ ≤ m - ∑_{i ∈ F} μᵢ`. -/
lemma norm_sub_sum_le_of_hasSum {ι G : Type*} [NormedAddCommGroup G] {a : ι → G} {A : G}
    {μ : ι → ℝ} {m : ℝ} (ha : HasSum a A) (hμ : HasSum μ m) (hle : ∀ i, ‖a i‖ ≤ μ i)
    (F : Finset ι) : ‖A - ∑ i ∈ F, a i‖ ≤ m - ∑ i ∈ F, μ i := by
  classical
  exact (hasSum_ite_not_mem ha F).norm_le_of_bounded (hasSum_ite_not_mem hμ F) fun i => by
    by_cases hi : i ∈ F
    · simp [hi]
    · simp [hi, hle i]

end TraceClass

open TraceClass in
/-- **Canonical expansion of a positive trace-class operator.** There is a Hilbert basis `(bᵢ)` of
eigenvectors, `T bᵢ = μᵢ bᵢ` with `μᵢ ≥ 0`, such that `∑ᵢ μᵢ = ‖T‖₁ = tr T` and
`T = ∑ᵢ μᵢ |bᵢ⟩⟨bᵢ|` in the trace norm. -/
theorem IsTraceClass.exists_hasSum_rankOne {T : H →L[ℂ] H} (hT : IsTraceClass T) (h0 : 0 ≤ T) :
    ∃ (w : Set H) (b : HilbertBasis w ℂ H) (μ : w → ℝ), ⇑b = ((↑) : w → H) ∧
      (∀ i, T (b i) = (μ i : ℂ) • b i) ∧ (∀ i, 0 ≤ μ i) ∧ HasSum μ (traceNorm T hT) ∧
      HasSum (fun i => (μ i : ℂ)) (trace T hT) ∧
      HasSum (fun i => ofOperator ((μ i : ℂ) • rankOne ℂ (b i) (b i))
        (isTraceClass_smul _ (isTraceClass_rankOne_self _))) (ofOperator T hT) := by
  have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp h0
  obtain ⟨w, b, hb, heig⟩ :=
    ContinuousLinearMap.exists_hilbertBasis_eigenvectors hT.isCompactOperator hpos.isSymmetric
  set μ : w → ℝ := fun i => (⟪b i, T (b i)⟫_ℂ).re
  have hnorm : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hμ : ∀ i, T (b i) = (μ i : ℂ) • b i := fun i => by
    obtain ⟨c, hc⟩ := heig (b i) (by simp [hb])
    have hc' : ⟪b i, T (b i)⟫_ℂ = c := by
      rw [hc, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]; simp
    have him : c.im = 0 := by
      rw [← hc']; exact (Complex.nonneg_iff.1 (hpos.inner_nonneg_right (b i))).2.symm
    rw [hc, show (μ i : ℂ) = c by simp [μ, hc', Complex.ext_iff, him]]
  have hμ0 : ∀ i, 0 ≤ μ i := fun i => hpos.re_inner_nonneg_right (b i)
  have hsum : Summable μ := by
    simpa [CFC.abs_of_nonneg T h0] using isTraceClass_iff.mp hT w b
  have hnormSum : HasSum μ (traceNorm T hT) := by
    rw [traceNorm_eq_of_hilbertBasis hT b]
    simpa [CFC.abs_of_nonneg T h0] using hsum.hasSum
  have htrace : HasSum (fun i => (μ i : ℂ)) (trace T hT) := by
    rw [trace_eq_of_hilbertBasis_of_nonneg h0 hT b]
    convert (Complex.hasSum_ofReal.mpr hsum.hasSum) using 1
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun i => by rw [hμ i, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]; simp
  refine ⟨w, b, μ, hb, hμ, hμ0, hnormSum, htrace, ?_⟩
  -- The series is absolutely summable in the Banach space `𝒮₁(H)`.
  set a : w → TraceClass H := fun i => ofOperator ((μ i : ℂ) • rankOne ℂ (b i) (b i))
    (isTraceClass_smul _ (isTraceClass_rankOne_self _))
  have ha : ∀ i, ‖a i‖ = μ i := fun i => by
    rw [norm_eq_traceNorm]
    simp only [a, ofOperator_coe]
    rw [traceNorm_smul _ (isTraceClass_rankOne_self _), traceNorm_rankOne_self, hnorm]
    simp [abs_of_nonneg (hμ0 i)]
  obtain ⟨S, hS⟩ : Summable a := .of_norm (by simpa [ha] using hsum)
  -- Its sum agrees with `T` on the basis, hence everywhere.
  have hSb : ∀ j, S.1 (b j) = T (b j) := fun j => by
    classical
    have h := (hS.mapL toOperator).mapL (ContinuousLinearMap.apply ℂ H (b j))
    have hterm : ∀ i, (ContinuousLinearMap.apply ℂ H (b j)) (toOperator (a i)) =
        if i = j then (μ j : ℂ) • b j else 0 := fun i => by
      by_cases hij : i = j
      · subst hij; simp [a, rankOne_apply, inner_self_eq_norm_sq_to_K, hnorm]
      · simp [a, rankOne_apply, hij, orthonormal_iff_ite.mp b.orthonormal i j]
    simp only [hterm] at h
    rw [hμ j]
    simpa using h.unique (hasSum_ite_eq j _)
  have hST : S.1 = T := ContinuousLinearMap.ext fun x =>
    ((b.hasSum_repr x).mapL S.1).unique (by simpa [hSb] using (b.hasSum_repr x).mapL T)
  rwa [show S = ofOperator T hT from Subtype.ext hST] at hS

end ProbabilisticTheory
