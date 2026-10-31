/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.ProbabilisticTheory.HilbertSpace.TraceClass.CanonicalExpansion
public import ForPhyslib.QuantumMechanics.DensityOperator
public import ForPhyslib.QuantumMechanics.Wigner.Kadison
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The trace norm on density operators

## i. Overview

Three facts about the trace norm `‖·‖₁` that hold in any dimension.

* **Affine maps contract.** A map `Φ` that sends density operators to density operators and
  preserves their convex combinations satisfies `‖Φ ρ - Φ σ‖₁ ≤ ‖ρ - σ‖₁`. Write
  `ρ - σ = A⁺ - A⁻` with `tr A⁺ = tr A⁻ = t`, so that `‖ρ - σ‖₁ = 2t`. For `t > 0` the operators
  `ρ' = A⁺ / t` and `σ' = A⁻ / t` are density operators with `ρ + t σ' = σ + t ρ'`; dividing by
  `1 + t` turns this into an equality of two convex combinations, so
  `Φ ρ - Φ σ = t (Φ ρ' - Φ σ')`, which has trace norm at most `2t`.
* **Conjugation is continuous.** If `t ↦ U t` is strongly continuous with `‖U t‖ ≤ 1`, then
  `t ↦ U t ρ (U t)†` is continuous in the trace norm for every positive trace-class `ρ`. The
  canonical expansion `ρ = ∑ᵢ μᵢ |bᵢ⟩⟨bᵢ|` reduces this to rank-one operators, and
  `‖|x⟩⟨x| - |y⟩⟨y|‖₁ ≤ (‖x‖ + ‖y‖) ‖x - y‖`.
* **Pure states are closed.** In the trace norm, the pure states are the positive operators of
  trace norm one that are idempotent; each condition is closed.

## ii. Key results

- `QuantumMechanics.traceNorm_eq_toReal_posTrace_abs`, `traceNorm_of_nonneg`,
  `traceNorm_eq_posPart_add_negPart`: the trace norm through the trace in `[0, ∞]`.
- `QuantumMechanics.AffineOnDensityOperators.traceNorm_sub_le`: affine maps contract.
- `QuantumMechanics.traceNorm_rankOne_le`, `traceNorm_proj_sub_proj_le`: rank-one bounds.
- `QuantumMechanics.continuous_conj`: conjugation by a strongly continuous family of contractions.
- `QuantumMechanics.isClosed_setOf_isPure`: the pure states are closed in `𝒮₁(E)`;
  `isPure_of_tendsto_traceENorm`: a trace-norm limit of pure states is pure.
- `QuantumMechanics.traceENorm`: the trace norm `tr |T| ∈ [0, ∞]` of any operator.

## iii. Table of contents

- A. The trace norm through the trace in `[0, ∞]`
- B. Affine maps contract the trace norm
- C. Rank-one operators
- D. Continuity of conjugation
- E. The pure states are closed
- F. The trace norm in `[0, ∞]`

## iv. References

- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton (1976), Lemma 5.3.
- B. Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS (2005), Thm 3.1.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder
open Filter Topology InnerProductSpace ProbabilisticTheory ProbabilisticTheory.TraceClass
  QuantumMechanics.Wigner
open ContinuousLinearMap (posTrace posTraceBasis re_inner_apply_nonneg posTrace_add posTrace_smul
  posTrace_eq_zero_iff)

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. The trace norm through the trace in `[0, ∞]` -/

/-- The trace norm does not depend on the trace-class witness, even across an equality. -/
lemma traceNorm_eq_of_eq {X Y : E →L[ℂ] E} (h : X = Y) (hX : IsTraceClass X)
    (hY : IsTraceClass Y) : traceNorm X hX = traceNorm Y hY := by
  subst h; rfl

/-- `‖T‖₁ = tr |T|`. -/
theorem traceNorm_eq_toReal_posTrace_abs {T : E →L[ℂ] E} (h : IsTraceClass T) :
    traceNorm T h = (posTrace (CFC.abs T)).toReal := by
  have h0 : ∀ i, 0 ≤ (⟪posTraceBasis E i, CFC.abs T (posTraceBasis E i)⟫_ℂ).re := fun _ =>
    re_inner_apply_nonneg (CFC.abs_nonneg T) _
  rw [traceNorm_eq_of_hilbertBasis h (posTraceBasis E), posTrace,
    ← ENNReal.ofReal_tsum_of_nonneg h0 (isTraceClass_iff.mp h _ _),
    ENNReal.toReal_ofReal (tsum_nonneg h0)]

/-- For a positive operator, `‖T‖₁ = tr T`. -/
theorem traceNorm_of_nonneg {T : E →L[ℂ] E} (hT : 0 ≤ T) (h : IsTraceClass T) :
    traceNorm T h = (posTrace T).toReal := by
  rw [traceNorm_eq_toReal_posTrace_abs, CFC.abs_of_nonneg T hT]

lemma IsDensityOperator.traceNorm_eq_one {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    traceNorm ρ hρ.isTraceClass = 1 := by
  rw [traceNorm_of_nonneg hρ.nonneg, hρ.posTrace_eq_one, ENNReal.toReal_one]

lemma IsDensityOperator.norm_ofOperator {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    ‖ofOperator ρ hρ.isTraceClass‖ = 1 :=
  hρ.traceNorm_eq_one

lemma posTrace_ne_top {T : E →L[ℂ] E} (hT : 0 ≤ T) (h : IsTraceClass T) : posTrace T ≠ ⊤ :=
  (isTraceClass_iff_posTrace_ne_top hT).mp h

/-- For a self-adjoint operator, `‖T‖₁ = tr T⁺ + tr T⁻`. -/
theorem traceNorm_eq_posPart_add_negPart {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    (h : IsTraceClass T) :
    traceNorm T h = (posTrace T⁺).toReal + (posTrace T⁻).toReal := by
  rw [traceNorm_eq_toReal_posTrace_abs, ← CFC.posPart_add_negPart T hT,
    posTrace_add (CFC.posPart_nonneg T) (CFC.negPart_nonneg T),
    ENNReal.toReal_add (posTrace_ne_top (CFC.posPart_nonneg T)
      (isTraceClass_posPart_of_isSelfAdjoint hT h))
    (posTrace_ne_top (CFC.negPart_nonneg T) (isTraceClass_negPart_of_isSelfAdjoint hT h))]

/-! ## B. Affine maps contract the trace norm -/

/-- A map on operators is affine on density operators if it preserves the convex combinations
`t ρ + (1 - t) σ` of two density operators. -/
def AffineOnDensityOperators (Φ : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  ∀ ρ σ, IsDensityOperator ρ → IsDensityOperator σ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    Φ ((t : ℂ) • ρ + ((1 - t : ℝ) : ℂ) • σ) = (t : ℂ) • Φ ρ + ((1 - t : ℝ) : ℂ) • Φ σ

/-- `P / tr P` is a density operator for a positive operator of finite nonzero trace. -/
lemma isDensityOperator_inv_smul {P : E →L[ℂ] E} (hP : 0 ≤ P) {t : ℝ} (ht : 0 < t)
    (htr : posTrace P = ENNReal.ofReal t) : IsDensityOperator (((t⁻¹ : ℝ) : ℂ) • P) := by
  refine isDensityOperator_iff.mpr ⟨?_, ?_⟩
  · rw [Complex.coe_smul]; exact smul_nonneg (inv_nonneg.mpr ht.le) hP
  rw [posTrace_smul (inv_nonneg.mpr ht.le), htr, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le),
    inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one]

/-- **Affine maps contract the trace norm** (Simon 1976, Lemma 5.3): a map that sends density
operators to density operators and preserves their convex combinations satisfies
`‖Φ ρ - Φ σ‖₁ ≤ ‖ρ - σ‖₁`. -/
theorem AffineOnDensityOperators.traceNorm_sub_le {Φ : (E →L[ℂ] E) → E →L[ℂ] E}
    (hA : AffineOnDensityOperators Φ) (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (Φ ρ))
    {ρ σ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ)
    (h₁ : IsTraceClass (Φ ρ - Φ σ)) (h₂ : IsTraceClass (ρ - σ)) :
    traceNorm (Φ ρ - Φ σ) h₁ ≤ traceNorm (ρ - σ) h₂ := by
  set A := ρ - σ
  have hsa : IsSelfAdjoint A := hρ.isSelfAdjoint.sub hσ.isSelfAdjoint
  set P := A⁺
  set N := A⁻
  have hP0 : 0 ≤ P := CFC.posPart_nonneg A
  have hN0 : 0 ≤ N := CFC.negPart_nonneg A
  have hPf := posTrace_ne_top hP0 (isTraceClass_posPart_of_isSelfAdjoint hsa h₂)
  have hNf := posTrace_ne_top hN0 (isTraceClass_negPart_of_isSelfAdjoint hsa h₂)
  -- `ρ + A⁻ = σ + A⁺`, so `tr A⁺ = tr A⁻`.
  have hsplit : ρ + N = σ + P := by
    have h : ρ - σ = P - N := (CFC.posPart_sub_negPart A hsa).symm
    rw [sub_eq_sub_iff_add_eq_add] at h
    rw [h, add_comm]
  have hPN : posTrace P = posTrace N := by
    have h := congrArg posTrace hsplit
    rw [posTrace_add hρ.nonneg hN0, posTrace_add hσ.nonneg hP0, hρ.posTrace_eq_one,
      hσ.posTrace_eq_one] at h
    exact ((ENNReal.add_right_inj ENNReal.one_ne_top).mp h).symm
  set t := (posTrace P).toReal
  have hnorm : traceNorm A h₂ = 2 * t := by
    rw [traceNorm_eq_posPart_add_negPart hsa, ← hPN]; ring
  rw [hnorm]
  rcases (ENNReal.toReal_nonneg (a := posTrace P)).eq_or_lt with ht | ht
  · -- `t = 0`: then `A⁺ = A⁻ = 0` and `ρ = σ`.
    have hP : P = 0 := (posTrace_eq_zero_iff hP0).mp
      ((ENNReal.toReal_eq_zero_iff _).mp ht.symm |>.resolve_right hPf)
    have hN : N = 0 := (posTrace_eq_zero_iff hN0).mp (by rw [← hPN, (posTrace_eq_zero_iff hP0).2 hP])
    have hρσ : ρ = σ := by simpa [hP, hN] using hsplit
    rw [show t = 0 from ht.symm, mul_zero, traceNorm_eq_of_eq (by rw [hρσ, sub_self]) h₁ isTraceClass_zero,
      traceNorm_zero]
  -- `t > 0`: normalize `A⁺` and `A⁻`.
  have htP : posTrace P = ENNReal.ofReal t := (ENNReal.ofReal_toReal hPf).symm
  set ρ' := (((t⁻¹ : ℝ) : ℂ)) • P
  set σ' := (((t⁻¹ : ℝ) : ℂ)) • N
  have hρ' := isDensityOperator_inv_smul hP0 ht htP
  have hσ' := isDensityOperator_inv_smul hN0 ht (hPN ▸ htP)
  have hPt : P = (t : ℂ) • ρ' := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
  have hNt : N = (t : ℂ) • σ' := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one, one_smul]
  set s : ℝ := (1 + t)⁻¹
  have hs0 : 0 < s := inv_pos.mpr (by linarith)
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hts : ((1 - s : ℝ) : ℂ) = (t : ℂ) * (s : ℂ) := by
    have : 1 + t ≠ 0 := by linarith
    rw [← Complex.ofReal_mul]; congr 1
    change (1 : ℝ) - (1 + t)⁻¹ = t * (1 + t)⁻¹
    field_simp; ring
  have hmix : (s : ℂ) • ρ + ((1 - s : ℝ) : ℂ) • σ' = (s : ℂ) • σ + ((1 - s : ℝ) : ℂ) • ρ' := by
    rw [hts, mul_comm, ← smul_smul, ← smul_smul, ← smul_add, ← smul_add, ← hPt, ← hNt, hsplit]
  have hΦ := congrArg Φ hmix
  rw [hA ρ σ' hρ hσ' s hs0.le hs1, hA σ ρ' hσ hρ' s hs0.le hs1, hts, mul_comm, ← smul_smul,
    ← smul_smul, ← smul_add, ← smul_add] at hΦ
  have hΦ' := smul_right_injective _ (by exact_mod_cast hs0.ne' : (s : ℂ) ≠ 0) hΦ
  have hdiff : Φ ρ - Φ σ = (t : ℂ) • (Φ ρ' - Φ σ') := by
    rw [smul_sub, sub_eq_sub_iff_add_eq_add, hΦ', add_comm]
  have hρ'' := (hD _ hρ').isTraceClass
  have hσ'' := (hD _ hσ').isTraceClass
  change ‖ofOperator (Φ ρ - Φ σ) h₁‖ ≤ 2 * t
  rw [show ofOperator (Φ ρ - Φ σ) h₁ = (t : ℂ) • (ofOperator _ hρ'' - ofOperator _ hσ'') from
    Subtype.ext hdiff, norm_smul, Complex.norm_real, Real.norm_of_nonneg ht.le, mul_comm]
  gcongr
  calc ‖ofOperator _ hρ'' - ofOperator _ hσ''‖ ≤ ‖ofOperator _ hρ''‖ + ‖ofOperator _ hσ''‖ :=
        norm_sub_le _ _
    _ = 2 := by rw [(hD _ hρ').norm_ofOperator, (hD _ hσ').norm_ofOperator]; norm_num

/-! ## C. Rank-one operators -/

lemma isTraceClass_rankOne (x y : E) : IsTraceClass (rankOne ℂ x y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using isTraceClass_zero
  have h : rankOne ℂ x y = ((‖y‖ ^ 2 : ℝ)⁻¹ : ℂ) • rankOne ℂ x y * rankOne ℂ y y * 1 := by
    have hy' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
    ext z
    simp only [rankOne_apply, mul_apply_eq_comp, smul_apply,
      one_apply_eq_self, map_smul, smul_smul,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    congr 1; field_simp; simp
  rw [h]
  exact isTraceClass_mul_mul (isTraceClass_rankOne_self y)

/-- `‖|x⟩⟨y|‖₁ ≤ ‖x‖ ‖y‖`. -/
theorem traceNorm_rankOne_le (x y : E) :
    traceNorm (rankOne ℂ x y) (isTraceClass_rankOne x y) ≤ ‖x‖ * ‖y‖ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [traceNorm_zero]
  set B : E →L[ℂ] E := ((‖y‖ ^ 2 : ℝ)⁻¹ : ℂ) • rankOne ℂ x y
  have h : rankOne ℂ x y = B * rankOne ℂ y y * 1 := by
    have hy' : (‖y‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
    ext z
    simp only [B, rankOne_apply, mul_apply_eq_comp, smul_apply,
      one_apply_eq_self, map_smul, smul_smul,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    congr 1; field_simp; simp
  rw [traceNorm_eq_of_eq h _ (isTraceClass_mul_mul (isTraceClass_rankOne_self y))]
  refine (traceNorm_mul_mul_le (isTraceClass_rankOne_self y) _).trans ?_
  rw [traceNorm_rankOne_self]
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  calc ‖B‖ * ‖y‖ ^ 2 * ‖(1 : E →L[ℂ] E)‖ ≤ ‖B‖ * ‖y‖ ^ 2 * 1 := by
        gcongr; exact ContinuousLinearMap.norm_id_le
    _ = ‖x‖ * ‖y‖ := by
        simp only [B, norm_smul, norm_rankOne, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg ‖y‖)]
        field_simp

/-- `‖|x⟩⟨x| - |y⟩⟨y|‖₁ ≤ (‖x‖ + ‖y‖) ‖x - y‖`. -/
theorem norm_ofOperator_proj_sub_le (x y : E) :
    ‖ofOperator (proj x) (isTraceClass_rankOne_self x) -
      ofOperator (proj y) (isTraceClass_rankOne_self y)‖ ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have h : ofOperator (proj x) (isTraceClass_rankOne_self x) -
      ofOperator (proj y) (isTraceClass_rankOne_self y) =
      ofOperator _ (isTraceClass_rankOne (x - y) x) + ofOperator _ (isTraceClass_rankOne y (x - y)) :=
    Subtype.ext (by
      change proj x - proj y = rankOne ℂ (x - y) x + rankOne ℂ y (x - y)
      ext z
      simp only [sub_apply, add_apply,
        rankOne_apply, inner_sub_left, sub_smul, smul_sub]
      abel)
  rw [h]
  refine (norm_add_le _ _).trans ?_
  have h1 := traceNorm_rankOne_le (x - y) x
  have h2 := traceNorm_rankOne_le y (x - y)
  calc _ ≤ ‖x - y‖ * ‖x‖ + ‖y‖ * ‖x - y‖ := add_le_add h1 h2
    _ = _ := by ring

theorem continuous_ofOperator_proj :
    Continuous fun x : E => ofOperator (proj x) (isTraceClass_rankOne_self x) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous fun x : E => (‖x‖ + ‖y‖) * ‖x - y‖ := by fun_prop
  have h0 := hc.tendsto y
  simp only [sub_self, norm_zero, mul_zero] at h0
  exact squeeze_zero (fun _ => norm_nonneg _) (fun x => norm_ofOperator_proj_sub_le x y) h0

/-! ## D. Continuity of conjugation -/

/-- Conjugation by a contraction does not increase the trace norm. -/
lemma norm_le_of_coe_eq_conj {U : E →L[ℂ] E} (hU : ‖U‖ ≤ 1) {Z W : TraceClass E}
    (h : Z.1 = U * W.1 * star U) : ‖Z‖ ≤ ‖W‖ := by
  rw [norm_eq_traceNorm, norm_eq_traceNorm,
    traceNorm_eq_of_eq h _ (isTraceClass_mul_mul (isTraceClass_coe W))]
  refine (traceNorm_mul_mul_le (isTraceClass_coe W) _).trans ?_
  rw [norm_star]
  have h0 := traceNorm_nonneg W.1 (isTraceClass_coe W)
  have h1 : ‖U‖ * traceNorm W.1 (isTraceClass_coe W) ≤ traceNorm W.1 (isTraceClass_coe W) :=
    mul_le_of_le_one_left h0 hU
  nlinarith [norm_nonneg U]

lemma mul_proj_mul_star (U : E →L[ℂ] E) (x : E) : U * proj x * star U = proj (U x) := by
  ext z
  simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- **Conjugation is continuous in the trace norm.** If `t ↦ U t` is strongly continuous and each
`U t` is a contraction, then `t ↦ U t ρ (U t)†` is trace-norm continuous for every positive
trace-class `ρ`. -/
theorem continuous_conj {X : Type*} [TopologicalSpace X] {U : X → E →L[ℂ] E}
    (hU : ∀ t, ‖U t‖ ≤ 1) (hc : ∀ x, Continuous fun t => U t x) {ρ : E →L[ℂ] E} (hρ0 : 0 ≤ ρ)
    (hρ : IsTraceClass ρ) :
    Continuous fun t => ofOperator (U t * ρ * star (U t)) (isTraceClass_mul_mul hρ) := by
  obtain ⟨w, b, μ, -, -, -, -, -, hS⟩ := hρ.exists_hasSum_rankOne hρ0
  set a : w → TraceClass E := fun i => ofOperator ((μ i : ℂ) • rankOne ℂ (b i) (b i))
    (isTraceClass_smul _ (isTraceClass_rankOne_self _))
  -- The truncations `t ↦ ∑_{i ∈ F} μᵢ |U t bᵢ⟩⟨U t bᵢ|`.
  set G : Finset w → X → TraceClass E := fun F t =>
    ∑ i ∈ F, (μ i : ℂ) • ofOperator (proj (U t (b i))) (isTraceClass_rankOne_self _)
  have hG : ∀ F, Continuous (G F) := fun F =>
    continuous_finsetSum _ fun i _ => by
      have h := (continuous_ofOperator_proj (E := E)).comp (hc (b i))
      exact h.const_smul (μ i : ℂ)
  -- They differ from the conjugate of `ρ` by the conjugate of the tail of the expansion.
  have hdiff : ∀ F t, (ofOperator (U t * ρ * star (U t)) (isTraceClass_mul_mul hρ) - G F t).1 =
      U t * (ofOperator ρ hρ - ∑ i ∈ F, a i).1 * star (U t) := fun F t => by
    have h1 : (ofOperator ρ hρ - ∑ i ∈ F, a i).1 = ρ - ∑ i ∈ F, (μ i : ℂ) • proj (b i) := by
      rw [← toOperator_apply, map_sub, map_sum]; rfl
    have h2 : (G F t).1 = ∑ i ∈ F, (μ i : ℂ) • proj (U t (b i)) := by
      rw [← toOperator_apply, map_sum]; rfl
    change U t * ρ * star (U t) - (G F t).1 = _
    rw [h1, h2, mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, mul_proj_mul_star]
  refine (Metric.tendstoUniformly_iff.mpr fun ε hε => ?_).continuous (p := atTop)
    (Frequently.of_forall hG)
  have hS' : Tendsto (fun F : Finset w => ∑ i ∈ F, a i) atTop (𝓝 (ofOperator ρ hρ)) := hS
  filter_upwards [Metric.tendsto_nhds.mp hS' ε hε] with F hF t
  rw [dist_eq_norm]
  refine (norm_le_of_coe_eq_conj (hU t) (hdiff F t)).trans_lt ?_
  rw [dist_eq_norm, norm_sub_rev] at hF
  exact hF

/-! ## E. The pure states are closed -/

/-- A pure state is a positive idempotent operator of trace norm one. -/
theorem isPure_iff_of_isTraceClass {ρ : E →L[ℂ] E} (hρ : IsTraceClass ρ) :
    IsPure ρ ↔ 0 ≤ ρ ∧ traceNorm ρ hρ = 1 ∧ ρ * ρ = ρ := by
  constructor
  · rintro ⟨ψ, hψ, rfl⟩
    exact ⟨proj_nonneg ψ, (isDensityOperator_proj hψ).traceNorm_eq_one,
      (isIdempotentElem_rankOne_self hψ).eq⟩
  · rintro ⟨h0, h1, h2⟩
    have hD : IsDensityOperator ρ := isDensityOperator_iff.mpr ⟨h0, by
      rw [traceNorm_of_nonneg h0] at h1
      rw [← ENNReal.ofReal_toReal (posTrace_ne_top h0 hρ), h1, ENNReal.ofReal_one]⟩
    exact hD.eq_proj_of_isIdempotentElem h2

/-- **The pure states are closed in the trace norm.** -/
theorem isClosed_setOf_isPure : IsClosed {T : TraceClass E | IsPure T.1} := by
  have h : {T : TraceClass E | IsPure T.1} =
      toOperator ⁻¹' Set.Ici 0 ∩ {T | ‖T‖ = 1} ∩ {T | toOperator T * toOperator T = toOperator T} := by
    ext T
    simp only [Set.mem_ofPred_eq, isPure_iff_of_isTraceClass (isTraceClass_coe T), Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_Ici, toOperator_apply, norm_eq_traceNorm, and_assoc]
  rw [h]
  refine ((isClosed_Ici.preimage toOperator.continuous).inter
    (isClosed_eq continuous_norm continuous_const)).inter
    (isClosed_eq (toOperator.continuous.mul toOperator.continuous) toOperator.continuous)

/-! ## F. The trace norm in `[0, ∞]` -/

/-- The trace norm `tr |T| ∈ [0, ∞]` of any operator. It is finite exactly for trace-class `T`
(`traceENorm_ne_top_iff`), where it is `‖T‖₁` (`traceENorm_eq_ofReal`). -/
def traceENorm (T : E →L[ℂ] E) : ℝ≥0∞ := posTrace (CFC.abs T)

lemma isTraceClass_abs_iff {T : E →L[ℂ] E} : IsTraceClass (CFC.abs T) ↔ IsTraceClass T := by
  simp only [IsTraceClass, CFC.abs_of_nonneg _ (CFC.abs_nonneg T)]

theorem traceENorm_ne_top_iff {T : E →L[ℂ] E} : traceENorm T ≠ ⊤ ↔ IsTraceClass T := by
  rw [traceENorm, ← isTraceClass_iff_posTrace_ne_top (CFC.abs_nonneg T), isTraceClass_abs_iff]

theorem traceENorm_eq_ofReal {T : E →L[ℂ] E} (h : IsTraceClass T) :
    traceENorm T = ENNReal.ofReal (traceNorm T h) := by
  rw [traceNorm_eq_toReal_posTrace_abs]
  exact (ENNReal.ofReal_toReal (traceENorm_ne_top_iff.mpr h)).symm

lemma traceENorm_eq_top {T : E →L[ℂ] E} (h : ¬ IsTraceClass T) : traceENorm T = ⊤ := by
  by_contra h'
  exact h (traceENorm_ne_top_iff.mp h')

theorem traceENorm_of_nonneg {T : E →L[ℂ] E} (hT : 0 ≤ T) : traceENorm T = posTrace T := by
  rw [traceENorm, CFC.abs_of_nonneg T hT]

lemma IsDensityOperator.traceENorm_eq_one {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    traceENorm ρ = 1 := by
  rw [traceENorm_of_nonneg hρ.nonneg, hρ.posTrace_eq_one]

@[simp] lemma traceENorm_zero : traceENorm (0 : E →L[ℂ] E) = 0 := by
  rw [traceENorm_eq_ofReal isTraceClass_zero, traceNorm_zero, ENNReal.ofReal_zero]

lemma traceENorm_neg (T : E →L[ℂ] E) : traceENorm (-T) = traceENorm T := by
  by_cases h : IsTraceClass T
  · rw [traceENorm_eq_ofReal h, traceENorm_eq_ofReal (isTraceClass_neg h),
      traceNorm_neg h (isTraceClass_neg h)]
  · rw [traceENorm_eq_top h, traceENorm_eq_top fun h' => h (by simpa using isTraceClass_neg h')]

lemma traceENorm_sub_comm (S T : E →L[ℂ] E) : traceENorm (S - T) = traceENorm (T - S) := by
  rw [← traceENorm_neg, neg_sub]

theorem traceENorm_add_le (S T : E →L[ℂ] E) :
    traceENorm (S + T) ≤ traceENorm S + traceENorm T := by
  by_cases hS : IsTraceClass S
  · by_cases hT : IsTraceClass T
    · rw [traceENorm_eq_ofReal hS, traceENorm_eq_ofReal hT,
        traceENorm_eq_ofReal (isTraceClass_add hS hT),
        ← ENNReal.ofReal_add (traceNorm_nonneg _ _) (traceNorm_nonneg _ _)]
      exact ENNReal.ofReal_le_ofReal (traceNorm_add_le hS hT _)
    · simp [traceENorm_eq_top hT]
  · simp [traceENorm_eq_top hS]

lemma traceENorm_sub_le (R S T : E →L[ℂ] E) :
    traceENorm (R - T) ≤ traceENorm (R - S) + traceENorm (S - T) := by
  simpa using traceENorm_add_le (R - S) (S - T)

theorem traceENorm_smul (c : ℂ) {T : E →L[ℂ] E} (h : IsTraceClass T) :
    traceENorm (c • T) = ‖c‖ₑ * traceENorm T := by
  rw [traceENorm_eq_ofReal h, traceENorm_eq_ofReal (isTraceClass_smul c h), traceNorm_smul c h,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm]

theorem traceENorm_mul_mul_le (A B : E →L[ℂ] E) {T : E →L[ℂ] E} (h : IsTraceClass T) :
    traceENorm (A * T * B) ≤ ‖A‖ₑ * traceENorm T * ‖B‖ₑ := by
  rw [traceENorm_eq_ofReal h, traceENorm_eq_ofReal (isTraceClass_mul_mul h), ← ofReal_norm,
    ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg A),
    ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg A) (traceNorm_nonneg _ _))]
  exact ENNReal.ofReal_le_ofReal (traceNorm_mul_mul_le h _)

/-- The operator norm is at most the trace norm. -/
theorem enorm_le_traceENorm (T : E →L[ℂ] E) : ‖T‖ₑ ≤ traceENorm T := by
  by_cases h : IsTraceClass T
  · rw [traceENorm_eq_ofReal h, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (opNorm_le_traceNorm h)
  · simp [traceENorm_eq_top h]

/-- Trace-norm convergence of trace-class operators, in `𝒮₁(E)` or through `traceENorm`. -/
theorem tendsto_ofOperator_iff {α : Type*} {l : Filter α} {f : α → E →L[ℂ] E} {T : E →L[ℂ] E}
    (hf : ∀ a, IsTraceClass (f a)) (hT : IsTraceClass T) :
    Tendsto (fun a => ofOperator (f a) (hf a)) l (𝓝 (ofOperator T hT)) ↔
      Tendsto (fun a => traceENorm (f a - T)) l (𝓝 0) := by
  have h : ∀ a, traceENorm (f a - T) =
      ENNReal.ofReal ‖ofOperator (f a) (hf a) - ofOperator T hT‖ := fun a => by
    change traceENorm (ofOperator (f a) (hf a) - ofOperator T hT).1 = _
    rw [traceENorm_eq_ofReal (isTraceClass_coe _), norm_eq_traceNorm]
  simp_rw [h]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine ⟨fun h0 => by simpa using ENNReal.tendsto_ofReal h0, fun h0 => ?_⟩
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h1

lemma traceENorm_sub_le_add (S T : E →L[ℂ] E) :
    traceENorm (S - T) ≤ traceENorm S + traceENorm T := by
  simpa [sub_eq_add_neg, traceENorm_neg] using traceENorm_add_le S (-T)

/-- `‖|x⟩⟨x| - |y⟩⟨y|‖₁ ≤ (‖x‖ + ‖y‖) ‖x - y‖`. -/
theorem traceENorm_proj_sub_le (x y : E) :
    traceENorm (proj x - proj y) ≤ ENNReal.ofReal ((‖x‖ + ‖y‖) * ‖x - y‖) := by
  have h := norm_ofOperator_proj_sub_le x y
  change traceENorm (ofOperator (proj x) (isTraceClass_rankOne_self x) -
    ofOperator (proj y) (isTraceClass_rankOne_self y)).1 ≤ _
  rw [traceENorm_eq_ofReal (isTraceClass_coe _), ← norm_eq_traceNorm]
  exact ENNReal.ofReal_le_ofReal h

/-- Two pure states are close in the trace norm if the component of `u` orthogonal to `φ` is
small: `‖|φ⟩⟨φ| - |u⟩⟨u|‖₁ ≤ 4 ‖u - ⟪φ, u⟫ φ‖`. -/
theorem traceENorm_proj_sub_proj_le {u φ : E} (hu : ‖u‖ = 1) (hφ : ‖φ‖ = 1) :
    traceENorm (proj φ - proj u) ≤ ENNReal.ofReal (4 * ‖u - ⟪φ, u⟫_ℂ • φ‖) := by
  set c := ⟪φ, u⟫_ℂ
  set w := u - c • φ
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hφw : ⟪φ, w⟫_ℂ = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, hφφ, mul_one, c, sub_self]
  have hpy : 1 = ‖w‖ ^ 2 + ‖c‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) w (c • φ)
      (by rw [inner_smul_right, inner_eq_zero_symm.mp hφw, mul_zero])
    rw [sub_add_cancel, norm_smul, hφ, mul_one, hu] at h
    nlinarith
  have hw1 : ‖w‖ ≤ 1 := by nlinarith [norm_nonneg w, norm_nonneg c]
  rcases eq_or_ne c 0 with hc | hc
  · have hw : ‖w‖ = 1 := by rw [hc, norm_zero] at hpy; nlinarith [norm_nonneg w]
    refine (traceENorm_sub_le_add _ _).trans ?_
    rw [(isDensityOperator_proj hφ).traceENorm_eq_one,
      (isDensityOperator_proj hu).traceENorm_eq_one,
      hw, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one zero_le_one]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hc1 : ‖c‖ ≤ 1 := by nlinarith [norm_nonneg w]
  set a : ℂ := ((‖c‖ : ℂ))⁻¹ * c
  have ha : ‖a‖ = 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hc0.ne']
  have hproj : proj (a • φ) = proj φ := by
    rw [proj_smul, ha, one_pow, Complex.ofReal_one, one_smul]
  have hca : ‖c - a‖ = 1 - ‖c‖ := by
    have h : c - a = ((‖c‖ - 1 : ℝ) : ℂ) * a := by
      simp only [a]
      push_cast
      field_simp
    rw [h, norm_mul, ha, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hdist : ‖u - a • φ‖ ≤ 2 * ‖w‖ := by
    have h : u - a • φ = w + (c - a) • φ := by simp only [w, sub_smul]; abel
    rw [h]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, hφ, mul_one, hca]
    nlinarith [norm_nonneg w]
  rw [traceENorm_sub_comm, ← hproj]
  refine (traceENorm_proj_sub_le u (a • φ)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [hu, norm_smul, ha, hφ]
  linarith

/-- **Trace-norm bounds extend from pure states to density operators.** If a bounded linear map
`D` on operators satisfies `‖D |ψ⟩⟨ψ|‖₁ ≤ c` on pure states, then `‖D ρ‖₁ ≤ c` on density operators:
expand `ρ = ∑ᵢ μᵢ |bᵢ⟩⟨bᵢ|` and sum `∑ᵢ μᵢ D |bᵢ⟩⟨bᵢ|` in `𝒮₁(E)`. -/
theorem traceENorm_apply_le_of_forall_proj (D : (E →L[ℂ] E) →L[ℂ] E →L[ℂ] E) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ ψ : E, ‖ψ‖ = 1 → traceENorm (D (proj ψ)) ≤ ENNReal.ofReal c)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) : traceENorm (D ρ) ≤ ENNReal.ofReal c := by
  obtain ⟨w, b, μ, -, -, hμ0, hμ, -, hS⟩ := hρ.isTraceClass.exists_hasSum_rankOne hρ.nonneg
  rw [hρ.traceNorm_eq_one] at hμ
  have hb : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have htc : ∀ i, IsTraceClass (D (proj (b i))) := fun i =>
    traceENorm_ne_top_iff.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h _ (hb i)))
  have hle : ∀ i, traceNorm (D (proj (b i))) (htc i) ≤ c := fun i => by
    have h' := h _ (hb i)
    rw [traceENorm_eq_ofReal (htc i)] at h'
    exact (ENNReal.ofReal_le_ofReal_iff hc).mp h'
  set a : w → TraceClass E := fun i => (μ i : ℂ) • ofOperator (D (proj (b i))) (htc i)
  have ha : ∀ i, ‖a i‖ ≤ μ i * c := fun i => by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ0 i), norm_eq_traceNorm]
    exact mul_le_mul_of_nonneg_left (hle i) (hμ0 i)
  obtain ⟨A, hA⟩ : Summable a := .of_norm_bounded (hμ.summable.mul_right c) ha
  have hAle : ‖A‖ ≤ c := by simpa using hA.norm_le_of_bounded (hμ.mul_right c) ha
  have hDA : A.1 = D ρ := by
    have h1 := hA.mapL toOperator
    have h2 := (hS.mapL toOperator).mapL D
    refine h1.unique (h2.congr_fun fun i => ?_)
    simp only [a, map_smul, toOperator_apply, ofOperator_coe]
  rw [← hDA, traceENorm_eq_ofReal A.2, ← norm_eq_traceNorm]
  exact ENNReal.ofReal_le_ofReal hAle

/-- **Conjugation is continuous in the trace norm**, along a filter: if `U a → U₀` strongly with
all `‖U a‖ ≤ 1` and `‖U₀‖ ≤ 1`, then `U a ρ (U a)† → U₀ ρ U₀†` in trace norm for every density
operator `ρ`. -/
theorem tendsto_traceENorm_conj {α : Type*} {l : Filter α} {U : α → E →L[ℂ] E} {U₀ : E →L[ℂ] E}
    (hU : ∀ a, ‖U a‖ ≤ 1) (hU₀ : ‖U₀‖ ≤ 1) (hc : ∀ x, Tendsto (fun a => U a x) l (𝓝 (U₀ x)))
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    Tendsto (fun a => traceENorm (U a * ρ * star (U a) - U₀ * ρ * star U₀)) l (𝓝 0) := by
  obtain ⟨w, b, μ, -, -, hμ0, -, -, hS⟩ := hρ.isTraceClass.exists_hasSum_rankOne hρ.nonneg
  set ρ' := ofOperator ρ hρ.isTraceClass
  set p : w → TraceClass E := fun i => ofOperator ((μ i : ℂ) • rankOne ℂ (b i) (b i))
    (isTraceClass_smul _ (isTraceClass_rankOne_self _))
  set conj : (E →L[ℂ] E) → TraceClass E → TraceClass E := fun V Z =>
    ofOperator (V * Z.1 * star V) (isTraceClass_mul_mul Z.2)
  have hconj_sub : ∀ V Z Z', conj V Z - conj V Z' = conj V (Z - Z') := fun V Z Z' =>
    Subtype.ext (by change V * Z.1 * star V - V * Z'.1 * star V = V * (Z.1 - Z'.1) * star V
                    rw [mul_sub, sub_mul])
  have hconj_sum : ∀ V (F : Finset w), conj V (∑ i ∈ F, p i) =
      ∑ i ∈ F, (μ i : ℂ) • ofOperator (proj (V (b i))) (isTraceClass_rankOne_self _) := by
    intro V F
    refine Subtype.ext ?_
    change V * (∑ i ∈ F, p i).1 * star V = (∑ i ∈ F, _ : TraceClass E).1
    rw [← toOperator_apply, ← toOperator_apply, map_sum, map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [p, toOperator_apply, ofOperator_coe, map_smul]
    rw [mul_smul_comm, smul_mul_assoc]
    exact congrArg _ (mul_proj_mul_star V (b i))
  have hnorm : ∀ {V : E →L[ℂ] E}, ‖V‖ ≤ 1 → ∀ Z, ‖conj V Z‖ ≤ ‖Z‖ := fun hV Z =>
    norm_le_of_coe_eq_conj hV rfl
  -- reduce to trace-class convergence
  have key : Tendsto (fun a => conj (U a) ρ' - conj U₀ ρ') l (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hS' : Tendsto (fun F : Finset w => ∑ i ∈ F, p i) atTop (𝓝 ρ') := hS
    obtain ⟨F, hF⟩ := (Metric.tendsto_nhds.mp hS' (ε / 3) (by positivity)).exists
    rw [dist_eq_norm, norm_sub_rev] at hF
    set G : α → TraceClass E := fun a => ∑ i ∈ F, (μ i : ℂ) •
      (ofOperator (proj (U a (b i))) (isTraceClass_rankOne_self _) -
        ofOperator (proj (U₀ (b i))) (isTraceClass_rankOne_self _))
    have hG : Tendsto G l (𝓝 0) := by
      have : (0 : TraceClass E) = ∑ i ∈ F, (μ i : ℂ) •
          (ofOperator (proj (U₀ (b i))) (isTraceClass_rankOne_self _) -
            ofOperator (proj (U₀ (b i))) (isTraceClass_rankOne_self _)) := by simp
      rw [this]
      refine tendsto_finsetSum _ fun i _ =>
        ((?_ : Tendsto _ _ _).sub tendsto_const_nhds).const_smul _
      exact (continuous_ofOperator_proj.tendsto _).comp (hc (b i))
    filter_upwards [Metric.tendsto_nhds.mp hG (ε / 3) (by positivity)] with a ha
    rw [dist_zero_right] at ha ⊢
    have hsplit : conj (U a) ρ' - conj U₀ ρ' =
        conj (U a) (ρ' - ∑ i ∈ F, p i) - conj U₀ (ρ' - ∑ i ∈ F, p i) + G a := by
      rw [← hconj_sub, ← hconj_sub, hconj_sum, hconj_sum]
      simp only [G, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [hsplit]
    calc ‖conj (U a) (ρ' - ∑ i ∈ F, p i) - conj U₀ (ρ' - ∑ i ∈ F, p i) + G a‖
        ≤ ‖conj (U a) (ρ' - ∑ i ∈ F, p i)‖ + ‖conj U₀ (ρ' - ∑ i ∈ F, p i)‖ + ‖G a‖ :=
          (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ < ε / 3 + ε / 3 + ε / 3 := by
          gcongr
          · exact (hnorm (hU a) _).trans_lt hF
          · exact (hnorm hU₀ _).trans_lt hF
      _ = ε := by ring
  have key' : Tendsto (fun a => conj (U a) ρ') l (𝓝 (conj U₀ ρ')) :=
    tendsto_sub_nhds_zero_iff.mp key
  exact (tendsto_ofOperator_iff (f := fun a => (conj (U a) ρ').1)
    (fun a => (conj (U a) ρ').2) (conj U₀ ρ').2).mp key'

/-- **Density operators with support in `P a` are dense**, for star projections `P a → 1`
strongly: `P a ρ P a / tr (P a ρ P a) → ρ` in the trace norm. -/
theorem exists_isDensityOperator_mul_eq {α : Type*} {l : Filter α} [l.NeBot]
    {P : α → E →L[ℂ] E} (hP : ∀ a, IsStarProjection (P a))
    (hc : ∀ x, Tendsto (fun a => P a x) l (𝓝 x)) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a σ, IsDensityOperator σ ∧ P a * σ = σ ∧ traceENorm (ρ - σ) < ENNReal.ofReal ε := by
  have hconv := tendsto_traceENorm_conj (U := P) (U₀ := 1)
    (fun a => IsStarProjection.norm_le _ (hP a)) ContinuousLinearMap.norm_id_le (by simpa using hc)
    hρ
  simp only [one_mul, star_one, mul_one] at hconv
  set δ := min (ε / 2) 2⁻¹
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  obtain ⟨a, ha⟩ := (hconv.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδ))).exists
  set X := P a * ρ * star (P a)
  have hX0 : 0 ≤ X := star_right_conjugate_nonneg hρ.nonneg _
  have hXtc : IsTraceClass X := isTraceClass_mul_mul hρ.isTraceClass
  have hdtc : IsTraceClass (X - ρ) := by
    rw [sub_eq_add_neg]; exact isTraceClass_add hXtc (isTraceClass_neg hρ.isTraceClass)
  set d := traceNorm (X - ρ) hdtc
  have hd0 : 0 ≤ d := traceNorm_nonneg _ _
  rw [traceENorm_eq_ofReal hdtc, ENNReal.ofReal_lt_ofReal_iff hδ] at ha
  have hdδ : d < δ := ha
  have hδ2 : δ ≤ 2⁻¹ := min_le_right _ _
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  set c := (posTrace X).toReal
  have hXc : traceENorm X = ENNReal.ofReal c := by
    rw [traceENorm_of_nonneg hX0, ENNReal.ofReal_toReal (posTrace_ne_top hX0 hXtc)]
  -- `|c - 1| ≤ d`
  have hc1 : c ≤ d + 1 := by
    have h := traceENorm_add_le (X - ρ) ρ
    rw [sub_add_cancel, hXc, traceENorm_eq_ofReal hdtc, hρ.traceENorm_eq_one, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add hd0 zero_le_one] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hc2 : 1 ≤ d + c := by
    have h := traceENorm_add_le (ρ - X) X
    rw [sub_add_cancel, hXc, traceENorm_sub_comm, traceENorm_eq_ofReal hdtc, hρ.traceENorm_eq_one,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add hd0 ENNReal.toReal_nonneg] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hcpos : 0 < c := by linarith
  set σ := ((c⁻¹ : ℝ) : ℂ) • X
  have hσ : IsDensityOperator σ :=
    isDensityOperator_inv_smul hX0 hcpos (ENNReal.ofReal_toReal (posTrace_ne_top hX0 hXtc)).symm
  have hPP : P a * P a = P a := (hP a).isIdempotentElem.eq
  refine ⟨a, σ, hσ, ?_, ?_⟩
  · simp only [σ, X, mul_smul_comm, ← mul_assoc, hPP]
  · have hXσ : X - σ = ((1 - c⁻¹ : ℝ) : ℂ) • X := by
      simp only [σ, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    have h2 : traceENorm (X - σ) = ENNReal.ofReal |c - 1| := by
      rw [hXσ, traceENorm_smul _ hXtc, hXc, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_of_pos hcpos, ← abs_mul, abs_of_pos hcpos]
      congr 2
      field_simp
    calc traceENorm (ρ - σ) ≤ traceENorm (ρ - X) + traceENorm (X - σ) := traceENorm_sub_le _ _ _
      _ = ENNReal.ofReal d + ENNReal.ofReal |c - 1| := by
          rw [traceENorm_sub_comm, traceENorm_eq_ofReal hdtc, h2]
      _ = ENNReal.ofReal (d + |c - 1|) := (ENNReal.ofReal_add hd0 (abs_nonneg _)).symm
      _ < ENNReal.ofReal ε := by
          rw [ENNReal.ofReal_lt_ofReal_iff hε]
          have : |c - 1| ≤ d := abs_le.mpr ⟨by linarith, by linarith⟩
          linarith

/-- **A trace-norm limit of pure states is pure.** -/
theorem isPure_of_tendsto_traceENorm {α : Type*} {l : Filter α} [l.NeBot] {f : α → E →L[ℂ] E}
    {T : E →L[ℂ] E} (hf : ∀ᶠ a in l, IsPure (f a))
    (h : Tendsto (fun a => traceENorm (f a - T)) l (𝓝 0)) : IsPure T := by
  classical
  obtain ⟨a, ⟨ψ, -, ha⟩, hfin⟩ :=
    (hf.and (h.eventually (gt_mem_nhds ENNReal.zero_lt_top))).exists
  have hT : IsTraceClass T := by
    have h1 := isTraceClass_neg (traceENorm_ne_top_iff.mp hfin.ne)
    rw [ha] at h1
    convert isTraceClass_add (isTraceClass_rankOne_self ψ : IsTraceClass (proj ψ)) h1 using 1
    abel
  set g : α → E →L[ℂ] E := fun a => if IsPure (f a) then f a else T
  have hg : ∀ a, IsTraceClass (g a) := fun a => by
    simp only [g]
    split_ifs with ha
    · obtain ⟨ψ, -, hψ⟩ := ha
      rw [hψ]
      exact isTraceClass_rankOne_self ψ
    · exact hT
  have hgf : ∀ᶠ a in l, g a = f a := hf.mono fun a ha => by simp [g, ha]
  have hlim := (tendsto_ofOperator_iff hg hT).mpr
    (h.congr' (hgf.mono fun a ha => by simp only [ha]))
  exact isClosed_setOf_isPure.mem_of_tendsto hlim ((hf.and hgf).mono fun a ha => by
    change IsPure (g a)
    rw [ha.2]
    exact ha.1)

end QuantumMechanics
