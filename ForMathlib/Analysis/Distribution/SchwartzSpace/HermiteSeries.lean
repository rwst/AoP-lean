/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteSeminorm
public import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Hermite series with rapidly decreasing coefficients

On `ℝ^ι`, `ι` nonempty, a family `c : (ι → ℕ) → ℂ` with `sup_α (1 + |α|)^K |c_α| < ∞` for every
`K` is the family of Hermite coefficients of a Schwartz function, the sum `∑_α c_α h_α`, and the
Schwartz seminorms of the sum are bounded by these weighted suprema. Together with
`SchwartzMap.exists_hermiteNorm_le_seminorm`, the Hermite coefficients identify `𝓢(ℝ^ι)` with
the space of rapidly decreasing families, as topological vector spaces.

The sum converges, with all its derivatives, because the Schwartz seminorms of `h_α` grow
polynomially in `|α|` (`SchwartzMap.exists_seminorm_le_hermiteNorm` applied to `h_α`), so
`contDiff_tsum` and `iteratedFDeriv_tsum_apply` apply.

## Main definitions

* `SchwartzMap.coeffNorm K c = sup_α (1 + |α|)^K |c_α|`;
* `SchwartzMap.hermiteSeries c hc = ∑_α c_α h_α`.

## Main results

* `SchwartzMap.hermiteCoeff_hermiteSeries`: the coefficients of `∑_α c_α h_α` are `c`;
* `SchwartzMap.exists_seminorm_hermiteSeries_le`: its seminorms are bounded by `coeffNorm L c`.
-/

open MeasureTheory Finset Module
open scoped SchwartzMap LineDeriv InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace SchwartzMap

variable {ι : Type*} [Fintype ι]

/-- The weighted supremum `sup_α (1 + |α|)^K |c_α|` of a family of coefficients. -/
def coeffNorm (K : ℕ) (c : (ι → ℕ) → ℂ) : ℝ≥0∞ :=
  ⨆ α, (hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ

lemma hermiteNorm_eq_coeffNorm (K : ℕ) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    hermiteNorm K f = coeffNorm K fun α => hermiteCoeff α f :=
  rfl

lemma weight_mul_le_coeffNorm (K : ℕ) (α : ι → ℕ) (c : (ι → ℕ) → ℂ) :
    (hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ ≤ coeffNorm K c :=
  le_iSup (fun α => (hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ) α

/-- `∑_α (1 + |α|)^K |c_α| ≤ Z^dim ‖c‖_{K + 2 dim}`. -/
lemma tsum_weight_mul_le (K : ℕ) (c : (ι → ℕ) → ℂ) :
    ∑' α, (hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ ≤
      (∑' k, invSq k) ^ Fintype.card ι * coeffNorm (K + 2 * Fintype.card ι) c := by
  have hterm : ∀ α, (hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ ≤
      (∏ i, invSq (α i)) * coeffNorm (K + 2 * Fintype.card ι) c := by
    intro α
    set P : ℝ≥0∞ := (∏ i, ((α i : ℝ≥0∞) + 1)) ^ 2
    have hP0 : P ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => by positivity)
    have hPt : P ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.prod_ne_top fun i _ => by simp)
    have hinv : P⁻¹ = ∏ i, invSq (α i) := by
      change ((∏ i, ((α i : ℝ≥0∞) + 1)) ^ 2)⁻¹ = _
      rw [← Finset.prod_pow, ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inl (by positivity))]
      rfl
    have hprod : ∏ i, ((α i : ℝ≥0∞) + 1) ≤ (hermiteWeight α : ℝ≥0∞) ^ Fintype.card ι := by
      rw [← Finset.card_univ]
      refine Finset.prod_le_pow_card _ _ _ fun i _ => ?_
      exact_mod_cast coord_add_one_le_hermiteWeight α i
    have hle : P * ((hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ) ≤
        coeffNorm (K + 2 * Fintype.card ι) c := by
      calc P * ((hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ)
          ≤ ((hermiteWeight α : ℝ≥0∞) ^ Fintype.card ι) ^ 2 *
              ((hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ) :=
            mul_le_mul_left (pow_le_pow_left₀ (by positivity) hprod 2) _
        _ = (hermiteWeight α : ℝ≥0∞) ^ (K + 2 * Fintype.card ι) * ‖c α‖ₑ := by ring
        _ ≤ coeffNorm (K + 2 * Fintype.card ι) c := weight_mul_le_coeffNorm _ _ _
    rw [← hinv]
    calc (hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ
        = P⁻¹ * (P * ((hermiteWeight α : ℝ≥0∞) ^ K * ‖c α‖ₑ)) :=
          (ENNReal.inv_mul_cancel_left hP0 hPt).symm
      _ ≤ P⁻¹ * coeffNorm (K + 2 * Fintype.card ι) c := by gcongr
  have h1 := CompleteLattice.summable.tsum_le_tsum hterm CompleteLattice.summable
  rw [ENNReal.tsum_mul_right] at h1
  refine h1.trans (mul_le_mul_left ((tsum_pi_prod_le invSq).trans_eq ?_) _)
  rw [Finset.prod_const, Finset.card_univ]

/-! ### Seminorms of the Hermite functions -/

lemma hermiteNorm_hermitePi_le (K : ℕ) (β : ι → ℕ) :
    hermiteNorm K (hermitePi β) ≤ (hermiteWeight β : ℝ≥0∞) ^ K := by
  refine iSup_le fun α => ?_
  rw [hermiteCoeff_hermitePi]
  split_ifs with h
  · subst h
    simp
  · simp

/-- The Schwartz seminorms of `h_β` grow polynomially in `|β|`. -/
lemma exists_seminorm_hermitePi_le [Nonempty ι] [DecidableEq ι] (k m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ β : ι → ℕ, ENNReal.ofReal (SchwartzMap.seminorm ℂ k m (hermitePi β)) ≤
      C * (hermiteWeight β : ℝ≥0∞) ^ (2 * Fintype.card ι + k + m) := by
  obtain ⟨C, hC, h⟩ := exists_seminorm_le_hermiteNorm (ι := ι) k m
  exact ⟨C, hC, fun β => (h _).trans (by gcongr; exact hermiteNorm_hermitePi_le _ _)⟩

/-! ### The Hermite series -/

variable [Nonempty ι] [DecidableEq ι] (c : (ι → ℕ) → ℂ)

lemma summable_norm_mul_seminorm (hc : ∀ K, coeffNorm K c ≠ ⊤) (k m : ℕ) :
    Summable fun α => ‖c α‖ * SchwartzMap.seminorm ℂ k m (hermitePi α) := by
  obtain ⟨C, hC, h⟩ := exists_seminorm_hermitePi_le (ι := ι) k m
  set L := 2 * Fintype.card ι + k + m
  have hfin : ∑' α, C * ((hermiteWeight α : ℝ≥0∞) ^ L * ‖c α‖ₑ) ≠ ⊤ := by
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hC (ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top tsum_invSq_ne_top) (hc _)) (tsum_weight_mul_le _ c))
  refine (ENNReal.summable_toReal hfin).of_nonneg_of_le (fun α => by positivity) fun α => ?_
  rw [← ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top hfin
    (le_tsum (fun α => C * ((hermiteWeight α : ℝ≥0∞) ^ L * ‖c α‖ₑ)) α)),
    ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
  calc ‖c α‖ₑ * ENNReal.ofReal (SchwartzMap.seminorm ℂ k m (hermitePi α))
      ≤ ‖c α‖ₑ * (C * (hermiteWeight α : ℝ≥0∞) ^ L) := by gcongr; exact h α
    _ = C * ((hermiteWeight α : ℝ≥0∞) ^ L * ‖c α‖ₑ) := by ring

omit [Nonempty ι] [DecidableEq ι] in
lemma contDiff_smul_hermitePi (α : ι → ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ⇑(c α • hermitePi α) :=
  (c α • hermitePi α).smooth ⊤

omit [Nonempty ι] [DecidableEq ι] in
lemma norm_iteratedFDeriv_smul_hermitePi_le (α : ι → ℕ) (k : ℕ) (x : EuclideanSpace ℝ ι) :
    ‖iteratedFDeriv ℝ k ⇑(c α • hermitePi α) x‖ ≤
      ‖c α‖ * SchwartzMap.seminorm ℂ 0 k (hermitePi α) :=
  (norm_iteratedFDeriv_le_seminorm ℂ _ k x).trans_eq (map_smul_eq_mul _ _ _)

lemma iteratedFDeriv_tsum_smul_hermitePi (hc : ∀ K, coeffNorm K c ≠ ⊤) (k : ℕ)
    (x : EuclideanSpace ℝ ι) :
    iteratedFDeriv ℝ k (fun y => ∑' α, (c α • hermitePi α) y) x =
      ∑' α, iteratedFDeriv ℝ k ⇑(c α • hermitePi α) x :=
  iteratedFDeriv_tsum_apply (v := fun k α => ‖c α‖ * SchwartzMap.seminorm ℂ 0 k (hermitePi α))
    (N := ⊤) (contDiff_smul_hermitePi c) (fun k _ => summable_norm_mul_seminorm c hc 0 k)
    (fun k α x _ => norm_iteratedFDeriv_smul_hermitePi_le c α k x) (by exact_mod_cast le_top) x

lemma norm_pow_mul_iteratedFDeriv_tsum_le (hc : ∀ K, coeffNorm K c ≠ ⊤) (k m : ℕ)
    (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun y => ∑' α, (c α • hermitePi α) y) x‖ ≤
      ∑' α, ‖c α‖ * SchwartzMap.seminorm ℂ k m (hermitePi α) := by
  rw [iteratedFDeriv_tsum_smul_hermitePi c hc m x]
  have hs : Summable fun α => ‖iteratedFDeriv ℝ m ⇑(c α • hermitePi α) x‖ :=
    (summable_norm_mul_seminorm c hc 0 m).of_nonneg_of_le (fun α => norm_nonneg _)
      fun α => norm_iteratedFDeriv_smul_hermitePi_le c α m x
  calc ‖x‖ ^ k * ‖∑' α, iteratedFDeriv ℝ m ⇑(c α • hermitePi α) x‖
      ≤ ‖x‖ ^ k * ∑' α, ‖iteratedFDeriv ℝ m ⇑(c α • hermitePi α) x‖ := by
        gcongr
        exact norm_tsum_le_tsum_norm hs
    _ = ∑' α, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m ⇑(c α • hermitePi α) x‖ := (tsum_mul_left).symm
    _ ≤ ∑' α, ‖c α‖ * SchwartzMap.seminorm ℂ k m (hermitePi α) := by
        refine (hs.mul_left _).tsum_le_tsum (fun α => ?_) (summable_norm_mul_seminorm c hc k m)
        exact (le_seminorm ℂ k m _ x).trans_eq (map_smul_eq_mul _ _ _)

/-- The Hermite series `∑_α c_α h_α` of a rapidly decreasing family of coefficients. -/
def hermiteSeries (hc : ∀ K, coeffNorm K c ≠ ⊤) : 𝓢(EuclideanSpace ℝ ι, ℂ) where
  toFun x := ∑' α, (c α • hermitePi α) x
  smooth' := contDiff_tsum (v := fun k α => ‖c α‖ * SchwartzMap.seminorm ℂ 0 k (hermitePi α))
    (N := ⊤) (contDiff_smul_hermitePi c) (fun k _ => summable_norm_mul_seminorm c hc 0 k)
    (fun k α x _ => norm_iteratedFDeriv_smul_hermitePi_le c α k x)
  decay' k m := ⟨_, norm_pow_mul_iteratedFDeriv_tsum_le c hc k m⟩

lemma hermiteSeries_apply (hc : ∀ K, coeffNorm K c ≠ ⊤) (x : EuclideanSpace ℝ ι) :
    hermiteSeries c hc x = ∑' α, c α * hermitePiFun α x := by
  change ∑' α, (c α • hermitePi α) x = _
  simp only [smul_apply, hermitePi_apply, smul_eq_mul]

/-- The Hermite coefficients of `∑_α c_α h_α` are the `c_α`. -/
theorem hermiteCoeff_hermiteSeries (hc : ∀ K, coeffNorm K c ≠ ⊤) (β : ι → ℕ) :
    hermiteCoeff β (hermiteSeries c hc) = c β := by
  have hint : ∀ α, ∫ x, hermitePiFun β x * (c α * hermitePiFun α x) =
      c α * if β = α then 1 else 0 := by
    intro α
    rw [← hermiteCoeff_hermitePi, hermiteCoeff_eq_integral, ← integral_const_mul]
    congr 1
    funext x
    rw [hermitePi_apply]
    ring
  have hint' : ∀ α, Integrable fun x => hermitePiFun β x * (c α * hermitePiFun α x) := by
    intro α
    simpa [hermitePi_apply] using integrable_hermitePiFun_mul β (c α • hermitePi α)
  have hβint : Integrable fun x => ‖hermitePiFun β x‖ := by
    simpa [hermitePi_apply] using (hermitePi β).integrable.norm
  have hsum : Summable fun α => ∫ x, ‖hermitePiFun β x * (c α * hermitePiFun α x)‖ := by
    refine ((summable_norm_mul_seminorm c hc 0 0).mul_left
      (∫ x, ‖hermitePiFun β x‖)).of_nonneg_of_le
      (fun α => integral_nonneg fun x => norm_nonneg _) fun α => ?_
    calc ∫ x, ‖hermitePiFun β x * (c α * hermitePiFun α x)‖
        ≤ ∫ x, ‖hermitePiFun β x‖ * (‖c α‖ * SchwartzMap.seminorm ℂ 0 0 (hermitePi α)) := by
          refine integral_mono (hint' α).norm (hβint.mul_const _) fun x => ?_
          rw [norm_mul, norm_mul]
          gcongr
          simpa [hermitePi_apply] using norm_le_seminorm ℂ (hermitePi α) x
      _ = (∫ x, ‖hermitePiFun β x‖) * (‖c α‖ * SchwartzMap.seminorm ℂ 0 0 (hermitePi α)) :=
          integral_mul_const _ _
  rw [hermiteCoeff_eq_integral]
  have hfun : (fun x => hermitePiFun β x * hermiteSeries c hc x) =
      fun x => ∑' α, hermitePiFun β x * (c α * hermitePiFun α x) := by
    funext x
    rw [hermiteSeries_apply, ← tsum_mul_left]
  rw [hfun, ← integral_tsum_of_summable_integral_norm hint' hsum]
  simp_rw [hint, mul_ite, mul_one, mul_zero, @eq_comm _ β]
  exact tsum_ite_eq β c

/-- The Schwartz seminorms of a Hermite series are bounded by the weighted suprema of its
coefficients. -/
theorem exists_seminorm_hermiteSeries_le (k m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ L : ℕ, ∀ (c : (ι → ℕ) → ℂ) (hc : ∀ K, coeffNorm K c ≠ ⊤),
      ENNReal.ofReal (SchwartzMap.seminorm ℂ k m (hermiteSeries c hc)) ≤ C * coeffNorm L c := by
  obtain ⟨C, hC, h⟩ := exists_seminorm_hermitePi_le (ι := ι) k m
  set L := 2 * Fintype.card ι + k + m
  refine ⟨C * (∑' k, invSq k) ^ Fintype.card ι, ENNReal.mul_ne_top hC
    (ENNReal.pow_ne_top tsum_invSq_ne_top), L + 2 * Fintype.card ι, fun c hc => ?_⟩
  have hs := summable_norm_mul_seminorm c hc k m
  have hsem : SchwartzMap.seminorm ℂ k m (hermiteSeries c hc) ≤
      ∑' α, ‖c α‖ * SchwartzMap.seminorm ℂ k m (hermitePi α) :=
    seminorm_le_bound ℂ k m _ (tsum_nonneg fun α => by positivity)
      (norm_pow_mul_iteratedFDeriv_tsum_le c hc k m)
  calc ENNReal.ofReal (SchwartzMap.seminorm ℂ k m (hermiteSeries c hc))
      ≤ ENNReal.ofReal (∑' α, ‖c α‖ * SchwartzMap.seminorm ℂ k m (hermitePi α)) :=
        ENNReal.ofReal_le_ofReal hsem
    _ = ∑' α, ‖c α‖ₑ * ENNReal.ofReal (SchwartzMap.seminorm ℂ k m (hermitePi α)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun α => by positivity) hs]
        congr 1
        funext α
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm]
    _ ≤ ∑' α, C * ((hermiteWeight α : ℝ≥0∞) ^ L * ‖c α‖ₑ) := by
        refine CompleteLattice.summable.tsum_le_tsum (fun α => ?_) CompleteLattice.summable
        calc ‖c α‖ₑ * ENNReal.ofReal (SchwartzMap.seminorm ℂ k m (hermitePi α))
            ≤ ‖c α‖ₑ * (C * (hermiteWeight α : ℝ≥0∞) ^ L) := by gcongr; exact h α
          _ = C * ((hermiteWeight α : ℝ≥0∞) ^ L * ‖c α‖ₑ) := by ring
    _ ≤ C * ((∑' k, invSq k) ^ Fintype.card ι * coeffNorm (L + 2 * Fintype.card ι) c) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact tsum_weight_mul_le L c
    _ = C * (∑' k, invSq k) ^ Fintype.card ι * coeffNorm (L + 2 * Fintype.card ι) c := by ring

end SchwartzMap
