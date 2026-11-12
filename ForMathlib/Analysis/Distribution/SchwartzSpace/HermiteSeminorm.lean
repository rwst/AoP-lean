/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteCoeff
import ForMathlib.Analysis.Distribution.SchwartzSpace.SupNorm
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.InnerProductSpace.Parseval

/-!
# Schwartz seminorms are bounded by Hermite coefficients

Every Schwartz seminorm `sup_x ‖x‖^k ‖D^m f(x)‖` of a Schwartz function `f` on `ℝ^ι`, `ι`
nonempty, is bounded by a constant times the weighted supremum
`‖f‖_K = sup_α (1 + |α|)^K |c_α(f)|` of its Hermite coefficients, with `K = 2 dim + k + m`.

The proof bounds `‖x‖^k ‖D^m f(x)‖` by the values of the functions `xⱼ^k ∂^I f`, the values of a
Schwartz function `g` by the `L²` norms of `g` and of `∂ᵢ^dim g` (`exists_norm_le_toLp_two`), an
`L²` norm by `‖·‖_dim` (Parseval, with `∑_α ∏ᵢ (αᵢ + 1)^(-2) < ∞`), and finally
`‖xⱼ^k ∂^I f‖_{2 dim}` by `‖f‖_K` with the shift bounds.

## Main results

* `SchwartzMap.enorm_toLp_le_hermiteNorm`: `‖g‖_{L²} ≤ Z^dim ‖g‖_dim`;
* `SchwartzMap.exists_enorm_apply_le_hermiteNorm`: `|g(x)| ≤ C ‖g‖_{2 dim}`;
* `SchwartzMap.exists_seminorm_le_hermiteNorm`: `p_{k,m}(f) ≤ C ‖f‖_{2 dim + k + m}`.
-/

open MeasureTheory Finset Module
open scoped SchwartzMap LineDeriv InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace SchwartzMap

variable {ι : Type*} [Fintype ι]

lemma _root_.ENNReal.le_of_sq_le_sq {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  have := ENNReal.mul_lt_mul hlt hlt
  rw [sq, sq] at h
  exact absurd h (not_le.2 this)

/-! ### Iterated shift bounds -/

lemma coordMulCLM_iterate_apply (i : ι) (k : ℕ) (g : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (x : EuclideanSpace ℝ ι) :
    (coordMulCLM i)^[k] g x = (x i : ℂ) ^ k * g x := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', coordMulCLM_apply, ih]; ring

lemma exists_hermiteNorm_coordMulCLM_iterate_le (K k : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (i : ι) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)),
      hermiteNorm K ((coordMulCLM i)^[k] g) ≤ C * hermiteNorm (K + k) g := by
  classical
  induction k generalizing K with
  | zero => exact ⟨1, ENNReal.one_ne_top, fun i g => by simp⟩
  | succ k ih =>
    obtain ⟨C, hC, h⟩ := ih (K + 1)
    refine ⟨2 ^ (K + 2) * C, ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hC,
      fun i g => ?_⟩
    rw [Function.iterate_succ_apply']
    calc hermiteNorm K (coordMulCLM i ((coordMulCLM i)^[k] g))
        ≤ 2 ^ (K + 2) * hermiteNorm (K + 1) ((coordMulCLM i)^[k] g) :=
          hermiteNorm_coordMulCLM_le _ _ _
      _ ≤ 2 ^ (K + 2) * (C * hermiteNorm (K + 1 + k) g) := by gcongr; exact h i g
      _ = 2 ^ (K + 2) * C * hermiteNorm (K + (k + 1)) g := by
          rw [show K + 1 + k = K + (k + 1) by ring]; ring

lemma exists_hermiteNorm_lineDerivOp_iterate_le [DecidableEq ι] (K N : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (i : ι) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)),
      hermiteNorm K ((fun h => ∂_{EuclideanSpace.single i (1 : ℝ)} h)^[N] g) ≤
        C * hermiteNorm (K + N) g := by
  induction N generalizing K with
  | zero => exact ⟨1, ENNReal.one_ne_top, fun i g => by simp⟩
  | succ N ih =>
    obtain ⟨C, hC, h⟩ := ih (K + 1)
    refine ⟨2 ^ (K + 2) * C, ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hC,
      fun i g => ?_⟩
    rw [Function.iterate_succ_apply', ← coordDerivCLM_apply]
    calc hermiteNorm K (coordDerivCLM i
          ((fun h => ∂_{EuclideanSpace.single i (1 : ℝ)} h)^[N] g))
        ≤ 2 ^ (K + 2) * hermiteNorm (K + 1)
            ((fun h => ∂_{EuclideanSpace.single i (1 : ℝ)} h)^[N] g) :=
          hermiteNorm_coordDerivCLM_le _ _ _
      _ ≤ 2 ^ (K + 2) * (C * hermiteNorm (K + 1 + N) g) := by gcongr; exact h i g
      _ = 2 ^ (K + 2) * C * hermiteNorm (K + (N + 1)) g := by
          rw [show K + 1 + N = K + (N + 1) by ring]; ring

lemma exists_hermiteNorm_iteratedLineDerivOp_le [DecidableEq ι] (K m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (I : Fin m → ι) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)),
      hermiteNorm K (∂^{fun j => EuclideanSpace.single (I j) (1 : ℝ)} g) ≤
        C * hermiteNorm (K + m) g := by
  induction m generalizing K with
  | zero => exact ⟨1, ENNReal.one_ne_top, fun I g => by simp⟩
  | succ m ih =>
    obtain ⟨C, hC, h⟩ := ih (K + 1)
    refine ⟨2 ^ (K + 2) * C, ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) hC,
      fun I g => ?_⟩
    rw [LineDeriv.iteratedLineDerivOp_succ_left, ← coordDerivCLM_apply]
    calc hermiteNorm K (coordDerivCLM (I 0)
          (∂^{Fin.tail fun j => EuclideanSpace.single (I j) (1 : ℝ)} g))
        ≤ 2 ^ (K + 2) * hermiteNorm (K + 1)
            (∂^{fun j => EuclideanSpace.single (Fin.tail I j) (1 : ℝ)} g) :=
          hermiteNorm_coordDerivCLM_le _ _ _
      _ ≤ 2 ^ (K + 2) * (C * hermiteNorm (K + 1 + m) g) := by gcongr; exact h _ g
      _ = 2 ^ (K + 2) * C * hermiteNorm (K + (m + 1)) g := by
          rw [show K + 1 + m = K + (m + 1) by ring]; ring

/-! ### The `L²` norm -/

/-- The terms `(k + 1)^(-2)` of a convergent series. -/
def invSq (k : ℕ) : ℝ≥0∞ := ((k + 1 : ℝ≥0∞) ^ 2)⁻¹

lemma invSq_eq_ofReal (k : ℕ) : invSq k = ENNReal.ofReal (1 / ((k : ℝ) + 1) ^ 2) := by
  rw [invSq, one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

lemma tsum_invSq_ne_top : ∑' k, invSq k ≠ ⊤ := by
  have hs : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  simp_rw [invSq_eq_ofReal]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs]
  exact ENNReal.ofReal_ne_top

lemma one_le_tsum_invSq : 1 ≤ ∑' k, invSq k := by
  refine le_trans ?_ (le_tsum invSq 0)
  simp [invSq]

lemma tsum_pi_prod_le (g : ℕ → ℝ≥0∞) : ∑' α : ι → ℕ, ∏ i, g (α i) ≤ ∏ _i : ι, ∑' k, g k := by
  classical
  rw [tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  set t := Finset.range (s.sup (fun α => ∑ i, α i) + 1)
  calc ∑ α ∈ s, ∏ i, g (α i) ≤ ∑ α ∈ Fintype.piFinset (fun _ : ι => t), ∏ i, g (α i) := by
        refine Finset.sum_le_sum_of_subset fun α hα => Fintype.mem_piFinset.2 fun i => ?_
        refine Finset.mem_range.2 (Nat.lt_succ_of_le ?_)
        exact (Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _) (mem_univ i)).trans
          (Finset.le_sup (f := fun α : ι → ℕ => ∑ i, α i) hα)
    _ = ∏ _i : ι, ∑ k ∈ t, g k := (Finset.prod_univ_sum (fun _ => t) (fun _ k => g k)).symm
    _ ≤ ∏ _i : ι, ∑' k, g k := Finset.prod_le_prod fun i _ => sum_le_tsum _

lemma enorm_hermiteCoeff_sq_le (α : ι → ℕ) (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ‖hermiteCoeff α g‖ₑ ^ 2 ≤ (∏ i, invSq (α i)) * hermiteNorm (Fintype.card ι) g ^ 2 := by
  set P : ℝ≥0∞ := (∏ i, ((α i : ℝ≥0∞) + 1)) ^ 2
  have hP0 : P ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun i _ => by positivity)
  have hPt : P ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.prod_ne_top fun i _ => by simp)
  have hinv : P⁻¹ = ∏ i, invSq (α i) := by
    change ((∏ i, ((α i : ℝ≥0∞) + 1)) ^ 2)⁻¹ = _
    rw [← Finset.prod_pow, ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inl (by positivity))]
    rfl
  have hle : P * ‖hermiteCoeff α g‖ₑ ^ 2 ≤ hermiteNorm (Fintype.card ι) g ^ 2 := by
    have hprod : ∏ i, ((α i : ℝ≥0∞) + 1) ≤ (hermiteWeight α : ℝ≥0∞) ^ Fintype.card ι := by
      rw [← Finset.card_univ]
      refine Finset.prod_le_pow_card _ _ _ fun i _ => ?_
      exact_mod_cast coord_add_one_le_hermiteWeight α i
    calc P * ‖hermiteCoeff α g‖ₑ ^ 2
        ≤ ((hermiteWeight α : ℝ≥0∞) ^ Fintype.card ι) ^ 2 * ‖hermiteCoeff α g‖ₑ ^ 2 :=
          mul_le_mul_left (pow_le_pow_left₀ (by positivity) hprod 2) _
      _ = ((hermiteWeight α : ℝ≥0∞) ^ Fintype.card ι * ‖hermiteCoeff α g‖ₑ) ^ 2 := by ring
      _ ≤ hermiteNorm (Fintype.card ι) g ^ 2 := by gcongr; exact le_hermiteNorm _ _ _
  rw [← hinv]
  calc ‖hermiteCoeff α g‖ₑ ^ 2 = P⁻¹ * (P * ‖hermiteCoeff α g‖ₑ ^ 2) :=
        (ENNReal.inv_mul_cancel_left hP0 hPt).symm
    _ ≤ P⁻¹ * hermiteNorm (Fintype.card ι) g ^ 2 := by gcongr

/-- Parseval: the `L²` norm is bounded by the weighted supremum of order `dim`. -/
theorem enorm_toLp_le_hermiteNorm (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    ‖g.toLp 2‖ₑ ≤ (∑' k, invSq k) ^ Fintype.card ι * hermiteNorm (Fintype.card ι) g := by
  have hZ1 : 1 ≤ (∑' k, invSq k) ^ Fintype.card ι := one_le_pow₀ one_le_tsum_invSq
  have h3 : ∑' α : ι → ℕ, ∏ i, invSq (α i) ≤ (∑' k, invSq k) ^ Fintype.card ι := by
    refine (tsum_pi_prod_le invSq).trans_eq ?_
    rw [Finset.prod_const, Finset.card_univ]
  have hpars : ‖g.toLp 2‖ₑ ^ 2 = ∑' α, ‖hermiteCoeff α g‖ₑ ^ 2 := by
    have h := (hermitePiBasis (ι := ι)).tsum_enorm_sq_inner (g.toLp 2)
    rw [← h]
    exact tsum_congr fun α => by rw [hermiteCoeff_apply]
  have h1 : ∑' α, ‖hermiteCoeff α g‖ₑ ^ 2 ≤
      ∑' α : ι → ℕ, (∏ i, invSq (α i)) * hermiteNorm (Fintype.card ι) g ^ 2 :=
    CompleteLattice.summable.tsum_le_tsum (fun α => enorm_hermiteCoeff_sq_le α g)
      CompleteLattice.summable
  rw [ENNReal.tsum_mul_right] at h1
  generalize (∑' k, invSq k) ^ Fintype.card ι = Z at hZ1 h3 ⊢
  refine ENNReal.le_of_sq_le_sq ?_
  rw [hpars, mul_pow]
  refine h1.trans (mul_le_mul_left (h3.trans (le_self_pow₀ hZ1 two_ne_zero)) _)

/-! ### Values -/

/-- The values of a Schwartz function are bounded by the weighted supremum of order `2 dim`. -/
theorem exists_enorm_apply_le_hermiteNorm [Nonempty ι] [DecidableEq ι] :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (g : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι),
      ‖g x‖ₑ ≤ C * hermiteNorm (2 * Fintype.card ι) g := by
  have hn : finrank ℝ (EuclideanSpace ℝ ι) < 2 * Fintype.card ι := by
    rw [finrank_euclideanSpace]
    have := Fintype.card_pos (α := ι)
    omega
  obtain ⟨C₀, hC₀, hsob⟩ := exists_norm_le_toLp_two (H := ℂ) (EuclideanSpace.basisFun ι ℝ) hn
  obtain ⟨CD, hCD, hD⟩ :=
    exists_hermiteNorm_lineDerivOp_iterate_le (ι := ι) (Fintype.card ι) (Fintype.card ι)
  have hZ : (∑' k, invSq k) ^ Fintype.card ι ≠ ⊤ := ENNReal.pow_ne_top tsum_invSq_ne_top
  have hL2 : ∀ h : 𝓢(EuclideanSpace ℝ ι, ℂ), ENNReal.ofReal ‖h.toLp 2‖ ≤
      (∑' k, invSq k) ^ Fintype.card ι * hermiteNorm (Fintype.card ι) h := fun h => by
    rw [ofReal_norm]
    exact enorm_toLp_le_hermiteNorm h
  generalize (∑' k, invSq k) ^ Fintype.card ι = Z at hZ hL2
  refine ⟨ENNReal.ofReal C₀ * (Z + Fintype.card ι * (Z * CD)),
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hZ,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hZ hCD)⟩),
    fun g x => ?_⟩
  have hmono : hermiteNorm (Fintype.card ι) g ≤ hermiteNorm (2 * Fintype.card ι) g :=
    hermiteNorm_mono (by omega) g
  have h' := ENNReal.ofReal_le_ofReal (hsob g x)
  rw [ENNReal.ofReal_mul hC₀, ENNReal.ofReal_add (norm_nonneg _)
    (Finset.sum_nonneg fun i _ => norm_nonneg _),
    ENNReal.ofReal_sum_of_nonneg fun i _ => norm_nonneg _, ofReal_norm] at h'
  have hb : ∀ i, hermiteNorm (Fintype.card ι)
      ((∂_{(EuclideanSpace.basisFun ι ℝ) i})^[Fintype.card ι] g) ≤
        CD * hermiteNorm (2 * Fintype.card ι) g := fun i => by
    simpa only [EuclideanSpace.basisFun_apply, two_mul] using hD i g
  refine h'.trans ((mul_le_mul_right (add_le_add ((hL2 g).trans (mul_le_mul_right hmono Z))
    (Finset.sum_le_sum fun i _ => (hL2 _).trans (mul_le_mul_right (hb i) Z))) _).trans_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-! ### Seminorms -/

lemma norm_le_sum_abs_coord (x : EuclideanSpace ℝ ι) : ‖x‖ ≤ ∑ j, |x j| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  simp only [Real.norm_eq_abs]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _

lemma norm_pow_le_sum [Nonempty ι] (k : ℕ) (x : EuclideanSpace ℝ ι) :
    ‖x‖ ^ k ≤ (Fintype.card ι : ℝ) ^ k * ∑ j, |x j| ^ k := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image univ (fun j => |x j|) univ_nonempty
  have h1 : ‖x‖ ≤ Fintype.card ι * |x j₀| := by
    refine (norm_le_sum_abs_coord x).trans ?_
    have := Finset.sum_le_card_nsmul univ (fun j => |x j|) |x j₀| fun j _ => hj₀ j (mem_univ j)
    simpa [nsmul_eq_mul] using this
  calc ‖x‖ ^ k ≤ (Fintype.card ι * |x j₀|) ^ k := pow_le_pow_left₀ (norm_nonneg _) h1 k
    _ = (Fintype.card ι : ℝ) ^ k * |x j₀| ^ k := mul_pow _ _ _
    _ ≤ (Fintype.card ι : ℝ) ^ k * ∑ j, |x j| ^ k := by
        gcongr
        exact Finset.single_le_sum (f := fun j => |x j| ^ k) (fun j _ => by positivity)
          (mem_univ j₀)

/-- A multilinear map on `ℝ^ι` is bounded by its values on the coordinate vectors. -/
lemma norm_le_sum_single [DecidableEq ι] {m : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin m => EuclideanSpace ℝ ι) ℂ) :
    ‖A‖ ≤ ∑ I : Fin m → ι, ‖A fun j => EuclideanSpace.single (I j) (1 : ℝ)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun I _ => norm_nonneg _) fun v => ?_
  have hv : A v = ∑ I : Fin m → ι,
      A fun j => (v j) (I j) • EuclideanSpace.single (I j) (1 : ℝ) := by
    have : v = fun j => ∑ i, (v j) i • EuclideanSpace.single i (1 : ℝ) := by
      funext j
      conv_lhs => rw [← (EuclideanSpace.basisFun ι ℝ).sum_repr (v j)]
      simp [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    conv_lhs => rw [this]
    exact A.map_sum _
  rw [hv, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun I _ => ?_)
  rw [A.map_smul_univ, norm_smul, norm_prod, mul_comm]
  gcongr with j
  exact PiLp.norm_apply_le (v j) (I j)

/-- **Schwartz seminorms are bounded by Hermite coefficients**:
`p_{k,m}(f) ≤ C sup_α (1 + |α|)^(2 dim + k + m) |c_α(f)|`. -/
theorem exists_seminorm_le_hermiteNorm [Nonempty ι] [DecidableEq ι] (k m : ℕ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : 𝓢(EuclideanSpace ℝ ι, ℂ),
      ENNReal.ofReal (SchwartzMap.seminorm ℂ k m f) ≤
        C * hermiteNorm (2 * Fintype.card ι + k + m) f := by
  obtain ⟨Cs, hCs, hs⟩ := exists_enorm_apply_le_hermiteNorm (ι := ι)
  obtain ⟨CX, hCX, hX⟩ := exists_hermiteNorm_coordMulCLM_iterate_le (ι := ι) (2 * Fintype.card ι) k
  obtain ⟨CD, hCD, hD⟩ :=
    exists_hermiteNorm_iteratedLineDerivOp_le (ι := ι) (2 * Fintype.card ι + k) m
  have hC : (Fintype.card ι : ℝ≥0∞) ^ k * (Fintype.card ι * ((Fintype.card ι : ℝ≥0∞) ^ m *
      (Cs * (CX * CD)))) ≠ ⊤ := by
    have := ENNReal.natCast_ne_top (Fintype.card ι)
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top this) (ENNReal.mul_ne_top this
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top this) (ENNReal.mul_ne_top hCs
        (ENNReal.mul_ne_top hCX hCD))))
  generalize hCdef : (Fintype.card ι : ℝ≥0∞) ^ k * (Fintype.card ι * ((Fintype.card ι : ℝ≥0∞) ^ m *
      (Cs * (CX * CD)))) = C at hC
  refine ⟨C, hC, fun f => ?_⟩
  set N := hermiteNorm (2 * Fintype.card ι + k + m) f
  have hfin : C * N ≠ ⊤ := ENNReal.mul_ne_top hC (hermiteNorm_ne_top _ _)
  have hpt : ∀ x, ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖) ≤ C * N := by
    intro x
    have h1 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖ ≤ (Fintype.card ι : ℝ) ^ k * ∑ j, ∑ I : Fin m → ι,
        ‖(coordMulCLM j)^[k] (∂^{fun l => EuclideanSpace.single (I l) (1 : ℝ)} f) x‖ := by
      calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖
          ≤ ((Fintype.card ι : ℝ) ^ k * ∑ j, |x j| ^ k) * ∑ I : Fin m → ι,
              ‖iteratedFDeriv ℝ m f x fun l => EuclideanSpace.single (I l) (1 : ℝ)‖ :=
            mul_le_mul (norm_pow_le_sum k x) (norm_le_sum_single _) (norm_nonneg _)
              (by positivity)
        _ = (Fintype.card ι : ℝ) ^ k * ∑ j, ∑ I : Fin m → ι,
              ‖(coordMulCLM j)^[k] (∂^{fun l => EuclideanSpace.single (I l) (1 : ℝ)} f) x‖ := by
            rw [mul_assoc, Finset.sum_mul]
            congr 1
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun I _ => ?_
            rw [coordMulCLM_iterate_apply, norm_mul, norm_pow, Complex.norm_real,
              Real.norm_eq_abs, iteratedLineDerivOp_eq_iteratedFDeriv]
    calc ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ m f x‖)
        ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) ^ k * ∑ j, ∑ I : Fin m → ι,
            ‖(coordMulCLM j)^[k] (∂^{fun l => EuclideanSpace.single (I l) (1 : ℝ)} f) x‖) :=
          ENNReal.ofReal_le_ofReal h1
      _ = (Fintype.card ι : ℝ≥0∞) ^ k * ∑ j, ∑ I : Fin m → ι,
            ‖(coordMulCLM j)^[k] (∂^{fun l => EuclideanSpace.single (I l) (1 : ℝ)} f) x‖ₑ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
            ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun j _ =>
              Finset.sum_nonneg fun I _ => norm_nonneg _]
          simp_rw [ENNReal.ofReal_sum_of_nonneg fun I _ => norm_nonneg _, ofReal_norm]
      _ ≤ (Fintype.card ι : ℝ≥0∞) ^ k * ∑ _j : ι, ∑ _I : Fin m → ι, Cs * (CX * (CD * N)) := by
          gcongr with j _ I _
          calc ‖(coordMulCLM j)^[k] (∂^{fun l => EuclideanSpace.single (I l) (1 : ℝ)} f) x‖ₑ
              ≤ Cs * hermiteNorm (2 * Fintype.card ι)
                  ((coordMulCLM j)^[k] (∂^{fun l => EuclideanSpace.single (I l) (1 : ℝ)} f)) :=
                hs _ x
            _ ≤ Cs * (CX * hermiteNorm (2 * Fintype.card ι + k)
                  (∂^{fun l => EuclideanSpace.single (I l) (1 : ℝ)} f)) := by
                gcongr
                exact hX j _
            _ ≤ Cs * (CX * (CD * N)) := by
                gcongr
                exact hD I f
      _ = C * N := by
          rw [← hCdef]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  have hsem : SchwartzMap.seminorm ℂ k m f ≤ (C * N).toReal :=
    seminorm_le_bound ℂ k m f ENNReal.toReal_nonneg fun x =>
      (ENNReal.ofReal_le_iff_le_toReal hfin).1 (hpt x)
  calc ENNReal.ofReal (SchwartzMap.seminorm ℂ k m f) ≤ ENNReal.ofReal (C * N).toReal :=
        ENNReal.ofReal_le_ofReal hsem
    _ = C * N := ENNReal.ofReal_toReal hfin

end SchwartzMap
