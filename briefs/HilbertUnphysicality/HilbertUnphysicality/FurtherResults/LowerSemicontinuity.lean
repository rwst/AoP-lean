/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import HilbertUnphysicality
public import ForMathlib.Analysis.Normed.Lp.Semicontinuous

/-!
# Further results: [B]COBS fails in one direction only

Not part of the brief. This file formalizes Sec. 1 of `further-results.tex` in the brief's
directory (R. Stephan, *Further results on the brief "Unphysicality of Hilbert spaces for
quantum mechanics"*).

Proposition 2 of the brief shows that the expectation of the number operator `N` is not
continuous in the Hilbert norm. Here: it is lower semicontinuous, with values in `[0, ∞]`, on
all nonzero vectors. So along a convergent sequence of states the expectations can jump up in
the limit, as in the brief's example, but never down. The same holds for every diagonal
operator with nonnegative entries.

## Main results

* `diagForm`, `lowerSemicontinuous_diagForm`  the form `∑ wᵢ |xᵢ|²` of a diagonal operator with
  entries `wᵢ ≥ 0`, with value `∞` off the form domain, is lower semicontinuous on `ℓ²(ι)`
  (`lp.lowerSemicontinuous_tsum_mul_enorm_pow`, in `ForMathlib`);
* `diagForm_ne_top_iff`, `diagForm_eq_ofReal`  it is finite exactly on the form domain, and
  there it is the real sum;
* `diagExpectation`, `lowerSemicontinuousOn_diagExpectation`  the expectation `⟨x, A x⟩ / ‖x‖²`
  is lower semicontinuous on `x ≠ 0`;
* `numberExpectation_eq_ofReal`  for `N`, it agrees on `D(N) ∖ {0}` with the brief's `expN`;
* `le_liminf_numberExpectation`  if `xₖ → y ≠ 0`, then `E_N(y) ≤ liminf E_N(xₖ)`;
* `not_upperSemicontinuousWithinAt_numberExpectation`  and the inequality can be strict: the
  brief's sequence `xʲ → |0⟩` has `E_N(xʲ) = 1 > 0 = E_N(|0⟩)`.

## References

* K. Schmüdgen, Unbounded Self-adjoint Operators on Hilbert Space, GTM 265, Springer 2012,
  Prop. 10.1: a semibounded form is closed iff it is lower semicontinuous.
* B. Simon, A notion of convergence of quadratic forms, arXiv:1711.00528, Thm. 10.14 (attributed
  there to Davies and Kato).
-/

open InconsistentConvergence Filter Topology Set
open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace HilbertUnphysicality.FurtherResults

/-! ### Positive diagonal operators -/

section Diagonal

variable {ι : Type*} (w : ι → ℝ≥0)

/-- The quadratic form `∑ wᵢ |xᵢ|²` of the diagonal operator with entries `wᵢ ≥ 0`, as a value
in `[0, ∞]`: it is `∞` exactly off the form domain. -/
def diagForm (x : lp (fun _ : ι => ℂ) 2) : ℝ≥0∞ := ∑' i, (w i : ℝ≥0∞) * ‖x i‖ₑ ^ 2

/-- The form is lower semicontinuous in the `ℓ²` norm. -/
theorem lowerSemicontinuous_diagForm : LowerSemicontinuous (diagForm w) :=
  lp.lowerSemicontinuous_tsum_mul_enorm_pow w 2

lemma diagForm_term (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    (w i : ℝ≥0∞) * ‖x i‖ₑ ^ 2 = ((w i * ‖x i‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  simp [enorm]

/-- The form is finite exactly on the form domain `{x | ∑ wᵢ |xᵢ|² < ∞}`. -/
theorem diagForm_ne_top_iff (x : lp (fun _ : ι => ℂ) 2) :
    diagForm w x ≠ ⊤ ↔ Summable fun i => (w i : ℝ) * ‖x i‖ ^ 2 := by
  simp_rw [diagForm, diagForm_term, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp

/-- On the form domain the form is the real sum `∑ wᵢ |xᵢ|²`. -/
theorem diagForm_eq_ofReal (x : lp (fun _ : ι => ℂ) 2)
    (h : Summable fun i => (w i : ℝ) * ‖x i‖ ^ 2) :
    diagForm w x = ENNReal.ofReal (∑' i, (w i : ℝ) * ‖x i‖ ^ 2) := by
  have h' : Summable fun i => w i * ‖x i‖₊ ^ 2 := by
    rw [← NNReal.summable_coe]; simpa using h
  simp_rw [diagForm, diagForm_term, ← ENNReal.coe_tsum h']
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_tsum]
  simp

/-- Scaling: `q(c x) = c² q(x)`. -/
theorem diagForm_smul (c : ℝ) (x : lp (fun _ : ι => ℂ) 2) :
    diagForm w (c • x) = ENNReal.ofReal (c ^ 2) * diagForm w x := by
  simp only [diagForm, ← ENNReal.tsum_mul_left]
  congr 1 with i
  rw [lp.coeFn_smul, Pi.smul_apply, enorm_smul, mul_pow, mul_left_comm, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- The expectation `⟨x, A x⟩ / ‖x‖²` of the diagonal operator in the state of the ray of `x`,
as the form at `x / ‖x‖`. -/
def diagExpectation (x : lp (fun _ : ι => ℂ) 2) : ℝ≥0∞ := diagForm w (‖x‖⁻¹ • x)

/-- The expectation is lower semicontinuous on the nonzero vectors. -/
theorem lowerSemicontinuousOn_diagExpectation :
    LowerSemicontinuousOn (diagExpectation w) {x | x ≠ 0} :=
  ((lowerSemicontinuous_diagForm w).lowerSemicontinuousOn univ).comp
    ((continuous_norm.continuousOn.inv₀ fun _ hx => norm_ne_zero_iff.mpr hx).smul
      continuousOn_id) (mapsTo_univ _ _)

/-- So, at a nonzero limit, the expectation can only jump up:
`E(y) ≤ liminf E(xₖ)` whenever `xₖ → y ≠ 0`. -/
theorem le_liminf_diagExpectation {x : ℕ → lp (fun _ : ι => ℂ) 2} {y : lp (fun _ : ι => ℂ) 2}
    (hx : Tendsto x atTop (𝓝 y)) (hy : y ≠ 0) :
    diagExpectation w y ≤ liminf (fun k => diagExpectation w (x k)) atTop := by
  have h := lowerSemicontinuousOn_diagExpectation w y hy
  have hx' : Tendsto x atTop (𝓝[{x | x ≠ 0}] y) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, hx.eventually_ne hy⟩
  refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
  exact le_liminf_of_le (by isBoundedDefault) ((hx'.eventually (h b hb)).mono fun _ => le_of_lt)

end Diagonal

/-! ### The number operator of the brief -/

section Number

/-- The form `∑ n |xₙ|²` of the number operator `N`. -/
def numberForm : H → ℝ≥0∞ := diagForm fun n : ℕ => (n : ℝ≥0)

/-- The expectation `E_N` of the number operator, with values in `[0, ∞]`. -/
def numberExpectation : H → ℝ≥0∞ := diagExpectation fun n : ℕ => (n : ℝ≥0)

/-- `⟨x, N x⟩` is finite exactly on the form domain of `N`, which contains `D(N)`. -/
theorem numberForm_ne_top_iff (x : H) :
    numberForm x ≠ ⊤ ↔ Summable fun n : ℕ => (n : ℝ) * ‖x n‖ ^ 2 := by
  rw [numberForm, diagForm_ne_top_iff]
  simp

lemma summable_of_mem_numberDomain {x : H} (hx : x ∈ numberDomain) :
    Summable fun n : ℕ => (n : ℝ) * ‖x n‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hx
  have : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- On the form domain, `⟨x, N x⟩` is the brief's `numberExp`. -/
theorem numberForm_eq_ofReal {x : H} (h : Summable fun n : ℕ => (n : ℝ) * ‖x n‖ ^ 2) :
    numberForm x = ENNReal.ofReal (numberExp x) := by
  rw [numberForm, diagForm_eq_ofReal _ _ (by simpa using h), numberExp]
  simp

/-- On `D(N) ∖ {0}`, `E_N` is the brief's `expN`. -/
theorem numberExpectation_eq_ofReal {x : H} (hx : x ∈ numberDomain) (hx0 : x ≠ 0) :
    numberExpectation x = ENNReal.ofReal (expN x) := by
  have hs := summable_of_mem_numberDomain hx
  rw [numberExpectation, diagExpectation, diagForm_smul, ← numberForm,
    numberForm_eq_ofReal hs, ← ENNReal.ofReal_mul (by positivity), expN, inv_pow,
    div_eq_inv_mul]

/-- `E_N` is lower semicontinuous on the nonzero vectors. -/
theorem lowerSemicontinuousOn_numberExpectation :
    LowerSemicontinuousOn numberExpectation {x | x ≠ 0} :=
  lowerSemicontinuousOn_diagExpectation _

/-- If `xₖ → y ≠ 0`, then `E_N(y) ≤ liminf E_N(xₖ)`. -/
theorem le_liminf_numberExpectation {x : ℕ → H} {y : H} (hx : Tendsto x atTop (𝓝 y))
    (hy : y ≠ 0) : numberExpectation y ≤ liminf (fun k => numberExpectation (x k)) atTop :=
  le_liminf_diagExpectation _ hx hy

lemma e_ne_zero {j : ℕ} (hj : 1 ≤ j) : e j ≠ 0 := fun h0 => by
  simpa [h0] using norm_e hj

theorem numberExpectation_e {j : ℕ} (hj : 1 ≤ j) : numberExpectation (e j) = 1 := by
  rw [numberExpectation_eq_ofReal (e_mem_numberDomain j) (e_ne_zero hj), expN, numberExp_e hj,
    norm_e hj]
  simp

theorem numberExpectation_ground : numberExpectation ground = 0 := by
  rw [numberExpectation_eq_ofReal ground_mem_numberDomain.1 ground_mem_numberDomain.2, expN,
    numberExp_ground]
  simp

/-- The inequality can be strict: for the brief's sequence `xʲ → |0⟩` of Proposition 2,
`E_N(xʲ) = 1` and `E_N(|0⟩) = 0`. So `E_N` is not upper semicontinuous at the ground state. -/
theorem not_upperSemicontinuousWithinAt_numberExpectation :
    ¬ UpperSemicontinuousWithinAt numberExpectation {x | x ≠ 0} ground := by
  intro h
  have hmem : ∀ᶠ j in atTop, e j ∈ {x : H | x ≠ 0} :=
    (eventually_ge_atTop 1).mono fun _ hj => e_ne_zero hj
  have hlt := (tendsto_nhdsWithin_iff.mpr ⟨tendsto_e, hmem⟩).eventually
    (h 1 (by simp [numberExpectation_ground]))
  obtain ⟨j, hj, hj1⟩ := ((eventually_ge_atTop 1).and hlt).exists
  exact (numberExpectation_e hj).not_lt hj1

end Number

end HilbertUnphysicality.FurtherResults
