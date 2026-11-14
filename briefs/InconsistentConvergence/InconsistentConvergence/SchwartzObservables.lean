/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import InconsistentConvergence.NumberOperator
public import InconsistentConvergence.SchwartzSequences

/-!
# Inconsistent convergence: observables on the Schwartz sequence space

The brief closes Sec. 3 with "A topology that keeps track of all moments, like the Schwartz
topology, would not allow this kind of convergence." This module proves it for the expected
number, and for the expectations of polynomials in the ladder operators.

* `S(ℕ)` lies in the domains of `a`, `a†` and `N`, and the three operators restrict to continuous
  linear endomorphisms of `S(ℕ)` (`annihilationS`, `creationS`, `numberOpS`), with
  `N = a† a` on `S(ℕ)` (`numberOpS_eq_comp`).
* The expected number `x ↦ ⟨x|N|x⟩ = numberExp x` is continuous on `S(ℕ)`
  (`continuous_inner_numberOpS`, `continuous_numberExp`), while it is not continuous on `ℓ²`
  (`not_continuousAt_numberExp` in the main file).
* This gives Proposition 1 the way the brief argues it: `eʲ` has no limit in `S(ℕ)`, since such
  a limit would be `|0⟩`, with expected number `0`, while `⟨eʲ|N|eʲ⟩ = 1`
  (`not_tendsto_eS_of_numberExp`).
* Every polynomial in `a` and `a†`, such as the position `(a + a†)/√2`, the momentum
  `i(a† − a)/√2` (`positionS`, `momentumS`) and the energy `N + 1/2` (`hamiltonianS`), is a
  continuous linear endomorphism of `S(ℕ)`, so its expectation is continuous on `S(ℕ)`
  (`continuous_inner_of_mem_adjoin`).

The continuity of expectations is `SchwartzSeq.continuous_inner_apply` in `ForMathlib`, and the
construction of continuous endomorphisms from weighted bounds is `SchwartzSeq.mkCLM`.

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.

## References

* J. E. Roberts, The Dirac bra and ket formalism, J. Math. Phys. 7 (1966) 1097–1104, Theorem 1;
  Rigged Hilbert spaces in quantum mechanics, Commun. Math. Phys. 3 (1966) 98–119,
  Proposition 11: the coarsest topology making a set of observables continuous on their maximal
  invariant domain.
* J.-P. Antoine, Dirac formalism and symmetry problems in quantum mechanics. I, J. Math. Phys.
  10 (1969) 53–69.
-/

open Filter Topology
open scoped InnerProductSpace

@[expose] public noncomputable section

namespace InconsistentConvergence

lemma sqrt_le_succ (n : ℕ) : √((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ### Domains -/

lemma schwartzSeq_le_annihilationDomain : SchwartzSeq.submodule ℂ ≤ annihilation.domain :=
  fun x hx => mem_annihilationDomain.2 <|
    SchwartzSeq.memℓp_of_norm_le 1 (SchwartzSeq.mk x hx) fun n => by
      rw [SchwartzSeq.toLp_mk, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), pow_one]
      gcongr
      exact (Real.sqrt_le_sqrt (by linarith)).trans (sqrt_le_succ n)

lemma schwartzSeq_le_creationDomain : SchwartzSeq.submodule ℂ ≤ creation.domain :=
  fun x hx => mem_creationDomain.2 <|
    SchwartzSeq.memℓp_of_norm_le 1 (SchwartzSeq.mk x hx) fun n => by
      rw [SchwartzSeq.toLp_mk, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), pow_one]
      gcongr
      exact sqrt_le_succ n

lemma schwartzSeq_le_numberOp_domain : SchwartzSeq.submodule ℂ ≤ numberOp.domain :=
  fun x hx => mem_domain_numberOp.2 <|
    SchwartzSeq.memℓp_of_norm_le 1 (SchwartzSeq.mk x hx) fun n => by
      rw [SchwartzSeq.toLp_mk, norm_mul, Complex.norm_natCast, pow_one]
      gcongr
      linarith

/-! ### The ladder operators on `S(ℕ)` -/

lemma annihilation_bound (k : ℕ) (x : S) (n : ℕ) :
    ((n : ℝ) + 1) ^ k * ‖(√((n : ℝ) + 1) : ℂ) * SchwartzSeq.toLp x (n + 1)‖ ≤
      1 * SchwartzSeq.seminormFamily ℂ (k + 1) x := by
  have h := SchwartzSeq.mul_norm_le_seminorm (k + 1) x (n + 1)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), ← mul_assoc,
    one_mul]
  refine le_trans ?_ h
  push_cast
  gcongr
  rw [pow_succ]
  gcongr
  · linarith
  · exact (sqrt_le_succ n).trans (by linarith)

lemma creation_bound (k : ℕ) (x : S) (n : ℕ) :
    ((n : ℝ) + 1) ^ k * ‖creationSeq (SchwartzSeq.toLp x) n‖ ≤
      2 ^ k * SchwartzSeq.seminormFamily ℂ (k + 1) x := by
  rcases n with _ | n
  · rw [creationSeq, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) (apply_nonneg _ _)
  · have h := SchwartzSeq.mul_norm_le_seminorm (k + 1) x n
    rw [creationSeq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      ← mul_assoc]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h (by positivity))
    rw [pow_succ, ← mul_assoc, ← mul_assoc, ← mul_pow]
    push_cast
    gcongr
    · linarith
    · exact sqrt_le_succ n

lemma numberOp_bound (k : ℕ) (x : S) (n : ℕ) :
    ((n : ℝ) + 1) ^ k * ‖(n : ℂ) * SchwartzSeq.toLp x n‖ ≤
      1 * SchwartzSeq.seminormFamily ℂ (k + 1) x := by
  have h := SchwartzSeq.mul_norm_le_seminorm (k + 1) x n
  rw [norm_mul, Complex.norm_natCast, ← mul_assoc, one_mul]
  refine le_trans ?_ h
  rw [pow_succ]
  gcongr
  linarith

/-- The annihilation operator `a`, as a continuous linear endomorphism of `S(ℕ)`:
`(n + 1)ᵏ |(a x)ₙ| ≤ p (k + 1) x`. -/
def annihilationS : S →L[ℂ] S :=
  SchwartzSeq.mkCLM (annihilation.toFun ∘ₗ Submodule.inclusion schwartzSeq_le_annihilationDomain)
    fun k => ⟨k + 1, 1, annihilation_bound k⟩

theorem toLp_annihilationS (x : S) :
    SchwartzSeq.toLp (annihilationS x) =
      annihilation
        ⟨SchwartzSeq.toLp x, schwartzSeq_le_annihilationDomain (SchwartzSeq.toLp_mem x)⟩ :=
  rfl

/-- The creation operator `a†`, as a continuous linear endomorphism of `S(ℕ)`:
`(n + 1)ᵏ |(a† x)ₙ| ≤ 2ᵏ p (k + 1) x`. -/
def creationS : S →L[ℂ] S :=
  SchwartzSeq.mkCLM (creation.toFun ∘ₗ Submodule.inclusion schwartzSeq_le_creationDomain)
    fun k => ⟨k + 1, 2 ^ k, creation_bound k⟩

theorem toLp_creationS (x : S) :
    SchwartzSeq.toLp (creationS x) =
      creation ⟨SchwartzSeq.toLp x, schwartzSeq_le_creationDomain (SchwartzSeq.toLp_mem x)⟩ :=
  rfl

/-- The number operator `N`, as a continuous linear endomorphism of `S(ℕ)`:
`(n + 1)ᵏ |(N x)ₙ| ≤ p (k + 1) x`. -/
def numberOpS : S →L[ℂ] S :=
  SchwartzSeq.mkCLM (numberOp.toFun ∘ₗ Submodule.inclusion schwartzSeq_le_numberOp_domain)
    fun k => ⟨k + 1, 1, fun x n => by
      change _ * ‖numberOp ⟨SchwartzSeq.toLp x,
        schwartzSeq_le_numberOp_domain (SchwartzSeq.toLp_mem x)⟩ n‖ ≤ _
      rw [numberOp_apply]
      exact numberOp_bound k x n⟩

theorem toLp_numberOpS (x : S) :
    SchwartzSeq.toLp (numberOpS x) =
      numberOp ⟨SchwartzSeq.toLp x, schwartzSeq_le_numberOp_domain (SchwartzSeq.toLp_mem x)⟩ :=
  rfl

/-- `N = a† a` on `S(ℕ)`. -/
theorem numberOpS_eq_comp : numberOpS = creationS ∘L annihilationS := by
  ext x n
  rw [toLp_numberOpS, numberOp_apply, ContinuousLinearMap.comp_apply, toLp_creationS]
  cases n with
  | zero => simp [creation_apply_zero]
  | succ n =>
    rw [creation_apply_succ]
    change _ = _ * ((√((n : ℝ) + 1) : ℂ) * SchwartzSeq.toLp x (n + 1))
    rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    rfl

/-! ### The expected number is continuous on `S(ℕ)` -/

/-- On `S(ℕ)`, `⟨x|N|x⟩ = numberExp x`. -/
theorem inner_numberOpS (x : S) :
    ⟪SchwartzSeq.toLp x, SchwartzSeq.toLp (numberOpS x)⟫_ℂ = numberExp (SchwartzSeq.toLp x) :=
  inner_numberOp _

/-- **The expected number is continuous on `S(ℕ)`.** -/
theorem continuous_inner_numberOpS :
    Continuous fun x : S => ⟪SchwartzSeq.toLp x, SchwartzSeq.toLp (numberOpS x)⟫_ℂ :=
  SchwartzSeq.continuous_inner_apply numberOpS

/-- `numberExp` is continuous on `S(ℕ)`, although it is not continuous on `ℓ²`
(`not_continuousAt_numberExp`). -/
theorem continuous_numberExp : Continuous fun x : S => numberExp (SchwartzSeq.toLp x) := by
  have h := Complex.continuous_re.comp continuous_inner_numberOpS
  simpa only [Function.comp_def, inner_numberOpS, Complex.ofReal_re] using h

/-- **Proposition 1, by the expected number.** `eʲ` has no limit in `S(ℕ)`: the limit would be
`|0⟩`, with `⟨0|N|0⟩ = 0`, while `⟨eʲ|N|eʲ⟩ = 1` for `j ≥ 1`. -/
theorem not_tendsto_eS_of_numberExp (g : S) : ¬ Tendsto eS atTop (𝓝 g) := fun h => by
  have hg : SchwartzSeq.toLp g = ground :=
    tendsto_nhds_unique ((SchwartzSeq.continuous_toLp.tendsto g).comp h) tendsto_toLp_eS
  have h0 := (continuous_numberExp.tendsto g).comp h
  simp only [hg, numberExp_ground] at h0
  have h1 : Tendsto ((fun x : S => numberExp (SchwartzSeq.toLp x)) ∘ eS) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun j hj => (numberExp_e hj).symm)
  exact one_ne_zero (tendsto_nhds_unique h1 h0)

/-! ### Polynomial observables -/

/-- The position `x̂ = (a + a†)/√2`, on `S(ℕ)`. -/
def positionS : S →L[ℂ] S := ((√2 : ℝ) : ℂ)⁻¹ • (annihilationS + creationS)

/-- The momentum `p̂ = i(a† − a)/√2`, on `S(ℕ)`. -/
def momentumS : S →L[ℂ] S := (Complex.I / ((√2 : ℝ) : ℂ)) • (creationS - annihilationS)

/-- The energy `N + 1/2` of the oscillator, on `S(ℕ)`. -/
def hamiltonianS : S →L[ℂ] S := numberOpS + (1 / 2 : ℂ) • 1

lemma annihilationS_mem_adjoin : annihilationS ∈ Algebra.adjoin ℂ {annihilationS, creationS} :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

lemma creationS_mem_adjoin : creationS ∈ Algebra.adjoin ℂ {annihilationS, creationS} :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

lemma positionS_mem_adjoin : positionS ∈ Algebra.adjoin ℂ {annihilationS, creationS} :=
  Subalgebra.smul_mem _ (add_mem annihilationS_mem_adjoin creationS_mem_adjoin) _

lemma momentumS_mem_adjoin : momentumS ∈ Algebra.adjoin ℂ {annihilationS, creationS} :=
  Subalgebra.smul_mem _ (sub_mem creationS_mem_adjoin annihilationS_mem_adjoin) _

lemma hamiltonianS_mem_adjoin : hamiltonianS ∈ Algebra.adjoin ℂ {annihilationS, creationS} := by
  refine add_mem ?_ (Subalgebra.smul_mem _ (one_mem _) _)
  rw [numberOpS_eq_comp]
  exact mul_mem creationS_mem_adjoin annihilationS_mem_adjoin

/-- **Polynomial observables have continuous expectations on `S(ℕ)`.** For every polynomial `T`
in `a` and `a†`, such as the powers of `x̂`, `p̂` and `N + 1/2`, the expectation `x ↦ ⟨x|T|x⟩` is
continuous on `S(ℕ)`. The polynomials are continuous linear endomorphisms of `S(ℕ)`, since `a`
and `a†` are. -/
theorem continuous_inner_of_mem_adjoin {T : S →L[ℂ] S}
    (_ : T ∈ Algebra.adjoin ℂ {annihilationS, creationS}) :
    Continuous fun x : S => ⟪SchwartzSeq.toLp x, SchwartzSeq.toLp (T x)⟫_ℂ :=
  SchwartzSeq.continuous_inner_apply T

end InconsistentConvergence
