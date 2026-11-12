/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import InconsistentConvergence
public import ForMathlib.Analysis.InnerProductSpace.l2Diagonal
public import ForMathlib.LinearAlgebra.LinearPMap

/-!
# Inconsistent convergence: the number operator

The main file of the brief writes the expected number `⟨x|N|x⟩` as the weighted sum
`numberExp x = ∑ n |xₙ|²`, defined on all of `ℓ²(ℕ)`. This module constructs the operators behind
it, as unbounded operators on their maximal domains, and shows that the weighted sum is the
expectation of `N` on its domain.

* The annihilation operator `a`, `(a x)ₙ = √(n + 1) xₙ₊₁`, on `D(a) = {x | (√n xₙ)ₙ ∈ ℓ²}`
  (`annihilation`), and the creation operator, `(a† y)ₙ₊₁ = √(n + 1) yₙ` and `(a† y)₀ = 0`, on
  `{y | (√(n + 1) yₙ)ₙ ∈ ℓ²}` (`creation`). On the eigenstates, `a |n + 1⟩ = √(n + 1) |n⟩`,
  `a |0⟩ = 0` and `a† |n⟩ = √(n + 1) |n + 1⟩`.
* The creation operator is the adjoint of the annihilation operator (`adjoint_annihilation`).
* The number operator `N`, `(N x)ₙ = n xₙ`, on `D(N) = {x | (n xₙ)ₙ ∈ ℓ²}` (`numberOp`), is
  self-adjoint (`isSelfAdjoint_numberOp`), with `N |n⟩ = n |n⟩` (`numberOp_level`).
* `N = a† a`, with the composition taken on its natural domain
  `{x ∈ D(a) | a x ∈ D(a†)}` (`numberOp_eq_adjoint_compMax`).
* On `D(N)`, `⟨x|N|x⟩ = numberExp x` (`inner_numberOp`), and on `D(a)`, the form domain,
  `numberExp x = ‖a x‖²` (`numberExp_eq_norm_sq`). The states `eʲ` of the brief lie in `D(N)`,
  with `⟨eʲ|N|eʲ⟩ = 1` for `j ≥ 1` (`inner_numberOp_e`).

The diagonal operator and its self-adjointness, and the composition on the natural domain, are
`lp.diagonal` and `LinearPMap.compMax` in `ForMathlib`.

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.
-/

open scoped InnerProductSpace ComplexConjugate LinearPMap

@[expose] public noncomputable section

namespace InconsistentConvergence

/-- `(f (n + 1))ₙ ∈ ℓ²` iff `f ∈ ℓ²`. -/
lemma memℓp_two_succ_iff {f : ℕ → ℂ} : Memℓp (fun n => f (n + 1)) 2 ↔ Memℓp f 2 := by
  simp only [memℓp_gen_iff (p := 2) (by norm_num)]
  exact summable_nat_add_iff (G := ℝ) (f := fun n => ‖f n‖ ^ (2 : ENNReal).toReal) 1

/-- Membership in `ℓ²` only depends on the norms of the entries. -/
lemma memℓp_two_congr_norm {f g : ℕ → ℂ} (h : ∀ n, ‖f n‖ = ‖g n‖) :
    Memℓp f 2 ↔ Memℓp g 2 :=
  ⟨fun hf => hf.mono' fun n => (h n).ge, fun hg => hg.mono' fun n => (h n).le⟩

lemma inner_level_right (f : H) (n : ℕ) : ⟪f, level n⟫_ℂ = conj (f n) := by
  rw [level, lp.inner_single_right]
  simp

/-! ### The number operator -/

/-- The number operator `N`, `(N x)ₙ = n xₙ`, on its maximal domain `{x | (n xₙ)ₙ ∈ ℓ²}`. -/
def numberOp : H →ₗ.[ℂ] H := lp.diagonal fun n : ℕ => (n : ℝ)

theorem mem_domain_numberOp {x : H} :
    x ∈ numberOp.domain ↔ Memℓp (fun n : ℕ => (n : ℂ) * x n) 2 := by
  rw [numberOp, lp.domain_diagonal, lp.mem_diagonalDomain]
  simp

theorem numberOp_apply (x : numberOp.domain) (n : ℕ) : numberOp x n = n * (x : H) n :=
  (lp.diagonal_apply _ x n).trans (by simp)

/-- `N` is self-adjoint. -/
theorem isSelfAdjoint_numberOp : IsSelfAdjoint numberOp := lp.isSelfAdjoint_diagonal _

lemma level_mem_domain_numberOp (n : ℕ) : level n ∈ numberOp.domain :=
  lp.single_mem_diagonalDomain _ n 1

/-- `N |n⟩ = n |n⟩`. -/
theorem numberOp_level (n : ℕ) :
    numberOp ⟨level n, level_mem_domain_numberOp n⟩ = (n : ℂ) • level n :=
  lp.ext <| funext fun m => by
    rw [numberOp_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, level_apply]
    split_ifs with h
    · rw [h]
    · simp

/-! ### The annihilation and creation operators -/

/-- The domain `D(a) = {x | (√n xₙ)ₙ ∈ ℓ²}` of the annihilation operator. -/
def annihilationDomain : Submodule ℂ H := lp.diagonalDomain fun n : ℕ => √(n : ℝ)

lemma mem_annihilationDomain {x : H} :
    x ∈ annihilationDomain ↔ Memℓp (fun n : ℕ => (√(n : ℝ) : ℂ) * x n) 2 :=
  memℓp_two_congr_norm fun n => by simp

lemma memℓp_annihilation {x : H} (hx : x ∈ annihilationDomain) :
    Memℓp (fun n : ℕ => (√((n : ℝ) + 1) : ℂ) * x (n + 1)) 2 :=
  (memℓp_two_congr_norm fun n => by simp).1 (memℓp_two_succ_iff.2 (mem_annihilationDomain.1 hx))

/-- The annihilation operator `a`, `(a x)ₙ = √(n + 1) xₙ₊₁`, on `D(a)`. -/
def annihilation : H →ₗ.[ℂ] H where
  domain := annihilationDomain
  toFun :=
    { toFun x := ⟨fun n => (√((n : ℝ) + 1) : ℂ) * x.1 (n + 1), memℓp_annihilation x.2⟩
      map_add' x y := lp.ext <| funext fun n => by simp [mul_add]; rfl
      map_smul' c x := lp.ext <| funext fun n => by simp [mul_left_comm] }

theorem annihilation_apply (x : annihilation.domain) (n : ℕ) :
    annihilation x n = (√((n : ℝ) + 1) : ℂ) * (x : H) (n + 1) :=
  rfl

/-- The domain `{y | (√(n + 1) yₙ)ₙ ∈ ℓ²}` of the creation operator. -/
def creationDomain : Submodule ℂ H := lp.diagonalDomain fun n : ℕ => √((n : ℝ) + 1)

lemma mem_creationDomain {y : H} :
    y ∈ creationDomain ↔ Memℓp (fun n : ℕ => (√((n : ℝ) + 1) : ℂ) * y n) 2 :=
  memℓp_two_congr_norm fun n => by simp

/-- The coordinates of `a† y`: `(a† y)₀ = 0` and `(a† y)ₙ₊₁ = √(n + 1) yₙ`. -/
def creationSeq (y : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => (√((n : ℝ) + 1) : ℂ) * y n

/-- The creation operator `a†`, `(a† y)₀ = 0` and `(a† y)ₙ₊₁ = √(n + 1) yₙ`, on its maximal
domain. -/
def creation : H →ₗ.[ℂ] H where
  domain := creationDomain
  toFun :=
    { toFun y := ⟨creationSeq y.1, memℓp_two_succ_iff.1 y.2⟩
      map_add' x y := lp.ext <| funext fun n => by
        change creationSeq (x.1 + y.1) n = creationSeq x.1 n + creationSeq y.1 n
        cases n <;> simp [creationSeq, mul_add]
      map_smul' c x := lp.ext <| funext fun n => by
        cases n <;> simp [creationSeq, mul_left_comm] }

theorem creation_apply_zero (y : creation.domain) : creation y 0 = 0 :=
  rfl

theorem creation_apply_succ (y : creation.domain) (n : ℕ) :
    creation y (n + 1) = (√((n : ℝ) + 1) : ℂ) * (y : H) n :=
  rfl

lemma level_mem_annihilationDomain (n : ℕ) : level n ∈ annihilation.domain :=
  lp.single_mem_diagonalDomain _ n 1

lemma level_mem_creationDomain (n : ℕ) : level n ∈ creation.domain :=
  lp.single_mem_diagonalDomain _ n 1

/-- `a |0⟩ = 0`. -/
theorem annihilation_level_zero : annihilation ⟨level 0, level_mem_annihilationDomain 0⟩ = 0 :=
  lp.ext <| funext fun m => by simp [annihilation_apply, level_apply]

/-- `a |n + 1⟩ = √(n + 1) |n⟩`. -/
theorem annihilation_level_succ (n : ℕ) :
    annihilation ⟨level (n + 1), level_mem_annihilationDomain (n + 1)⟩ =
      (√((n : ℝ) + 1) : ℂ) • level n :=
  lp.ext <| funext fun m => by
    simp only [annihilation_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, level_apply,
      add_left_inj]
    split_ifs with h
    · rw [h]
    · simp

/-- `a† |n⟩ = √(n + 1) |n + 1⟩`. -/
theorem creation_level (n : ℕ) :
    creation ⟨level n, level_mem_creationDomain n⟩ = (√((n : ℝ) + 1) : ℂ) • level (n + 1) :=
  lp.ext <| funext fun m => by
    cases m with
    | zero =>
      rw [creation_apply_zero, lp.coeFn_smul, Pi.smul_apply, level_apply]
      simp
    | succ m =>
      simp only [creation_apply_succ, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, level_apply,
        add_left_inj]
      split_ifs with h
      · rw [h]
      · simp

/-- `a†` is a formal adjoint of `a`: `⟪a x, y⟫ = ⟪x, a† y⟫`. -/
theorem isFormalAdjoint_annihilation_creation : annihilation.IsFormalAdjoint creation := by
  intro x y
  have hs := lp.summable_inner (𝕜 := ℂ) (x : H) (creation y)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, hs.tsum_eq_zero_add, creation_apply_zero,
    inner_zero_right, zero_add]
  congr 1
  funext n
  rw [annihilation_apply, creation_apply_succ]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-- **`a†` is the adjoint of `a`.** -/
theorem adjoint_annihilation : annihilation† = creation := by
  have hT : Dense (annihilation.domain : Set H) := lp.dense_diagonalDomain _
  refine le_antisymm ?_ (isFormalAdjoint_annihilation_creation.le_adjoint hT)
  -- Test `a†` against the eigenstates, which lie in `D(a)`.
  have key (y : annihilation†.domain) (n : ℕ) :
      (annihilation† y : H) n = creationSeq (y : H) n := by
    have h := (LinearPMap.adjoint_isFormalAdjoint hT) y ⟨level n, level_mem_annihilationDomain n⟩
    cases n with
    | zero =>
      rw [annihilation_level_zero, inner_zero_right] at h
      simpa [inner_level_right, creationSeq] using h
    | succ n =>
      rw [annihilation_level_succ, inner_smul_right] at h
      simp only [inner_level_right] at h
      simpa [creationSeq] using congrArg conj h
  have hdom (y : annihilation†.domain) : (y : H) ∈ creation.domain := by
    have := memℓp_two_succ_iff.2 (lp.memℓp (annihilation† y))
    simp only [key] at this
    exact this
  refine ⟨fun y hy => hdom ⟨y, hy⟩, fun y z hyz => lp.ext <| funext fun n => ?_⟩
  rw [key y n, hyz]
  rfl

/-! ### `N = a† a` and the expected number -/

/-- `N = a† a`, with the composition on its natural domain `{x ∈ D(a) | a x ∈ D(a†)}`. -/
theorem numberOp_eq_compMax : numberOp = creation.compMax annihilation := by
  have hsq (n : ℕ) : (√((n : ℝ) + 1) : ℂ) * (√((n : ℝ) + 1) : ℂ) = ((n + 1 : ℕ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast
    ring
  refine LinearPMap.ext (Submodule.ext fun x => ?_) fun x hx hx' => lp.ext <| funext fun n => ?_
  · rw [LinearPMap.mem_domain_compMax, mem_domain_numberOp]
    have hc (hx : x ∈ annihilation.domain) :
        annihilation ⟨x, hx⟩ ∈ creation.domain ↔
          Memℓp (fun n : ℕ => ((n + 1 : ℕ) : ℂ) * x (n + 1)) 2 := by
      rw [show creation.domain = creationDomain from rfl, mem_creationDomain]
      simp only [annihilation_apply, ← mul_assoc, hsq]
    constructor
    · intro hx
      have ha : x ∈ annihilation.domain := by
        refine mem_annihilationDomain.2 (hx.mono' fun n => ?_)
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_natCast,
          Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        gcongr
        rw [Real.sqrt_le_left (Nat.cast_nonneg n)]
        exact_mod_cast Nat.le_self_pow two_ne_zero n
      exact ⟨ha, (hc ha).2 ((memℓp_two_succ_iff (f := fun n : ℕ => (n : ℂ) * x n)).2 hx)⟩
    · rintro ⟨h1, h2⟩
      exact (memℓp_two_succ_iff (f := fun n : ℕ => (n : ℂ) * x n)).1 ((hc h1).1 h2)
  · rw [numberOp_apply, LinearPMap.compMax_apply]
    cases n with
    | zero => simp [creation_apply_zero]
    | succ n => rw [creation_apply_succ, annihilation_apply, ← mul_assoc, hsq]

/-- **`N = a† a`**, with `a†` the adjoint of `a`. -/
theorem numberOp_eq_adjoint_compMax : numberOp = annihilation†.compMax annihilation := by
  rw [adjoint_annihilation, numberOp_eq_compMax]

/-- **The expected number.** On `D(N)`, `⟨x|N|x⟩ = ∑ n |xₙ|² = numberExp x`. -/
theorem inner_numberOp (x : numberOp.domain) : ⟪(x : H), numberOp x⟫_ℂ = numberExp x := by
  rw [lp.inner_eq_tsum, numberExp, Complex.ofReal_tsum]
  congr 1
  funext n
  rw [numberOp_apply, RCLike.inner_apply', mul_left_comm, Complex.conj_mul', Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_natCast]

/-- On the form domain `D(a)`, `numberExp x = ‖a x‖²`. -/
theorem numberExp_eq_norm_sq (x : annihilation.domain) :
    numberExp x = ‖annihilation x‖ ^ 2 := by
  have hterm (n : ℕ) :
      ‖annihilation x n‖ ^ 2 = ((n + 1 : ℕ) : ℝ) * ‖(x : H) (n + 1)‖ ^ 2 := by
    rw [annihilation_apply, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  have hs : Summable fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ‖(x : H) (n + 1)‖ ^ 2 := by
    simp only [← hterm]
    simpa [Real.rpow_two] using
      (memℓp_gen_iff (p := 2) (by norm_num)).1 (lp.memℓp (annihilation x))
  rw [norm_sq_eq_tsum, numberExp, ((summable_nat_add_iff (G := ℝ) 1).1 hs).tsum_eq_zero_add]
  simp only [hterm, Nat.cast_zero, zero_mul, zero_add]

/-- The states `eʲ` lie in `D(N)`. -/
lemma e_mem_domain_numberOp (j : ℕ) : e j ∈ numberOp.domain :=
  add_mem (Submodule.smul_mem _ _ (level_mem_domain_numberOp 0))
    (Submodule.smul_mem _ _ (level_mem_domain_numberOp j))

/-- Eq. (4) for the operator `N`: `⟨eʲ|N|eʲ⟩ = 1` for `j ≥ 1`. -/
theorem inner_numberOp_e {j : ℕ} (hj : 1 ≤ j) :
    ⟪e j, numberOp ⟨e j, e_mem_domain_numberOp j⟩⟫_ℂ = 1 := by
  have h := inner_numberOp ⟨e j, e_mem_domain_numberOp j⟩
  rw [numberExp_e hj, Complex.ofReal_one] at h
  exact h

end InconsistentConvergence
