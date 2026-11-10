/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Diagonal operators on `ℓ²`

For a real sequence `a : ι → ℝ`, the diagonal operator `x ↦ (a i * x i)ᵢ` on `ℓ²(ι, 𝕜)` is
defined on its maximal domain `{x | (a i * x i)ᵢ ∈ ℓ²}`. This file shows that it is a
densely defined self-adjoint operator, unbounded when `a` is.

## Main definitions

* `lp.diagonalDomain a`: the maximal domain;
* `lp.diagonal a`: the diagonal operator, as a partially defined linear map.

## Main results

* `lp.dense_diagonalDomain`: the domain contains the finitely supported sequences and is dense;
* `lp.isSelfAdjoint_diagonal`: the diagonal operator is self-adjoint;
* `lp.le_diagonal`, `lp.eq_diagonal`: every symmetric operator with the basis vectors as
  eigenvectors, with eigenvalues `a i`, is a restriction of it, and every self-adjoint one is it;
* `lp.exists_lt_norm_diagonal`: it is unbounded when `|a|` is.
-/

open scoped InnerProductSpace ComplexConjugate LinearPMap lp

@[expose] public noncomputable section

namespace lp

variable {ι 𝕜 : Type*} [RCLike 𝕜] (a : ι → ℝ)

/-- The maximal domain of the diagonal operator with entries `a`. -/
def diagonalDomain : Submodule 𝕜 ℓ²(ι, 𝕜) where
  carrier := {x | Memℓp (fun i => (a i : 𝕜) * x i) 2}
  add_mem' {x y} hx hy := by
    show Memℓp _ 2
    convert hx.add hy using 1
    funext i
    simp [mul_add]
  zero_mem' := by
    show Memℓp _ 2
    convert (zero_memℓp : Memℓp (0 : ι → 𝕜) 2) using 1
    funext i
    simp
  smul_mem' c x hx := by
    show Memℓp _ 2
    convert hx.const_smul c using 1
    funext i
    simp [mul_left_comm]

lemma mem_diagonalDomain {x : ℓ²(ι, 𝕜)} :
    x ∈ diagonalDomain a ↔ Memℓp (fun i => (a i : 𝕜) * x i) 2 :=
  Iff.rfl

/-- The diagonal operator `x ↦ (a i * x i)ᵢ` on its maximal domain. -/
def diagonal : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜) where
  domain := diagonalDomain a
  toFun :=
    { toFun x := ⟨fun i => (a i : 𝕜) * x.1 i, x.2⟩
      map_add' x y := lp.ext <| funext fun i => by simp [mul_add]; rfl
      map_smul' c x := lp.ext <| funext fun i => by simp [mul_left_comm] }

lemma domain_diagonal : (diagonal a : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜)).domain = diagonalDomain a :=
  rfl

@[simp]
lemma diagonal_apply (x : (diagonal a : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜)).domain) (i : ι) :
    diagonal a x i = a i * (x : ℓ²(ι, 𝕜)) i :=
  rfl

variable [DecidableEq ι]

lemma mul_single (i : ι) (c : 𝕜) :
    (fun j => (a j : 𝕜) * (lp.single 2 i c : ℓ²(ι, 𝕜)) j) = lp.single 2 i ((a i : 𝕜) * c) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma single_mem_diagonalDomain (i : ι) (c : 𝕜) : lp.single 2 i c ∈ diagonalDomain a := by
  rw [mem_diagonalDomain, mul_single]
  exact lp.memℓp _

lemma diagonal_single (i : ι) (c : 𝕜) :
    diagonal a ⟨lp.single 2 i c, single_mem_diagonalDomain a i c⟩ =
      lp.single 2 i ((a i : 𝕜) * c) :=
  lp.ext (mul_single a i c)

omit [DecidableEq ι] in
/-- The domain is dense: it contains the finite partial sums of every `x ∈ ℓ²`. -/
theorem dense_diagonalDomain : Dense (diagonalDomain (𝕜 := 𝕜) a : Set ℓ²(ι, 𝕜)) := by
  classical
  refine fun x => mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
    (Filter.Eventually.of_forall fun s => ?_)
  exact Submodule.sum_mem _ fun i _ => single_mem_diagonalDomain a i _

omit [DecidableEq ι] in
/-- The diagonal operator with real entries is symmetric. -/
theorem isFormalAdjoint_diagonal :
    (diagonal a : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜)).IsFormalAdjoint (diagonal a) := fun x y => by
  simp only [lp.inner_eq_tsum, diagonal_apply]
  congr 1
  funext i
  simp only [RCLike.inner_apply', map_mul, RCLike.conj_ofReal]
  ring

omit [DecidableEq ι] in
/-- The diagonal operator with real entries is self-adjoint on its maximal domain. -/
theorem isSelfAdjoint_diagonal :
    IsSelfAdjoint (diagonal a : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜)) := by
  classical
  set T : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜) := diagonal a
  have hT : Dense (T.domain : Set ℓ²(ι, 𝕜)) := dense_diagonalDomain a
  have hsym : T.IsFormalAdjoint T := isFormalAdjoint_diagonal a
  -- `T† ≤ T`: test `T†` against the basis vectors, which lie in `D(T)`.
  have hle : T† ≤ T := by
    have key (y : T†.domain) (i : ι) : (T† y : ℓ²(ι, 𝕜)) i = a i * (y : ℓ²(ι, 𝕜)) i := by
      have h := (LinearPMap.adjoint_isFormalAdjoint hT).symm
        ⟨lp.single 2 i 1, single_mem_diagonalDomain a i 1⟩ y
      rw [show T ⟨lp.single 2 i 1, _⟩ = lp.single 2 i ((a i : 𝕜) * 1) from
        diagonal_single a i 1, lp.inner_single_left, lp.inner_single_left,
        RCLike.inner_apply', RCLike.inner_apply'] at h
      simpa using h.symm
    have hdom (y : T†.domain) : (y : ℓ²(ι, 𝕜)) ∈ T.domain := by
      rw [show T.domain = diagonalDomain a from rfl, mem_diagonalDomain]
      simpa [← key y] using lp.memℓp (T† y)
    refine ⟨fun y hy => hdom ⟨y, hy⟩, fun y z hyz => lp.ext <| funext fun i => ?_⟩
    rw [key y i, hyz]
    rfl
  exact LinearPMap.isSelfAdjoint_def.mpr (le_antisymm hle (hsym.le_adjoint hT))

/-- A symmetric operator that has each basis vector `lp.single 2 i 1` as an eigenvector, with
eigenvalue `a i`, is a restriction of `diagonal a`. -/
theorem le_diagonal {T : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜)} (hT : T.IsFormalAdjoint T)
    (h : ∀ i, ∃ hi : lp.single 2 i (1 : 𝕜) ∈ T.domain,
      T ⟨_, hi⟩ = (a i : 𝕜) • lp.single 2 i (1 : 𝕜)) :
    T ≤ diagonal a := by
  have key (y : T.domain) (i : ι) : (T y : ℓ²(ι, 𝕜)) i = a i * (y : ℓ²(ι, 𝕜)) i := by
    obtain ⟨hi, he⟩ := h i
    have h' := hT ⟨_, hi⟩ y
    rw [he, ← lp.single_smul, lp.inner_single_left, lp.inner_single_left,
      RCLike.inner_apply', RCLike.inner_apply'] at h'
    simpa using h'.symm
  have hdom (y : T.domain) : (y : ℓ²(ι, 𝕜)) ∈ diagonalDomain a := by
    rw [mem_diagonalDomain]
    simpa [← key y] using lp.memℓp (T y)
  refine ⟨fun y hy => hdom ⟨y, hy⟩, fun y z hyz => lp.ext <| funext fun i => ?_⟩
  rw [key y i, hyz]
  rfl

/-- A self-adjoint operator that has each basis vector `lp.single 2 i 1` as an eigenvector, with
eigenvalue `a i`, is `diagonal a`. -/
theorem eq_diagonal {T : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜)} (hT : IsSelfAdjoint T)
    (h : ∀ i, ∃ hi : lp.single 2 i (1 : 𝕜) ∈ T.domain,
      T ⟨_, hi⟩ = (a i : 𝕜) • lp.single 2 i (1 : 𝕜)) :
    T = diagonal a := by
  have hsym := LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hT] at hsym
  have hle := le_diagonal a hsym h
  -- `D(diagonal a) ⊆ D(T†) = D(T)`, tested against `T ≤ diagonal a`.
  refine LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 fun x hx => ?_)
  rw [← LinearPMap.isSelfAdjoint_def.mp hT]
  refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨diagonal a ⟨x, hx⟩, fun y => ?_⟩
  rw [hle.2 (y := ⟨y, hle.1 y.2⟩) rfl]
  exact isFormalAdjoint_diagonal a ⟨x, hx⟩ ⟨y, hle.1 y.2⟩

/-- The diagonal operator is unbounded on its domain when `|a|` is unbounded. -/
theorem exists_lt_norm_diagonal (ha : ¬ BddAbove (Set.range fun i => |a i|)) (C : ℝ) :
    ∃ x : (diagonal a : ℓ²(ι, 𝕜) →ₗ.[𝕜] ℓ²(ι, 𝕜)).domain,
      C * ‖(x : ℓ²(ι, 𝕜))‖ < ‖diagonal a x‖ := by
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := not_bddAbove_iff.mp ha C
  refine ⟨⟨lp.single 2 i 1, single_mem_diagonalDomain a i 1⟩, ?_⟩
  rw [diagonal_single, lp.norm_single (by norm_num), lp.norm_single (by norm_num)]
  simpa using hi

end lp
