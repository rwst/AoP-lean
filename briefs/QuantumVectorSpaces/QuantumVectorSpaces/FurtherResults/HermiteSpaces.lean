/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.LocallyConvex.PowerSeriesSpace
public import ForMathlib.Order.GradedEnumeration

/-!
# Further results: spaces defined by Hermite coefficients remember the dimension

Not part of the brief. This file formalizes the Fréchet half of Sec. 5 of `further-results.tex`
in the brief's directory (R. Stephan, *Further results on the brief "Physical vector spaces for
quantum mechanics"*).

A function on `ℝⁿ` is described by its Hermite coefficients `c : (Fin n → ℕ) → 𝕜`. The Hermite
function `h_k` is an eigenvector of the number operator `N` with eigenvalue `|k| = ∑ i, k i`.
For an increasing `f : ℕ → ℝ`, `HermiteSpace 𝕜 r f n` is the space of coefficient families with
`(exp (t * f |k|) * c k)_k ∈ ℓ²` for every real `t < r`: the vectors in the domain of
`exp (t f(N))`. With `f d = d ^ (1 / (2μ))` and `r = ⊤` this is the Beurling-type Gelfand–Shilov
space `Σ^μ_μ(ℝⁿ)`; with `r = 0` it is the strong dual of `S^μ_μ(ℝⁿ)`. These identifications are
cited (Langenbruch; Gramchev–Pilipović–Rodino), not formalized; here the spaces are defined by
their coefficients.

Listing the multi-indices by increasing degree (`HermiteSpace.enum`) identifies
`HermiteSpace 𝕜 r f n` with the power series space `Λ_r(a)`, where `a j = f (level n j)` and
`level n j` is the `j`-th eigenvalue of `N`, counted with multiplicity. The classification of
power series spaces then decides when two such spaces are isomorphic. Counting multi-indices
gives `level n j ≍ j ^ (1 / n)`, and so for `f d = d ^ s`:

  `HermiteSpace 𝕜 r (· ^ s) n ≅ HermiteSpace 𝕜 r (· ^ s') m` if and only if `s / n = s' / m`.

In particular the spaces `Σ^μ_μ(ℝⁿ)` remember `μ n`, and for fixed `μ` they remember the number
of degrees of freedom `n`. The Schwartz spaces do not (`SchwartzMap.nonempty_schwartzEquiv`).

## Main definitions

* `HermiteSpace 𝕜 r f n`: coefficient families on `ℕⁿ` with `exp (t f(|k|)) c_k ∈ ℓ²`, `t < r`,
  with the topology of the seminorms `‖(exp (t f(|k|)) c_k)_k‖`.
* `HermiteSpace.level n j`: the `j`-th eigenvalue of the number operator on `ℝⁿ`.

## Main statements

* `HermiteSpace.toPowerSeriesSpace`: `HermiteSpace 𝕜 r f n ≅ Λ_r(f ∘ level n)`.
* `HermiteSpace.level_le`, `HermiteSpace.rpow_inv_le_level_add_one`: `level n j ≍ j ^ (1 / n)`.
* `HermiteSpace.nonempty_continuousLinearEquiv_iff`: the general criterion, for monotone
  nonnegative `f` and `g`.
* `HermiteSpace.nonempty_continuousLinearEquiv_rpow_iff`: for `f = (· ^ s)`, `g = (· ^ s')`,
  isomorphic if and only if `s / n = s' / m`.
* `HermiteSpace.nonempty_continuousLinearEquiv_rpow_iff_eq`: for fixed `s`, if and only if
  `n = m`.
* `HermiteSpace.nonempty_continuousLinearEquiv_gelfandShilov_iff`: for the Gelfand–Shilov
  exponents `s = 1 / (2μ)`, if and only if `μ n = ν m`.
-/

@[expose] public section

open Set Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumVectorSpaces.FurtherResults

namespace HermiteSpace

/-! ### Multi-indices by degree -/

/-- The degree `|k| = ∑ i, k i` of a multi-index, the eigenvalue of `h_k` under the number
operator. -/
def degree {n : ℕ} (k : Fin n → ℕ) : ℕ := ∑ i, k i

theorem le_degree {n : ℕ} (k : Fin n → ℕ) (i : Fin n) : k i ≤ degree k :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem finite_setOf_degree_le (n d : ℕ) : {k : Fin n → ℕ | degree k ≤ d}.Finite :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (d + 1)).finite_toSet.subset fun k hk =>
    Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_degree k i).trans hk)))

variable (n : ℕ) [NeZero n]

/-- An enumeration of the multi-indices on `ℕⁿ` by nondecreasing degree. -/
def enum : ℕ ≃ (Fin n → ℕ) :=
  (exists_equiv_nat_monotone (finite_setOf_degree_le n)).choose

/-- The `j`-th eigenvalue of the number operator on `ℝⁿ`, counted with multiplicity. -/
def level (j : ℕ) : ℕ := degree (enum n j)

theorem monotone_level : Monotone (level n) :=
  (exists_equiv_nat_monotone (finite_setOf_degree_le n)).choose_spec

/-- There are at most `(d + 1) ^ n` multi-indices of degree at most `d`, so
`j < (level n j + 1) ^ n`. -/
theorem succ_le_level_add_one_pow (j : ℕ) : j + 1 ≤ (level n j + 1) ^ n := by
  have h := succ_le_card_of_monotone (enum n) (monotone_level n)
    (s := Fintype.piFinset fun _ : Fin n => Finset.range (level n j + 1)) (j := j)
    fun k hk => Fintype.mem_piFinset.mpr fun i =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_degree k i).trans hk))
  simpa using h

/-- With `q = ⌈level n j / n⌉`, the `q ^ n` multi-indices with entries below `q` all have smaller
degree, so `q ^ n ≤ j`. -/
theorem exists_level_le_mul (j : ℕ) : ∃ q : ℕ, level n j ≤ n * q ∧ q ^ n ≤ j := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨D, hD⟩ : ∃ D, level n j = D := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, (D + n - 1) / n = q := ⟨_, rfl⟩
  have hdiv := Nat.div_add_mod (D + n - 1) n
  have hmod := Nat.mod_lt (D + n - 1) hn
  rw [hq] at hdiv
  generalize (D + n - 1) % n = rr at hdiv hmod
  generalize hP : n * q = P at hdiv
  refine ⟨q, by omega, ?_⟩
  have h := card_le_of_monotone (enum n) (monotone_level n)
    (s := Fintype.piFinset fun _ : Fin n => Finset.range q) (j := j) fun k hk => by
      rw [Fintype.mem_piFinset] at hk
      have hk' : ∀ i, k i ≤ q - 1 := fun i => by
        have := Finset.mem_range.mp (hk i); omega
      have hq1 : n ≤ P := hP ▸ Nat.le_mul_of_pos_right n
        (Nat.pos_of_ne_zero fun h0 => by simpa [h0] using hk ⟨0, hn⟩)
      have hle : degree k ≤ n * (q - 1) := by
        calc degree k ≤ ∑ _i : Fin n, (q - 1) := Finset.sum_le_sum fun i _ => hk' i
          _ = n * (q - 1) := by simp
      change degree k < level n j
      rw [Nat.mul_sub_one, hP] at hle
      omega
  simpa using h

/-- **Counting, upper bound:** `level n j ≤ n * j ^ (1 / n)`. -/
theorem level_le (j : ℕ) : (level n j : ℝ) ≤ n * (j : ℝ) ^ ((n : ℝ)⁻¹) := by
  obtain ⟨q, hq, hqj⟩ := exists_level_le_mul n j
  have hq' : (q : ℝ) ≤ (j : ℝ) ^ ((n : ℝ)⁻¹) := by
    rw [← Real.pow_rpow_inv_natCast (Nat.cast_nonneg q) (NeZero.ne n)]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqj) (by positivity)
  calc (level n j : ℝ) ≤ n * q := by exact_mod_cast hq
    _ ≤ n * (j : ℝ) ^ ((n : ℝ)⁻¹) := by gcongr

/-- **Counting, lower bound:** `j ^ (1 / n) ≤ level n j + 1`. -/
theorem rpow_inv_le_level_add_one (j : ℕ) : (j : ℝ) ^ ((n : ℝ)⁻¹) ≤ level n j + 1 := by
  rw [← Real.pow_rpow_inv_natCast (by positivity : (0 : ℝ) ≤ level n j + 1) (NeZero.ne n)]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  exact_mod_cast (Nat.le_succ j).trans (succ_le_level_add_one_pow n j)

/-! ### The coefficient spaces -/

variable (𝕜 : Type*) [RCLike 𝕜] (r : EReal) (f : ℕ → ℝ) (n : ℕ)

/-- The weighted family `k ↦ exp (t * f |k|) * c k`. -/
def weight (t : ℝ) (c : (Fin n → ℕ) → 𝕜) : (Fin n → ℕ) → 𝕜 :=
  fun k => (Real.exp (t * f (degree k)) : 𝕜) * c k

variable {𝕜 f n} in
theorem weight_add (t : ℝ) (c d : (Fin n → ℕ) → 𝕜) :
    weight 𝕜 f n t (c + d) = weight 𝕜 f n t c + weight 𝕜 f n t d :=
  funext fun _ => mul_add _ _ _

variable {𝕜 f n} in
theorem weight_smul (t : ℝ) (a : 𝕜) (c : (Fin n → ℕ) → 𝕜) :
    weight 𝕜 f n t (a • c) = a • weight 𝕜 f n t c :=
  funext fun _ => mul_left_comm _ _ _

/-- The coefficient families with `k ↦ exp (t * f |k|) * c k` in `ℓ²` for every real `t < r`. -/
def submodule : Submodule 𝕜 ((Fin n → ℕ) → 𝕜) where
  carrier := {c | ∀ t : ℝ, (t : EReal) < r → Memℓp (weight 𝕜 f n t c) 2}
  add_mem' hc hd t ht := by rw [weight_add]; exact (hc t ht).add (hd t ht)
  zero_mem' t _ := by
    rw [show weight 𝕜 f n t 0 = 0 from funext fun _ => mul_zero _]
    exact zero_memℓp
  smul_mem' a c hc t ht := by rw [weight_smul]; exact (hc t ht).const_smul a

end HermiteSpace

/-- The space of Hermite coefficient families `c` on `ℕⁿ` with `exp (t f(|k|)) c_k ∈ ℓ²` for all
real `t < r`, with the topology of the corresponding seminorms. -/
def HermiteSpace (𝕜 : Type*) [RCLike 𝕜] (r : EReal) (f : ℕ → ℝ) (n : ℕ) : Type _ :=
  HermiteSpace.submodule 𝕜 r f n

namespace HermiteSpace

open PowerSeriesSpace (Level)

variable {𝕜 : Type*} [RCLike 𝕜] {r : EReal} {f g : ℕ → ℝ} {n m : ℕ}

instance : AddCommGroup (HermiteSpace 𝕜 r f n) :=
  inferInstanceAs (AddCommGroup (submodule 𝕜 r f n))

instance : Module 𝕜 (HermiteSpace 𝕜 r f n) :=
  inferInstanceAs (Module 𝕜 (submodule 𝕜 r f n))

instance : CoeFun (HermiteSpace 𝕜 r f n) fun _ => (Fin n → ℕ) → 𝕜 :=
  ⟨fun c => (c : submodule 𝕜 r f n).1⟩

/-- Build an element of `HermiteSpace 𝕜 r f n` from a coefficient family. -/
def mk (c : (Fin n → ℕ) → 𝕜) (hc : c ∈ submodule 𝕜 r f n) : HermiteSpace 𝕜 r f n :=
  (⟨c, hc⟩ : submodule 𝕜 r f n)

@[simp] theorem coe_mk (c : (Fin n → ℕ) → 𝕜) (hc : c ∈ submodule 𝕜 r f n) : ⇑(mk c hc) = c :=
  rfl

theorem mem_submodule (c : HermiteSpace 𝕜 r f n) : ⇑c ∈ submodule 𝕜 r f n :=
  (c : submodule 𝕜 r f n).2

@[ext] theorem ext {c d : HermiteSpace 𝕜 r f n} (h : ⇑c = ⇑d) : c = d :=
  Subtype.ext h

variable (𝕜 r f n) in
/-- The map `c ↦ (exp (t * f |k|) * c k)_k` into `ℓ²(ℕⁿ)`. -/
def toL2 (t : Level r) : HermiteSpace 𝕜 r f n →ₗ[𝕜] lp (fun _ : Fin n → ℕ => 𝕜) 2 where
  toFun c := ⟨weight 𝕜 f n t c, (mem_submodule c) t t.2⟩
  map_add' _ _ := lp.ext (weight_add _ _ _)
  map_smul' _ _ := lp.ext (weight_smul _ _ _)

@[simp] theorem toL2_apply (t : Level r) (c : HermiteSpace 𝕜 r f n) (k : Fin n → ℕ) :
    toL2 𝕜 r f n t c k = (Real.exp (t * f (degree k)) : 𝕜) * c k := rfl

variable (𝕜 r f n) in
/-- The seminorm `|c|_t = (∑ k, ‖exp (t * f |k|) * c k‖ ^ 2) ^ (1 / 2)`. -/
def seminorm (t : Level r) : Seminorm 𝕜 (HermiteSpace 𝕜 r f n) :=
  (normSeminorm 𝕜 ↥(lp (fun _ : Fin n → ℕ => 𝕜) 2)).comp (toL2 𝕜 r f n t)

theorem seminorm_apply (t : Level r) (c : HermiteSpace 𝕜 r f n) :
    seminorm 𝕜 r f n t c = ‖toL2 𝕜 r f n t c‖ := rfl

instance : TopologicalSpace (HermiteSpace 𝕜 r f n) :=
  (show SeminormFamily 𝕜 (HermiteSpace 𝕜 r f n) (Level r) from
    seminorm 𝕜 r f n).moduleFilterBasis.topology

variable (𝕜 r f n) in
theorem withSeminorms : WithSeminorms (seminorm 𝕜 r f n) := ⟨rfl⟩

/-! ### Identification with a power series space -/

variable (f n) in
/-- The exponent sequence `j ↦ f (level n j)`. -/
def exponent [NeZero n] (j : ℕ) : ℝ := f (level n j)

variable [NeZero n]

theorem two_toReal_pos : 0 < (2 : ℝ≥0∞).toReal := by norm_num

theorem memℓp_comp_enum_iff {c : (Fin n → ℕ) → 𝕜} : Memℓp (c ∘ enum n) 2 ↔ Memℓp c 2 := by
  simp only [memℓp_gen_iff two_toReal_pos]
  exact (enum n).summable_iff (f := fun k => ‖c k‖ ^ (2 : ℝ≥0∞).toReal)

theorem norm_eq_of_comp_enum (x : lp (fun _ : ℕ => 𝕜) 2) (y : lp (fun _ : Fin n → ℕ => 𝕜) 2)
    (h : ∀ j, x j = y (enum n j)) : ‖x‖ = ‖y‖ := by
  rw [lp.norm_eq_tsum_rpow two_toReal_pos, lp.norm_eq_tsum_rpow two_toReal_pos]
  simp only [h]
  rw [(enum n).tsum_eq (fun k => ‖y k‖ ^ (2 : ℝ≥0∞).toReal)]

variable (𝕜 r f n) in
/-- Relabelling by `enum n`, as a linear equivalence. -/
def toPowerSeriesSpaceₗ :
    HermiteSpace 𝕜 r f n ≃ₗ[𝕜] PowerSeriesSpace 𝕜 r (exponent f n) where
  toFun c := PowerSeriesSpace.mk (c ∘ enum n) fun t ht =>
    (memℓp_comp_enum_iff (c := weight 𝕜 f n t c)).mpr (mem_submodule c t ht)
  invFun x := mk (x ∘ (enum n).symm) fun t ht => by
    rw [← memℓp_comp_enum_iff]
    have : weight 𝕜 f n t (x ∘ (enum n).symm) ∘ enum n =
        PowerSeriesSpace.weight 𝕜 (exponent f n) t x := funext fun j => by
      simp only [Function.comp_apply, weight, PowerSeriesSpace.weight, Equiv.symm_apply_apply,
        exponent, level]
    rw [this]
    exact PowerSeriesSpace.mem_submodule x t ht
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv c := ext (funext fun k => congrArg c ((enum n).apply_symm_apply k))
  right_inv x := PowerSeriesSpace.ext (funext fun j => congrArg x ((enum n).symm_apply_apply j))

@[simp] theorem toPowerSeriesSpaceₗ_apply (c : HermiteSpace 𝕜 r f n) (j : ℕ) :
    toPowerSeriesSpaceₗ 𝕜 r f n c j = c (enum n j) := rfl

theorem seminorm_toPowerSeriesSpaceₗ (t : Level r) (c : HermiteSpace 𝕜 r f n) :
    PowerSeriesSpace.seminorm 𝕜 r (exponent f n) t (toPowerSeriesSpaceₗ 𝕜 r f n c) =
      seminorm 𝕜 r f n t c :=
  norm_eq_of_comp_enum _ _ fun _ => rfl

theorem continuous_of_seminorm_le {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
    {p : SeminormFamily 𝕜 E (Level r)} {q : SeminormFamily 𝕜 F (Level r)}
    (hp : WithSeminorms p) (hq : WithSeminorms q) (L : E →ₗ[𝕜] F)
    (hL : ∀ t x, q t (L x) ≤ p t x) : Continuous L :=
  WithSeminorms.continuous_of_isBounded hp hq L
    (Seminorm.IsBounded.of_real fun t => ⟨{t}, 1, fun x => by simpa using hL t x⟩)

variable (𝕜 r f n) in
/-- **`HermiteSpace 𝕜 r f n` is the power series space `Λ_r(f ∘ level n)`**, by relabelling the
multi-indices in order of degree. The relabelling preserves every seminorm. -/
def toPowerSeriesSpace :
    HermiteSpace 𝕜 r f n ≃L[𝕜] PowerSeriesSpace 𝕜 r (exponent f n) where
  toLinearEquiv := toPowerSeriesSpaceₗ 𝕜 r f n
  continuous_toFun := continuous_of_seminorm_le (withSeminorms 𝕜 r f n)
    (PowerSeriesSpace.withSeminorms 𝕜 r _) (toPowerSeriesSpaceₗ 𝕜 r f n).toLinearMap
    fun t c => (seminorm_toPowerSeriesSpaceₗ t c).le
  continuous_invFun := continuous_of_seminorm_le (PowerSeriesSpace.withSeminorms 𝕜 r _)
    (withSeminorms 𝕜 r f n) (toPowerSeriesSpaceₗ 𝕜 r f n).symm.toLinearMap
    fun t x => le_of_eq (by
      rw [LinearEquiv.coe_coe, ← seminorm_toPowerSeriesSpaceₗ t, LinearEquiv.apply_symm_apply])

/-! ### Classification -/

/-- `a` is bounded by a positive multiple of `b` plus a constant. -/
def Dominated (a b : ℕ → ℝ) : Prop := ∃ C > 0, ∃ D, ∀ j, a j ≤ C * b j + D

theorem Dominated.trans {a b c : ℕ → ℝ} (hab : Dominated a b) (hbc : Dominated b c) :
    Dominated a c := by
  obtain ⟨C, hC, D, h⟩ := hab
  obtain ⟨C', hC', D', h'⟩ := hbc
  refine ⟨C * C', mul_pos hC hC', C * D' + D, fun j => ?_⟩
  nlinarith [h j, h' j]

theorem Dominated.of_le {a b : ℕ → ℝ} {C D : ℝ} (hC : 0 < C) (h : ∀ j, a j ≤ C * b j + D) :
    Dominated a b :=
  ⟨C, hC, D, h⟩

/-- **The general criterion.** For monotone nonnegative `f` and `g`, the spaces
`HermiteSpace 𝕜 r f n` and `HermiteSpace 𝕜 r g m`, of finite (`r = 0`) or infinite (`r = ⊤`) type,
are isomorphic if and only if `f ∘ level n` and `g ∘ level m` dominate each other. -/
theorem nonempty_continuousLinearEquiv_iff [NeZero m] (hr : r = 0 ∨ r = ⊤) (hf : Monotone f)
    (hf0 : 0 ≤ f) (hg : Monotone g) (hg0 : 0 ≤ g) :
    Nonempty (HermiteSpace 𝕜 r f n ≃L[𝕜] HermiteSpace 𝕜 r g m) ↔
      Dominated (exponent f n) (exponent g m) ∧ Dominated (exponent g m) (exponent f n) := by
  have e : Nonempty (HermiteSpace 𝕜 r f n ≃L[𝕜] HermiteSpace 𝕜 r g m) ↔
      Nonempty (PowerSeriesSpace 𝕜 r (exponent f n) ≃L[𝕜]
        PowerSeriesSpace 𝕜 r (exponent g m)) :=
    ⟨fun ⟨T⟩ => ⟨((toPowerSeriesSpace 𝕜 r f n).symm.trans T).trans
        (toPowerSeriesSpace 𝕜 r g m)⟩,
      fun ⟨T⟩ => ⟨((toPowerSeriesSpace 𝕜 r f n).trans T).trans
        (toPowerSeriesSpace 𝕜 r g m).symm⟩⟩
  have ha : Monotone (exponent f n) := hf.comp (monotone_level n)
  have hb : Monotone (exponent g m) := hg.comp (monotone_level m)
  rw [e]
  rcases hr with rfl | rfl
  · exact PowerSeriesSpace.nonempty_continuousLinearEquiv_iff_zero ha
      (fun j => hf0 (level n j)) hb (fun j => hg0 (level m j))
  · exact PowerSeriesSpace.nonempty_continuousLinearEquiv_iff_top ha
      (fun j => hf0 (level n j)) hb (fun j => hg0 (level m j))

/-! ### Power exponents -/

variable (n) in
/-- `level n j ^ s ≤ n ^ s * j ^ (s / n)`. -/
theorem rpow_level_le {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    (level n j : ℝ) ^ s ≤ (n : ℝ) ^ s * (j : ℝ) ^ (s / n) := by
  calc (level n j : ℝ) ^ s ≤ (n * (j : ℝ) ^ ((n : ℝ)⁻¹)) ^ s :=
        Real.rpow_le_rpow (by positivity) (level_le n j) hs
    _ = (n : ℝ) ^ s * (j : ℝ) ^ (s / n) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
          inv_mul_eq_div]

variable (n) in
/-- `j ^ (s / n) ≤ 2 ^ s * level n j ^ s + 2 ^ s`. -/
theorem rpow_le_rpow_level {s : ℝ} (hs : 0 ≤ s) (j : ℕ) :
    (j : ℝ) ^ (s / n) ≤ 2 ^ s * (level n j : ℝ) ^ s + 2 ^ s := by
  have h1 : (j : ℝ) ^ (s / n) ≤ ((level n j : ℝ) + 1) ^ s := by
    rw [← inv_mul_eq_div, Real.rpow_mul (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (rpow_inv_le_level_add_one n j) hs
  refine h1.trans ?_
  rcases Nat.eq_zero_or_pos (level n j) with h0 | hpos
  · rw [h0, Nat.cast_zero, zero_add, Real.one_rpow]
    have : (1 : ℝ) ≤ 2 ^ s := Real.one_le_rpow (by norm_num) hs
    have : (0 : ℝ) ≤ 2 ^ s * (0 : ℝ) ^ s := by positivity
    linarith
  · have hle : (level n j : ℝ) + 1 ≤ 2 * level n j := by
      have : (1 : ℝ) ≤ level n j := by exact_mod_cast hpos
      linarith
    calc ((level n j : ℝ) + 1) ^ s ≤ (2 * (level n j : ℝ)) ^ s :=
          Real.rpow_le_rpow (by positivity) hle hs
      _ = 2 ^ s * (level n j : ℝ) ^ s := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 ^ s * (level n j : ℝ) ^ s + 2 ^ s := le_add_of_nonneg_right (by positivity)

/-- If `j ^ α ≤ C * j ^ β + D` for all `j`, with `β ≥ 0`, then `α ≤ β`. -/
theorem le_of_dominated_rpow {α β : ℝ} (hβ : 0 ≤ β)
    (h : Dominated (fun j => (j : ℝ) ^ α) (fun j => (j : ℝ) ^ β)) : α ≤ β := by
  by_contra hlt
  push Not at hlt
  obtain ⟨C, hC, D, h⟩ := h
  have ht : Tendsto (fun j : ℕ => (j : ℝ) ^ (α - β)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hlt)).comp tendsto_natCast_atTop_atTop
  obtain ⟨j, hj, hj1⟩ := ((ht.eventually_gt_atTop (C + |D|)).and (eventually_ge_atTop 1)).exists
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have hβ1 : (1 : ℝ) ≤ (j : ℝ) ^ β := Real.one_le_rpow (by exact_mod_cast hj1) hβ
  have hsplit : (j : ℝ) ^ α = (j : ℝ) ^ (α - β) * (j : ℝ) ^ β := by
    rw [← Real.rpow_add hjpos, sub_add_cancel]
  have := h j
  simp only at this
  rw [hsplit] at this
  nlinarith [le_abs_self D, abs_nonneg D]

variable (n) in
theorem dominated_rpow_exponent {s : ℝ} (hs : 0 ≤ s) :
    Dominated (fun j => (j : ℝ) ^ (s / n)) (exponent (fun d => (d : ℝ) ^ s) n) :=
  ⟨2 ^ s, by positivity, 2 ^ s, fun j => by simpa [exponent] using rpow_le_rpow_level n hs j⟩

variable (n) in
theorem dominated_exponent_rpow {s : ℝ} (hs : 0 ≤ s) :
    Dominated (exponent (fun d => (d : ℝ) ^ s) n) (fun j => (j : ℝ) ^ (s / n)) :=
  ⟨(n : ℝ) ^ s, Real.rpow_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos n)) s, 0,
    fun j => by simpa [exponent] using rpow_level_le n hs j⟩

theorem div_le_div_of_dominated_exponent [NeZero m] {s s' : ℝ} (hs : 0 ≤ s) (hs' : 0 ≤ s')
    (h : Dominated (exponent (fun d => (d : ℝ) ^ s) n) (exponent (fun d => (d : ℝ) ^ s') m)) :
    s / n ≤ s' / m :=
  le_of_dominated_rpow (by positivity) <|
    (dominated_rpow_exponent n hs).trans (h.trans (dominated_exponent_rpow m hs'))

/-- **Power exponents.** For `s, s' > 0`, `HermiteSpace 𝕜 r (· ^ s) n` and
`HermiteSpace 𝕜 r (· ^ s') m` are isomorphic if and only if `s / n = s' / m`. -/
theorem nonempty_continuousLinearEquiv_rpow_iff [NeZero m] (hr : r = 0 ∨ r = ⊤) {s s' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') :
    Nonempty (HermiteSpace 𝕜 r (fun d => (d : ℝ) ^ s) n ≃L[𝕜]
      HermiteSpace 𝕜 r (fun d => (d : ℝ) ^ s') m) ↔ s / n = s' / m := by
  have hmono : ∀ {s : ℝ}, 0 < s → Monotone fun d : ℕ => (d : ℝ) ^ s := fun hs _ _ h =>
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) hs.le
  rw [nonempty_continuousLinearEquiv_iff hr (hmono hs) (fun _ => by positivity) (hmono hs')
    (fun _ => by positivity)]
  refine ⟨fun ⟨h, h'⟩ => (div_le_div_of_dominated_exponent hs.le hs'.le h).antisymm
    (div_le_div_of_dominated_exponent hs'.le hs.le h'), fun h => ⟨?_, ?_⟩⟩
  · exact (dominated_exponent_rpow n hs.le).trans (h ▸ dominated_rpow_exponent m hs'.le)
  · exact (dominated_exponent_rpow m hs'.le).trans (h ▸ dominated_rpow_exponent n hs.le)

/-- **The coefficient spaces remember the number of degrees of freedom.** For fixed `s > 0`,
`HermiteSpace 𝕜 r (· ^ s) n ≅ HermiteSpace 𝕜 r (· ^ s) m` if and only if `n = m`. -/
theorem nonempty_continuousLinearEquiv_rpow_iff_eq [NeZero m] (hr : r = 0 ∨ r = ⊤) {s : ℝ}
    (hs : 0 < s) :
    Nonempty (HermiteSpace 𝕜 r (fun d => (d : ℝ) ^ s) n ≃L[𝕜]
      HermiteSpace 𝕜 r (fun d => (d : ℝ) ^ s) m) ↔ n = m := by
  rw [nonempty_continuousLinearEquiv_rpow_iff hr hs hs]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  constructor
  · intro h
    rw [div_eq_div_iff hn hm] at h
    exact_mod_cast (mul_left_cancel₀ hs.ne' h).symm
  · rintro rfl; rfl

/-- **Gelfand–Shilov exponents.** With `f d = d ^ (1 / (2μ))`, the spaces for `(μ, n)` and
`(ν, m)` are isomorphic if and only if `μ n = ν m`. For `r = ⊤` these are the coefficient spaces
of `Σ^μ_μ(ℝⁿ)`; for `r = 0`, of the strong dual of `S^μ_μ(ℝⁿ)`. -/
theorem nonempty_continuousLinearEquiv_gelfandShilov_iff [NeZero m] (hr : r = 0 ∨ r = ⊤)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    Nonempty (HermiteSpace 𝕜 r (fun d => (d : ℝ) ^ (1 / (2 * μ))) n ≃L[𝕜]
      HermiteSpace 𝕜 r (fun d => (d : ℝ) ^ (1 / (2 * ν))) m) ↔ μ * n = ν * m := by
  rw [nonempty_continuousLinearEquiv_rpow_iff hr (by positivity) (by positivity)]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [div_div, div_div, div_eq_div_iff (by positivity) (by positivity)]
  constructor <;> intro h <;> linarith

end HermiteSpace

end QuantumVectorSpaces.FurtherResults

end
