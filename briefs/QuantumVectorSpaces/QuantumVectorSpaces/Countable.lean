/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces
public import ForMathlib.Analysis.LocallyConvex.FirstCountable
public import Mathlib.Data.Finsupp.Pointwise

/-!
# A countable generating set of observables

The brief claims (Sec. 5, "Number of defining observables") that "separability/second
countability would allow us to find a countable subset of observables from a bigger set that
generates the same topology". This file proves the claim for first countability, which second
countability implies, and refutes it for separability.

## Main results

* `firstCountableTopology_topology`  with countably many observables, `V` is first countable;
* `exists_countable_topology_eq_iff`  a countable subfamily of the observables generates the
  topology if and only if the topology is first countable;
* `IsQuantumVectorSpace.exists_countable`  every quantum vector space is one with countably many
  defining observables, closed under the commutation relations;
* `Diagonal.separableSpace`, `Diagonal.not_exists_countable`  the space of finitely supported
  sequences, with every real multiplication operator as a defining observable, is separable, but
  no countable subfamily of the observables generates its topology.
-/

open Topology Filter
open scoped NNReal ComplexConjugate

@[expose] public noncomputable section

namespace QuantumVectorSpaces

section Countable

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : PreInnerProductSpace.Core ℂ V)
  {ι : Type*} (X : ι → Module.End ℂ V)

/-- With countably many defining observables, the topology is first countable. -/
theorem firstCountableTopology_topology [Countable ι] :
    @FirstCountableTopology V (topology c X) := by
  let := topology c X
  have : Countable (FreeMonoid ι) := .of_equiv _ (FreeMonoid.toListEquiv (α := ι)).symm
  exact (withSeminorms_word c X).firstCountableTopology

/-- Fewer defining observables give a coarser topology. (In Mathlib's order on topologies,
coarser is larger.) -/
theorem topology_le_of_range_subset {κ : Type*} (Y : κ → Module.End ℂ V)
    (h : Set.range Y ⊆ Set.range X) : topology c X ≤ topology c Y := by
  refine (isGreatest_topology c Y).2 ?_
  have ht := isAdmissible_topology c X
  refine ⟨ht.isTopologicalAddGroup, ht.continuousSMul, fun k => ?_, ht.continuous_inner⟩
  obtain ⟨i, hi⟩ := h ⟨k, rfl⟩
  rw [← hi]
  exact ht.continuous_obs i

/-- A product of observables whose indices lie in `J` is in the algebra of the subfamily on
`J`. -/
lemma lift_mem_algebra {J : Set ι} {w : FreeMonoid ι} (hw : ∀ i ∈ w.toList, i ∈ J) :
    FreeMonoid.lift X w ∈ algebra fun j : J => X j := by
  rw [FreeMonoid.lift_apply]
  refine Subalgebra.list_prod_mem _ fun A hA => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hA
  exact Algebra.subset_adjoin ⟨⟨i, hw i hi⟩, rfl⟩

/-- If the topology is first countable, then a countable subfamily of the defining observables
generates it. -/
theorem exists_countable_topology_eq [h : @FirstCountableTopology V (topology c X)] :
    ∃ J : Set ι, J.Countable ∧ topology c (fun j : J => X j) = topology c X := by
  let := topology c X
  obtain ⟨W, hWc, hW⟩ := (withSeminorms_word c X).exists_countable
  let J : Set ι := ⋃ w ∈ W, {i | i ∈ FreeMonoid.toList w}
  refine ⟨J, hWc.biUnion fun w _ => (FreeMonoid.toList w).finite_toSet.countable, ?_⟩
  refine le_antisymm ?_ (topology_le_of_range_subset c X _ (Set.range_comp_subset_range _ X))
  rw [← continuous_id_iff_le]
  let := topology c fun j : J => X j
  have := (withSeminorms c fun j : J => X j).isTopologicalAddGroup
  refine @WithSeminorms.continuous_of_continuous_comp ℂ ℂ V V _ _ _ _ _ _ _ _ _ _
    (topology c fun j : J => X j) _ (topology c X) hW LinearMap.id fun w => ?_
  have hw : ∀ i ∈ FreeMonoid.toList w.1, i ∈ J := fun i hi =>
    Set.mem_biUnion w.2 hi
  exact (withSeminorms c fun j : J => X j).continuous_seminorm ⟨_, lift_mem_algebra X hw⟩

/-- A countable subfamily of the defining observables generates the topology if and only if the
topology is first countable. -/
theorem exists_countable_topology_eq_iff :
    (∃ J : Set ι, J.Countable ∧ topology c (fun j : J => X j) = topology c X) ↔
      @FirstCountableTopology V (topology c X) := by
  constructor
  · rintro ⟨J, hJ, h⟩
    have := hJ.to_subtype
    exact h ▸ firstCountableTopology_topology c fun j : J => X j
  · intro h
    exact exists_countable_topology_eq c X

/-- Two families of observables with the same topology have the same uniform structure. -/
lemma uniformSpace_congr {κ : Type*} {Y : κ → Module.End ℂ V} (h : topology c Y = topology c X) :
    uniformSpace c Y = uniformSpace c X := by
  have key : ∀ (t t' : TopologicalSpace V), t = t' → ∀ (h₁ : @IsTopologicalAddGroup V t _)
      (h₂ : @IsTopologicalAddGroup V t' _), @IsTopologicalAddGroup.rightUniformSpace V _ t h₁ =
        @IsTopologicalAddGroup.rightUniformSpace V _ t' h₂ := by
    rintro t _ rfl _ _
    rfl
  exact key _ _ h _ _

/-- The sets obtained from `J` by adding, `n` times, the supports of the structure constants of
pairs of indices already present. -/
def supportClosure (C : ι → ι → ι →₀ ℂ) (J : Set ι) : ℕ → Set ι
  | 0 => J
  | n + 1 => supportClosure C J n ∪
      ⋃ i ∈ supportClosure C J n, ⋃ j ∈ supportClosure C J n, ((C i j).support : Set ι)

lemma supportClosure_countable (C : ι → ι → ι →₀ ℂ) {J : Set ι} (hJ : J.Countable) (n : ℕ) :
    (supportClosure C J n).Countable := by
  induction n with
  | zero => exact hJ
  | succ n ih =>
    exact ih.union (ih.biUnion fun i _ => ih.biUnion fun j _ => (C i j).support.countable_toSet)

lemma monotone_supportClosure (C : ι → ι → ι →₀ ℂ) (J : Set ι) :
    Monotone (supportClosure C J) :=
  monotone_nat_of_le_succ fun _ => Set.subset_union_left

/-- Every quantum vector space is one with countably many defining observables: a countable
subfamily, closed under the commutation relations, has the same topology. -/
theorem IsQuantumVectorSpace.exists_countable {ħ : ℝ} {C : ι → ι → ι →₀ ℂ}
    (hQ : IsQuantumVectorSpace c X ħ C) :
    ∃ (K : Set ι) (C' : K → K → K →₀ ℂ), K.Countable ∧
      topology c (fun k : K => X k) = topology c X ∧
      IsQuantumVectorSpace c (fun k : K => X k) ħ C' := by
  classical
  have := hQ.secondCountableTopology
  obtain ⟨J, hJ, hJX⟩ := exists_countable_topology_eq c X
  let K : Set ι := ⋃ n, supportClosure C J n
  have hK : ∀ i ∈ K, ∀ j ∈ K, ((C i j).support : Set ι) ⊆ K := by
    intro i hi j hj
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hi
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 hj
    refine fun l hl => Set.mem_iUnion.2 ⟨max a b + 1, Set.mem_union_right _ ?_⟩
    exact Set.mem_biUnion (monotone_supportClosure C J (le_max_left a b) ha)
      (Set.mem_biUnion (monotone_supportClosure C J (le_max_right a b) hb) hl)
  have hKX : topology c (fun k : K => X k) = topology c X := by
    refine le_antisymm ?_ (topology_le_of_range_subset c X _ (Set.range_comp_subset_range _ X))
    refine hJX ▸ topology_le_of_range_subset c _ _ ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨⟨j, Set.mem_iUnion.2 ⟨0, j.2⟩⟩, rfl⟩
  refine ⟨K, fun i j => (C i j).subtypeDomain (· ∈ K),
    Set.countable_iUnion (supportClosure_countable C hJ), hKX, ⟨fun k => hQ.isSymmetric k,
      fun i j => ?_, uniformSpace_congr c X hKX ▸ hQ.completeSpace,
      hKX ▸ hQ.secondCountableTopology⟩⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum_subtypeDomain_index
    (h := fun i a => a • X i) fun l hl => hK i i.2 j j.2 hl, ← Finsupp.linearCombination_apply]
  exact hQ.comm i j

end Countable

/-! ### Separability is not enough -/

namespace Diagonal

open Complex

/-- The finitely supported sequences, as vectors of `ℓ²`. -/
def toLp : (ℕ →₀ ℂ) →ₗ[ℂ] lp (fun _ : ℕ => ℂ) 2 where
  toFun v := ⟨⇑v, (memℓp_zero (v.support.finite_toSet.subset fun _ hi =>
    Finsupp.mem_support_iff.2 hi)).of_exponent_ge zero_le⟩
  map_add' v w := Subtype.ext (Finsupp.coe_add v w)
  map_smul' r v := Subtype.ext (Finsupp.coe_smul r v)

@[simp]
lemma toLp_apply (v : ℕ →₀ ℂ) (n : ℕ) : toLp v n = v n := rfl

/-- The `ℓ²` inner product `⟨v, w⟩ = ∑ conj(vₙ) wₙ` on finitely supported sequences. -/
@[instance_reducible]
def core : PreInnerProductSpace.Core ℂ (ℕ →₀ ℂ) where
  inner v w := inner ℂ (toLp v) (toLp w)
  conj_inner_symm v w := inner_conj_symm _ _
  re_inner_nonneg v := inner_self_nonneg (𝕜 := ℂ) (x := toLp v)
  add_left u v w := by rw [map_add, inner_add_left]
  smul_left u v r := by rw [map_smul, inner_smul_left]

lemma core_toSeminorm (v : ℕ →₀ ℂ) : core.toSeminorm v = ‖toLp v‖ :=
  (norm_eq_sqrt_re_inner (𝕜 := ℂ) (toLp v)).symm

lemma core_toSeminorm_single (n : ℕ) (a : ℂ) : core.toSeminorm (Finsupp.single n a) = ‖a‖ := by
  rw [core_toSeminorm, ← lp.norm_single (p := 2) (E := fun _ : ℕ => ℂ) (by norm_num) n a]
  congr 1
  ext m
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The multiplication operator `(M_f v)ₙ = fₙ vₙ` of a real sequence `f`. -/
def mulOp (f : ℕ → ℝ) : Module.End ℂ (ℕ →₀ ℂ) where
  toFun v := (fun n => (f n : ℂ)) • v
  map_add' v w := by
    ext n
    simp [Finsupp.coe_pointwise_smul, mul_add]
  map_smul' r v := by
    ext n
    simp [Finsupp.coe_pointwise_smul, mul_left_comm]

@[simp]
lemma mulOp_apply (f : ℕ → ℝ) (v : ℕ →₀ ℂ) (n : ℕ) : mulOp f v n = f n * v n := by
  simp [mulOp]

lemma mulOp_single (f : ℕ → ℝ) (n : ℕ) (a : ℂ) :
    mulOp f (Finsupp.single n a) = Finsupp.single n (f n * a) := by
  ext m
  simp only [mulOp_apply, Finsupp.single_apply]
  split_ifs with h <;> simp [h]

/-- The multiplication operators are symmetric. -/
theorem isSymmetric_mulOp (f : ℕ → ℝ) : IsSymmetric core (mulOp f) := fun v w => by
  change inner ℂ (toLp (mulOp f v)) (toLp w) = inner ℂ (toLp v) (toLp (mulOp f w))
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [toLp_apply, mulOp_apply, RCLike.inner_apply, map_mul, conj_ofReal]
  ring

/-- The multiplication operators commute. -/
theorem mulOp_comm (f g : ℕ → ℝ) : mulOp f * mulOp g = mulOp g * mulOp f := by
  ext v n
  simp [mul_left_comm]

/-- With every real multiplication operator as a defining observable, the finitely supported
sequences are separable: they are the union of the countably many finite-dimensional subspaces
`ℂ^s`, which embed continuously in every vector-space topology. -/
theorem separableSpace : @TopologicalSpace.SeparableSpace (ℕ →₀ ℂ) (topology core mulOp) := by
  let := topology core mulOp
  have hp := withSeminorms core mulOp
  have := hp.isTopologicalAddGroup
  have := hp.continuousSMul
  let L (s : Finset ℕ) : (s → ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
    Fintype.linearCombination ℂ fun i : s => Finsupp.single (i : ℕ) (1 : ℂ)
  have hU : (Set.univ : Set (ℕ →₀ ℂ)) = ⋃ s, Set.range (L s) := by
    refine (Set.eq_univ_of_forall fun v => ?_).symm
    refine Set.mem_iUnion.2 ⟨v.support, fun i => v i, ?_⟩
    rw [Fintype.linearCombination_apply, Finset.sum_coe_sort v.support
      fun i => v i • Finsupp.single i (1 : ℂ)]
    simp_rw [Finsupp.smul_single_one]
    exact Finsupp.sum_single v
  rw [← TopologicalSpace.isSeparable_univ_iff, hU]
  exact .iUnion fun s => TopologicalSpace.isSeparable_range (L s).continuous_of_finiteDimensional

/-- The topology is not first countable: for countably many neighbourhoods `Uₙ` of `0`, a
multiplication operator `M_f` with `fₙ` large enough has `‖M_f(tₙ eₙ)‖ = 1` for vectors
`tₙ eₙ ∈ Uₙ`. -/
theorem not_firstCountableTopology :
    ¬ @FirstCountableTopology (ℕ →₀ ℂ) (topology core mulOp) := by
  intro h
  let := topology core mulOp
  have hp := withSeminorms core mulOp
  obtain ⟨x, hx0, hx⟩ := hp.hasBasis_zero_ball.exists_antitone_subbasis
  let e (n : ℕ) : ℕ →₀ ℂ := Finsupp.single n 1
  let t (n : ℕ) : ℝ := (x n).2 / (2 * (1 + ((x n).1.sup (seminormFamily core mulOp)) (e n)))
  have ht (n : ℕ) : 0 < t n := div_pos (hx0 n) (by positivity)
  let f (n : ℕ) : ℝ := (t n)⁻¹
  let A : algebra mulOp := ⟨mulOp f, Algebra.subset_adjoin ⟨f, rfl⟩⟩
  have hO : {v | seminormFamily core mulOp A v < 1} ∈ 𝓝 0 :=
    (isOpen_lt (hp.continuous_seminorm A) continuous_const).mem_nhds (by simp)
  obtain ⟨n, -, hn⟩ := hx.1.mem_iff.1 hO
  have hmem : ((t n : ℂ) • e n) ∈ ((x n).1.sup (seminormFamily core mulOp)).ball 0 (x n).2 := by
    rw [Seminorm.mem_ball_zero, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (ht n).le]
    have hq := apply_nonneg ((x n).1.sup (seminormFamily core mulOp)) (e n)
    change (x n).2 / _ * _ < _
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hx0 n]
  have h1 := hn hmem
  simp only [Set.mem_ofPred_eq] at h1
  change core.toSeminorm (mulOp f ((t n : ℂ) • e n)) < 1 at h1
  simp only [e] at h1
  rw [map_smul, mulOp_single, Finsupp.smul_single, core_toSeminorm_single] at h1
  simp [f, (ht n).ne'] at h1

/-- Separability is not enough: no countable subfamily of the multiplication operators generates
the topology of the separable space `separableSpace`. -/
theorem not_exists_countable :
    ¬ ∃ J : Set (ℕ → ℝ), J.Countable ∧
      topology core (fun j : J => mulOp j) = topology core mulOp :=
  fun h => not_firstCountableTopology ((exists_countable_topology_eq_iff core mulOp).1 h)

end Diagonal

end QuantumVectorSpaces
