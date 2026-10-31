/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Wigner.Density

/-!
# Affine maps of density operators are restrictions of linear maps

On a finite-dimensional complex Hilbert space the density operators span the operators: every
self-adjoint operator is a real combination of pure states, by the spectral theorem, and every
operator is `ℜ A + i ℑ A`. So there is a basis of density operators. An affine map `T` of the
density operators agrees on them with the linear map that extends its values on such a basis: the
coefficients of a density operator in the basis are real, and moving the negative ones to the
other side turns the expansion into an equality of two positive combinations, which `T`
preserves.

## Main results

* `QuantumMechanics.Wigner.isClosed_setOf_isDensity`: the density operators are closed.
* `QuantumMechanics.Wigner.exists_basis_isDensity`: a basis of density operators.
* `QuantumMechanics.Wigner.AffineOnDensities.basis_constr_apply`: an affine map agrees on density
  operators with the linear extension of its values on such a basis.
* `QuantumMechanics.Wigner.AffineOnDensities.exists_linearMap`.
-/

@[expose] public section

namespace QuantumMechanics.Wigner

open ComplexConjugate
open scoped InnerProductSpace ComplexStarModule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The density operators are closed. -/
lemma isClosed_setOf_isDensity : IsClosed {ρ : E →L[ℂ] E | IsDensity ρ} := by
  have hs : {ρ : E →L[ℂ] E | IsDensity ρ} =
      ((⋂ x : E, ⋂ y : E, {ρ : E →L[ℂ] E | ⟪ρ x, y⟫_ℂ = ⟪x, ρ y⟫_ℂ}) ∩
        ⋂ x : E, {ρ : E →L[ℂ] E | 0 ≤ RCLike.re ⟪ρ x, x⟫_ℂ}) ∩
        {ρ : E →L[ℂ] E | LinearMap.trace ℂ E ρ = 1} := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨⟨h.isPositive.1, h.isPositive.2⟩, h.trace_eq_one⟩,
      fun h => ⟨⟨h.1.1, h.1.2⟩, h.2⟩⟩
  have hap : ∀ x : E, Continuous fun ρ : E →L[ℂ] E => ρ x := fun x =>
    continuous_id.clm_apply continuous_const
  rw [hs]
  refine ((isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq
    ((hap x).inner continuous_const) (continuous_const.inner (hap y))).inter
    (isClosed_iInter fun x => isClosed_le continuous_const
      (RCLike.continuous_re.comp ((hap x).inner continuous_const)))).inter
    (isClosed_eq ?_ continuous_const)
  exact LinearMap.continuous_of_finiteDimensional
    ((LinearMap.trace ℂ E).comp (ContinuousLinearMap.coeLM ℂ))

/-- The spectral decomposition of a symmetric operator: `A = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|` over an orthonormal
eigenbasis. -/
lemma eq_sum_proj_of_isSymmetric {A : E →L[ℂ] E} (hA : (A : E →ₗ[ℂ] E).IsSymmetric) :
    A = ∑ i, (hA.eigenvalues rfl i : ℂ) • proj (hA.eigenvectorBasis rfl i) := by
  set b := hA.eigenvectorBasis rfl
  refine ContinuousLinearMap.coe_injective (b.toBasis.ext fun j => ?_)
  have h := hA.apply_eigenvectorBasis rfl j
  simp only [ContinuousLinearMap.coe_coe] at h
  simpa [b.inner_eq_ite, Complex.coe_smul] using h

variable [CompleteSpace E]

/-- The density operators span the operators. -/
lemma span_setOf_isDensity : ⊤ ≤ Submodule.span ℂ {ρ : E →L[ℂ] E | IsDensity ρ} := by
  have hsa : ∀ B : E →L[ℂ] E, IsSelfAdjoint B →
      B ∈ Submodule.span ℂ {ρ : E →L[ℂ] E | IsDensity ρ} := by
    intro B hB
    have hS : (B : E →ₗ[ℂ] E).IsSymmetric :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB
    rw [eq_sum_proj_of_isSymmetric hS]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (isDensity_proj ((hS.eigenvectorBasis rfl).orthonormal.1 i)))
  intro A _
  rw [← realPart_add_I_smul_imaginaryPart A]
  exact Submodule.add_mem _ (hsa _ (ℜ A).2) (Submodule.smul_mem _ _ (hsa _ (ℑ A).2))

/-- A basis of the operators that consists of density operators. -/
theorem exists_basis_isDensity : ∃ (s : Set (E →L[ℂ] E)) (_ : Fintype s)
    (b : Module.Basis s ℂ (E →L[ℂ] E)), ∀ i, IsDensity (b i) := by
  set b := Module.Basis.ofSpan (span_setOf_isDensity (E := E))
  have : Finite _ := Module.Finite.finite_basis b
  refine ⟨_, Fintype.ofFinite _, b, fun i => ?_⟩
  rw [Module.Basis.coe_ofSpan]
  exact (linearIndepOn_empty ℂ id).extend_subset (Set.empty_subset _) i.2

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
/-- A map that is affine on density operators preserves equalities between positive
combinations of density operators. -/
theorem AffineOnDensities.sum_smul_eq {T : (E →L[ℂ] E) → E →L[ℂ] E} (hT : AffineOnDensities T)
    {ι : Type*} [Fintype ι] {ρ : ι → E →L[ℂ] E} (hρ : ∀ i, IsDensity (ρ i)) {a c : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (h : ∑ i, (a i : ℂ) • ρ i = ∑ i, (c i : ℂ) • ρ i) :
    ∑ i, (a i : ℂ) • T (ρ i) = ∑ i, (c i : ℂ) • T (ρ i) := by
  have htr : ∀ μ : ι → ℝ, LinearMap.trace ℂ E (∑ i, (μ i : ℂ) • ρ i : E →L[ℂ] E) = ∑ i, μ i := by
    intro μ
    simp [ContinuousLinearMap.toLinearMap_sum, (hρ _).trace_eq_one]
  have hs : ∑ i, a i = ∑ i, c i := by
    have := congrArg (fun A : E →L[ℂ] E => LinearMap.trace ℂ E A) h
    simp only [htr] at this
    exact_mod_cast this
  set s := ∑ i, a i
  rcases (Finset.sum_nonneg fun i _ => ha i : 0 ≤ s).eq_or_lt with hs0 | hs0
  · have ha0 : ∀ i, a i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => ha i).mp hs0.symm i (Finset.mem_univ i)
    have hc0 : ∀ i, c i = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hc i).mp (hs0.trans hs).symm i
        (Finset.mem_univ i)
    simp [ha0, hc0]
  have hconv : ∀ μ : ι → ℝ, (∀ i, 0 ≤ μ i) → ∑ i, μ i = s →
      T ((s⁻¹ : ℂ) • ∑ i, (μ i : ℂ) • ρ i) = (s⁻¹ : ℂ) • ∑ i, (μ i : ℂ) • T (ρ i) := by
    intro μ hμ hμs
    have h1 := hT.map_sum Finset.univ (μ := fun i => μ i / s)
      (fun i _ => div_nonneg (hμ i) hs0.le)
      (by rw [← Finset.sum_div, hμs, div_self hs0.ne']) fun i _ => hρ i
    have e : ∀ X : ι → E →L[ℂ] E,
        (s⁻¹ : ℂ) • ∑ i, (μ i : ℂ) • X i = ∑ i, ((μ i / s : ℝ) : ℂ) • X i := by
      intro X
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul]
      congr 1
      push_cast
      ring
    rw [e, e]
    exact h1
  have h1 := hconv a ha rfl
  rw [h, hconv c hc hs.symm] at h1
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have h2 := congrArg (fun A : E →L[ℂ] E => (s : ℂ) • A) h1
  simp only [smul_smul, mul_inv_cancel₀ hs', one_smul] at h2
  exact h2.symm

omit [FiniteDimensional ℂ E] in
/-- **Affine maps are restrictions of linear maps**: on density operators, a map that is affine on
density operators agrees with the linear extension of its values on a basis of density
operators. -/
theorem AffineOnDensities.basis_constr_apply {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hT : AffineOnDensities T) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ (E →L[ℂ] E))
    (hb : ∀ i, IsDensity (b i)) {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    b.constr ℂ (fun i => T (b i)) ρ = T ρ := by
  have hsa : ∀ σ : E →L[ℂ] E, IsDensity σ → star σ = σ := fun σ hσ =>
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hσ.isPositive.isSymmetric
  set c := b.equivFun ρ
  have hρc : ρ = ∑ i, c i • b i := (b.sum_equivFun ρ).symm
  -- the coefficients are real
  have hreal : ∀ i, c i = ((c i).re : ℂ) := by
    have h : b.equivFun.symm (star c) = b.equivFun.symm c := by
      rw [b.equivFun_symm_apply, b.equivFun_symm_apply, ← hρc]
      calc ∑ i, star c i • b i = star (∑ i, c i • b i) := by
            simp only [star_sum, star_smul, hsa _ (hb _), Pi.star_apply]
        _ = ρ := by rw [← hρc, hsa ρ hρ]
    intro i
    have := congrFun (b.equivFun.symm.injective h) i
    rw [Pi.star_apply] at this
    exact (Complex.conj_eq_iff_re.mp this).symm
  set r : ι → ℝ := fun i => (c i).re
  have hρr : ρ = ∑ i, (r i : ℂ) • b i := by
    rw [hρc]
    exact Finset.sum_congr rfl fun i _ => by rw [← hreal i]
  -- `ρ + ∑ r⁻ bᵢ = ∑ r⁺ bᵢ`, an equality of positive combinations
  set ρ' : Option ι → E →L[ℂ] E := fun o => o.elim ρ b
  set a : Option ι → ℝ := fun o => o.elim 1 fun i => max (-r i) 0
  set a' : Option ι → ℝ := fun o => o.elim 0 fun i => max (r i) 0
  have hr : ∀ i, (r i : ℂ) = (max (r i) 0 : ℝ) - (max (-r i) 0 : ℝ) := fun i => by
    rw [← Complex.ofReal_sub, max_zero_sub_max_neg_zero_eq_self]
  have heq : ∑ o, (a o : ℂ) • ρ' o = ∑ o, (a' o : ℂ) • ρ' o := by
    simp only [Fintype.sum_option, a, a', ρ', Option.elim_none, Option.elim_some,
      Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, zero_add]
    rw [hρr, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hr i, sub_smul, sub_add_cancel]
  have hmap := hT.sum_smul_eq (ρ := ρ') (fun o => o.rec hρ hb) (a := a) (c := a')
    (fun o => o.rec zero_le_one fun i => le_max_right _ _)
    (fun o => o.rec le_rfl fun i => le_max_right _ _) heq
  simp only [Fintype.sum_option, a, a', ρ', Option.elim_none, Option.elim_some,
    Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul, zero_add] at hmap
  rw [Module.Basis.constr_apply_fintype (S := ℂ) b]
  have hcoef : ∀ i, b.equivFun ρ i = (max (r i) 0 : ℝ) - (max (-r i) 0 : ℝ) := fun i => by
    rw [← hr]
    exact hreal i
  simp only [hcoef, sub_smul, Finset.sum_sub_distrib]
  rw [← hmap]
  abel

/-- A map that is affine on density operators agrees on them with a linear map. -/
theorem AffineOnDensities.exists_linearMap {T : (E →L[ℂ] E) → E →L[ℂ] E}
    (hT : AffineOnDensities T) :
    ∃ T' : (E →L[ℂ] E) →ₗ[ℂ] E →L[ℂ] E, ∀ ρ, IsDensity ρ → T' ρ = T ρ := by
  obtain ⟨s, _, b, hb⟩ := exists_basis_isDensity (E := E)
  exact ⟨b.constr ℂ fun i => T (b i), fun ρ hρ => hT.basis_constr_apply b hb hρ⟩

end QuantumMechanics.Wigner
