/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ClassicalUncertaintyPrinciple.ExtendedVariance
public import ForMathlib.LinearAlgebra.Matrix.BilinearForm
public import ForMathlib.MeasureTheory.Function.Jacobian

/-!
# Classical uncertainty relation: several degrees of freedom

The brief *Classical uncertainty relation* imposes ZENT and GCUR "for each independent DOF":
on the marginal of each DOF, "independently of its representation". On the phase space
`(ℝ²)ⁿ⁺¹` the DOF `i` in the given coordinates is the pair `(qᵢ, pᵢ)`, with marginal
`ClassicalUncertaintyPrinciple.marginal ρ i`. For it, GCUR is
`ClassicalUncertaintyPrinciple.GeneralizedUncertaintyRelationPhaseSpace`, and Theorems 9 and 12
apply to each marginal that is an ensemble (the brief's FINENT for marginals): ZENT for every
marginal is equivalent to GCUR for every marginal.

Another canonical coordinate system can mix the pairs. A canonical transformation `Φ` is a
differentiable bijection whose derivative preserves the symplectic form
`ω = ∑ᵢ dqᵢ ∧ dpᵢ` at every point (`ClassicalUncertaintyPrinciple.IsCanonicalTransformation`).
By Liouville's theorem it preserves the Liouville measure: its Jacobian determinant has square
`1`, since it preserves a nondegenerate form. So the density in the new coordinates is
`ρ ∘ Φ⁻¹`, an ensemble with the same entropy, and the DOFs of the new coordinates are its pairs.
ZENT and GCUR independent of the representation quantify over all canonical coordinate systems,
and remain equivalent. The momentum shear `pᵢ ↦ pᵢ + ∑ⱼ Sᵢⱼ qⱼ`, `S` symmetric, is a canonical
transformation that mixes the pairs when `S` is not diagonal.

## Main definitions

All names are in the namespace `ClassicalUncertaintyPrinciple`.

* `GeneralizedUncertaintyRelationPhaseSpace`, `ExtendedGeneralizedUncertaintyRelationPhaseSpace`,
  `ExtendedUncertaintyRelationPhaseSpace`: GCUR and CUR for the marginal of every DOF.
* `symplecticForm`: `ω = ∑ᵢ dqᵢ ∧ dpᵢ`.
* `IsCanonicalTransformation`: canonical transformations.
* `canonicalDensity`: the density `ρ ∘ Φ⁻¹` in new coordinates.
* `LowerEntropicBoundCanonical`, `GeneralizedUncertaintyRelationCanonical`: ZENT and GCUR for
  the DOFs of every canonical coordinate system.
* `momentumShear`: a canonical transformation mixing the DOFs.

## Main results

* `lowerEntropicBoundPhaseSpace_iff_generalizedUncertaintyRelationPhaseSpace`,
  `lowerEntropicBoundPhaseSpace_iff_extendedGeneralizedUncertaintyRelationPhaseSpace`:
  Theorems 9 and 12 for `n + 1` DOFs.
* `IsCanonicalTransformation.measurePreserving`: Liouville's theorem.
* `IsCanonicalTransformation.entropy_canonicalDensity`: the entropy does not depend on the
  canonical coordinates.
* `lowerEntropicBoundCanonical_iff_generalizedUncertaintyRelationCanonical`: Theorems 9 and 12
  for the DOFs of every canonical coordinate system.
* `isCanonicalTransformation_momentumShear`: the momentum shear is canonical.
-/

@[expose] public section

open Real MeasureTheory Function

namespace ClassicalUncertaintyPrinciple

variable {n : ℕ} {ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ} {h : ℝ}

/-! ### GCUR for the marginal of each DOF -/

section Marginals

/-- Condition GCUR on the phase space `(ℝ²)ⁿ⁺¹`, for the marginal of every DOF. -/
def GeneralizedUncertaintyRelationPhaseSpace (h : ℝ) (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ i, GeneralizedUncertaintyRelation h (marginal ρ i)

/-- Condition GCUR, with extended variances, for the marginal of every DOF. -/
def ExtendedGeneralizedUncertaintyRelationPhaseSpace (h : ℝ)
    (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ i, ExtendedGeneralizedUncertaintyRelation h (marginal ρ i)

/-- Condition CUR, with extended variances, for the marginal of every DOF. -/
def ExtendedUncertaintyRelationPhaseSpace (h : ℝ) (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ i, ExtendedUncertaintyRelation h (marginal ρ i)

/-- **Theorem 9 for `n + 1` DOFs, GCUR.** -/
theorem generalizedUncertaintyRelationPhaseSpace_of_lowerEntropicBoundPhaseSpace (hh : 0 < h)
    (hm : ∀ i, IsEnsemble (marginal ρ i)) (hZ : LowerEntropicBoundPhaseSpace h ρ) :
    GeneralizedUncertaintyRelationPhaseSpace h ρ := fun i =>
  generalizedUncertaintyRelation_of_lowerEntropicBound hh (hm i) (hZ i)

/-- **Theorem 9 for `n + 1` DOFs, CUR with its equality case**, with extended variances. -/
theorem extendedUncertaintyRelationPhaseSpace_of_lowerEntropicBoundPhaseSpace (hh : 0 < h)
    (hm : ∀ i, IsEnsemble (marginal ρ i)) (hZ : LowerEntropicBoundPhaseSpace h ρ) :
    ExtendedUncertaintyRelationPhaseSpace h ρ := fun i =>
  extendedUncertaintyRelation_of_lowerEntropicBound hh (hm i) (hZ i)

/-- **Theorems 9 and 12 for `n + 1` DOFs.** If the marginal of every DOF is an ensemble, ZENT
for every DOF is equivalent to GCUR for every DOF. -/
theorem lowerEntropicBoundPhaseSpace_iff_generalizedUncertaintyRelationPhaseSpace (hh : 0 < h)
    (hm : ∀ i, IsEnsemble (marginal ρ i)) :
    LowerEntropicBoundPhaseSpace h ρ ↔ GeneralizedUncertaintyRelationPhaseSpace h ρ :=
  forall_congr' fun i => lowerEntropicBound_iff_generalizedUncertaintyRelation hh (hm i)

/-- **Theorems 9 and 12 for `n + 1` DOFs**, with extended variances. -/
theorem lowerEntropicBoundPhaseSpace_iff_extendedGeneralizedUncertaintyRelationPhaseSpace
    (hh : 0 < h) (hm : ∀ i, IsEnsemble (marginal ρ i)) :
    LowerEntropicBoundPhaseSpace h ρ ↔ ExtendedGeneralizedUncertaintyRelationPhaseSpace h ρ :=
  forall_congr' fun i => lowerEntropicBound_iff_extendedGeneralizedUncertaintyRelation hh (hm i)

end Marginals

/-! ### Canonical transformations -/

section Canonical

/-- The symplectic form `ω = ∑ᵢ dqᵢ ∧ dpᵢ` on `(ℝ²)ⁿ⁺¹`. -/
def symplecticForm : LinearMap.BilinForm ℝ (Fin (n + 1) → ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i, ((x i).1 * (y i).2 - (x i).2 * (y i).1))
    (fun x x' y => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
      ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring)
    (fun x y y' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add]
      ring)
    (fun c x y => by
      rw [smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring)

lemma symplecticForm_apply (x y : Fin (n + 1) → ℝ × ℝ) :
    symplecticForm x y = ∑ i, ((x i).1 * (y i).2 - (x i).2 * (y i).1) :=
  rfl

lemma symplecticForm_swap (x y : Fin (n + 1) → ℝ × ℝ) :
    symplecticForm y x = -symplecticForm x y := by
  rw [symplecticForm_apply, symplecticForm_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `ω` is nondegenerate. -/
theorem nondegenerate_symplecticForm : (symplecticForm (n := n)).Nondegenerate := by
  have key : ∀ x : Fin (n + 1) → ℝ × ℝ, (∀ y, symplecticForm x y = 0) → x = 0 := by
    intro x hx
    funext i
    have h1 := hx (Pi.single i (0, 1))
    have h2 := hx (Pi.single i (1, 0))
    simp only [symplecticForm_apply, Pi.single_apply, apply_ite Prod.fst, apply_ite Prod.snd,
      Prod.fst_zero, Prod.snd_zero, mul_ite, mul_zero, mul_one, ite_self, sub_zero, zero_sub,
      Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, neg_eq_zero]
      at h1 h2
    exact Prod.ext (by simpa using h1) (by simpa using h2)
  exact ⟨key, fun y hy => key y fun x => by rw [symplecticForm_swap, hy x, neg_zero]⟩

/-- A canonical transformation of `(ℝ²)ⁿ⁺¹`: a differentiable bijection whose derivative
preserves the symplectic form at every point. -/
structure IsCanonicalTransformation (Φ : (Fin (n + 1) → ℝ × ℝ) → Fin (n + 1) → ℝ × ℝ) :
    Prop where
  bijective : Bijective Φ
  differentiable : Differentiable ℝ Φ
  symplectic : ∀ x u v, symplecticForm (fderiv ℝ Φ x u) (fderiv ℝ Φ x v) = symplecticForm u v

lemma isCanonicalTransformation_id :
    IsCanonicalTransformation (id : (Fin (n + 1) → ℝ × ℝ) → Fin (n + 1) → ℝ × ℝ) where
  bijective := bijective_id
  differentiable := differentiable_id
  symplectic x u v := by simp

namespace IsCanonicalTransformation

variable {Φ : (Fin (n + 1) → ℝ × ℝ) → Fin (n + 1) → ℝ × ℝ} (H : IsCanonicalTransformation Φ)
include H

/-- The Jacobian determinant of a canonical transformation is `±1`. -/
lemma abs_det_fderiv (x : Fin (n + 1) → ℝ × ℝ) : |(fderiv ℝ Φ x).det| = 1 := by
  have h := LinearMap.BilinForm.det_sq_eq_one_of_comp_eq nondegenerate_symplecticForm
    (f := (fderiv ℝ Φ x : (Fin (n + 1) → ℝ × ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ × ℝ))
    (LinearMap.ext₂ fun u v => H.symplectic x u v)
  rw [← sq_abs] at h
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg _) two_ne_zero).1 h

/-- **Liouville's theorem.** A canonical transformation preserves the Liouville measure. -/
theorem measurePreserving : MeasurePreserving Φ :=
  measurePreserving_of_abs_det_fderiv_eq_one volume (fun x => (H.differentiable x).hasFDerivAt)
    H.bijective H.abs_det_fderiv

lemma measurableEmbedding : MeasurableEmbedding Φ :=
  H.differentiable.continuous.measurableEmbedding H.bijective.1

lemma integral_comp (g : (Fin (n + 1) → ℝ × ℝ) → ℝ) : ∫ x, g (Φ x) = ∫ y, g y :=
  H.measurePreserving.integral_comp H.measurableEmbedding g

lemma integrable_comp_iff {g : (Fin (n + 1) → ℝ × ℝ) → ℝ} :
    Integrable (fun x => g (Φ x)) ↔ Integrable g :=
  H.measurePreserving.integrable_comp_emb H.measurableEmbedding

end IsCanonicalTransformation

/-- The density in the coordinates `y = Φ x`, `ρ_Φ(y) = ρ(Φ⁻¹ y)`; a canonical transformation
preserves the Liouville measure, so there is no Jacobian factor. -/
noncomputable def canonicalDensity (Φ : (Fin (n + 1) → ℝ × ℝ) → Fin (n + 1) → ℝ × ℝ)
    (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) (y : Fin (n + 1) → ℝ × ℝ) : ℝ :=
  ρ (invFun Φ y)

lemma canonicalDensity_apply {Φ : (Fin (n + 1) → ℝ × ℝ) → Fin (n + 1) → ℝ × ℝ}
    (hΦ : Injective Φ) (x : Fin (n + 1) → ℝ × ℝ) : canonicalDensity Φ ρ (Φ x) = ρ x := by
  rw [canonicalDensity, leftInverse_invFun hΦ x]

lemma canonicalDensity_id : canonicalDensity id ρ = ρ :=
  funext fun y => canonicalDensity_apply injective_id y

namespace IsCanonicalTransformation

variable {Φ : (Fin (n + 1) → ℝ × ℝ) → Fin (n + 1) → ℝ × ℝ} (H : IsCanonicalTransformation Φ)
include H

/-- The density in canonical coordinates is an ensemble. -/
theorem isEnsemble_canonicalDensity (hρ : IsEnsemble ρ) : IsEnsemble (canonicalDensity Φ ρ) where
  nonneg y := by
    obtain ⟨x, rfl⟩ := H.bijective.2 y
    rw [canonicalDensity_apply H.bijective.1]
    exact hρ.nonneg x
  integral_eq_one := by
    rw [← H.integral_comp]
    simp_rw [canonicalDensity_apply H.bijective.1]
    exact hρ.integral_eq_one
  integrable_negMulLog := H.integrable_comp_iff.1 (by
    simp_rw [canonicalDensity_apply H.bijective.1]
    exact hρ.integrable_negMulLog)

/-- The entropy does not depend on the canonical coordinates. -/
theorem entropy_canonicalDensity (c : ℝ) : entropy c (canonicalDensity Φ ρ) = entropy c ρ := by
  rw [entropy, entropy, ← H.integral_comp]
  simp_rw [canonicalDensity_apply H.bijective.1]

/-- The marginals in canonical coordinates are ensembles if the new coordinates have finite
second moments. -/
theorem isEnsemble_marginal (hρ : IsEnsemble ρ)
    (hq : ∀ j, Integrable fun x => (Φ x j).1 ^ 2 * ρ x)
    (hp : ∀ j, Integrable fun x => (Φ x j).2 ^ 2 * ρ x) (i : Fin (n + 1)) :
    IsEnsemble (marginal (canonicalDensity Φ ρ) i) := by
  refine ClassicalUncertaintyPrinciple.isEnsemble_marginal (H.isEnsemble_canonicalDensity hρ)
    (fun j => H.integrable_comp_iff.1 ?_) (fun j => H.integrable_comp_iff.1 ?_) i
  · simpa only [canonicalDensity_apply H.bijective.1] using hq j
  · simpa only [canonicalDensity_apply H.bijective.1] using hp j

end IsCanonicalTransformation

/-- Condition ZENT independently of the representation: in every canonical coordinate system,
the marginal of every DOF has `S_h ≥ 0`. -/
def LowerEntropicBoundCanonical (h : ℝ) (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ Φ, IsCanonicalTransformation Φ → LowerEntropicBoundPhaseSpace h (canonicalDensity Φ ρ)

/-- Condition GCUR for every DOF of every canonical coordinate system. -/
def GeneralizedUncertaintyRelationCanonical (h : ℝ) (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ Φ, IsCanonicalTransformation Φ →
    GeneralizedUncertaintyRelationPhaseSpace h (canonicalDensity Φ ρ)

/-- Condition GCUR, with extended variances, for every DOF of every canonical coordinate
system. -/
def ExtendedGeneralizedUncertaintyRelationCanonical (h : ℝ)
    (ρ : (Fin (n + 1) → ℝ × ℝ) → ℝ) : Prop :=
  ∀ Φ, IsCanonicalTransformation Φ →
    ExtendedGeneralizedUncertaintyRelationPhaseSpace h (canonicalDensity Φ ρ)

/-- ZENT in every canonical coordinate system gives ZENT in the given one. -/
theorem LowerEntropicBoundCanonical.lowerEntropicBoundPhaseSpace
    (hZ : LowerEntropicBoundCanonical h ρ) : LowerEntropicBoundPhaseSpace h ρ := by
  simpa only [canonicalDensity_id] using hZ id isCanonicalTransformation_id

/-- **Theorems 9 and 12 for the DOFs of every canonical coordinate system.** If the marginals
in every canonical coordinate system are ensembles, ZENT independently of the representation is
equivalent to GCUR for every DOF of every canonical coordinate system. -/
theorem lowerEntropicBoundCanonical_iff_generalizedUncertaintyRelationCanonical (hh : 0 < h)
    (hm : ∀ Φ, IsCanonicalTransformation Φ → ∀ i, IsEnsemble (marginal (canonicalDensity Φ ρ) i)) :
    LowerEntropicBoundCanonical h ρ ↔ GeneralizedUncertaintyRelationCanonical h ρ :=
  forall₂_congr fun Φ H =>
    lowerEntropicBoundPhaseSpace_iff_generalizedUncertaintyRelationPhaseSpace hh (hm Φ H)

/-- **Theorems 9 and 12 for the DOFs of every canonical coordinate system**, with extended
variances. -/
theorem lowerEntropicBoundCanonical_iff_extendedGeneralizedUncertaintyRelationCanonical
    (hh : 0 < h)
    (hm : ∀ Φ, IsCanonicalTransformation Φ → ∀ i, IsEnsemble (marginal (canonicalDensity Φ ρ) i)) :
    LowerEntropicBoundCanonical h ρ ↔ ExtendedGeneralizedUncertaintyRelationCanonical h ρ :=
  forall₂_congr fun Φ H =>
    lowerEntropicBoundPhaseSpace_iff_extendedGeneralizedUncertaintyRelationPhaseSpace hh (hm Φ H)

/-! ### A canonical transformation that mixes the DOFs -/

/-- The linear part `x ↦ (0, S q)` of the momentum shear. -/
def shearPart (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ × ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ × ℝ where
  toFun x i := (0, ∑ j, S i j * (x j).1)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, Prod.fst_add, mul_add, Finset.sum_add_distrib, Prod.mk_add_mk,
      add_zero]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, Prod.smul_fst, smul_eq_mul, RingHom.id_apply, Prod.smul_mk,
      mul_zero, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

/-- The momentum shear `pᵢ ↦ pᵢ + ∑ⱼ Sᵢⱼ qⱼ`, positions unchanged. -/
def momentumShear (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin (n + 1) → ℝ × ℝ) :
    Fin (n + 1) → ℝ × ℝ :=
  x + shearPart S x

lemma shearPart_shearPart (S T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ × ℝ) : shearPart S (shearPart T x) = 0 := by
  funext i
  simp [shearPart]

lemma momentumShear_neg (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin (n + 1) → ℝ × ℝ) :
    momentumShear (-S) (momentumShear S x) = x := by
  have h : shearPart (-S) x = -shearPart S x := by
    funext i
    simp [shearPart]
  simp only [momentumShear, map_add, shearPart_shearPart, add_zero, h]
  abel

/-- **A canonical transformation mixing the DOFs.** For a symmetric matrix `S`, the momentum
shear `pᵢ ↦ pᵢ + ∑ⱼ Sᵢⱼ qⱼ` is a canonical transformation; for `Sᵢⱼ ≠ 0`, `i ≠ j`, its DOF `i`
depends on `qⱼ`. -/
theorem isCanonicalTransformation_momentumShear {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.IsSymm) : IsCanonicalTransformation (momentumShear S) := by
  set L := LinearMap.toContinuousLinearMap (shearPart S)
  have hd : ∀ x, HasFDerivAt (momentumShear S) (ContinuousLinearMap.id ℝ _ + L) x := fun x =>
    (hasFDerivAt_id x).add L.hasFDerivAt
  refine ⟨bijective_iff_has_inverse.2 ⟨momentumShear (-S), fun x => momentumShear_neg S x,
    fun x => by simpa using momentumShear_neg (-S) x⟩, fun x => (hd x).differentiableAt,
    fun x u v => ?_⟩
  rw [(hd x).fderiv]
  have hS' : ∀ i j, S i j = S j i := fun i j => (hS.apply i j).symm
  simp only [add_apply, ContinuousLinearMap.coe_id', id_eq,
    LinearMap.coe_toContinuousLinearMap', L, symplecticForm_apply, shearPart,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Prod.fst_add, Prod.snd_add, add_zero]
  have e : ∑ i, (u i).1 * ∑ j, S i j * (v j).1 = ∑ i, (v i).1 * ∑ j, S i j * (u j).1 := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hS' j i]; ring
  have : ∀ i, (u i).1 * ((v i).2 + ∑ j, S i j * (v j).1) -
      ((u i).2 + ∑ j, S i j * (u j).1) * (v i).1 =
      ((u i).1 * (v i).2 - (u i).2 * (v i).1) +
        ((u i).1 * ∑ j, S i j * (v j).1 - (v i).1 * ∑ j, S i j * (u j).1) := fun i => by ring
  have e2 : ∑ i, ((u i).1 * ∑ j, S i j * (v j).1 - (v i).1 * ∑ j, S i j * (u j).1) = 0 := by
    rw [Finset.sum_sub_distrib, e, sub_self]
  simp_rw [this]
  rw [Finset.sum_add_distrib, e2, add_zero]

end Canonical

end ClassicalUncertaintyPrinciple
