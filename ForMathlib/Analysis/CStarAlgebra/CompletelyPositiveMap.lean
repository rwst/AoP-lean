/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrals of completely positive maps

A Bochner integral `∫ x, φ x ∂μ` of continuous linear maps between C⋆-algebras that are
completely positive for almost every `x` is completely positive: applying it to the entries of a
positive matrix `M` gives `∫ x, M.map (φ x) ∂μ`, an integral of positive matrices, and the
positive cone of a C⋆-algebra is closed.

## Main definitions

* `CompletelyPositiveMap.integral`: the integral of almost everywhere completely positive maps,
  as a completely positive map.
-/

@[expose] public section

open scoped CStarAlgebra
open MeasureTheory

namespace CStarMatrix

section Mul

variable {n R A : Type*} [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring A]
  [DistribMulAction R A]

instance instIsScalarTowerMul [IsScalarTower R A A] :
    IsScalarTower R (CStarMatrix n n A) (CStarMatrix n n A) :=
  inferInstanceAs (IsScalarTower R (Matrix n n A) (Matrix n n A))

instance instSMulCommClassMul [SMulCommClass R A A] :
    SMulCommClass R (CStarMatrix n n A) (CStarMatrix n n A) :=
  inferInstanceAs (SMulCommClass R (Matrix n n A) (Matrix n n A))

end Mul

variable {m n A₁ A₂ : Type*} [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]

/-- Applying a continuous linear map to the entries of a fixed matrix, as a continuous linear
function of the map. -/
noncomputable def mapCLM (M : CStarMatrix m n A₁) : (A₁ →L[ℂ] A₂) →L[ℂ] CStarMatrix m n A₂ :=
  ofMatrixL.toContinuousLinearMap.comp <|
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
      ContinuousLinearMap.apply ℂ A₂ (M i j)

theorem mapCLM_apply (M : CStarMatrix m n A₁) (φ : A₁ →L[ℂ] A₂) : mapCLM M φ = M.map φ :=
  rfl

end CStarMatrix

namespace CompletelyPositiveMap

variable {α A₁ A₂ : Type*} [MeasurableSpace α] {μ : Measure α} [NonUnitalCStarAlgebra A₁]
  [NonUnitalCStarAlgebra A₂] [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁]
  [StarOrderedRing A₂]

/-- An integral of continuous linear maps that are completely positive almost everywhere is
completely positive. -/
theorem map_integral_nonneg {φ : α → A₁ →L[ℂ] A₂}
    (h : ∀ᵐ x ∂μ, ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 ≤ M → 0 ≤ M.map (φ x))
    {k : ℕ} {M : CStarMatrix (Fin k) (Fin k) A₁} (hM : 0 ≤ M) :
    0 ≤ M.map (∫ x, φ x ∂μ : A₁ →L[ℂ] A₂) := by
  by_cases hφ : Integrable φ μ
  · rw [← CStarMatrix.mapCLM_apply, ← (CStarMatrix.mapCLM M).integral_comp_comm hφ]
    -- The real scalars of the integral come from the complex normed space, those of the order
    -- from the entries; the two agree only up to unfolding, so the instance is passed by hand.
    have hmod : IsOrderedModule ℝ (CStarMatrix (Fin k) (Fin k) A₂) := inferInstance
    exact @integral_nonneg_of_ae _ _ _ _ _ _ _ _ hmod _ _ (h.mono fun x hx => hx k M hM)
  · rw [integral_undef hφ]
    exact (CStarMatrix.mapCLM M).map_zero.symm.le

/-- The integral of continuous linear maps that are completely positive almost everywhere, as a
completely positive map. -/
noncomputable def integral (φ : α → A₁ →L[ℂ] A₂) (μ : Measure α)
    (h : ∀ᵐ x ∂μ, ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 ≤ M → 0 ≤ M.map (φ x)) :
    A₁ →CP A₂ where
  toLinearMap := ((∫ x, φ x ∂μ : A₁ →L[ℂ] A₂) : A₁ →ₗ[ℂ] A₂)
  map_cstarMatrix_nonneg' _ _ hM := map_integral_nonneg h hM

@[simp]
theorem coe_integral (φ : α → A₁ →L[ℂ] A₂) (μ : Measure α)
    (h : ∀ᵐ x ∂μ, ∀ (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁), 0 ≤ M → 0 ≤ M.map (φ x)) :
    ⇑(integral φ μ h) = ⇑(∫ x, φ x ∂μ) :=
  rfl

end CompletelyPositiveMap
