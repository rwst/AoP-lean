/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Qubit.AntisymplecticReflection
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Geometry.Manifold.Flow.TimeDependent
public import TauCeti.Geometry.Symplectic.Hamiltonian.SymplecticVectorField
import ForMathlib.Topology.Compactification.OnePoint.SimplyConnected
import TauCeti.Geometry.Manifold.DeRham.SimplyConnected
import TauCeti.Geometry.Manifold.DifferentialForm.Flow.TimeDependent

/-!
# Hamiltonian evolution on the classical qubit

A smooth vector field `X` preserves a closed two-form `σ`, `L_X σ = 0`, exactly when its
contraction `ι_X σ` is closed (Cartan's formula). It is Hamiltonian when `ι_X σ = df` is exact.
The obstruction is the class `[ι_X σ] ∈ H¹_dR(M)`, which vanishes on a simply connected manifold.
So on a simply connected manifold the infinitesimal symmetries of `σ` are exactly the Hamiltonian
vector fields, and for a nondegenerate `σ` every symplectic vector field is `-X_f` for a smooth
`f`.

The Riemann sphere `OnePoint ℂ ≅ ℙ ℂ (Fin 2 → ℂ)`, the phase space of the classical qubit, is
simply connected. So a smooth vector field preserves the Fubini–Study form `ω_FS` exactly when it is
the Hamiltonian vector field of a smooth function. No flux homomorphism is needed: the flux takes
values in `H¹_dR`, which vanishes here.

The same holds for evolutions. The time-dependent flow `φ_{s,t}` of a time-dependent vector field
`X` preserves `σ` exactly when `L_{X_t} σ = 0` for all `t`, so on the Riemann sphere a jointly
smooth time-dependent flow preserves `ω_FS` exactly when every `X t` is Hamiltonian. Such flows
never reach complex conjugation, which preserves the area but reverses `ω_FS`. So Hamiltonian
evolution of the classical qubit is the area-form-preserving evolution, not the area-preserving
one.

## Main results

- `TauCeti.SmoothTwoForm.mem_symplecticVectorFields_iff_exists_isHamiltonianVectorField`: on a
  simply connected manifold, a smooth vector field has closed contraction exactly when it is
  Hamiltonian for a smooth function.
- `TauCeti.SmoothTwoForm.mlieDerivForm_eq_zero_iff_exists_isHamiltonianVectorField`: for closed
  `σ`, the smooth vector fields with `L_X σ = 0` are the Hamiltonian ones.
- `TauCeti.SmoothTwoForm.IsNondegenerate.range_negHamiltonianₗ_eq_top`: for nondegenerate `σ`,
  every symplectic vector field is `-X_f`.
- `QuantumMechanics.Qubit.mlieDerivForm_fubiniStudyForm_eq_zero_iff`: a smooth vector field on
  the Riemann sphere preserves `ω_FS` exactly when it is Hamiltonian.
- `QuantumMechanics.Qubit.range_negHamiltonianₗ_fubiniStudyForm`: every symplectic vector field
  of `ω_FS` is `-X_f`.
- `TauCeti.SmoothTwoForm.mpullback_timeDependentFlowOf_of_isHamiltonianVectorField`: a
  time-dependent Hamiltonian flow preserves a closed form.
- `TauCeti.SmoothTwoForm.forall_mpullback_timeDependentFlowOf_eq_iff`: on a simply connected
  manifold, a time-dependent flow preserves a closed form exactly when it is Hamiltonian.
- `QuantumMechanics.Qubit.mpullback_timeDependentFlowOf_fubiniStudyForm`,
  `QuantumMechanics.Qubit.forall_mpullback_timeDependentFlowOf_fubiniStudyForm_iff`: the same on
  the Riemann sphere, where every suspension is complete.
- `QuantumMechanics.Qubit.timeDependentFlowOf_ne_conjSphere`: no time map of a time-dependent
  Hamiltonian flow is complex conjugation.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M] {σ : SmoothTwoForm I M}

section SimplyConnected

variable [SimplyConnectedSpace M]

/-- On a simply connected manifold the class `[ι_X σ] ∈ H¹_dR(M)` of a symplectic vector field
vanishes. -/
theorem interiorClass_eq_zero_of_simplyConnectedSpace (X : σ.symplecticVectorFields) :
    σ.interiorClass X = 0 :=
  have := subsingleton_deRhamCohomology_one_of_simplyConnectedSpace (I := I) (M := M)
  Subsingleton.elim _ _

/-- **Symplectic vector fields on a simply connected manifold are Hamiltonian.** A smooth vector
field has closed contraction `ι_X σ` exactly when it is the Hamiltonian vector field of a smooth
function. -/
theorem mem_symplecticVectorFields_iff_exists_isHamiltonianVectorField
    {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    X ∈ σ.symplecticVectorFields ↔
      ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ σ.IsHamiltonianVectorField f X := by
  refine ⟨fun hX ↦ ?_, fun ⟨f, hf, hfX⟩ ↦ ?_⟩
  · obtain ⟨φ, hφ⟩ := (interiorClass_eq_zero_iff ⟨X, hX⟩).1
      (interiorClass_eq_zero_of_simplyConnectedSpace _)
    refine ⟨fun y ↦ φ.1 y 0, isSmoothForm_ofFunction_iff.1 ?_, hφ⟩
    rw [← RoughForm.eq_ofFunction]
    exact φ.isSmoothForm
  · refine mem_symplecticVectorFields_of_isHamiltonianVectorField (φ := ⟨RoughForm.ofFunction I f,
      (isSmoothForm_ofFunction_iff.2 hf).mem_smoothBundleForms⟩) ?_
    convert hfX using 2 with y
    exact RoughForm.ofFunction_apply f y 0

/-- **Infinitesimal symmetries of a closed form on a simply connected manifold are
Hamiltonian.** For closed `σ`, a smooth vector field satisfies `L_X σ = 0` exactly when it is the
Hamiltonian vector field of a smooth function. -/
theorem mlieDerivForm_eq_zero_iff_exists_isHamiltonianVectorField (hσ : σ.IsClosed)
    {X : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯} :
    mlieDerivForm X σ.1 = 0 ↔
      ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ σ.IsHamiltonianVectorField f X :=
  (mem_symplecticVectorFields_iff_mlieDerivForm_eq_zero hσ).symm.trans
    mem_symplecticVectorFields_iff_exists_isHamiltonianVectorField

/-- For a nondegenerate form on a simply connected manifold, every symplectic vector field is
`-X_f` for a smooth function `f`: the map `f ↦ -X_f` is onto. -/
theorem IsNondegenerate.range_negHamiltonianₗ_eq_top (h : σ.IsNondegenerate) :
    LinearMap.range h.negHamiltonianₗ = ⊤ :=
  eq_top_iff.2 fun X _ ↦
    (h.exact_negHamiltonianₗ_interiorClass X).1 (interiorClass_eq_zero_of_simplyConnectedSpace X)

end SimplyConnected

/-! ### Time-dependent flows -/

section TimeDependent

variable [I.Boundaryless] {X : ℝ → (x : M) → TangentSpace I x}

/-- **Time-dependent Hamiltonian flows preserve the form.** Let `X` be a jointly `C²`
time-dependent vector field with complete suspension, such that each `X t` is the Hamiltonian
vector field of a `C²` function `H t` for a closed form `σ`. Then the time-dependent flow of `X`
satisfies `φ_{s,t}^* σ = σ`. -/
theorem mpullback_timeDependentFlowOf_of_isHamiltonianVectorField (hσ : σ.IsClosed)
    (hc : IsCompleteVectorField (timeDependentSuspensionField X))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent 2
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {H : ℝ → M → ℝ} (hH : ∀ t, ContMDiff I 𝓘(ℝ) 2 (H t))
    (hXH : ∀ t, σ.IsHamiltonianVectorField (H t) (X t)) (s t : ℝ) :
    mpullback I I (timeDependentFlowOf X s t) σ.1 = σ.1 :=
  mpullback_timeDependentFlowOf_of_mextDeriv_interior_eq_zero hc hX σ.mdifferentiable
    ((SmoothForm.isClosed_def σ).1 hσ)
    (fun u ↦ by rw [isHamiltonianVectorField_iff_interior_eq.1 (hXH u),
      mextDeriv_mextDeriv_ofFunction (hH u)]) s t

/-- **Form-preserving time-dependent flows are Hamiltonian.** On a simply connected manifold, let
`X` be a jointly smooth time-dependent vector field with complete suspension and `σ` a closed
form. The time-dependent flow of `X` preserves `σ` at all times exactly when every `X t` is the
Hamiltonian vector field of a smooth function. -/
theorem forall_mpullback_timeDependentFlowOf_eq_iff [SimplyConnectedSpace M] (hσ : σ.IsClosed)
    (hc : IsCompleteVectorField (timeDependentSuspensionField X))
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M))) :
    (∀ s t, mpullback I I (timeDependentFlowOf X s t) σ.1 = σ.1) ↔
      ∀ t, ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ σ.IsHamiltonianVectorField f (X t) := by
  rw [mpullback_timeDependentFlowOf_eq_self_iff hc (hX.of_le (by simp)) σ.mdifferentiable]
  refine forall_congr' fun t ↦ ?_
  let Xt : Cₛ^∞⟮I; E, TangentSpace I (M := M)⟯ :=
    ⟨X t, hX.comp ((contMDiff_const (c := t)).prodMk contMDiff_id)⟩
  exact mlieDerivForm_eq_zero_iff_exists_isHamiltonianVectorField (X := Xt) hσ

end TimeDependent

end TauCeti.SmoothTwoForm

namespace QuantumMechanics.Qubit

open OnePoint (fubiniStudyForm isSymplectic_fubiniStudyForm)
open TauCeti
open scoped TauCeti.ComplexManifold

/-- **Area-form-preserving vector fields on the classical qubit are Hamiltonian.** A smooth vector
field on the Riemann sphere satisfies `L_X ω_FS = 0` exactly when it is the Hamiltonian vector
field of a smooth function. -/
theorem mlieDerivForm_fubiniStudyForm_eq_zero_iff
    {X : Cₛ^∞⟮𝓘(ℝ, ℂ); ℂ, TangentSpace 𝓘(ℝ, ℂ) (M := OnePoint ℂ)⟯} :
    mlieDerivForm X fubiniStudyForm.1 = 0 ↔
      ∃ f : OnePoint ℂ → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ f ∧
        fubiniStudyForm.IsHamiltonianVectorField f X :=
  SmoothTwoForm.mlieDerivForm_eq_zero_iff_exists_isHamiltonianVectorField
    isSymplectic_fubiniStudyForm.isClosed

/-- Every symplectic vector field of `ω_FS` on the Riemann sphere is `-X_f` for a smooth `f`. -/
theorem range_negHamiltonianₗ_fubiniStudyForm :
    LinearMap.range isSymplectic_fubiniStudyForm.isNondegenerate.negHamiltonianₗ = ⊤ :=
  isSymplectic_fubiniStudyForm.isNondegenerate.range_negHamiltonianₗ_eq_top

/-- A jointly `C¹` time-dependent vector field on the Riemann sphere has a complete suspension,
since the sphere is compact. -/
theorem isCompleteVectorField_timeDependentSuspensionField_onePoint
    {X : ℝ → (x : OnePoint ℂ) → TangentSpace 𝓘(ℝ, ℂ) x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ).tangent 1
      (fun p : ℝ × OnePoint ℂ ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)))) :
    IsCompleteVectorField (timeDependentSuspensionField X) :=
  isCompleteVectorField_timeDependentSuspensionField hX isCompact_univ
    fun _ _ hy ↦ absurd (Set.mem_univ _) hy

/-- **Time-dependent Hamiltonian evolution of the classical qubit preserves the area form.** If
each `X t` of a jointly `C²` time-dependent vector field on the Riemann sphere is the Hamiltonian
vector field of a `C²` function `H t`, its time-dependent flow preserves `ω_FS`. -/
theorem mpullback_timeDependentFlowOf_fubiniStudyForm
    {X : ℝ → (x : OnePoint ℂ) → TangentSpace 𝓘(ℝ, ℂ) x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ).tangent 2
      (fun p : ℝ × OnePoint ℂ ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ))))
    {H : ℝ → OnePoint ℂ → ℝ} (hH : ∀ t, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (H t))
    (hXH : ∀ t, fubiniStudyForm.IsHamiltonianVectorField (H t) (X t)) (s t : ℝ) :
    mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (timeDependentFlowOf X s t) fubiniStudyForm.1 =
      fubiniStudyForm.1 :=
  SmoothTwoForm.mpullback_timeDependentFlowOf_of_isHamiltonianVectorField
    isSymplectic_fubiniStudyForm.isClosed
    (isCompleteVectorField_timeDependentSuspensionField_onePoint (hX.of_le one_le_two)) hX hH hXH
    s t

/-- **Complex conjugation is not a time-dependent Hamiltonian evolution.** No time map of the
time-dependent flow of `C²` Hamiltonians on the Riemann sphere is complex conjugation, although
complex conjugation preserves the area. -/
theorem timeDependentFlowOf_ne_conjSphere
    {X : ℝ → (x : OnePoint ℂ) → TangentSpace 𝓘(ℝ, ℂ) x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ).tangent 2
      (fun p : ℝ × OnePoint ℂ ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ))))
    {H : ℝ → OnePoint ℂ → ℝ} (hH : ∀ t, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 (H t))
    (hXH : ∀ t, fubiniStudyForm.IsHamiltonianVectorField (H t) (X t)) (s t : ℝ) :
    timeDependentFlowOf X s t ≠ conjSphere :=
  ne_conjSphere_of_mpullback_eq (mpullback_timeDependentFlowOf_fubiniStudyForm hX hH hXH s t)

/-- **Area-form-preserving evolutions of the classical qubit are Hamiltonian.** The time-dependent
flow of a jointly smooth time-dependent vector field on the Riemann sphere preserves `ω_FS` at all
times exactly when every `X t` is the Hamiltonian vector field of a smooth function. -/
theorem forall_mpullback_timeDependentFlowOf_fubiniStudyForm_iff
    {X : ℝ → (x : OnePoint ℂ) → TangentSpace 𝓘(ℝ, ℂ) x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ).tangent ∞
      (fun p : ℝ × OnePoint ℂ ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)))) :
    (∀ s t, mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (timeDependentFlowOf X s t) fubiniStudyForm.1 =
        fubiniStudyForm.1) ↔
      ∀ t, ∃ f : OnePoint ℂ → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ f ∧
        fubiniStudyForm.IsHamiltonianVectorField f (X t) :=
  SmoothTwoForm.forall_mpullback_timeDependentFlowOf_eq_iff isSymplectic_fubiniStudyForm.isClosed
    (isCompleteVectorField_timeDependentSuspensionField_onePoint (hX.of_le (by simp))) hX

end QuantumMechanics.Qubit
