/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Qubit.BlochRotation
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
import TauCeti.Geometry.Symplectic.Hamiltonian.CommutingFlow

/-!
# An area-preserving map of the Bloch sphere that is not Hamiltonian

The phase space of a classical qubit is the sphere of pure states `ℙ ℂ (Fin 2 → ℂ) ≅ OnePoint ℂ`
with the Fubini–Study form `ω_FS = ρ(z) dx ∧ dy`, `ρ(z) = 1 / (π (1 + |z|²)²)`. Complex conjugation
`z ↦ conj z` of the Riemann sphere is smooth, preserves the density `ρ`, hence the area, and
pulls `ω_FS` back to `-ω_FS`. The time-`t` map of a Hamiltonian flow pulls `ω_FS` back to itself,
so complex conjugation is the time-`t` map of no Hamiltonian flow. On the Bloch sphere it is the
reflection `(a₀, a₁, a₂) ↦ (a₀, -a₁, a₂)`, the action of the antiunitary complex conjugation of
`ℂ²` (`QuantumMechanics.Qubit.conjAction`).

So "volume-preserving" does not characterize Hamiltonian evolution: the area-preserving
diffeomorphisms of the sphere include orientation-reversing ones.

## Key results

- `QuantumMechanics.Qubit.conjSphere`: complex conjugation of `OnePoint ℂ`.
- `QuantumMechanics.Qubit.contMDiff_conjSphere`: it is smooth as a map of real surfaces.
- `QuantumMechanics.Qubit.fubiniStudyDensity_conj`: it preserves the area density.
- `QuantumMechanics.Qubit.mpullback_conjSphere`: it pulls `ω_FS` back to `-ω_FS`.
- `QuantumMechanics.Qubit.ne_conjSphere_of_mpullback_eq`: no map preserving `ω_FS` is complex
  conjugation.
- `QuantumMechanics.Qubit.globalFlow_ne_conjSphere`: it is not the time-`t` map of a Hamiltonian
  flow.
- `QuantumMechanics.Qubit.equivProjectivization_conjSphere`: under `OnePoint ℂ ≃ ℙ ℂ (Fin 2 → ℂ)`
  it is `conjAction`.
-/

@[expose] public noncomputable section

open Complex ComplexConjugate Matrix Projectivization TauCeti Set
open OnePoint (chartAt_coe chartAt_infty invChart_symm_zero invChart_symm_of_ne_zero
  equivProjectivization equivProjectivization_apply_infinity equivProjectivization_apply_coe
  fubiniStudyDensity fubiniStudyDensity_def fubiniStudyForm eval₂_fubiniStudyForm
  eval₂_fubiniStudyForm_infty isSymplectic_fubiniStudyForm)
open scoped Manifold ContDiff TauCeti.ComplexManifold LinearAlgebra.Projectivization

namespace QuantumMechanics.Qubit

/-- Complex conjugation of the Riemann sphere, fixing `∞`. -/
def conjSphere : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.map conj

@[simp]
lemma conjSphere_coe (z : ℂ) : conjSphere z = (conj z : ℂ) :=
  rfl

@[simp]
lemma conjSphere_infty : conjSphere OnePoint.infty = OnePoint.infty :=
  rfl

lemma conjSphere_conjSphere (x : OnePoint ℂ) : conjSphere (conjSphere x) = x := by
  induction x using OnePoint.rec <;> simp

lemma continuous_conjSphere : Continuous conjSphere :=
  OnePoint.continuous_map continuous_conj <| by
    have h : Filter.Tendsto (starRingEnd ℂ) (Filter.cocompact ℂ) (Filter.cocompact ℂ) :=
      Complex.conjCLE.toHomeomorph.isClosedEmbedding.tendsto_cocompact.congr fun z ↦ by
        simp [Complex.conjCAE_apply]
    simpa using h

/-- In the chart at `x` and the chart at its image, complex conjugation of the sphere is complex
conjugation of `ℂ`. -/
lemma writtenInExtChartAt_conjSphere (x : OnePoint ℂ) :
    writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x conjSphere = conj := by
  funext w
  induction x using OnePoint.rec with
  | coe z => simp [writtenInExtChartAt, chartAt_coe, OnePoint.affineChart_symm_apply]
  | infty =>
    rcases eq_or_ne w 0 with rfl | hw
    · simp [writtenInExtChartAt, chartAt_infty, invChart_symm_zero]
    · simp [writtenInExtChartAt, chartAt_infty, invChart_symm_of_ne_zero hw]

lemma contMDiff_conjSphere : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ conjSphere := fun x ↦ by
  rw [contMDiffAt_iff]
  refine ⟨continuous_conjSphere.continuousAt, ?_⟩
  have h := writtenInExtChartAt_conjSphere x
  simp only [writtenInExtChartAt] at h
  rw [h]
  exact Complex.conjCLE.contDiff.contDiffWithinAt

/-- Complex conjugation as a map of tangent spaces of the sphere, identified with `ℂ`. -/
def conjTangent (x : OnePoint ℂ) :
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (conjSphere x) :=
  Complex.conjCLE.toContinuousLinearMap

lemma conjTangent_apply (x : OnePoint ℂ) (v : TangentSpace 𝓘(ℝ, ℂ) x) :
    conjTangent x v = starRingEnd ℂ v :=
  Complex.conjCLE_apply v

/-- The derivative of complex conjugation of the sphere is complex conjugation, in the charts. -/
lemma hasMFDerivAt_conjSphere (x : OnePoint ℂ) :
    HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) conjSphere x (conjTangent x) := by
  refine ⟨continuous_conjSphere.continuousAt, ?_⟩
  rw [writtenInExtChartAt_conjSphere]
  have hc : (⇑Complex.conjCLE : ℂ → ℂ) = starRingEnd ℂ := funext Complex.conjCLE_apply
  have h := Complex.conjCLE.hasFDerivAt (x := extChartAt 𝓘(ℝ, ℂ) x x)
  rw [hc] at h
  convert h.hasFDerivWithinAt using 1
  ext v
  rfl

/-- The coordinate of the image point is the conjugate coordinate. -/
lemma chartAt_conjSphere (x : OnePoint ℂ) :
    chartAt ℂ (conjSphere x) (conjSphere x) = conj (chartAt ℂ x x) := by
  induction x using OnePoint.rec <;> simp [chartAt_coe, chartAt_infty]

/-- The Fubini–Study density is invariant under complex conjugation. -/
theorem fubiniStudyDensity_conj (z : ℂ) : fubiniStudyDensity (conj z) = fubiniStudyDensity z := by
  simp [fubiniStudyDensity_def]

/-- **Complex conjugation reverses the Fubini–Study form**: it pulls `ω_FS` back to `-ω_FS`. -/
theorem mpullback_conjSphere :
    SmoothForm.mpullback conjSphere contMDiff_conjSphere fubiniStudyForm = -fubiniStudyForm := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, (hasMFDerivAt_conjSphere x).mfderiv,
    SmoothBundleForm.eval₂_neg]
  refine (eval₂_fubiniStudyForm _ _ _).trans
    (Eq.trans ?_ (congrArg Neg.neg (eval₂_fubiniStudyForm x v w)).symm)
  rw [chartAt_conjSphere, fubiniStudyDensity_conj, conjTangent_apply, conjTangent_apply,
    ← mul_neg]
  congr 1
  have key (a b : ℂ) : (conj (conj a) * conj b).im = -(conj a * b).im := by
    simp only [conj_conj, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  exact key v w

/-- The rough form of `mpullback_conjSphere`, in the form produced by Hamiltonian flows. -/
theorem mpullback_conjSphere_coe :
    TauCeti.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) conjSphere fubiniStudyForm.1 = -fubiniStudyForm.1 := by
  rw [← SmoothForm.coe_mpullback conjSphere contMDiff_conjSphere, mpullback_conjSphere]
  rfl

/-- A map that pulls `ω_FS` back to itself is not complex conjugation, which pulls it back to
`-ω_FS`. -/
theorem ne_conjSphere_of_mpullback_eq {φ : OnePoint ℂ → OnePoint ℂ}
    (hφ : TauCeti.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φ fubiniStudyForm.1 = fubiniStudyForm.1) :
    φ ≠ conjSphere := by
  rintro rfl
  rw [mpullback_conjSphere_coe] at hφ
  have h2 : fubiniStudyForm.1 OnePoint.infty ![(1 : ℂ), I] = Real.pi⁻¹ :=
    (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans
      ((eval₂_fubiniStudyForm_infty 1 I).trans (by simp))
  have h3 := congrArg (fun α ↦ α OnePoint.infty ![(1 : ℂ), I]) hφ
  simp only [Pi.neg_apply, ContinuousAlternatingMap.neg_apply, h2] at h3
  have hπ : 0 < Real.pi⁻¹ := inv_pos.mpr Real.pi_pos
  linarith

/-- **Complex conjugation is not Hamiltonian.** For a `C²` Hamiltonian vector field `X` of a `C²`
function on the Riemann sphere with the Fubini–Study form, no time-`t` map of the flow of `X` is
complex conjugation, although complex conjugation preserves the area. -/
theorem globalFlow_ne_conjSphere {f : OnePoint ℂ → ℝ}
    {X : (x : OnePoint ℂ) → TangentSpace 𝓘(ℝ, ℂ) x}
    (hX : fubiniStudyForm.IsHamiltonianVectorField f X) (hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) 2 f)
    (hv : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ).tangent 2
      (fun y ↦ (⟨y, X y⟩ : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ))))
    (t : ℝ) :
    globalFlow X (hv.of_le one_le_two)
      (isCompleteVectorField_of_compactSpace (hv.of_le one_le_two)) t ≠ conjSphere :=
  ne_conjSphere_of_mpullback_eq (hX.mpullback_globalFlow isSymplectic_fubiniStudyForm.isClosed hf
    (isCompleteVectorField_of_compactSpace (hv.of_le one_le_two)) hv t)

/-- Under the identification `OnePoint ℂ ≃ ℙ ℂ (Fin 2 → ℂ)`, `z ↦ [z : 1]`, complex conjugation
of the sphere is the antiunitary complex conjugation of rays. -/
theorem equivProjectivization_conjSphere (x : OnePoint ℂ) :
    equivProjectivization ℂ (conjSphere x) = conjAction (equivProjectivization ℂ x) := by
  induction x using OnePoint.rec with
  | infty =>
    simp only [conjSphere_infty, equivProjectivization_apply_infinity, conjAction,
      Projectivization.map_mk]
    congr 1
    ext i
    fin_cases i <;> simp
  | coe z =>
    simp only [conjSphere_coe, equivProjectivization_apply_coe, conjAction,
      Projectivization.map_mk]
    congr 1
    ext i
    fin_cases i <;> simp

end QuantumMechanics.Qubit
