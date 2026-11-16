/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.InformationTheory.ChangeOfVariables
public import Mathlib.LinearAlgebra.SymplecticGroup

import ForMathlib.InformationTheory.EntropyPreserving
import ForMathlib.LinearAlgebra.BilinearMap.OrthogonalityPreserving
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# Further results: the classical counterpart

Not part of the brief. This file formalizes Sec. 1 of `further-results.tex` in the brief's
directory: the classical statement that the brief's conclusion cites, "Hamiltonian evolution is
equivalent to the preservation of Shannon entropy (Liouville's theorem) and of the definitional
independence of degrees of freedom".

The phase space of `n` degrees of freedom is `ℝ²ⁿ`, here `PhaseSpace ι = ι ⊕ ι → ℝ` with
`ξ (inl i) = qᵢ` and `ξ (inr i) = pᵢ`, and `ω(u, v) = ∑ᵢ (u_qᵢ v_pᵢ - u_pᵢ v_qᵢ)` is the symplectic
form (`symplecticForm`). An evolution `φ t₀ t₁ : PhaseSpace ι → PhaseSpace ι` from time `t₀` to
time `t₁` is deterministic and reversible: `φ t t = id` and `φ t₁ t₂ ∘ φ t₀ t₁ = φ t₀ t₂` for all
times, so `φ t₁ t₀` reconstructs the past. It is also differentiable: `(t, ξ) ↦ φ t₀ t ξ` is `C²`
(`IsFlow`). Its displacement field is `S t ξ = ∂ₛ φ t s ξ` at `s = t` (`displacement`). The
conditions are:

* `IsHamiltonian φ` (Hamilton's equations): there is `H t ξ` with `dH = ω(S, ·)`, that is,
  `q̇ᵢ = ∂H/∂pᵢ` and `ṗᵢ = -∂H/∂qᵢ` along every orbit (`IsFlow.hamilton_equations`);
* `PreservesEntropy φ` (DR-INFO): every probability density `ρ` and its evolution, the density
  `ρ ∘ φ⁻¹ / |det Dφ|` of the evolved ensemble, have the same Shannon (differential) entropy;
* `PreservesIndependence φ` (independence of degrees of freedom): the linearized evolution maps
  `ω`-orthogonal displacements to `ω`-orthogonal displacements. Two degrees of freedom are
  independent exactly when they are `ω`-orthogonal, and the area within each is `ω`.

`IsFlow.isHamiltonian_iff` proves
`IsHamiltonian φ ↔ PreservesEntropy φ ∧ PreservesIndependence φ`. The proof follows the quantum
one. Entropy is preserved iff `|det Dφ| = 1`. A linear map that preserves `ω`-orthogonality
multiplies `ω` by a constant `c`, and `|det| = 1` gives `c = ±1`, the analogue of Wigner's
unitary or anti-unitary. Continuity in time from `φ t₀ t₀ = id` excludes `c = -1`, so the
evolution is symplectic (`IsSymplectic`). Differentiating at `t₁ = t₀`, the 1-form `ω(S, ·)` is
closed, and on `ℝ²ⁿ` the Poincaré lemma gives `H`. Conversely, along a Hamiltonian flow
`ω(Dφ u, Dφ v)` has derivative zero, so the flow is symplectic, and then `det Dφ = 1`
(Liouville, `IsSymplectic.det_eq_one`).

For one degree of freedom every linear map preserves `ω`-orthogonality, and entropy alone is
equivalent (`IsFlow.isHamiltonian_iff_preservesEntropy`). For two it is not: a squeeze preserves
the entropy but is not Hamiltonian (`squeezeFlow_counterexample`), and a dilation preserves the
independence of degrees of freedom but not the entropy (`dilationFlow_counterexample`).

The differentiability `IsFlow.contDiff` is assumed on both sides; Mathlib does not have the
smooth dependence of solutions of ODEs on their initial values, which would derive it from a
smooth `H`.

The comparator lane, which certifies the main file of the brief, does not depend on this module.

## Main results

* `IsFlow.isHamiltonian_iff`: Hamiltonian iff entropy and independence of degrees of freedom
  are preserved;
* `IsFlow.isHamiltonian_iff_isSymplectic`: Hamiltonian iff symplectic;
* `IsFlow.isSymplectic_iff`: symplectic iff entropy and independence are preserved;
* `IsSymplectic.det_eq_one`: Liouville's theorem, `det Dφ = 1`;
* `IsFlow.isHamiltonian_iff_preservesEntropy`: for one degree of freedom, entropy suffices;
* `squeezeFlow_counterexample`, `dilationFlow_counterexample`: for two degrees of freedom,
  neither condition suffices alone.
-/

open Matrix Real MeasureTheory Function Set ContinuousLinearMap

@[expose] public noncomputable section

namespace UnitaryEntropy.FurtherResults

/-! ### Two-variable calculus -/

section Calculus

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

section Partial

variable {F : ℝ × X → Y}

/-- The `ξ`-derivative of `F (s, ·)` is the derivative of `F` along `inr`. -/
theorem hasFDerivAt_partial_right (hF : Differentiable ℝ F) (s : ℝ) (y : X) :
    HasFDerivAt (fun y => F (s, y)) ((fderiv ℝ F (s, y)).comp (inr ℝ ℝ X)) y :=
  (hF (s, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)

/-- The `s`-derivative of `F (·, y)` is the derivative of `F` along `(1, 0)`. -/
theorem hasDerivAt_partial_left (hF : Differentiable ℝ F) (s : ℝ) (y : X) :
    HasDerivAt (fun s => F (s, y)) (fderiv ℝ F (s, y) (1, 0)) s :=
  (hF (s, y)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s y))

end Partial

variable {F : ℝ × X → X}

/-- The mixed derivative `∂ₛ ∂_ξ F` at `(t, y)`. -/
noncomputable def mixedDeriv (F : ℝ × X → X) (t : ℝ) (y : X) : X →L[ℝ] X :=
  (fderiv ℝ (fderiv ℝ F) (t, y) (1, 0)).comp (inr ℝ ℝ X)

variable (hF : ContDiff ℝ 2 F)
include hF

/-- `s ↦ ∂_ξ F (s, y)` has derivative `mixedDeriv F t y` at `t`. -/
theorem hasDerivAt_fderiv_partial (t : ℝ) (y : X) :
    HasDerivAt (fun s => fderiv ℝ (fun y => F (s, y)) y) (mixedDeriv F t y) t := by
  have h1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h3 : HasDerivAt (fun s => fderiv ℝ F (s, y)) (fderiv ℝ (fderiv ℝ F) (t, y) (1, 0)) t :=
    hasDerivAt_partial_left h2 t y
  have h4 := h3.clm_comp (hasDerivAt_const t (inr ℝ ℝ X))
  simp only [comp_zero, add_zero] at h4
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  exact (hasFDerivAt_partial_right h1 s y).fderiv

/-- `ξ ↦ ∂ₛ F (s, ξ)` at `s = t` has derivative `mixedDeriv F t y` at `y`: the mixed partial
derivatives agree. -/
theorem hasFDerivAt_deriv_partial (t : ℝ) (y : X) :
    HasFDerivAt (fun y => deriv (fun s => F (s, y)) t) (mixedDeriv F t y) y := by
  have h1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hc : HasFDerivAt (fun y => fderiv ℝ F (t, y))
      ((fderiv ℝ (fderiv ℝ F) (t, y)).comp (inr ℝ ℝ X)) y :=
    hasFDerivAt_partial_right h2 t y
  have h4 := hc.clm_apply (hasFDerivAt_const ((1 : ℝ), (0 : X)) y)
  simp only [comp_zero, zero_add] at h4
  have hsymm : IsSymmSndFDerivAt ℝ F (t, y) :=
    ContDiffAt.isSymmSndFDerivAt hF.contDiffAt (by simp)
  have heq : (((fderiv ℝ (fderiv ℝ F) (t, y)).comp (inr ℝ ℝ X)).flip ((1 : ℝ), (0 : X))) =
      mixedDeriv F t y := by
    ext1 u
    simp only [flip_apply, coe_comp, Function.comp_apply, inr_apply, mixedDeriv]
    exact hsymm _ _
  rw [heq] at h4
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  exact (hasDerivAt_partial_left h1 t y).deriv

end Calculus

/-! ### Phase space -/

/-- The phase space of the degrees of freedom `ι`: `ξ (inl i) = qᵢ`, `ξ (inr i) = pᵢ`. -/
abbrev PhaseSpace (ι : Type) := ι ⊕ ι → ℝ

variable {ι : Type} [Fintype ι]

/-! ### Evolutions of phase space -/

/-- An evolution of phase space from time `t₀` to time `t₁` that is deterministic and reversible
(`φ t t = id`, `φ t₁ t₂ ∘ φ t₀ t₁ = φ t₀ t₂` for all times) and differentiable (EVDIFF:
`(t, ξ) ↦ φ t₀ t ξ` is `C²`). -/
structure IsFlow (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) : Prop where
  apply_self : ∀ t ξ, φ t t ξ = ξ
  apply_apply : ∀ t₀ t₁ t₂ ξ, φ t₁ t₂ (φ t₀ t₁ ξ) = φ t₀ t₂ ξ
  contDiff : ∀ t₀, ContDiff ℝ 2 fun z : ℝ × PhaseSpace ι => φ t₀ z.1 z.2

/-- The displacement field `S t ξ = ∂ₛ φ t s ξ` at `s = t`. -/
def displacement (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) (t : ℝ) (ξ : PhaseSpace ι) :
    PhaseSpace ι :=
  deriv (fun s => φ t s ξ) t

/-- The derivative of the displacement field: `∂ₛ D(φ t s)` at `s = t`. -/
def displacementDeriv (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) (t : ℝ) (ξ : PhaseSpace ι) :
    PhaseSpace ι →L[ℝ] PhaseSpace ι :=
  mixedDeriv (fun z : ℝ × PhaseSpace ι => φ t z.1 z.2) t ξ

namespace IsFlow

variable {φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι} (hφ : IsFlow φ)
include hφ

theorem contDiff_apply (t₀ t₁ : ℝ) : ContDiff ℝ 2 (φ t₀ t₁) :=
  (hφ.contDiff t₀).comp (contDiff_const.prodMk contDiff_id)

theorem hasFDerivAt (t₀ t₁ : ℝ) (ξ : PhaseSpace ι) :
    HasFDerivAt (φ t₀ t₁) (fderiv ℝ (φ t₀ t₁) ξ) ξ :=
  ((hφ.contDiff_apply t₀ t₁).differentiable (by norm_num) ξ).hasFDerivAt

theorem continuous_fderiv (t₀ t₁ : ℝ) : Continuous (fderiv ℝ (φ t₀ t₁)) :=
  (hφ.contDiff_apply t₀ t₁).continuous_fderiv (by norm_num)

theorem injective (t₀ t₁ : ℝ) : Injective (φ t₀ t₁) :=
  fun ξ η h => by rw [← hφ.apply_self t₀ ξ, ← hφ.apply_self t₀ η, ← hφ.apply_apply t₀ t₁ t₀ ξ,
    ← hφ.apply_apply t₀ t₁ t₀ η, h]

theorem fderiv_self (t : ℝ) (ξ : PhaseSpace ι) : fderiv ℝ (φ t t) ξ = .id ℝ _ := by
  have : φ t t = id := funext (hφ.apply_self t)
  rw [this, fderiv_id]

theorem fderiv_apply_apply (t₀ t₁ t₂ : ℝ) (ξ : PhaseSpace ι) :
    fderiv ℝ (φ t₀ t₂) ξ = (fderiv ℝ (φ t₁ t₂) (φ t₀ t₁ ξ)).comp (fderiv ℝ (φ t₀ t₁) ξ) := by
  have : φ t₀ t₂ = φ t₁ t₂ ∘ φ t₀ t₁ := funext fun ξ => (hφ.apply_apply t₀ t₁ t₂ ξ).symm
  rw [this]
  exact ((hφ.hasFDerivAt t₁ t₂ _).comp ξ (hφ.hasFDerivAt t₀ t₁ ξ)).fderiv

theorem det_ne_zero (t₀ t₁ : ℝ) (ξ : PhaseSpace ι) : (fderiv ℝ (φ t₀ t₁) ξ).det ≠ 0 := by
  have h := congrArg ContinuousLinearMap.det (hφ.fderiv_apply_apply t₀ t₁ t₀ ξ)
  rw [hφ.fderiv_self] at h
  have h1 : LinearMap.det (fderiv ℝ (φ t₁ t₀) (φ t₀ t₁ ξ) : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι) *
      LinearMap.det (fderiv ℝ (φ t₀ t₁) ξ : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι) = 1 := by
    rw [← LinearMap.det_comp]
    calc _ = (fderiv ℝ (φ t₁ t₀) (φ t₀ t₁ ξ) ∘SL fderiv ℝ (φ t₀ t₁) ξ).det := rfl
      _ = 1 := by rw [← h, ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  exact right_ne_zero_of_mul (h1 ▸ one_ne_zero)

/-- The displacement field has derivative `displacementDeriv`. -/
theorem hasFDerivAt_displacement (t : ℝ) (ξ : PhaseSpace ι) :
    HasFDerivAt (displacement φ t) (displacementDeriv φ t ξ) ξ :=
  hasFDerivAt_deriv_partial (hφ.contDiff t) t ξ

/-- `s ↦ D(φ t s)` has derivative `displacementDeriv φ t ξ` at `s = t`. -/
theorem hasDerivAt_fderiv_self (t : ℝ) (ξ : PhaseSpace ι) :
    HasDerivAt (fun s => fderiv ℝ (φ t s) ξ) (displacementDeriv φ t ξ) t :=
  hasDerivAt_fderiv_partial (hφ.contDiff t) t ξ

/-- The variational equation: `∂ₛ D(φ t₀ s) = DS(φ t₀ s) ∘ D(φ t₀ s)`. -/
theorem hasDerivAt_fderiv (t₀ s : ℝ) (ξ : PhaseSpace ι) :
    HasDerivAt (fun s => fderiv ℝ (φ t₀ s) ξ)
      ((displacementDeriv φ s (φ t₀ s ξ)).comp (fderiv ℝ (φ t₀ s) ξ)) s := by
  have h := (hφ.hasDerivAt_fderiv_self s (φ t₀ s ξ)).clm_comp
    (hasDerivAt_const s (fderiv ℝ (φ t₀ s) ξ))
  simp only [comp_zero, add_zero] at h
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s' => ?_)
  exact hφ.fderiv_apply_apply t₀ s s' ξ

theorem continuous_fderiv_time (t₀ : ℝ) (ξ : PhaseSpace ι) :
    Continuous fun s => fderiv ℝ (φ t₀ s) ξ :=
  continuous_iff_continuousAt.2 fun s => (hφ.hasDerivAt_fderiv t₀ s ξ).continuousAt

/-- Every orbit moves with the displacement field. -/
theorem hasDerivAt_orbit (t₀ s : ℝ) (ξ : PhaseSpace ι) :
    HasDerivAt (fun s => φ t₀ s ξ) (displacement φ s (φ t₀ s ξ)) s := by
  have h : HasDerivAt (fun s' => φ s s' (φ t₀ s ξ)) (displacement φ s (φ t₀ s ξ)) s :=
    ((hasDerivAt_partial_left ((hφ.contDiff s).differentiable (by norm_num)) s
      (φ t₀ s ξ)).differentiableAt).hasDerivAt
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s' => ?_)
  exact (hφ.apply_apply t₀ s s' ξ).symm

end IsFlow

/-! ### The symplectic form -/

variable [DecidableEq ι]

/-- The symplectic form `ω(u, v) = ∑ᵢ (u_qᵢ v_pᵢ - u_pᵢ v_qᵢ)`, with matrix `-J`. -/
noncomputable def symplecticForm : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι →ₗ[ℝ] ℝ :=
  Matrix.toLinearMap₂' ℝ (-J ι ℝ)

theorem symplecticForm_apply (u v : PhaseSpace ι) :
    symplecticForm u v = ∑ i, (u (.inl i) * v (.inr i) - u (.inr i) * v (.inl i)) := by
  simp only [symplecticForm, Matrix.toLinearMap₂'_apply', dotProduct, mulVec, J,
    Fintype.sum_sum_type, Matrix.neg_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, neg_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_const_zero, add_zero, mul_neg, ← sub_eq_add_neg]
  rw [Finset.sum_sub_distrib]
  simp only [zero_sub, mul_neg, Finset.sum_neg_distrib]
  ring

theorem symplecticForm_swap (u v : PhaseSpace ι) : symplecticForm v u = -symplecticForm u v := by
  simp only [symplecticForm_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symplecticForm_self (u : PhaseSpace ι) : symplecticForm u u = 0 := by
  simp [symplecticForm_apply, mul_comm]

/-- The unit vector of `qᵢ` or `pᵢ`. -/
abbrev unitVec (k : ι ⊕ ι) : PhaseSpace ι := Pi.single k 1

theorem symplecticForm_unitVec_inr (u : PhaseSpace ι) (i : ι) :
    symplecticForm u (unitVec (.inr i)) = u (.inl i) := by
  simp [symplecticForm_apply, Pi.single_apply]

theorem symplecticForm_unitVec_inl (u : PhaseSpace ι) (i : ι) :
    symplecticForm u (unitVec (.inl i)) = -u (.inr i) := by
  simp [symplecticForm_apply, Pi.single_apply]

theorem symplecticForm_unitVec (i : ι) :
    symplecticForm (unitVec (.inl i)) (unitVec (.inr i)) = 1 := by
  simp [symplecticForm_unitVec_inr]

/-- `ω` is nondegenerate. -/
theorem symplecticForm_ne_zero {u : PhaseSpace ι} (hu : u ≠ 0) : symplecticForm u ≠ 0 := by
  intro h
  apply hu
  funext k
  rcases k with i | i
  · simpa [symplecticForm_unitVec_inr] using LinearMap.congr_fun h (unitVec (.inr i))
  · simpa [symplecticForm_unitVec_inl] using LinearMap.congr_fun h (unitVec (.inl i))

/-- `ω` as a continuous bilinear map. -/
noncomputable def symplecticCLM : PhaseSpace ι →L[ℝ] PhaseSpace ι →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap ∘ₗ (symplecticForm (ι := ι)))

@[simp] theorem symplecticCLM_apply (u v : PhaseSpace ι) :
    symplecticCLM u v = symplecticForm u v := rfl

attribute [irreducible] symplecticCLM

/-- A linear map that multiplies `ω` by `c` has `det² = c²ⁿ`. -/
theorem det_sq_eq_of_symplecticForm (A : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι) (c : ℝ)
    (h : ∀ u v, symplecticForm (A u) (A v) = c * symplecticForm u v) :
    LinearMap.det A ^ 2 = c ^ (2 * Fintype.card ι) := by
  have hB : (symplecticForm (ι := ι)).compl₁₂ A A = c • symplecticForm := by
    ext u v
    simp [h]
  have hM := congrArg (LinearMap.toMatrix₂' ℝ) hB
  rw [LinearMap.toMatrix₂'_compl₁₂, map_smul, symplecticForm,
    LinearMap.toMatrix'_toLinearMap₂'] at hM
  have hd := congrArg Matrix.det hM
  rw [det_mul, det_mul, det_transpose, det_smul, LinearMap.det_toMatrix'] at hd
  have hJ : (-J ι ℝ).det ≠ 0 := by
    rw [det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_J ι ℝ).ne_zero
  rw [Fintype.card_sum, ← two_mul] at hd
  have : LinearMap.det A * LinearMap.det A = c ^ (2 * Fintype.card ι) :=
    mul_right_cancel₀ hJ (by linear_combination hd)
  rw [sq, this]


/-- The derivative in time of `ω(L s u, L s v)`. -/
theorem hasDerivAt_symplecticForm {L : ℝ → PhaseSpace ι →L[ℝ] PhaseSpace ι}
    {L' : PhaseSpace ι →L[ℝ] PhaseSpace ι} {s : ℝ} (hL : HasDerivAt L L' s) (u v : PhaseSpace ι) :
    HasDerivAt (fun s => symplecticForm (L s u) (L s v))
      (symplecticForm (L' u) (L s v) + symplecticForm (L s u) (L' v)) s := by
  have hu := hL.clm_apply (hasDerivAt_const s u)
  have hv := hL.clm_apply (hasDerivAt_const s v)
  simp only [map_zero, add_zero] at hu hv
  have hu' := hasDerivAt_pi.1 hu
  have hv' := hasDerivAt_pi.1 hv
  simp only [symplecticForm_apply]
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    ((hu' (.inl i)).mul (hv' (.inr i))).sub ((hu' (.inr i)).mul (hv' (.inl i)))
  convert h using 1
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### The conditions -/

/-- **Hamilton's equations.** There is a Hamiltonian `H t ξ` with `dH = ω(S, ·)`: `q̇ᵢ = ∂H/∂pᵢ`
and `ṗᵢ = -∂H/∂qᵢ` (`IsHamiltonian.hasDerivAt_q`, `IsHamiltonian.hasDerivAt_p`). -/
def IsHamiltonian (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) : Prop :=
  ∃ H : ℝ → PhaseSpace ι → ℝ, ∀ t ξ, HasFDerivAt (H t) (symplecticCLM (displacement φ t ξ)) ξ

/-- The evolution of a density `ρ` from `t₀` to `t₁`: `ρ ∘ φ⁻¹ / |det Dφ|` on the range. -/
def evolveDensity (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) (t₀ t₁ : ℝ)
    (ρ : PhaseSpace ι → ℝ) : PhaseSpace ι → ℝ :=
  pushDensity (φ t₀ t₁) (fderiv ℝ (φ t₀ t₁)) ρ

/-- **DR-INFO.** The evolution preserves the Shannon entropy of every probability density. -/
def PreservesEntropy (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) : Prop :=
  ∀ t₀ t₁ (ρ : PhaseSpace ι → ℝ), (∀ ξ, 0 ≤ ρ ξ) → Integrable ρ → ∫ ξ, ρ ξ = 1 →
    ∫ ξ, negMulLog (evolveDensity φ t₀ t₁ ρ ξ) = ∫ ξ, negMulLog (ρ ξ)

/-- **Independence of degrees of freedom.** The linearized evolution maps `ω`-orthogonal
displacements to `ω`-orthogonal displacements. -/
def PreservesIndependence (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) : Prop :=
  ∀ t₀ t₁ ξ u v, symplecticForm u v = 0 →
    symplecticForm (fderiv ℝ (φ t₀ t₁) ξ u) (fderiv ℝ (φ t₀ t₁) ξ v) = 0

/-- The linearized evolution preserves `ω`. -/
def IsSymplectic (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) : Prop :=
  ∀ t₀ t₁ ξ u v,
    symplecticForm (fderiv ℝ (φ t₀ t₁) ξ u) (fderiv ℝ (φ t₀ t₁) ξ v) = symplecticForm u v



/-! ### Hamiltonian evolution is symplectic, and conversely -/

variable {φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι}

namespace IsFlow

variable (hφ : IsFlow φ)
include hφ

/-- If `dH = ω(S, ·)`, then `ω(DS a, b) = ω(DS b, a)`: the second derivative of `H` is
symmetric. -/
theorem symplecticForm_displacementDeriv_of_hasFDerivAt {H : PhaseSpace ι → ℝ} {t : ℝ}
    (hH : ∀ ξ, HasFDerivAt H (symplecticCLM (displacement φ t ξ)) ξ) (ξ a b : PhaseSpace ι) :
    symplecticForm (displacementDeriv φ t ξ a) b =
      symplecticForm (displacementDeriv φ t ξ b) a := by
  have h2 : HasFDerivAt (fun η => symplecticCLM (displacement φ t η))
      (symplecticCLM.comp (displacementDeriv φ t ξ)) ξ :=
    symplecticCLM.hasFDerivAt.comp ξ (hφ.hasFDerivAt_displacement t ξ)
  have := second_derivative_symmetric_of_eventually (Filter.Eventually.of_forall hH) h2 a b
  simp only [ContinuousLinearMap.comp_apply, symplecticCLM_apply] at this
  exact this

/-- If every `DS` is infinitesimally symplectic, then the evolution is symplectic: along the
variational equation `ω(Dφ u, Dφ v)` has derivative zero. -/
theorem isSymplectic_of_forall
    (hA : ∀ t ξ a b, symplecticForm (displacementDeriv φ t ξ a) b =
      symplecticForm (displacementDeriv φ t ξ b) a) : IsSymplectic φ := by
  intro t₀ t₁ ξ u v
  set g := fun s => symplecticForm (fderiv ℝ (φ t₀ s) ξ u) (fderiv ℝ (φ t₀ s) ξ v) with hg_def
  have hg : ∀ s, HasDerivAt g 0 s := fun s => by
    have := hasDerivAt_symplecticForm (hφ.hasDerivAt_fderiv t₀ s ξ) u v
    convert this using 1
    simp only [ContinuousLinearMap.comp_apply]
    rw [symplecticForm_swap (displacementDeriv φ s (φ t₀ s ξ) (fderiv ℝ (φ t₀ s) ξ v)),
      hA s _ (fderiv ℝ (φ t₀ s) ξ u)]
    ring
  have := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv)
    t₁ t₀
  simpa [g, hφ.fderiv_self] using this

/-- **Hamiltonian evolution is symplectic.** -/
theorem isSymplectic_of_isHamiltonian (h : IsHamiltonian φ) : IsSymplectic φ := by
  obtain ⟨H, hH⟩ := h
  exact hφ.isSymplectic_of_forall fun t ξ a b =>
    hφ.symplecticForm_displacementDeriv_of_hasFDerivAt (hH t) ξ a b

/-- A symplectic evolution has an infinitesimally symplectic displacement field. -/
theorem symplecticForm_displacementDeriv_of_isSymplectic (h : IsSymplectic φ) (t : ℝ)
    (ξ a b : PhaseSpace ι) :
    symplecticForm (displacementDeriv φ t ξ a) b =
      symplecticForm (displacementDeriv φ t ξ b) a := by
  have h1 := hasDerivAt_symplecticForm (hφ.hasDerivAt_fderiv_self t ξ) a b
  have h0 : HasDerivAt
      (fun s => symplecticForm (fderiv ℝ (φ t s) ξ a) (fderiv ℝ (φ t s) ξ b)) 0 t := by
    have : (fun s => symplecticForm (fderiv ℝ (φ t s) ξ a) (fderiv ℝ (φ t s) ξ b)) =
        fun _ => symplecticForm a b := funext fun s => h t s ξ a b
    rw [this]
    exact hasDerivAt_const _ _
  have := h1.unique h0
  rw [hφ.fderiv_self] at this
  simp only [ContinuousLinearMap.id_apply] at this
  have hs := symplecticForm_swap (displacementDeriv φ t ξ b) a
  linarith

/-- **A symplectic evolution is Hamiltonian.** The 1-form `ω(S, ·)` is closed, and on phase space
the Poincaré lemma gives `H`. -/
theorem isHamiltonian_of_isSymplectic (h : IsSymplectic φ) : IsHamiltonian φ := by
  have : ∀ t, ∃ H : PhaseSpace ι → ℝ,
      ∀ ξ, HasFDerivAt H (symplecticCLM (displacement φ t ξ)) ξ := fun t => by
    have hα : ∀ ξ, HasFDerivAt (fun η => symplecticCLM (displacement φ t η))
        (symplecticCLM.comp (displacementDeriv φ t ξ)) ξ := fun ξ =>
      symplecticCLM.hasFDerivAt.comp ξ (hφ.hasFDerivAt_displacement t ξ)
    obtain ⟨H, hH⟩ := convex_univ.exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_univ
      (fun ξ _ => (hα ξ).differentiableAt.differentiableWithinAt) fun a _ x y => by
        rw [(hα a).fderiv]
        simp only [ContinuousLinearMap.comp_apply, symplecticCLM_apply]
        exact hφ.symplecticForm_displacementDeriv_of_isSymplectic h t a x y
    exact ⟨H, fun ξ => hH ξ (mem_univ ξ)⟩
  choose H hH using this
  exact ⟨H, hH⟩

/-- **Hamiltonian iff symplectic.** -/
theorem isHamiltonian_iff_isSymplectic : IsHamiltonian φ ↔ IsSymplectic φ :=
  ⟨hφ.isSymplectic_of_isHamiltonian, hφ.isHamiltonian_of_isSymplectic⟩

end IsFlow


/-! ### Entropy and the independence of degrees of freedom -/

namespace IsSymplectic

/-- **Liouville's theorem.** A symplectic evolution has `det Dφ = 1`. -/
theorem det_eq_one (h : IsSymplectic φ) (t₀ t₁ : ℝ) (ξ : PhaseSpace ι) :
    (fderiv ℝ (φ t₀ t₁) ξ).det = 1 := by
  set D : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι := ↑(fderiv ℝ (φ t₀ t₁) ξ)
  have hB : (symplecticForm (ι := ι)).compl₁₂ D D = symplecticForm :=
    LinearMap.ext₂ fun u v => h t₀ t₁ ξ u v
  have hM := congrArg (LinearMap.toMatrix₂' ℝ) hB
  rw [LinearMap.toMatrix₂'_compl₁₂, symplecticForm, LinearMap.toMatrix'_toLinearMap₂'] at hM
  have hJ : LinearMap.toMatrix' D ∈ symplecticGroup ι ℝ := by
    rw [SymplecticGroup.mem_iff']
    simpa [Matrix.mul_neg, Matrix.neg_mul] using hM
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix']
  exact SymplecticGroup.det_eq_one hJ

theorem preservesIndependence (h : IsSymplectic φ) : PreservesIndependence φ :=
  fun t₀ t₁ ξ u v huv => by rw [h, huv]

theorem preservesEntropy (h : IsSymplectic φ) (hφ : IsFlow φ) : PreservesEntropy φ :=
  fun t₀ t₁ ρ _ _ _ => integral_negMulLog_pushDensity_of_abs_det_eq_one (hφ.hasFDerivAt t₀ t₁)
    (hφ.injective t₀ t₁) (fun ξ => by rw [h.det_eq_one]; simp) ρ

end IsSymplectic

namespace IsFlow

variable (hφ : IsFlow φ)
include hφ

omit [DecidableEq ι] in
/-- DR-INFO gives `|det Dφ| = 1`. -/
theorem abs_det_eq_one_of_preservesEntropy (h : PreservesEntropy φ) (t₀ t₁ : ℝ)
    (ξ : PhaseSpace ι) : |(fderiv ℝ (φ t₀ t₁) ξ).det| = 1 :=
  abs_det_eq_one_of_integral_negMulLog_pushDensity (hφ.hasFDerivAt t₀ t₁) (hφ.injective t₀ t₁)
    (hφ.det_ne_zero t₀ t₁) (hφ.continuous_fderiv t₀ t₁) (h t₀ t₁) ξ

omit hφ in
/-- Preserving the independence of degrees of freedom multiplies `ω` by a constant. -/
theorem exists_symplecticForm_eq_mul (h : PreservesIndependence φ) (t₀ t₁ : ℝ)
    (ξ : PhaseSpace ι) : ∃ c : ℝ, ∀ u v,
      symplecticForm (fderiv ℝ (φ t₀ t₁) ξ u) (fderiv ℝ (φ t₀ t₁) ξ v) =
        c * symplecticForm u v := by
  set D : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι := ↑(fderiv ℝ (φ t₀ t₁) ξ)
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_of_forall_isOrtho_imp
    (B := symplecticForm) (B' := (symplecticForm (ι := ι)).compl₁₂ D D)
    (fun u hu => symplecticForm_ne_zero hu) fun u v huv => h t₀ t₁ ξ u v huv
  exact ⟨c, fun u v => LinearMap.congr_fun (LinearMap.congr_fun hc u) v⟩

/-- **Entropy and independence give a symplectic evolution.** At each time `ω` is multiplied by
`κ t = ±1`; `κ` is continuous with `κ t₀ = 1`, so `κ = 1`. -/
theorem isSymplectic_of_preservesEntropy_of_preservesIndependence (hE : PreservesEntropy φ)
    (hI : PreservesIndependence φ) : IsSymplectic φ := by
  intro t₀ t₁ ξ u v
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · simp [symplecticForm_apply]
  set e : PhaseSpace ι := unitVec (.inl i₀)
  set f : PhaseSpace ι := unitVec (.inr i₀)
  set κ : ℝ → ℝ := fun t => symplecticForm (fderiv ℝ (φ t₀ t) ξ e) (fderiv ℝ (φ t₀ t) ξ f)
  have hmul : ∀ t u v, symplecticForm (fderiv ℝ (φ t₀ t) ξ u) (fderiv ℝ (φ t₀ t) ξ v) =
      κ t * symplecticForm u v := fun t u v => by
    obtain ⟨c, hc⟩ := exists_symplecticForm_eq_mul hI t₀ t ξ
    have hce : κ t = c := by simp only [κ, hc, e, f, symplecticForm_unitVec, mul_one]
    rw [hce, hc]
  have hsq : ∀ t, κ t ^ 2 = 1 := fun t => by
    have hd := det_sq_eq_of_symplecticForm
      (↑(fderiv ℝ (φ t₀ t) ξ) : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι) (κ t) (hmul t)
    have h1 : LinearMap.det (fderiv ℝ (φ t₀ t) ξ : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι) ^ 2 = 1 := by
      rw [← sq_abs]
      have := hφ.abs_det_eq_one_of_preservesEntropy hE t₀ t ξ
      rw [ContinuousLinearMap.det] at this
      rw [this, one_pow]
    rw [h1, pow_mul] at hd
    exact (pow_eq_one_iff_of_nonneg (sq_nonneg _) (Fintype.card_pos_iff.2 ⟨i₀⟩).ne').1 hd.symm
  have hκ : Continuous κ := continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_symplecticForm (hφ.hasDerivAt_fderiv t₀ s ξ) e f).continuousAt
  have hκ0 : κ t₀ = 1 := by
    simp only [κ, hφ.fderiv_self, ContinuousLinearMap.id_apply, e, f, symplecticForm_unitVec]
  have hκ1 : κ t₁ = 1 := by
    by_contra hne
    have hneg : κ t₁ = -1 := by
      have h2 : (κ t₁ - 1) * (κ t₁ + 1) = 0 := by linear_combination hsq t₁
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd (by linarith) hne
      · linarith
    obtain ⟨t, ht⟩ : (0 : ℝ) ∈ range κ :=
      intermediate_value_univ t₁ t₀ hκ ⟨by rw [hneg]; norm_num, by rw [hκ0]; norm_num⟩
    have := hsq t
    rw [ht] at this
    norm_num at this
  rw [hmul, hκ1, one_mul]

/-- **Symplectic iff entropy and independence of degrees of freedom are preserved.** -/
theorem isSymplectic_iff : IsSymplectic φ ↔ PreservesEntropy φ ∧ PreservesIndependence φ :=
  ⟨fun h => ⟨h.preservesEntropy hφ, h.preservesIndependence⟩,
    fun h => hφ.isSymplectic_of_preservesEntropy_of_preservesIndependence h.1 h.2⟩

/-- **The classical counterpart.** An evolution is Hamiltonian iff it preserves the Shannon
entropy and the independence of degrees of freedom. -/
theorem isHamiltonian_iff : IsHamiltonian φ ↔ PreservesEntropy φ ∧ PreservesIndependence φ :=
  hφ.isHamiltonian_iff_isSymplectic.trans hφ.isSymplectic_iff

/-- **Hamilton's equations** along every orbit: `q̇ᵢ = ∂H/∂pᵢ`, `ṗᵢ = -∂H/∂qᵢ`. -/
theorem hamilton_equations {H : ℝ → PhaseSpace ι → ℝ}
    (hH : ∀ t ξ, HasFDerivAt (H t) (symplecticCLM (displacement φ t ξ)) ξ) (t₀ s : ℝ)
    (ξ : PhaseSpace ι) (i : ι) :
    HasDerivAt (fun s => φ t₀ s ξ (.inl i)) (fderiv ℝ (H s) (φ t₀ s ξ) (unitVec (.inr i))) s ∧
      HasDerivAt (fun s => φ t₀ s ξ (.inr i))
        (-fderiv ℝ (H s) (φ t₀ s ξ) (unitVec (.inl i))) s := by
  have h := hasDerivAt_pi.1 (hφ.hasDerivAt_orbit t₀ s ξ)
  rw [(hH s _).fderiv]
  simp only [symplecticCLM_apply, symplecticForm_unitVec_inr, symplecticForm_unitVec_inl, neg_neg]
  exact ⟨h _, h _⟩

end IsFlow

/-! ### One degree of freedom -/

/-- For one degree of freedom every linear map multiplies `ω` by `ω(A e_q, A e_p)`. -/
theorem symplecticForm_map_of_unique [Unique ι] (A : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι)
    (u v : PhaseSpace ι) :
    symplecticForm (A u) (A v) = symplecticForm (A (unitVec (.inl default)))
      (A (unitVec (.inr default))) * symplecticForm u v := by
  set e : PhaseSpace ι := unitVec (.inl default)
  set f : PhaseSpace ι := unitVec (.inr default)
  have hdec : ∀ w : PhaseSpace ι, w = w (.inl default) • e + w (.inr default) • f := fun w => by
    funext k
    rcases k with i | i <;> simp [e, f, Unique.eq_default i]
  have hef : symplecticForm e f = 1 := symplecticForm_unitVec _
  rw [hdec u, hdec v]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    symplecticForm_self, symplecticForm_swap (A e) (A f), symplecticForm_swap e f, hef]
  ring

/-- For one degree of freedom the independence of degrees of freedom is always preserved. -/
theorem preservesIndependence_of_unique [Unique ι] (φ : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι) :
    PreservesIndependence φ := fun t₀ t₁ ξ u v h => by
  have := symplecticForm_map_of_unique
    (↑(fderiv ℝ (φ t₀ t₁) ξ) : PhaseSpace ι →ₗ[ℝ] PhaseSpace ι) u v
  simp only [ContinuousLinearMap.coe_coe] at this
  rw [this, h, mul_zero]

/-- **One degree of freedom.** An evolution is Hamiltonian iff it preserves the Shannon
entropy. -/
theorem IsFlow.isHamiltonian_iff_preservesEntropy [Unique ι] (hφ : IsFlow φ) :
    IsHamiltonian φ ↔ PreservesEntropy φ :=
  hφ.isHamiltonian_iff.trans (and_iff_left (preservesIndependence_of_unique φ))


/-! ### Two degrees of freedom: neither condition suffices alone -/

/-- The linear evolution `ξₖ ↦ e^{(t₁ - t₀) wₖ} ξₖ`. -/
def scaleFlow (w : ι ⊕ ι → ℝ) (t₀ t₁ : ℝ) (ξ : PhaseSpace ι) : PhaseSpace ι :=
  fun k => exp ((t₁ - t₀) * w k) * ξ k

/-- The diagonal map `uₖ ↦ dₖ uₖ`. -/
def scaleCLM (d : ι ⊕ ι → ℝ) : PhaseSpace ι →L[ℝ] PhaseSpace ι :=
  ContinuousLinearMap.pi fun k => (d k • ContinuousLinearMap.id ℝ ℝ).comp (proj k)

omit [Fintype ι] [DecidableEq ι] in
theorem scaleCLM_apply (d : ι ⊕ ι → ℝ) (u : PhaseSpace ι) : scaleCLM d u = fun k => d k * u k :=
  rfl

omit [DecidableEq ι] in
theorem det_scaleCLM (d : ι ⊕ ι → ℝ) : (scaleCLM d).det = ∏ k, d k := by
  rw [scaleCLM, ContinuousLinearMap.det_pi]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [ContinuousLinearMap.det]

omit [DecidableEq ι] in
theorem isFlow_scaleFlow (w : ι ⊕ ι → ℝ) : IsFlow (scaleFlow w) where
  apply_self t ξ := by funext k; simp [scaleFlow]
  apply_apply t₀ t₁ t₂ ξ := by
    funext k
    simp only [scaleFlow]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  contDiff t₀ := contDiff_pi.2 fun k => by
    have hk : ContDiff ℝ 2 fun z : ℝ × PhaseSpace ι => z.2 k :=
      contDiff_pi.1 contDiff_snd k
    exact (Real.contDiff_exp.comp ((contDiff_fst.sub contDiff_const).mul contDiff_const)).mul hk

omit [Fintype ι] [DecidableEq ι] in
theorem fderiv_scaleFlow (w : ι ⊕ ι → ℝ) (t₀ t₁ : ℝ) (ξ : PhaseSpace ι) :
    fderiv ℝ (scaleFlow w t₀ t₁) ξ = scaleCLM fun k => exp ((t₁ - t₀) * w k) := by
  have : scaleFlow w t₀ t₁ = scaleCLM fun k => exp ((t₁ - t₀) * w k) := rfl
  rw [this]
  exact ContinuousLinearMap.fderiv _

/-- A squeeze of two degrees of freedom: `q₁ ↦ e^t q₁`, `q₂ ↦ e^{-t} q₂`, momenta fixed. -/
def squeezeFlow : ℝ → ℝ → PhaseSpace (Fin 2) → PhaseSpace (Fin 2) :=
  scaleFlow (Sum.elim ![1, -1] 0)

/-- **Entropy alone is not enough.** The squeeze preserves the Shannon entropy of every density,
but it breaks the independence of the degrees of freedom `q₁ + q₂` and `p₁ - p₂`, and it is not
Hamiltonian. -/
theorem squeezeFlow_counterexample :
    IsFlow squeezeFlow ∧ PreservesEntropy squeezeFlow ∧ ¬PreservesIndependence squeezeFlow ∧
      ¬IsHamiltonian squeezeFlow := by
  have hφ : IsFlow squeezeFlow := isFlow_scaleFlow _
  have hE : PreservesEntropy squeezeFlow := fun t₀ t₁ ρ _ _ _ =>
    integral_negMulLog_pushDensity_of_abs_det_eq_one (hφ.hasFDerivAt t₀ t₁)
      (hφ.injective t₀ t₁) (fun ξ => by
        rw [squeezeFlow, fderiv_scaleFlow, det_scaleCLM]
        simp [Fintype.prod_sum_type, Fin.prod_univ_two, ← Real.exp_add]) ρ
  have hI : ¬PreservesIndependence squeezeFlow := fun h => by
    have := h 0 1 0 (Sum.elim ![1, 1] 0) (Sum.elim 0 ![1, -1])
      (by simp [symplecticForm_apply, Fin.sum_univ_two])
    rw [squeezeFlow, fderiv_scaleFlow] at this
    simp [symplecticForm_apply, Fin.sum_univ_two, scaleCLM_apply] at this
    have h1 := Real.exp_injective (by linarith : exp 1 = exp (-1))
    norm_num at h1
  exact ⟨hφ, hE, hI, fun h => hI ((hφ.isHamiltonian_iff.1 h).2)⟩

/-- A dilation of all of phase space: `ξ ↦ e^t ξ`. -/
def dilationFlow : ℝ → ℝ → PhaseSpace ι → PhaseSpace ι :=
  scaleFlow fun _ => 1

/-- **Independence alone is not enough.** The dilation preserves the independence of degrees of
freedom, but not the Shannon entropy, and it is not Hamiltonian. -/
theorem dilationFlow_counterexample [Nonempty ι] :
    IsFlow (dilationFlow (ι := ι)) ∧ PreservesIndependence (dilationFlow (ι := ι)) ∧
      ¬PreservesEntropy (dilationFlow (ι := ι)) ∧ ¬IsHamiltonian (dilationFlow (ι := ι)) := by
  have hφ : IsFlow (dilationFlow (ι := ι)) := isFlow_scaleFlow _
  have hD : ∀ t₀ t₁ ξ u, fderiv ℝ (dilationFlow (ι := ι) t₀ t₁) ξ u = exp (t₁ - t₀) • u :=
    fun t₀ t₁ ξ u => by
      rw [dilationFlow, fderiv_scaleFlow, scaleCLM_apply]
      funext k
      simp
  have hI : PreservesIndependence (dilationFlow (ι := ι)) := fun t₀ t₁ ξ u v h => by
    simp only [hD, map_smul, LinearMap.smul_apply, smul_eq_mul, h, mul_zero]
  have hS : ¬IsSymplectic (dilationFlow (ι := ι)) := fun h => by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := h 0 1 0 (unitVec (.inl i)) (unitVec (.inr i))
    rw [hD, hD, map_smul, map_smul] at this
    simp only [LinearMap.smul_apply, symplecticForm_unitVec, smul_eq_mul, mul_one, sub_zero]
      at this
    have h1 : exp 1 * exp 1 = exp 0 := by rw [this, Real.exp_zero]
    rw [← Real.exp_add] at h1
    norm_num at h1
  refine ⟨hφ, hI, fun hE => hS (hφ.isSymplectic_iff.2 ⟨hE, hI⟩), fun h =>
    hS (hφ.isSymplectic_of_isHamiltonian h)⟩


end UnitaryEntropy.FurtherResults
