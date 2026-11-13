/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import NonLinearQuantum
public import ForPhyslib.QuantumMechanics.UnitaryEquivalence

/-!
# Non-linear representations: density operators and entropy on `m(H)`

The proof of Theorem 4 of the brief says that QST:H "remains valid on `m(H)`": the states are
unchanged, and "density operators will be left unchanged together with their entropy". As
operators on the common carrier they change: the pure state `|v⟩⟨v|` moved over through `m` is not
even additive for the addition of `E` (`not_map_add_transport_projOp`, main file). This module
proves what holds, for the space `Twisted v θ` with the structure carried over along `m`:

* `Twisted v θ` is a Hilbert space when `E` is (`instCompleteSpaceTwisted`), separable when `E`
  is (`instSeparableSpaceTwisted`), and of the same dimension (`finrank_twisted`). So QST:H, which
  asks for a separable Hilbert space, applies to it.
* `m` keeps every state: the ray of `m x` in `m(E)` is the ray of `x` (`mk_twistedIsometry`).
* `ρ ↦ m ρ m⁻¹` (`transportOp`) is a bijection from the density operators of `E` onto those of
  `m(E)` (`densityEquiv`). It keeps the spectrum (`spectrum_transportOp`) and the von Neumann
  entropy (`vonNeumannEntropy_densityEquiv`).
* On the common carrier, `transportOp ρ` is `x ↦ m (ρ (m⁻¹ x))` (`transportOp_toTwisted`), which
  for `ρ = |v⟩⟨v|` is not additive for the addition of `E` (`not_map_add_transportOp_projOp`).
  So the density operators are not "left unchanged"; they are carried over, with their entropy.

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.
-/

open scoped InnerProductSpace
open QuantumMechanics

@[expose] public noncomputable section

namespace NonLinearQuantum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : E) (θ : ℝ)

/-! ### `m(E)` is a separable Hilbert space of the same dimension -/

instance instCompleteSpaceTwisted [CompleteSpace E] : CompleteSpace (Twisted v θ) :=
  (completeSpace_congr (e := (twistedIsometry v θ).toEquiv)
    (twistedIsometry v θ).isometry.isUniformEmbedding).1 inferInstance

instance instSeparableSpaceTwisted [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.SeparableSpace (Twisted v θ) :=
  (twistedIsometry v θ).surjective.denseRange.separableSpace (twistedIsometry v θ).continuous

instance [FiniteDimensional ℂ E] : FiniteDimensional ℂ (Twisted v θ) :=
  (twistedIsometry v θ).toLinearEquiv.finiteDimensional

theorem finrank_twisted : Module.finrank ℂ (Twisted v θ) = Module.finrank ℂ E :=
  (twistedIsometry v θ).toLinearEquiv.finrank_eq.symm

/-! ### States -/

lemma toTwisted_ne_zero {x : E} (hx : x ≠ 0) : toTwisted v θ x ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_toTwisted, norm_ne_zero_iff]
  exact hx

/-- `m` keeps every state: in `m(E)`, the ray of `m x` is the ray of `x`. -/
theorem mk_twistedIsometry {x : E} (hx : x ≠ 0) :
    Projectivization.mk ℂ (twistedIsometry v θ x)
        ((twistedIsometry v θ).map_ne_zero_iff.mpr hx) =
      Projectivization.mk ℂ (toTwisted v θ x) (toTwisted_ne_zero v θ hx) :=
  (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    ⟨phase v θ x, by rw [twistedIsometry_apply, nlMap, toTwisted_smul]⟩

lemma twistedIsometry_symm_toTwisted (x : E) :
    (twistedIsometry v θ).symm (toTwisted v θ x) = nlMap v (-θ) x := by
  rw [LinearIsometryEquiv.symm_apply_eq, twistedIsometry_apply, nlMap_nlMap_neg]

/-! ### Density operators and entropy -/

variable [CompleteSpace E]

/-- Operators moved over through `m`: `ρ ↦ m ρ m⁻¹`, from `E` to `m(E)`. -/
def transportOp : (E →L[ℂ] E) ≃⋆ₐ[ℂ] (Twisted v θ →L[ℂ] Twisted v θ) :=
  (twistedIsometry v θ).conjStarAlgEquiv

/-- On the common carrier, `transportOp ρ` is `x ↦ m (ρ (m⁻¹ x))`. -/
theorem transportOp_toTwisted (ρ : E →L[ℂ] E) (x : E) :
    transportOp v θ ρ (toTwisted v θ x) = toTwisted v θ (nlMap v θ (ρ (nlMap v (-θ) x))) := by
  rw [transportOp, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    twistedIsometry_symm_toTwisted, twistedIsometry_apply]

/-- `ρ ↦ m ρ m⁻¹` keeps the real spectrum. -/
theorem spectrum_transportOp (ρ : E →L[ℂ] E) :
    spectrum ℝ (transportOp v θ ρ) = spectrum ℝ ρ := by
  have h : spectrum ℂ (transportOp v θ ρ) = spectrum ℂ ρ :=
    AlgEquiv.spectrum_eq (twistedIsometry v θ).toContinuousLinearEquiv.conjContinuousAlgEquiv ρ
  rw [← spectrum.preimage_algebraMap ℂ, h, spectrum.preimage_algebraMap]

theorem isDensityOperator_transportOp_iff {ρ : E →L[ℂ] E} :
    IsDensityOperator (transportOp v θ ρ) ↔ IsDensityOperator ρ :=
  isDensityOperator_conjStarAlgEquiv_iff

/-- `ρ ↦ m ρ m⁻¹` is a bijection from the density operators of `E` onto those of `m(E)`. -/
def densityEquiv :
    {ρ : E →L[ℂ] E // IsDensityOperator ρ} ≃
      {σ : Twisted v θ →L[ℂ] Twisted v θ // IsDensityOperator σ} :=
  (transportOp v θ).toEquiv.subtypeEquiv fun _ => (isDensityOperator_transportOp_iff v θ).symm

lemma densityEquiv_apply (ρ : {ρ : E →L[ℂ] E // IsDensityOperator ρ}) :
    (densityEquiv v θ ρ : Twisted v θ →L[ℂ] Twisted v θ) = transportOp v θ ρ :=
  rfl

/-- `ρ ↦ m ρ m⁻¹` keeps the von Neumann entropy. -/
theorem vonNeumannEntropy_densityEquiv (ρ : {ρ : E →L[ℂ] E // IsDensityOperator ρ}) :
    vonNeumannEntropy (densityEquiv v θ ρ : Twisted v θ →L[ℂ] Twisted v θ) =
      vonNeumannEntropy (ρ : E →L[ℂ] E) :=
  ρ.2.vonNeumannEntropy_conjStarAlgEquiv

/-- The proof of Theorem 4, made precise: `m(E)` is a Hilbert space of the same dimension as `E`,
`m` keeps every state and the Born rule, and `ρ ↦ m ρ m⁻¹` is a bijection of the density
operators that keeps spectra and entropy. -/
theorem qst_twisted :
    Module.finrank ℂ (Twisted v θ) = Module.finrank ℂ E ∧
    (∀ x y : E, born (toTwisted v θ x) (toTwisted v θ y) = born x y) ∧
    (∀ (x : E) (hx : x ≠ 0),
      Projectivization.mk ℂ (twistedIsometry v θ x)
          ((twistedIsometry v θ).map_ne_zero_iff.mpr hx) =
        Projectivization.mk ℂ (toTwisted v θ x) (toTwisted_ne_zero v θ hx)) ∧
    (∀ ρ : {ρ : E →L[ℂ] E // IsDensityOperator ρ},
      spectrum ℝ (densityEquiv v θ ρ : Twisted v θ →L[ℂ] Twisted v θ) =
          spectrum ℝ (ρ : E →L[ℂ] E) ∧
        vonNeumannEntropy (densityEquiv v θ ρ : Twisted v θ →L[ℂ] Twisted v θ) =
          vonNeumannEntropy (ρ : E →L[ℂ] E)) :=
  ⟨finrank_twisted v θ, born_toTwisted v θ, fun _ hx => mk_twistedIsometry v θ hx,
    fun ρ => ⟨spectrum_transportOp v θ ρ, vonNeumannEntropy_densityEquiv v θ ρ⟩⟩

variable {v} {w : E}

/-- The pure state `|v⟩⟨v|` moved over to `m(E)`, read on the common carrier, is not additive for
the addition of `E`: the density operators are carried over, not "left unchanged". -/
theorem not_map_add_transportOp_projOp (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ¬ ∀ x y : E, (toTwisted v θ).symm (transportOp v θ (projOp v) (toTwisted v θ (x + y))) =
      (toTwisted v θ).symm (transportOp v θ (projOp v) (toTwisted v θ x)) +
        (toTwisted v θ).symm (transportOp v θ (projOp v) (toTwisted v θ y)) := by
  intro h
  have h' := h v w
  simp only [transportOp_toTwisted, Equiv.symm_apply_apply] at h'
  exact not_map_add_transport_projOp hvw hθ h'

end NonLinearQuantum
