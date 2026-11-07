/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.MeasureTheory.Function.LpSpace.Multiplication
public import ForPhyslib.QuantumMechanics.Stone
public import TauCeti.MeasureTheory.Function.Lp.Translation

/-!
# Howland's extended space: the quasi-energy operator of a unitary propagator

A strongly continuous unitary propagator `U t s` (evolution from time `s` to time `t`) is not a
one-parameter group, so Stone's theorem does not apply to it. Howland's trick is to add time as
a coordinate: on `L²(ℝ; E)`,

  `(W σ f)(t) = U t (t - σ) f(t - σ)`

shifts the time coordinate by `σ` and evolves the value along with it. `W` is a strongly
continuous unitary group, so by Stone's theorem it is `e^{-iσK/ħ}` for a self-adjoint `K`, the
quasi-energy operator, formally `K = -iħ ∂ₜ + H(t)`. No hypothesis on a generator `H(t)` enters:
unitarity and strong continuity of `U` are enough.

## i. Overview

`W σ` is translation by `σ` (`shiftOp`) followed by the pointwise operator `U t (t - σ)`
(`diagOp`). Both are isometries; the propagator law `U t r U r s = U t s` gives
`W σ W ρ = W (σ + ρ)` and `W 0 = 1`, so each `W σ` is unitary. For strong continuity at `0`,
`W σ f - f = diagOp σ (shiftOp σ f - f) + (diagOp σ f - f)`: the first term is a translation
increment (`MeasureTheory.Lp.continuous_compMeasurePreserving_add_right`), the second tends to `0`
by dominated convergence, as `U t (t - σ) f(t) → f(t)` pointwise. The pointwise operator is
strongly measurable because `(t, x) ↦ U t (t - σ) x` is jointly continuous: strongly continuous
and uniformly bounded.

## ii. Key results

- `QuantumMechanics.UnitaryPropagator`: a strongly continuous unitary propagator; a strongly
  continuous unitary group gives one (`StronglyContinuousUnitaryGroup.toUnitaryPropagator`).
- `QuantumMechanics.UnitaryPropagator.howland`: the group `W σ`.
- `QuantumMechanics.UnitaryPropagator.howlandGroup`: `W` is a strongly continuous unitary group.
- `QuantumMechanics.UnitaryPropagator.exists_howlandGenerator`: `W σ = e^{-iσK/ħ}` for a
  self-adjoint `K`.

## iii. References

- J. S. Howland, *Stationary scattering theory for time-dependent Hamiltonians*, Math. Ann. 207
  (1974), 315–335.
- M. Reed, B. Simon, *Methods of Modern Mathematical Physics II*, Section X.12.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A strongly continuous family of isometries is jointly continuous. -/
lemma continuous_uncurry_of_norm_map {A : ℝ → E →L[ℂ] E} (hA : ∀ x, Continuous fun t => A t x)
    (hn : ∀ t x, ‖A t x‖ = ‖x‖) : Continuous (Function.uncurry fun t (x : E) => A t x) := by
  refine continuous_iff_continuousAt.mpr fun q => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hle : ∀ p : ℝ × E, ‖A p.1 p.2 - A q.1 q.2‖ ≤ ‖p.2 - q.2‖ + ‖A p.1 q.2 - A q.1 q.2‖ :=
    fun p => by
      calc ‖A p.1 p.2 - A q.1 q.2‖ = ‖A p.1 (p.2 - q.2) + (A p.1 q.2 - A q.1 q.2)‖ := by
            rw [map_sub]
            abel_nf
        _ ≤ ‖A p.1 (p.2 - q.2)‖ + ‖A p.1 q.2 - A q.1 q.2‖ := norm_add_le _ _
        _ = ‖p.2 - q.2‖ + ‖A p.1 q.2 - A q.1 q.2‖ := by rw [hn]
  refine squeeze_zero (fun _ => norm_nonneg _) hle ?_
  have h1 : Continuous fun p : ℝ × E => ‖p.2 - q.2‖ := by fun_prop
  have h2 : Continuous fun p : ℝ × E => ‖A p.1 q.2 - A q.1 q.2‖ :=
    (((hA q.2).comp continuous_fst).sub continuous_const).norm
  convert (h1.add h2).tendsto q using 2
  simp

/-- Translation `f ↦ f(· - σ)` on `L²(ℝ; E)`. -/
def shiftOp (σ : ℝ) : Lp E 2 (volume : Measure ℝ) →L[ℂ] Lp E 2 (volume : Measure ℝ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_add_right volume (-σ))).toContinuousLinearMap

lemma coeFn_shiftOp (σ : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    shiftOp σ f =ᵐ[volume] fun t => f (t - σ) := by
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (-σ))]
    with t ht
  simp only [Function.comp_apply, ← sub_eq_add_neg] at ht
  exact ht

lemma norm_shiftOp (σ : ℝ) (f : Lp E 2 (volume : Measure ℝ)) : ‖shiftOp σ f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

lemma tendsto_shiftOp (f : Lp E 2 (volume : Measure ℝ)) :
    Tendsto (fun σ => shiftOp σ f) (𝓝 0) (𝓝 f) := by
  have hc := (Lp.continuous_compMeasurePreserving_add_right (mu := (volume : Measure ℝ))
    (p := 2) ENNReal.ofNat_ne_top f).comp continuous_neg
  have h0 : shiftOp 0 f = f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_shiftOp 0 f] with t ht
    rw [ht, sub_zero]
  have := hc.tendsto 0
  change Tendsto (fun σ => shiftOp σ f) (𝓝 0) (𝓝 (shiftOp 0 f)) at this
  rwa [h0] at this

variable [CompleteSpace E]

/-- A norm-preserving operator with a right inverse is unitary. -/
lemma mem_unitary_of_norm_map {T S : E →L[ℂ] E} (hT : ∀ x, ‖T x‖ = ‖x‖) (hS : T * S = 1) :
    T ∈ unitary (E →L[ℂ] E) := by
  have h₁ : star T * T = 1 := (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp
    (LinearIsometry.inner_map_map { toLinearMap := T.toLinearMap, norm_map' := hT })
  have h₂ : star T = S := by rw [← mul_one (star T), ← hS, ← mul_assoc, h₁, one_mul]
  exact ⟨h₁, by rw [h₂, hS]⟩

/-- A strongly continuous unitary propagator: `U t s` evolves from time `s` to time `t`, with
`U t t = 1`, `U t r U r s = U t s`, and `(t, s) ↦ U t s x` continuous for every `x`. -/
structure UnitaryPropagator (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  /-- The unitary from time `s` to time `t`. -/
  toFun : ℝ → ℝ → E →L[ℂ] E
  mem_unitary : ∀ t s, toFun t s ∈ unitary (E →L[ℂ] E)
  map_self : ∀ t, toFun t t = 1
  map_comp : ∀ t r s, toFun t r * toFun r s = toFun t s
  continuous_apply : ∀ x, Continuous fun p : ℝ × ℝ => toFun p.1 p.2 x

/-- A time-independent evolution: a strongly continuous unitary group `V` gives the propagator
`U t s = V (t - s)`. -/
def StronglyContinuousUnitaryGroup.toUnitaryPropagator (V : StronglyContinuousUnitaryGroup E) :
    UnitaryPropagator E where
  toFun t s := V (t - s)
  mem_unitary _ _ := V.mem_unitary _
  map_self t := by
    rw [sub_self, V.map_zero]
  map_comp t r s := by
    rw [← V.map_add, sub_add_sub_cancel]
  continuous_apply x := (V.continuous_apply x).comp (continuous_fst.sub continuous_snd)

namespace UnitaryPropagator

instance : CoeFun (UnitaryPropagator E) fun _ => ℝ → ℝ → E →L[ℂ] E := ⟨toFun⟩

variable (U : UnitaryPropagator E)
include U

lemma norm_apply (t s : ℝ) (x : E) : ‖U t s x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (U.mem_unitary t s) x

lemma comp_apply (t r s : ℝ) (x : E) : U t r (U r s x) = U t s x := by
  rw [← U.map_comp t r s]
  rfl

lemma self_apply (t : ℝ) (x : E) : U t t x = x := by
  rw [U.map_self]
  rfl

/-- `(t, x) ↦ U t (t - σ) x` is jointly continuous. -/
lemma continuous_uncurry_sub (σ : ℝ) :
    Continuous (Function.uncurry fun t (x : E) => U t (t - σ) x) :=
  continuous_uncurry_of_norm_map
    (fun x => (U.continuous_apply x).comp
      (continuous_id.prodMk (continuous_id.sub continuous_const)))
    fun t x => U.norm_apply t (t - σ) x

lemma memLp_diag (σ : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    MemLp (fun t => U t (t - σ) (f t)) 2 volume :=
  (Lp.memLp f).congr_norm ((U.continuous_uncurry_sub σ).comp_aestronglyMeasurable₂
    aestronglyMeasurable_id (Lp.aestronglyMeasurable f))
    (.of_forall fun _ => (U.norm_apply _ _ _).symm)

/-- The pointwise operator `f ↦ (t ↦ U t (t - σ) f(t))` on `L²(ℝ; E)`. -/
def diagOp (σ : ℝ) : Lp E 2 (volume : Measure ℝ) →L[ℂ] Lp E 2 (volume : Measure ℝ) :=
  LinearIsometry.toContinuousLinearMap
    { toFun := fun f => (U.memLp_diag σ f).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        filter_upwards [(U.memLp_diag σ (f + g)).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add ((U.memLp_diag σ f).toLp _) ((U.memLp_diag σ g).toLp _),
          (U.memLp_diag σ f).coeFn_toLp, (U.memLp_diag σ g).coeFn_toLp] with t h₁ h₂ h₃ h₄ h₅
        rw [h₁, h₃, Pi.add_apply, h₄, h₅, h₂, Pi.add_apply, map_add]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        filter_upwards [(U.memLp_diag σ (c • f)).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((U.memLp_diag σ f).toLp _), (U.memLp_diag σ f).coeFn_toLp]
          with t h₁ h₂ h₃ h₄
        rw [h₁, RingHom.id_apply, h₃, Pi.smul_apply, h₄, h₂, Pi.smul_apply, map_smul]
      norm_map' := fun f => by
        change ‖(U.memLp_diag σ f).toLp _‖ = ‖f‖
        rw [Lp.norm_toLp, Lp.norm_def]
        congr 1
        exact eLpNorm_congr_norm_ae (U.memLp_diag σ f).aestronglyMeasurable
          (Lp.aestronglyMeasurable f) (.of_forall fun _ => U.norm_apply _ _ _) }

lemma coeFn_diagOp (σ : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    U.diagOp σ f =ᵐ[volume] fun t => U t (t - σ) (f t) :=
  (U.memLp_diag σ f).coeFn_toLp

lemma norm_diagOp (σ : ℝ) (f : Lp E 2 (volume : Measure ℝ)) : ‖U.diagOp σ f‖ = ‖f‖ := by
  change ‖(U.memLp_diag σ f).toLp _‖ = ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  exact eLpNorm_congr_norm_ae (U.memLp_diag σ f).aestronglyMeasurable
    (Lp.aestronglyMeasurable f) (.of_forall fun _ => U.norm_apply _ _ _)

/-- The pointwise operator tends strongly to `1`, by dominated convergence. -/
lemma tendsto_diagOp (f : Lp E 2 (volume : Measure ℝ)) :
    Tendsto (fun σ => U.diagOp σ f) (𝓝 0) (𝓝 f) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have key := tendsto_eLpNorm_of_dominated (μ := (volume : Measure ℝ)) (p := 2)
    (l := 𝓝 (0 : ℝ)) (f := fun σ t => U t (t - σ) (f t) - f t) (F := fun t => 2 * ‖f t‖)
    ENNReal.ofNat_ne_top
    (.of_forall fun σ => (U.memLp_diag σ f).aestronglyMeasurable.sub (Lp.aestronglyMeasurable f))
    ((Lp.memLp f).norm.const_mul 2) (.of_forall fun σ => .of_forall fun t => ?_)
    (.of_forall fun t => ?_)
  · refine key.congr' (.of_forall fun σ => eLpNorm_congr_ae ?_)
    filter_upwards [U.coeFn_diagOp σ f] with t ht
    rw [Pi.sub_apply, ht]
  · calc ‖U t (t - σ) (f t) - f t‖ ≤ ‖U t (t - σ) (f t)‖ + ‖f t‖ := norm_sub_le _ _
      _ = 2 * ‖f t‖ := by rw [U.norm_apply]; ring
  · have hc : Continuous fun σ : ℝ => U t (t - σ) (f t) :=
      (U.continuous_apply (f t)).comp (continuous_const.prodMk (continuous_const.sub continuous_id))
    have := (hc.tendsto 0).sub_const (f t)
    rwa [sub_zero, U.self_apply, sub_self] at this

/-- **Howland's group** `(W σ f)(t) = U t (t - σ) f(t - σ)` on `L²(ℝ; E)`. -/
def howland (σ : ℝ) : Lp E 2 (volume : Measure ℝ) →L[ℂ] Lp E 2 (volume : Measure ℝ) :=
  U.diagOp σ ∘L shiftOp σ

lemma coeFn_howland (σ : ℝ) (f : Lp E 2 (volume : Measure ℝ)) :
    U.howland σ f =ᵐ[volume] fun t => U t (t - σ) (f (t - σ)) := by
  filter_upwards [U.coeFn_diagOp σ (shiftOp σ f), coeFn_shiftOp σ f] with t h₁ h₂
  rw [howland, ContinuousLinearMap.comp_apply, h₁, h₂]

lemma norm_howland (σ : ℝ) (f : Lp E 2 (volume : Measure ℝ)) : ‖U.howland σ f‖ = ‖f‖ := by
  rw [howland, ContinuousLinearMap.comp_apply, norm_diagOp, norm_shiftOp]

theorem howland_zero : U.howland 0 = 1 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  change U.howland 0 f =ᵐ[volume] f
  filter_upwards [U.coeFn_howland 0 f] with t ht
  rw [ht, sub_zero, U.self_apply]

/-- **The group law** `W (σ + ρ) = W σ W ρ`, from `U t (t - σ) U (t - σ) (t - σ - ρ) =
U t (t - σ - ρ)`. -/
theorem howland_add (σ ρ : ℝ) : U.howland (σ + ρ) = U.howland σ * U.howland ρ := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  change U.howland (σ + ρ) f =ᵐ[volume] U.howland σ (U.howland ρ f)
  filter_upwards [U.coeFn_howland (σ + ρ) f, U.coeFn_howland σ (U.howland ρ f),
    (measurePreserving_sub_right volume σ).quasiMeasurePreserving.ae_eq_comp
      (U.coeFn_howland ρ f)] with t h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, h₂, h₃, U.comp_apply, show t - (σ + ρ) = t - σ - ρ by ring]

theorem howland_mem_unitary (σ : ℝ) : U.howland σ ∈ unitary (Lp E 2 (volume : Measure ℝ) →L[ℂ]
    Lp E 2 (volume : Measure ℝ)) :=
  mem_unitary_of_norm_map (U.norm_howland σ)
    (by rw [← U.howland_add, add_neg_cancel, U.howland_zero])

/-- **Strong continuity**: `W σ f - f = diagOp σ (shiftOp σ f - f) + (diagOp σ f - f)`, a
translation increment plus a term that tends to `0` by dominated convergence. -/
theorem tendsto_howland_zero (f : Lp E 2 (volume : Measure ℝ)) :
    Tendsto (fun σ => U.howland σ f) (𝓝 0) (𝓝 f) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_shiftOp f)
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp (U.tendsto_diagOp f)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun σ => ?_) (by simpa using h1.add h2)
  calc ‖U.howland σ f - f‖ = ‖U.diagOp σ (shiftOp σ f - f) + (U.diagOp σ f - f)‖ := by
        rw [howland, ContinuousLinearMap.comp_apply, map_sub]
        abel_nf
    _ ≤ ‖U.diagOp σ (shiftOp σ f - f)‖ + ‖U.diagOp σ f - f‖ := norm_add_le _ _
    _ = ‖shiftOp σ f - f‖ + ‖U.diagOp σ f - f‖ := by rw [norm_diagOp]

theorem continuous_howland_apply (f : Lp E 2 (volume : Measure ℝ)) :
    Continuous fun σ => U.howland σ f := by
  refine continuous_iff_continuousAt.mpr fun σ₀ => ?_
  have h : Tendsto (fun σ => U.howland σ₀ (U.howland (σ - σ₀) f)) (𝓝 σ₀)
      (𝓝 (U.howland σ₀ f)) :=
    ((U.howland σ₀).continuous.tendsto f).comp ((U.tendsto_howland_zero f).comp
      (tendsto_sub_nhds_zero_iff.mpr tendsto_id))
  refine h.congr fun σ => ?_
  have := congrArg (fun T => T f) (U.howland_add σ₀ (σ - σ₀))
  rw [add_sub_cancel] at this
  exact this.symm

/-- **Howland's group is a strongly continuous unitary group** on `L²(ℝ; E)`. -/
def howlandGroup : StronglyContinuousUnitaryGroup (Lp E 2 (volume : Measure ℝ)) where
  toFun := U.howland
  mem_unitary := U.howland_mem_unitary
  map_zero := U.howland_zero
  map_add := U.howland_add
  continuous_apply := U.continuous_howland_apply

/-- **The Howland generator.** For every `ħ ≠ 0` there is a self-adjoint `K` on `L²(ℝ; E)`, the
quasi-energy operator, with `W σ = e^{-iσK/ħ}`: `W` solves the Schrödinger equation for `K`. -/
theorem exists_howlandGenerator {ħ : ℝ} (hħ : ħ ≠ 0) :
    ∃ (K : Lp E 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp E 2 (volume : Measure ℝ))
      (hK : IsSelfAdjoint K), SolvesSchrodinger ħ K U.howland ∧
        ∀ σ, U.howland σ = schrodingerPropagator hħ hK σ := by
  obtain ⟨K, hK, hS⟩ := U.howlandGroup.exists_solvesSchrodinger hħ
  exact ⟨K, hK, hS, hS.eq_schrodingerPropagator hħ hK U.howland_zero⟩

end UnitaryPropagator

end QuantumMechanics
