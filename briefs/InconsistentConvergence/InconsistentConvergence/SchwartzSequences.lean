/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import InconsistentConvergence.Oscillator
public import ForMathlib.Analysis.Normed.Lp.SchwartzSeq

/-!
# Inconsistent convergence: the Schwartz sequence space

The brief defines the Schwartz sequence space `S(ℕ) ⊂ ℓ²` by the seminorms `∑ᵢ |iᵏ xᵢ|²`. Here
it is the type `SchwartzSeq ℂ` of `ForMathlib`, with the seminorms `‖((n + 1)ᵏ xₙ)ₙ‖`, which are
the brief's with indices starting at `0`. This module proves the brief's statements about it in
its topology.

* The states `eʲ` lie in `S(ℕ)` (`eS`) and converge to `|0⟩` in `ℓ²` (`tendsto_toLp_eS`), but
  have no limit in `S(ℕ)` (`not_tendsto_eS`): the seminorm `‖((n + 1) eʲₙ)ₙ‖` is at least `√j`.
* The eigenstates `bʲ = |j⟩` lie in `S(ℕ)` (`levelS`), but have no limit in `S(ℕ)`
  (`not_tendsto_levelS`), since they have none in `ℓ²` and `S(ℕ) → ℓ²` is continuous.
* Under the unitary `U` of the Hermite basis, `S(ℕ)` is the Schwartz space: `U` restricts to a
  continuous linear equivalence `S(ℕ) ≃ 𝓢(ℝ)` (`hermiteSchwartzEquiv`,
  `toLp_hermiteSchwartzEquiv`), sending `|n⟩` to the Hermite function `ψₙ`
  (`toLp_hermiteSchwartzEquiv_levelS`).

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.
-/

open MeasureTheory Filter Topology TauCeti
open scoped SchwartzMap

@[expose] public noncomputable section

namespace InconsistentConvergence

/-- The Schwartz sequence space `S(ℕ)` of the brief. -/
abbrev S := SchwartzSeq ℂ

lemma level_mem_schwartzSeq (j : ℕ) : level j ∈ SchwartzSeq.submodule ℂ :=
  SchwartzSeq.single_mem_submodule j 1

lemma e_mem_schwartzSeq (j : ℕ) : e j ∈ SchwartzSeq.submodule ℂ :=
  add_mem (Submodule.smul_mem _ _ (level_mem_schwartzSeq 0))
    (Submodule.smul_mem _ _ (level_mem_schwartzSeq j))

/-- The eigenstate `bʲ = |j⟩`, as an element of `S(ℕ)`. -/
def levelS (j : ℕ) : S := SchwartzSeq.mk (level j) (level_mem_schwartzSeq j)

/-- The state `eʲ`, as an element of `S(ℕ)`. -/
def eS (j : ℕ) : S := SchwartzSeq.mk (e j) (e_mem_schwartzSeq j)

/-! ### The brief's sequences in `S(ℕ)` -/

/-- `eʲ → |0⟩` in `ℓ²`. -/
theorem tendsto_toLp_eS : Tendsto (fun j => SchwartzSeq.toLp (eS j)) atTop (𝓝 ground) :=
  tendsto_e

/-- `√j ≤ ‖((n + 1) eʲₙ)ₙ‖`, from the term `n = j`. -/
lemma sqrt_le_seminorm_eS {j : ℕ} (hj : 1 ≤ j) :
    √(j : ℝ) ≤ SchwartzSeq.seminormFamily ℂ 1 (eS j) := by
  have hj0 : j ≠ 0 := by omega
  have h := SchwartzSeq.mul_norm_le_seminorm 1 (eS j) j
  have ha0 : 0 ≤ ampⱼ j := Real.sqrt_nonneg _
  rw [eS, SchwartzSeq.toLp_mk, e_apply_self hj0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ha0, pow_one] at h
  refine le_trans ?_ h
  rw [Real.sqrt_le_left (by positivity)]
  have ha : ampⱼ j ^ 2 * j = 1 := by
    rw [ampⱼ_sq]
    have : (j : ℝ) ≠ 0 := by positivity
    field_simp
  have hj' : (j : ℝ) * (ampⱼ j ^ 2 * j) = j := by rw [ha, mul_one]
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * j + 1) (sq_nonneg (ampⱼ j))]

/-- The seminorm `‖((n + 1) eʲₙ)ₙ‖` diverges. -/
theorem tendsto_seminorm_eS :
    Tendsto (fun j => SchwartzSeq.seminormFamily ℂ 1 (eS j)) atTop atTop :=
  tendsto_atTop_mono' _ ((eventually_ge_atTop 1).mono fun _ hj => sqrt_le_seminorm_eS hj)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Proposition 1.** `eʲ` has no limit in `S(ℕ)`, although it converges to `|0⟩` in `ℓ²`. -/
theorem not_tendsto_eS (g : S) : ¬ Tendsto eS atTop (𝓝 g) :=
  SchwartzSeq.not_tendsto_of_tendsto_atTop tendsto_seminorm_eS g

/-- The eigenstates `bʲ = |j⟩` of `S(ℕ)` have no limit in `S(ℕ)`. -/
theorem not_tendsto_levelS (g : S) : ¬ Tendsto levelS atTop (𝓝 g) := fun h =>
  not_cauchySeq_level ((SchwartzSeq.continuous_toLp.tendsto g).comp h).cauchySeq

/-! ### `S(ℕ)` is the Schwartz space -/

lemma hermiteUnitary_symm_mem (f : 𝓢(ℝ, ℂ)) :
    hermiteUnitary.symm (f.toLp 2) ∈ SchwartzSeq.submodule ℂ :=
  (SchwartzSeq.mem_submodule_iff _).2 <|
    (exists_schwartz_iff _).1 ⟨f, (LinearIsometryEquiv.apply_symm_apply _ _).symm⟩

/-- The Hermite coefficients `f ↦ U⁻¹ f`, from `𝓢(ℝ)` to `S(ℕ)`. -/
def hermiteCoeffMap : 𝓢(ℝ, ℂ) →ₗ[ℂ] S :=
  (hermiteUnitary.symm.toLinearEquiv.toLinearMap ∘ₗ
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap).codRestrict
      (SchwartzSeq.submodule ℂ) hermiteUnitary_symm_mem

theorem toLp_hermiteCoeffMap (f : 𝓢(ℝ, ℂ)) :
    SchwartzSeq.toLp (hermiteCoeffMap f) = hermiteUnitary.symm (f.toLp 2) :=
  rfl

theorem hermiteCoeffMap_injective : Function.Injective hermiteCoeffMap := fun f g h => by
  have h' := congrArg SchwartzSeq.toLp h
  rw [toLp_hermiteCoeffMap, toLp_hermiteCoeffMap] at h'
  exact SchwartzMap.injective_toLp 2 volume (hermiteUnitary.symm.injective h')

theorem hermiteCoeffMap_surjective : Function.Surjective hermiteCoeffMap := fun x => by
  obtain ⟨f, hf⟩ := (exists_schwartz_iff (SchwartzSeq.toLp x)).2
    ((SchwartzSeq.mem_submodule_iff _).1 (SchwartzSeq.toLp_mem x))
  refine ⟨f, SchwartzSeq.toLp_injective ?_⟩
  rw [toLp_hermiteCoeffMap, hf, LinearIsometryEquiv.symm_apply_apply]

theorem continuous_hermiteCoeffMap : Continuous hermiteCoeffMap := by
  refine continuous_iff_continuousAt.2 fun g => SchwartzSeq.tendsto_iff.2 fun k ε hε => ?_
  filter_upwards [tendsto_schwartz_iff.1 (tendsto_id (x := 𝓝 g)) k ε hε] with f hf n
  rw [map_sub, lp.coeFn_sub, Pi.sub_apply, toLp_hermiteCoeffMap, toLp_hermiteCoeffMap]
  exact hf n

/-- The Hermite coefficients, as a linear equivalence `𝓢(ℝ) ≃ S(ℕ)`. -/
def hermiteCoeffEquiv : 𝓢(ℝ, ℂ) ≃ₗ[ℂ] S :=
  LinearEquiv.ofBijective hermiteCoeffMap ⟨hermiteCoeffMap_injective, hermiteCoeffMap_surjective⟩

lemma hermiteUnitary_symm_toLp_symm (x : S) :
    hermiteUnitary.symm ((hermiteCoeffEquiv.symm x).toLp 2) = SchwartzSeq.toLp x := by
  rw [← toLp_hermiteCoeffMap]
  exact congrArg SchwartzSeq.toLp (hermiteCoeffEquiv.apply_symm_apply x)

theorem continuous_hermiteCoeffEquiv_symm : Continuous hermiteCoeffEquiv.symm := by
  refine continuous_iff_continuousAt.2 fun x => tendsto_schwartz_iff.2 fun k ε hε => ?_
  filter_upwards [SchwartzSeq.tendsto_iff.1 (tendsto_id (x := 𝓝 x)) k ε hε] with y hy n
  rw [hermiteUnitary_symm_toLp_symm, hermiteUnitary_symm_toLp_symm]
  simpa only [map_sub, lp.coeFn_sub, Pi.sub_apply, id_eq] using hy n

/-- **`S(ℕ)` is the Schwartz space.** The unitary `U` of the Hermite basis restricts to a
continuous linear equivalence `S(ℕ) ≃ 𝓢(ℝ)`. -/
def hermiteSchwartzEquiv : S ≃L[ℂ] 𝓢(ℝ, ℂ) :=
  ContinuousLinearEquiv.symm
    { hermiteCoeffEquiv with
      continuous_toFun := continuous_hermiteCoeffMap
      continuous_invFun := continuous_hermiteCoeffEquiv_symm }

/-- `hermiteSchwartzEquiv` is `U`: `hermiteSchwartzEquiv x = U x` in `L²(ℝ)`. -/
theorem toLp_hermiteSchwartzEquiv (x : S) :
    (hermiteSchwartzEquiv x).toLp 2 = hermiteUnitary (SchwartzSeq.toLp x) := by
  rw [← hermiteUnitary_symm_toLp_symm x, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- `hermiteSchwartzEquiv |n⟩ = ψₙ`. -/
theorem toLp_hermiteSchwartzEquiv_levelS (n : ℕ) :
    (hermiteSchwartzEquiv (levelS n)).toLp 2 = hermiteFunctionLp ℂ n := by
  rw [toLp_hermiteSchwartzEquiv, levelS, SchwartzSeq.toLp_mk, hermiteUnitary_level]

end InconsistentConvergence
