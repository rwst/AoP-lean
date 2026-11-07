/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.HilbertBasisMaps
public import ForMathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Normed.Group.Tannery
public import UnitaryEntropy.MomentumExtensions

/-!
# The domain of the switched Hamiltonian is `H¹₀(0, 1)`

This continues `UnitaryEntropy.MomentumExtensions`. Let `ħ ≠ 0` and `e^{iα} ≠ e^{iβ}`. The
vectors `ψ` for which `t ↦ U(t) ψ` is differentiable at `0` are exactly the `ψ ∈ H¹₀(0, 1)`,
and on them `H₀ ψ = iħ U'(0) ψ = -i ψ'`. So `H₀` is the minimal momentum operator.

Here `H¹₀(0, 1)` is taken in its absolutely continuous form (`sobolevZero`): `ψ(x) = ∫₀ˣ g`
with `g ∈ L²(0, 1)` and `∫₀¹ g = 0`, so that `ψ(0) = ψ(1) = 0`.

## Proof

For each `γ`, the plane waves `eₙ = e^{i(γ + 2πn)x}`, `n ∈ ℤ`, form a Hilbert basis
(`twistedBasis`). They are eigenvectors of `U_γ(t)`, with eigenvalues `e^{-i(γ + 2πn)t/ħ}`. So
`t ↦ U_γ(t) ψ` has derivative `-(i/ħ) h` at `0` iff `⟨eₙ, h⟩ = (γ + 2πn) ⟨eₙ, ψ⟩` for all `n`.
Necessity holds already for one-sided derivatives (`inner_twistedBasis_of_hasDerivWithinAt`).
Sufficiency follows by dominated convergence of the coordinates
(`hasDerivAt_twistedTranslation_of_inner`).

Integration by parts gives, for `Φ(x) = ∫₀ˣ g`,
`⟨e^{iδx}, -i g⟩ = δ ⟨e^{iδx}, Φ⟩ - i e^{-iδ} Φ(1)` (`inner_planeWave_neg_I_smul`). If
`Φ(1) = 0`, this is the eigenvalue relation for every `γ`, so `H¹₀ ⊆ D`.

Conversely, let `ψ ∈ D` and `g = i H₀ ψ`. Then `f = ψ - Φ` satisfies
`(γ + 2πn) ⟨eₙ, f⟩ = -i e^{-iγ} Φ(1)` for `γ = α` and `γ = β`. If `e^{iγ} = 1`, this forces
`Φ(1) = 0`. Otherwise it forces `f` to be the constant `Φ(1)/(e^{iγ} - 1)`. As `e^{iα} ≠ e^{iβ}`,
both cases give `Φ(1) = 0` and `f = 0`.

## Main results

* `twistedBasis`, `inner_twistedBasis_twistedTranslation`: the eigenbasis of `U_γ`.
* `hasDerivAt_twistedTranslation_of_inner`: the eigenvalue relation gives the derivative.
* `inner_planeWave_neg_I_smul`: integration by parts against plane waves.
* `primitive_mem_switchedDomain`, `switchedHamiltonian_primitive`: `H¹₀ ⊆ D`, and
  `H₀ = -i d/dx` there.
* `exists_primitive_of_mem_switchedDomain`: `D ⊆ H¹₀`.
* `switchedDomain_eq`: `D = H¹₀`.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy

open MeasureTheory Filter Topology Set AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate Real

/-- The circle `ℝ/ℤ`. -/
local notation "𝕋" => AddCircle (1 : ℝ)

/-- Haar probability measure on `ℝ/ℤ`, which is Lebesgue measure on `[0, 1)`. -/
local notation "μc" => (haarAddCircle : Measure 𝕋)

/-- `L²(0, 1)`, as `L²` of the circle. -/
local notation "L²" => Lp ℂ 2 μc

local notation "U" => switchedPropagator

/-! ### The eigenbasis of `U_γ` -/

lemma norm_planeWaveFun (γ : ℝ) (x : 𝕋) : ‖planeWaveFun γ x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

lemma memLp_top_planeWaveFun (γ : ℝ) : MemLp (planeWaveFun γ) ∞ μc :=
  memLp_top_of_bound (measurable_planeWaveFun γ).aestronglyMeasurable 1
    (.of_forall fun x => (norm_planeWaveFun γ x).le)

lemma planeWaveFun_mul (γ δ : ℝ) (x : 𝕋) :
    planeWaveFun γ x * planeWaveFun δ x = planeWaveFun (γ + δ) x := by
  rw [planeWaveFun, planeWaveFun, planeWaveFun, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma mulL_planeWaveFun_mulL (γ δ : ℝ) (f : L²) :
    Lp.mulL (planeWaveFun γ) (Lp.mulL (planeWaveFun δ) f) = Lp.mulL (planeWaveFun (γ + δ)) f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_mulL (memLp_top_planeWaveFun γ) (Lp.mulL (planeWaveFun δ) f),
    Lp.coeFn_mulL (memLp_top_planeWaveFun δ) f,
    Lp.coeFn_mulL (memLp_top_planeWaveFun (γ + δ)) f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, ← mul_assoc, planeWaveFun_mul]

lemma mulL_planeWaveFun_zero (f : L²) : Lp.mulL (planeWaveFun 0) f = f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_mulL (memLp_top_planeWaveFun 0) f] with x hx
  simp [hx, planeWaveFun]

lemma norm_mulL_planeWaveFun (γ : ℝ) (f : L²) : ‖Lp.mulL (planeWaveFun γ) f‖ = ‖f‖ := by
  have h := Lp.coeFn_mulL (memLp_top_planeWaveFun γ) f
  refine le_antisymm (Lp.norm_le_norm_of_ae_le ?_) (Lp.norm_le_norm_of_ae_le ?_) <;>
    filter_upwards [h] with x hx <;>
    simp [hx, norm_planeWaveFun]

/-- Multiplication by `e^{iγx}`, a unitary on `L²(0, 1)`. -/
def planeWaveMul (γ : ℝ) : L² ≃ₗᵢ[ℂ] L² where
  toFun := Lp.mulL (planeWaveFun γ)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun := Lp.mulL (planeWaveFun (-γ))
  left_inv f := by simp only [mulL_planeWaveFun_mulL, neg_add_cancel, mulL_planeWaveFun_zero]
  right_inv f := by simp only [mulL_planeWaveFun_mulL, add_neg_cancel, mulL_planeWaveFun_zero]
  norm_map' := norm_mulL_planeWaveFun γ

/-- The eigenbasis `e^{i(γ + 2πn)x}`, `n ∈ ℤ`, of the twisted translations `U_γ`. -/
def twistedBasis (γ : ℝ) : HilbertBasis ℤ ℂ L² := (fourierBasis (T := 1)).map (planeWaveMul γ)

lemma twistedBasis_apply (γ : ℝ) (n : ℤ) : twistedBasis γ n = planeWave (γ + 2 * π * n) := by
  rw [twistedBasis, HilbertBasis.map_apply, coe_fourierBasis]
  change Lp.mulL (planeWaveFun γ) (fourierLp 2 n) = _
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_mulL (memLp_top_planeWaveFun γ) (fourierLp 2 n), coeFn_fourierLp 2 n,
    (memLp_planeWaveFun (γ + 2 * π * n)).coeFn_toLp] with x h₁ h₂ h₃
  rw [h₁, h₂, planeWave, h₃, fourier_eq, planeWaveFun, planeWaveFun, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma exp_twistedBasis_eigenvalue (γ : ℝ) (n : ℤ) :
    Complex.exp (-(Complex.I * ((γ + 2 * π * n : ℝ) : ℂ))) = Complex.exp (-(Complex.I * γ)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-n, by push_cast; ring⟩

/-- `e^{i(γ + 2πn)x}` is an eigenvector of `U_γ(sħ)`, with eigenvalue `e^{-i(γ + 2πn)s}`. -/
lemma twistedTranslation_twistedBasis (γ s : ℝ) (n : ℤ) :
    twistedTranslation γ s (twistedBasis γ n) =
      Complex.exp (-(Complex.I * (((γ + 2 * π * n) * s : ℝ) : ℂ))) • twistedBasis γ n := by
  rw [twistedBasis_apply]
  set δ := γ + 2 * π * n with hδ
  refine Lp.ext ?_
  filter_upwards [coeFn_twistedTranslation γ s (planeWave δ),
    (measurePreserving_sub s).quasiMeasurePreserving.ae_eq_comp
      (memLp_planeWaveFun δ).coeFn_toLp,
    Lp.coeFn_smul (Complex.exp (-(Complex.I * ((δ * s : ℝ) : ℂ)))) (planeWave δ),
    (memLp_planeWaveFun δ).coeFn_toLp] with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂
  have hx : circleRep (x - s) = Int.fract (circleRep x - s) := by
    rw [← circleRep_coe, AddCircle.coe_sub, coe_circleRep]
  rw [h₁, h₃, Pi.smul_apply, planeWave, h₂, h₄, smul_eq_mul, twistPhase, planeWaveFun,
    planeWaveFun, ← Complex.exp_add, ← Complex.exp_add, Complex.exp_eq_exp_iff_exists_int, hx,
    ← Int.self_sub_floor]
  exact ⟨-(n * ⌊circleRep x - s⌋), by rw [hδ]; push_cast; ring⟩

lemma inner_twistedTranslation_right (γ s : ℝ) (f g : L²) :
    ⟪f, twistedTranslation γ s g⟫_ℂ = ⟪twistedTranslation γ (-s) f, g⟫_ℂ := by
  have h : twistedTranslation γ s (twistedTranslation γ (-s) f) = f := by
    simpa using congrArg (fun T => T f) (twistedTranslation_mul_neg γ s)
  conv_lhs => rw [← h]
  exact inner_twistedTranslation γ s _ _

lemma inner_twistedBasis_twistedTranslation (γ s : ℝ) (n : ℤ) (f : L²) :
    ⟪twistedBasis γ n, twistedTranslation γ s f⟫_ℂ =
      Complex.exp (-(Complex.I * (((γ + 2 * π * n) * s : ℝ) : ℂ))) *
        ⟪twistedBasis γ n, f⟫_ℂ := by
  rw [inner_twistedTranslation_right, twistedTranslation_twistedBasis, inner_smul_left,
    ← Complex.exp_conj]
  congr 2
  rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-! ### Derivatives of `U_γ` and the eigenbasis -/

variable {ħ α β : ℝ}

/-- If `t ↦ U_γ(t) ψ` has derivative `v` at `0` within `s`, then
`⟨eₙ, v⟩ = -(i/ħ) (γ + 2πn) ⟨eₙ, ψ⟩`. -/
lemma inner_twistedBasis_of_hasDerivWithinAt {γ : ℝ} {s : Set ℝ} (hs : UniqueDiffWithinAt ℝ s 0)
    (h0 : (0 : ℝ) ∈ s) {ψ v : L²}
    (h : HasDerivWithinAt (fun t => twistedTranslation γ (t / ħ) ψ) v s 0) (n : ℤ) :
    ⟪twistedBasis γ n, v⟫_ℂ =
      -(Complex.I * (((γ + 2 * π * n) / ħ : ℝ) : ℂ)) * ⟪twistedBasis γ n, ψ⟫_ℂ := by
  have hg : HasDerivWithinAt (fun t => ⟪twistedBasis γ n, twistedTranslation γ (t / ħ) ψ⟫_ℂ)
      ⟪twistedBasis γ n, v⟫_ℂ s 0 := by
    simpa using (hasDerivWithinAt_const (0 : ℝ) s (twistedBasis γ n)).inner ℂ h
  exact eq_of_hasDerivWithinAt_phase hs h0 hg fun t _ =>
    inner_twistedBasis_twistedTranslation γ (t / ħ) n ψ

lemma norm_slope_phase_le (δ : ℝ) (c : ℂ) (t : ℝ) :
    ‖slope (fun t : ℝ => Complex.exp (-(Complex.I * ((δ * (t / ħ) : ℝ) : ℂ))) * c) 0 t‖ ≤
      ‖-(Complex.I * ((δ / ħ : ℝ) : ℂ)) * c‖ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp only [slope_same, norm_zero]
    positivity
  have ht' : |t| ≠ 0 := abs_ne_zero.mpr ht
  have he : ‖Complex.exp (-(Complex.I * ((δ * (t / ħ) : ℝ) : ℂ))) - 1‖ ≤ |δ * (t / ħ)| := by
    have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := -(δ * (t / ħ)))
    rwa [Complex.ofReal_neg, mul_neg, Real.norm_eq_abs, abs_neg] at h
  simp only [slope_def_module, sub_zero, zero_div, mul_zero, Complex.ofReal_zero, neg_zero,
    Complex.exp_zero, one_mul]
  rw [← sub_one_mul, norm_smul, norm_mul, norm_inv, Real.norm_eq_abs, norm_mul, norm_neg,
    norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |t|⁻¹ * (‖Complex.exp (-(Complex.I * ((δ * (t / ħ) : ℝ) : ℂ))) - 1‖ * ‖c‖)
      ≤ |t|⁻¹ * (|δ * (t / ħ)| * ‖c‖) := by gcongr
    _ = (|t|⁻¹ * |t|) * (|δ| / |ħ| * ‖c‖) := by rw [abs_mul, abs_div]; ring
    _ = |δ / ħ| * ‖c‖ := by rw [inv_mul_cancel₀ ht', one_mul, abs_div]

/-- **The eigenvalue relation gives the derivative**: if `⟨eₙ, v⟩ = -(i/ħ) (γ + 2πn) ⟨eₙ, ψ⟩`
for all `n`, then `t ↦ U_γ(t) ψ` has derivative `v` at `0`. -/
theorem hasDerivAt_twistedTranslation_of_inner {γ : ℝ} {ψ v : L²}
    (h : ∀ n : ℤ, ⟪twistedBasis γ n, v⟫_ℂ =
      -(Complex.I * (((γ + 2 * π * n) / ħ : ℝ) : ℂ)) * ⟪twistedBasis γ n, ψ⟫_ℂ) :
    HasDerivAt (fun t => twistedTranslation γ (t / ħ) ψ) v 0 := by
  set φ : ℤ → ℝ → ℂ := fun n t =>
    Complex.exp (-(Complex.I * (((γ + 2 * π * n) * (t / ħ) : ℝ) : ℂ))) *
      ⟪twistedBasis γ n, ψ⟫_ℂ with hφ
  have hcoef : ∀ t n, ⟪twistedBasis γ n,
      slope (fun t => twistedTranslation γ (t / ħ) ψ) 0 t - v⟫_ℂ =
        slope (φ n) 0 t - ⟪twistedBasis γ n, v⟫_ℂ := fun t n => by
    simp only [hφ, slope_def_module, inner_sub_right, RCLike.real_smul_eq_coe_smul (K := ℂ),
      inner_smul_right, inner_twistedBasis_twistedTranslation, smul_eq_mul]
  have hP : ∀ w : L², ‖w‖ = √(∑' n, ‖⟪twistedBasis γ n, w⟫_ℂ‖ ^ 2) := fun w => by
    rw [((twistedBasis γ).hasSum_norm_inner_sq w).tsum_eq, Real.sqrt_sq (norm_nonneg _)]
  have hT : Tendsto (fun t => ∑' n, ‖slope (φ n) 0 t - ⟪twistedBasis γ n, v⟫_ℂ‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[≠] (0 : ℝ))
      (f := fun t n => ‖slope (φ n) 0 t - ⟪twistedBasis γ n, v⟫_ℂ‖ ^ 2) (g := fun _ => (0 : ℝ))
      (bound := fun n => 4 * ‖⟪twistedBasis γ n, v⟫_ℂ‖ ^ 2)
      (((twistedBasis γ).hasSum_norm_inner_sq v).summable.mul_left 4) (fun n => ?_)
      (.of_forall fun t n => ?_)
    · simpa using this
    · have h1 := (((hasDerivAt_phase (ħ := ħ) (γ + 2 * π * n)
        ⟪twistedBasis γ n, ψ⟫_ℂ).tendsto_slope.sub_const ⟪twistedBasis γ n, v⟫_ℂ).norm.pow 2)
      rwa [← h n, sub_self, norm_zero, zero_pow two_ne_zero] at h1
    · have hle := norm_slope_phase_le (ħ := ħ) (γ + 2 * π * n) ⟪twistedBasis γ n, ψ⟫_ℂ t
      rw [← h n] at hle
      have h2 : ‖slope (φ n) 0 t - ⟪twistedBasis γ n, v⟫_ℂ‖ ≤ 2 * ‖⟪twistedBasis γ n, v⟫_ℂ‖ := by
        linarith [norm_sub_le (slope (φ n) 0 t) ⟪twistedBasis γ n, v⟫_ℂ]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (slope (φ n) 0 t - ⟪twistedBasis γ n, v⟫_ℂ)]
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  have h2 := (Real.continuous_sqrt.tendsto 0).comp hT
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun t => ?_
  rw [Function.comp_apply, hP (slope (fun t => twistedTranslation γ (t / ħ) ψ) 0 t - v)]
  exact congrArg _ (tsum_congr fun n => by rw [hcoef])

/-- Derivatives of `U_α` from the right and of `U_β` from the left give one of `U`. -/
lemma hasDerivAt_switchedPropagator {ψ v : L²}
    (hα : HasDerivAt (fun t => twistedTranslation α (t / ħ) ψ) v 0)
    (hβ : HasDerivAt (fun t => twistedTranslation β (t / ħ) ψ) v 0) :
    HasDerivAt (fun t => U ħ α β t ψ) v 0 := by
  have h₁ : HasDerivWithinAt (fun t => U ħ α β t ψ) v (Ici 0) 0 :=
    hα.hasDerivWithinAt.congr (fun t ht => by rw [switchedPropagator_of_nonneg ht])
      (by rw [switchedPropagator_of_nonneg le_rfl])
  have h₂ : HasDerivWithinAt (fun t => U ħ α β t ψ) v (Iic 0) 0 :=
    hβ.hasDerivWithinAt.congr (fun t ht => by rw [switchedPropagator_of_nonpos ht])
      (by rw [switchedPropagator_of_nonpos le_rfl])
  have h := h₂.union h₁
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at h

/-! ### Primitives and `H¹₀(0, 1)` -/

lemma intervalIntegrable_lift (g : L²) (a b : ℝ) :
    IntervalIntegrable (fun u : ℝ => g (u : 𝕋)) volume a b := by
  have hper : Function.Periodic (fun u : ℝ => g (u : 𝕋)) 1 := fun u => by
    simp only [AddCircle.coe_add_period]
  refine hper.intervalIntegrable₀ one_ne_zero ?_ a b
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hm := UnitAddCircle.measurePreserving_mk 0
  rw [zero_add] at hm
  have hg : Integrable (g : 𝕋 → ℂ) volume := by
    rw [volume_eq_haarAddCircle]
    exact (Lp.memLp g).integrable one_le_two
  exact (hm.integrable_comp hg.aestronglyMeasurable).mpr hg

lemma continuous_primitive_lift (g : L²) :
    Continuous fun r : ℝ => ∫ u in (0 : ℝ)..r, g (u : 𝕋) :=
  intervalIntegral.continuous_primitive (intervalIntegrable_lift g) 0

/-- The primitive `x ↦ ∫₀ˣ g`, for `x ∈ [0, 1)`. -/
def primitiveFun (g : L²) (x : 𝕋) : ℂ := ∫ u in (0 : ℝ)..circleRep x, g (u : 𝕋)

lemma memLp_primitiveFun (g : L²) : MemLp (primitiveFun g) 2 μc := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_primitive_lift g).continuousOn
  exact MemLp.of_bound
    ((continuous_primitive_lift g).measurable.comp measurable_circleRep).aestronglyMeasurable C
    (.of_forall fun x => hC _ (Ico_subset_Icc_self (circleRep_mem x)))

/-- The primitive `x ↦ ∫₀ˣ g` in `L²(0, 1)`. -/
def primitive (g : L²) : L² := (memLp_primitiveFun g).toLp

/-- `H¹₀(0, 1)`, in its absolutely continuous form: the `ψ(x) = ∫₀ˣ g` with `g ∈ L²(0, 1)` and
`∫₀¹ g = 0`, so that `ψ(0) = ψ(1) = 0`. -/
def sobolevZero : Set L² :=
  {ψ | ∃ g : L², ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0 ∧ ψ = primitive g}

lemma integral_comp_circleRep (F : ℝ → ℂ) :
    ∫ x, F (circleRep x) ∂μc = ∫ u in (0 : ℝ)..1, F u := by
  rw [← volume_eq_haarAddCircle, ← UnitAddCircle.intervalIntegral_preimage 0, zero_add]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(by simp [ae_iff] : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ 1)] with a ha hmem
  rw [uIoc_of_le zero_le_one] at hmem
  rw [circleRep_coe, Int.fract_eq_self.mpr ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ha⟩]

lemma inner_planeWave_eq_integral (δ : ℝ) {f : L²} {F : ℝ → ℂ}
    (hF : f =ᵐ[μc] fun x => F (circleRep x)) :
    ⟪planeWave δ, f⟫_ℂ =
      ∫ u in (0 : ℝ)..1, Complex.exp (-(Complex.I * ((δ * u : ℝ) : ℂ))) * F u := by
  rw [L2.inner_def, ← integral_comp_circleRep]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_planeWaveFun δ).coeFn_toLp, hF] with x h₁ h₂
  rw [planeWave, h₁, h₂, RCLike.inner_apply, planeWaveFun, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, neg_mul, mul_comm]

/-- **Integration by parts**: `⟨e^{iδx}, -i g⟩ = δ ⟨e^{iδx}, Φ⟩ - i e^{-iδ} Φ(1)` for the
primitive `Φ(x) = ∫₀ˣ g`. -/
lemma inner_planeWave_neg_I_smul (δ : ℝ) (g : L²) :
    ⟪planeWave δ, (-Complex.I) • g⟫_ℂ = δ * ⟪planeWave δ, primitive g⟫_ℂ -
      Complex.I * Complex.exp (-(Complex.I * δ)) * ∫ u in (0 : ℝ)..1, g (u : 𝕋) := by
  have hK : ∀ x : ℝ, HasDerivAt (fun u : ℝ => Complex.exp (-(Complex.I * ((δ * u : ℝ) : ℂ))))
      (Complex.exp (-(Complex.I * ((δ * x : ℝ) : ℂ))) * (-(Complex.I * δ))) x := fun x => by
    have := ((((hasDerivAt_id' x).const_mul δ).ofReal_comp).const_mul Complex.I).neg.cexp
    convert this using 1
    simp
  have hK' : Continuous fun x : ℝ =>
      Complex.exp (-(Complex.I * ((δ * x : ℝ) : ℂ))) * (-(Complex.I * δ)) := by fun_prop
  have ibp := intervalIntegral.integral_deriv_mul_primitive zero_le_one hK hK'
    (intervalIntegrable_lift g 0 1)
  have h₁ : ⟪planeWave δ, g⟫_ℂ = ∫ u in (0 : ℝ)..1,
      Complex.exp (-(Complex.I * ((δ * u : ℝ) : ℂ))) * g (u : 𝕋) :=
    inner_planeWave_eq_integral δ (.of_forall fun x => by
      change g x = g ((circleRep x : ℝ) : 𝕋)
      rw [coe_circleRep])
  have h₂ : ⟪planeWave δ, primitive g⟫_ℂ = ∫ u in (0 : ℝ)..1,
      Complex.exp (-(Complex.I * ((δ * u : ℝ) : ℂ))) * ∫ v in (0 : ℝ)..u, g (v : 𝕋) :=
    inner_planeWave_eq_integral δ (memLp_primitiveFun g).coeFn_toLp
  set B := ∫ u in (0 : ℝ)..1,
    Complex.exp (-(Complex.I * ((δ * u : ℝ) : ℂ))) * ∫ v in (0 : ℝ)..u, g (v : 𝕋)
  have hB : ∫ u in (0 : ℝ)..1, Complex.exp (-(Complex.I * ((δ * u : ℝ) : ℂ))) *
      (-(Complex.I * δ)) * ∫ v in (0 : ℝ)..u, g (v : 𝕋) = -(Complex.I * δ) * B := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext u
    ring
  rw [hB] at ibp
  rw [inner_smul_right, h₁, h₂]
  simp only [mul_one] at ibp
  linear_combination (-Complex.I) * ibp + (-(δ : ℂ) * B) * Complex.I_sq

/-! ### `H¹₀ ⊆ D`, and `H₀ = -i d/dx` -/

lemma hasDerivAt_twistedTranslation_primitive (γ : ℝ) {g : L²}
    (hg : ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0) :
    HasDerivAt (fun t => twistedTranslation γ (t / ħ) (primitive g))
      ((-(Complex.I * ((ħ⁻¹ : ℝ) : ℂ))) • (-Complex.I) • g) 0 := by
  refine hasDerivAt_twistedTranslation_of_inner fun n => ?_
  rw [inner_smul_right, twistedBasis_apply, inner_planeWave_neg_I_smul, hg, mul_zero, sub_zero]
  push_cast
  ring

/-- **`H¹₀ ⊆ D`**: `t ↦ U(t) ψ` is differentiable at `0` for `ψ(x) = ∫₀ˣ g`, `∫₀¹ g = 0`. -/
theorem primitive_mem_switchedDomain {g : L²} (hg : ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0) :
    primitive g ∈ switchedDomain ħ α β :=
  mem_switchedDomain.mpr (hasDerivAt_switchedPropagator
    (hasDerivAt_twistedTranslation_primitive α hg)
    (hasDerivAt_twistedTranslation_primitive β hg)).differentiableAt

/-- **`H₀ = -i d/dx`** on `H¹₀`. -/
theorem switchedHamiltonian_primitive (hħ : ħ ≠ 0) {g : L²}
    (hg : ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0) :
    switchedHamiltonian ħ α β ⟨primitive g, primitive_mem_switchedDomain hg⟩ =
      (-Complex.I) • g := by
  rw [switchedHamiltonian_apply, (hasDerivAt_switchedPropagator
    (hasDerivAt_twistedTranslation_primitive α hg)
    (hasDerivAt_twistedTranslation_primitive β hg)).deriv, smul_smul]
  have hħc : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  have h1 : Complex.I * ħ * -(Complex.I * ((ħ⁻¹ : ℝ) : ℂ)) = 1 := by
    calc Complex.I * ħ * -(Complex.I * ((ħ⁻¹ : ℝ) : ℂ))
        = -(Complex.I * Complex.I) * ((ħ : ℂ) * (ħ : ℂ)⁻¹) := by push_cast; ring
      _ = 1 := by rw [Complex.I_mul_I, mul_inv_cancel₀ hħc]; ring
  rw [h1, one_smul]

/-! ### `D ⊆ H¹₀` -/

lemma mul_inner_twistedBasis_planeWave_zero (γ : ℝ) (n : ℤ) :
    ((γ + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis γ n, planeWave 0⟫_ℂ =
      Complex.I * (Complex.exp (-(Complex.I * γ)) - 1) := by
  rw [twistedBasis_apply, inner_planeWave_planeWave_eq, ← exp_twistedBasis_eigenvalue γ n]
  set δ := γ + 2 * π * n
  rcases eq_or_ne δ 0 with hδ | hδ
  · simp [hδ]
  have hc : Complex.I * ((0 - δ : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast sub_ne_zero.mpr (Ne.symm hδ))
  rw [integral_exp_mul_complex hc, mul_div_assoc', div_eq_iff hc]
  have e₁ : Complex.I * ((0 - δ : ℝ) : ℂ) * ((1 : ℝ) : ℂ) = -(Complex.I * δ) := by
    push_cast
    ring
  have e₀ : Complex.I * ((0 - δ : ℝ) : ℂ) * ((0 : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [e₁, e₀, Complex.exp_zero]
  push_cast
  linear_combination ((δ : ℂ) * (Complex.exp (-(Complex.I * δ)) - 1)) * Complex.I_sq

lemma exists_add_two_pi_mul_eq_zero {γ : ℝ} (h1 : Complex.exp (Complex.I * γ) = 1) :
    ∃ m : ℤ, γ + 2 * π * m = 0 := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
  have h : Complex.I * (γ : ℂ) = Complex.I * ((2 * π * m : ℝ) : ℂ) := by
    rw [hm]
    push_cast
    ring
  have h' : γ = 2 * π * m := by exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero h
  exact ⟨-m, by rw [h']; push_cast; ring⟩

/-- If `(γ + 2πn) ⟨eₙ, f⟩ = -i e^{-iγ} c` for all `n` and `e^{iγ} = 1`, then `c = 0`. -/
lemma eq_zero_of_mul_inner_twistedBasis {γ : ℝ} {f : L²} {c : ℂ}
    (hf : ∀ n : ℤ, ((γ + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis γ n, f⟫_ℂ =
      -(Complex.I * Complex.exp (-(Complex.I * γ)) * c))
    (h1 : Complex.exp (Complex.I * γ) = 1) : c = 0 := by
  obtain ⟨m, hγ⟩ := exists_add_two_pi_mul_eq_zero h1
  have h := hf m
  rw [hγ, Complex.ofReal_zero, zero_mul] at h
  have hne : Complex.I * Complex.exp (-(Complex.I * γ)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.exp_ne_zero _)
  exact (mul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left hne

/-- If `(γ + 2πn) ⟨eₙ, f⟩ = -i e^{-iγ} c` for all `n` and `e^{iγ} ≠ 1`, then `f` is the
constant `c / (e^{iγ} - 1)`. -/
lemma eq_smul_of_mul_inner_twistedBasis {γ : ℝ} {f : L²} {c : ℂ}
    (hf : ∀ n : ℤ, ((γ + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis γ n, f⟫_ℂ =
      -(Complex.I * Complex.exp (-(Complex.I * γ)) * c))
    (h1 : Complex.exp (Complex.I * γ) ≠ 1) :
    f = (c / (Complex.exp (Complex.I * γ) - 1)) • planeWave 0 := by
  refine (twistedBasis γ).ext_inner fun n => ?_
  have hδ : ((γ + 2 * π * n : ℝ) : ℂ) ≠ 0 := by
    intro h0
    apply h1
    have h' : (γ : ℂ) = -(2 * π * n) := by
      push_cast at h0
      linear_combination h0
    rw [h', Complex.exp_eq_one_iff]
    exact ⟨-n, by push_cast; ring⟩
  refine mul_left_cancel₀ hδ ?_
  rw [hf n, inner_smul_right, mul_left_comm, mul_inner_twistedBasis_planeWave_zero,
    Complex.exp_neg]
  have hE : Complex.exp (Complex.I * γ) ≠ 0 := Complex.exp_ne_zero _
  have hE1 : Complex.exp (Complex.I * γ) - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp
  ring

/-- If `(γ + 2πn) ⟨eₙ, f⟩ = -i e^{-iγ} c` for all `n`, then `f` is a constant `k` with
`c = (e^{iγ} - 1) k`. -/
lemma exists_smul_of_mul_inner_twistedBasis {γ : ℝ} {f : L²} {c : ℂ}
    (hf : ∀ n : ℤ, ((γ + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis γ n, f⟫_ℂ =
      -(Complex.I * Complex.exp (-(Complex.I * γ)) * c)) :
    ∃ k : ℂ, f = k • planeWave 0 ∧ c = (Complex.exp (Complex.I * γ) - 1) * k := by
  by_cases h1 : Complex.exp (Complex.I * γ) = 1
  · have hc := eq_zero_of_mul_inner_twistedBasis hf h1
    obtain ⟨m, hγ⟩ := exists_add_two_pi_mul_eq_zero h1
    refine ⟨⟪twistedBasis γ m, f⟫_ℂ, ?_, by rw [hc, h1, sub_self, zero_mul]⟩
    have he : twistedBasis γ m = planeWave 0 := by rw [twistedBasis_apply, hγ]
    rw [← he]
    refine (twistedBasis γ).ext_inner fun n => ?_
    rw [inner_smul_right, orthonormal_iff_ite.mp (twistedBasis γ).orthonormal]
    split_ifs with hn
    · rw [hn, mul_one]
    · have hδ : ((γ + 2 * π * n : ℝ) : ℂ) ≠ 0 := by
        have : γ + 2 * π * n = 2 * π * (n - m : ℤ) := by push_cast; linear_combination hγ
        rw [this]
        exact_mod_cast mul_ne_zero (by positivity) (Int.cast_ne_zero.mpr (sub_ne_zero.mpr hn))
      have h := hf n
      rw [hc, mul_zero, neg_zero] at h
      rw [mul_zero]
      exact (mul_eq_zero.mp h).resolve_left hδ
  · refine ⟨_, eq_smul_of_mul_inner_twistedBasis hf h1, ?_⟩
    field_simp [sub_ne_zero.mpr h1]

lemma planeWave_zero_ne_zero : planeWave 0 ≠ 0 := by
  intro h
  have := inner_planeWave_planeWave_eq 0 0
  rw [h, inner_zero_left] at this
  simp at this

/-- **`D ⊆ H¹₀`**, and `H₀ = -i d/dx`: if `t ↦ U(t) ψ` is differentiable at `0`, then
`ψ(x) = ∫₀ˣ g` with `∫₀¹ g = 0` and `H₀ ψ = -i g`. -/
theorem exists_primitive_of_mem_switchedDomain (hħ : ħ ≠ 0)
    (h : Complex.exp (Complex.I * α) ≠ Complex.exp (Complex.I * β)) {ψ : L²}
    (hψ : ψ ∈ switchedDomain ħ α β) :
    ∃ g : L², ∫ u in (0 : ℝ)..1, g (u : 𝕋) = 0 ∧ ψ = primitive g ∧
      switchedHamiltonian ħ α β ⟨ψ, hψ⟩ = (-Complex.I) • g := by
  set v := deriv (fun t => U ħ α β t ψ) 0
  have hA := (mem_switchedDomain.mp hψ).hasDerivAt
  set g : L² := Complex.I • (Complex.I * ħ) • v
  have hg : (-Complex.I) • g = (Complex.I * ħ) • v := by
    rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
  have hħc : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  -- the eigenvalue relation for `γ = α` (from the right) and `γ = β` (from the left)
  have hcoef : ∀ γ : ℝ, (∀ n : ℤ, ⟪twistedBasis γ n, v⟫_ℂ =
      -(Complex.I * (((γ + 2 * π * n) / ħ : ℝ) : ℂ)) * ⟪twistedBasis γ n, ψ⟫_ℂ) →
      ∀ n : ℤ, ((γ + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis γ n, ψ - primitive g⟫_ℂ =
        -(Complex.I * Complex.exp (-(Complex.I * γ)) * ∫ u in (0 : ℝ)..1, g (u : 𝕋)) := by
    intro γ hγ n
    have hC := inner_planeWave_neg_I_smul (γ + 2 * π * n) g
    rw [← twistedBasis_apply, hg, inner_smul_right, hγ n, ← mul_assoc,
      exp_twistedBasis_eigenvalue] at hC
    have key : Complex.I * ħ * -(Complex.I * (((γ + 2 * π * n) / ħ : ℝ) : ℂ)) =
        ((γ + 2 * π * n : ℝ) : ℂ) := by
      rw [Complex.ofReal_div]
      calc Complex.I * ħ * -(Complex.I * (((γ + 2 * π * n : ℝ) : ℂ) / ħ))
          = -(Complex.I * Complex.I) * ((γ + 2 * π * n : ℝ) : ℂ) * ((ħ : ℂ) * (ħ : ℂ)⁻¹) := by
            ring
        _ = ((γ + 2 * π * n : ℝ) : ℂ) := by
            rw [Complex.I_mul_I, mul_inv_cancel₀ hħc]
            ring
    rw [key] at hC
    rw [inner_sub_right]
    linear_combination hC
  have hα := hcoef α (inner_twistedBasis_of_hasDerivWithinAt (uniqueDiffWithinAt_Ici 0)
    (mem_Ici.mpr le_rfl) (hA.hasDerivWithinAt.congr
      (fun t ht => by rw [switchedPropagator_of_nonneg ht])
      (by rw [switchedPropagator_of_nonneg le_rfl])))
  have hβ := hcoef β (inner_twistedBasis_of_hasDerivWithinAt (uniqueDiffWithinAt_Iic 0)
    (mem_Iic.mpr le_rfl) (hA.hasDerivWithinAt.congr
      (fun t ht => by rw [switchedPropagator_of_nonpos ht])
      (by rw [switchedPropagator_of_nonpos le_rfl])))
  -- `Φ(1) = 0` and `ψ = Φ`
  set c := ∫ u in (0 : ℝ)..1, g (u : 𝕋)
  have hc : c = 0 := by
    by_cases hα1 : Complex.exp (Complex.I * α) = 1
    · exact eq_zero_of_mul_inner_twistedBasis hα hα1
    by_cases hβ1 : Complex.exp (Complex.I * β) = 1
    · exact eq_zero_of_mul_inner_twistedBasis hβ hβ1
    have hk := (eq_smul_of_mul_inner_twistedBasis hα hα1).symm.trans
      (eq_smul_of_mul_inner_twistedBasis hβ hβ1)
    have hk' := smul_left_injective ℂ planeWave_zero_ne_zero hk
    rw [div_eq_div_iff (sub_ne_zero.mpr hα1) (sub_ne_zero.mpr hβ1)] at hk'
    have : c * (Complex.exp (Complex.I * β) - Complex.exp (Complex.I * α)) = 0 := by
      linear_combination hk'
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (Ne.symm h))
  have hf : ψ - primitive g = 0 := by
    by_cases hα1 : Complex.exp (Complex.I * α) = 1
    · have hβ1 : Complex.exp (Complex.I * β) ≠ 1 := hα1 ▸ Ne.symm h
      rw [eq_smul_of_mul_inner_twistedBasis hβ hβ1, hc, zero_div, zero_smul]
    · rw [eq_smul_of_mul_inner_twistedBasis hα hα1, hc, zero_div, zero_smul]
  refine ⟨g, hc, sub_eq_zero.mp hf, ?_⟩
  rw [switchedHamiltonian_apply, hg]

/-- **`D = H¹₀(0, 1)`** for `e^{iα} ≠ e^{iβ}`: `t ↦ U(t) ψ` is differentiable at `0` exactly
for `ψ(x) = ∫₀ˣ g` with `g ∈ L²(0, 1)` and `∫₀¹ g = 0`. -/
theorem switchedDomain_eq (hħ : ħ ≠ 0)
    (h : Complex.exp (Complex.I * α) ≠ Complex.exp (Complex.I * β)) :
    (switchedDomain ħ α β : Set L²) = sobolevZero := by
  ext ψ
  constructor
  · intro hψ
    obtain ⟨g, hg, hψg, -⟩ := exists_primitive_of_mem_switchedDomain hħ h hψ
    exact ⟨g, hg, hψg⟩
  · rintro ⟨g, hg, rfl⟩
    exact primitive_mem_switchedDomain hg

end UnitaryEntropy
