/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.MeasureTheory.Function.LpSpace.Multiplication
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Switching between two self-adjoint momenta: the derived Hamiltonian is not self-adjoint

On `L²(0, 1)`, the momentum `-i d/dx` with the boundary condition `ψ(1) = e^{iα} ψ(0)` is a
self-adjoint operator `H_α`. Its unitary group `U_α(t) = e^{-itH_α/ħ}` translates by `t/ħ`, with
the phase `e^{iα}` picked up at each wrap-around (`twistedTranslation`). Here `L²(0, 1)` is
`L²` of the circle `ℝ/ℤ` with Haar measure, and `x ↦ circleRep x ∈ [0, 1)` is the coordinate.

Let `H(t) = H_β` for `t < 0` and `H(t) = H_α` for `t ≥ 0`, with `e^{iα} ≠ e^{iβ}`, so that the
family differentiated at `t₀ = 0` is `U(t) = U_α(t)` for `t ≥ 0` and `U(t) = U_β(t)` for `t < 0`
(`switchedPropagator`). Every `U(t)` is unitary. Let `D` be the set of `ψ` for which
`t ↦ U(t) ψ` is differentiable at `0`, and `H₀ ψ = iħ U'(0) ψ` on `D` (`switchedHamiltonian`).
Then `D` is dense and `H₀` is symmetric, but `H₀` is not self-adjoint: the plane wave
`e^{iαx}` lies in the domain of `H₀†`, as `⟨e^{iαx}, H₀ ψ⟩ = α ⟨e^{iαx}, ψ⟩` on `D`, but not in
`D`. Indeed `t ↦ ⟨e^{iβx}, U(t) e^{iαx}⟩` has the right derivative `-iα/ħ c` and the left
derivative `-iβ/ħ c` at `0`, with `c = ⟨e^{iβx}, e^{iαx}⟩ ≠ 0`. So DR-INFO and EVDIFF on a
dense set of states, at one time `t₀`, do not give a self-adjoint `H(t₀)`.

`D` is in fact `H¹₀(0, 1)` and `H₀` the minimal momentum operator `-i d/dx`, when
`e^{iα} ≠ e^{iβ}` (`UnitaryEntropy.MomentumDomain`), and `U_α(t)` is `e^{-itH_α/ħ}`
(`UnitaryEntropy.MomentumPropagator`). The counterexample does not need either.

## Main results

* `twistedTranslation_mem_unitary`: each `U_α(t)` is unitary.
* `hasDerivAt_twistedTranslation_fourierDiff`, `dense_switchedDomain`: `D` is dense; it contains
  `e^{2πinx} - 1` for every `n`.
* `switchedHamiltonian_symm`: `H₀` is symmetric.
* `planeWave_mem_adjoint_domain`, `planeWave_not_mem_switchedDomain`.
* `not_isSelfAdjoint_switchedHamiltonian`, `switchedHamiltonian_counterexample`.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy

open MeasureTheory Filter Topology Set AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate Real LinearPMap

/-- The circle `ℝ/ℤ`. -/
local notation "𝕋" => AddCircle (1 : ℝ)

/-- Haar probability measure on `ℝ/ℤ`, which is Lebesgue measure on `[0, 1)`. -/
local notation "μc" => (haarAddCircle : Measure 𝕋)

/-- `L²(0, 1)`, as `L²` of the circle. -/
local notation "L²" => Lp ℂ 2 μc

/-- The coordinate of a point of `ℝ/ℤ` in `[0, 1)`. -/
def circleRep (x : 𝕋) : ℝ := (AddCircle.equivIco 1 0 x : ℝ)

lemma circleRep_coe (y : ℝ) : circleRep (y : 𝕋) = Int.fract y := by
  simp [circleRep]

lemma coe_circleRep (x : 𝕋) : ((circleRep x : ℝ) : 𝕋) = x := by
  simp [circleRep]

lemma circleRep_mem (x : 𝕋) : circleRep x ∈ Ico (0 : ℝ) 1 := by
  have h := (AddCircle.equivIco 1 0 x).2
  show (AddCircle.equivIco 1 0 x : ℝ) ∈ Ico 0 1
  exact ⟨h.1, by linarith [h.2]⟩

lemma measurable_circleRep : Measurable circleRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

lemma volume_eq_haarAddCircle : (volume : Measure 𝕋) = μc := by
  rw [volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

lemma haarAddCircle_singleton_zero : μc {0} = 0 := by
  rw [← volume_eq_haarAddCircle, ← (UnitAddCircle.measurePreserving_mk 0).measure_preimage
    (measurableSet_singleton _).nullMeasurableSet]
  have h0 : volume (((↑) : ℝ → 𝕋) ⁻¹' {0}) = 0 := by
    refine measure_mono_null (fun y (hy : ((y : ℝ) : 𝕋) = 0) => ?_)
      ((countable_range ((↑) : ℤ → ℝ)).measure_zero volume)
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hy
    exact ⟨n, by simpa using hn⟩
  exact nonpos_iff_eq_zero.mp ((Measure.restrict_le_self _).trans h0.le)

lemma ae_ne_zero : ∀ᵐ x ∂μc, x ≠ 0 := by
  simp [ae_iff, haarAddCircle_singleton_zero]

lemma measurePreserving_sub (s : ℝ) : MeasurePreserving (fun x : 𝕋 => x - s) μc μc :=
  measurePreserving_sub_right μc _

/-! ### Twisted translations -/

/-- The phase of the twisted translation by `s`: `e^{iγk}`, where `k` is the number of
wrap-arounds. -/
def twistPhase (γ s : ℝ) (x : 𝕋) : ℂ :=
  Complex.exp (Complex.I * ((γ * (circleRep x - circleRep (x - s) - s) : ℝ) : ℂ))

lemma measurable_twistPhase (γ s : ℝ) : Measurable (twistPhase γ s) := by
  unfold twistPhase
  have h1 := measurable_circleRep
  have h2 : Measurable fun x : 𝕋 => circleRep (x - s) :=
    measurable_circleRep.comp (measurable_id.sub_const _)
  fun_prop

lemma norm_twistPhase (γ s : ℝ) (x : 𝕋) : ‖twistPhase γ s x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

lemma memLp_twistPhase (γ s : ℝ) : MemLp (twistPhase γ s) ∞ μc :=
  memLp_top_of_bound (measurable_twistPhase γ s).aestronglyMeasurable 1
    (.of_forall fun x => (norm_twistPhase γ s x).le)

/-- Translation by `s` on `L²(ℝ/ℤ)`. -/
def circleShift (s : ℝ) : L² →L[ℂ] L² :=
  (Lp.compMeasurePreservingₗᵢ ℂ _ (measurePreserving_sub s)).toContinuousLinearMap

lemma coeFn_circleShift (s : ℝ) (f : L²) : circleShift s f =ᵐ[μc] fun x => f (x - s) :=
  Lp.coeFn_compMeasurePreserving _ _

lemma norm_circleShift (s : ℝ) (f : L²) : ‖circleShift s f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

/-- The twisted translation `U_γ(sħ) = e^{-isH_γ}`: `ψ(x) ↦ e^{iγk} ψ(x - s)`, with `k` the
number of wrap-arounds. -/
def twistedTranslation (γ s : ℝ) : L² →L[ℂ] L² :=
  Lp.mulL (twistPhase γ s) ∘L circleShift s

lemma coeFn_twistedTranslation (γ s : ℝ) (f : L²) :
    twistedTranslation γ s f =ᵐ[μc] fun x => twistPhase γ s x * f (x - s) := by
  filter_upwards [Lp.coeFn_mulL (memLp_twistPhase γ s) (circleShift s f),
    coeFn_circleShift s f] with x h₁ h₂
  rw [twistedTranslation, ContinuousLinearMap.comp_apply, h₁, h₂]

lemma norm_twistedTranslation (γ s : ℝ) (f : L²) : ‖twistedTranslation γ s f‖ = ‖f‖ := by
  rw [← norm_circleShift s f]
  have h := Lp.coeFn_mulL (memLp_twistPhase γ s) (circleShift s f)
  refine le_antisymm (Lp.norm_le_norm_of_ae_le ?_) (Lp.norm_le_norm_of_ae_le ?_) <;>
    filter_upwards [h] with x hx <;>
    simp [twistedTranslation, hx, norm_twistPhase]

lemma inner_twistedTranslation (γ s : ℝ) (f g : L²) :
    ⟪twistedTranslation γ s f, twistedTranslation γ s g⟫_ℂ = ⟪f, g⟫_ℂ :=
  LinearIsometry.inner_map_map
    { toLinearMap := (twistedTranslation γ s).toLinearMap
      norm_map' := norm_twistedTranslation γ s } f g

lemma twistedTranslation_zero (γ : ℝ) : twistedTranslation γ 0 = 1 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  change twistedTranslation γ 0 f =ᵐ[μc] f
  filter_upwards [coeFn_twistedTranslation γ 0 f] with x hx
  simp [hx, twistPhase]

lemma twistedTranslation_mul_neg (γ s : ℝ) :
    twistedTranslation γ s * twistedTranslation γ (-s) = 1 := by
  refine ContinuousLinearMap.ext fun f => Lp.ext ?_
  change twistedTranslation γ s (twistedTranslation γ (-s) f) =ᵐ[μc] f
  filter_upwards [coeFn_twistedTranslation γ s (twistedTranslation γ (-s) f),
    (measurePreserving_sub s).quasiMeasurePreserving.ae_eq_comp
      (coeFn_twistedTranslation γ (-s) f)] with x h₁ h₂
  rw [h₁]
  simp only [Function.comp_apply] at h₂
  have hx : x - (s : 𝕋) - ((-s : ℝ) : 𝕋) = x := by
    rw [AddCircle.coe_neg, sub_neg_eq_add, sub_add_cancel]
  rw [h₂, hx, twistPhase, twistPhase, hx, ← mul_assoc, ← Complex.exp_add]
  convert one_mul _ using 2
  rw [← Complex.exp_zero]
  congr 1
  push_cast
  ring

theorem twistedTranslation_mem_unitary (γ s : ℝ) :
    twistedTranslation γ s ∈ unitary (L² →L[ℂ] L²) := by
  have h₁ : star (twistedTranslation γ s) * twistedTranslation γ s = 1 :=
    (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self _).mp
      (inner_twistedTranslation γ s)
  have h₂ : star (twistedTranslation γ s) = twistedTranslation γ (-s) := by
    rw [← mul_one (star _), ← twistedTranslation_mul_neg γ s, ← mul_assoc, h₁, one_mul]
  refine ⟨h₁, ?_⟩
  rw [h₂, twistedTranslation_mul_neg]

/-! ### Plane waves -/

/-- The plane wave `e^{iγx}`, an eigenvector of `H_γ` with eigenvalue `γ`. -/
def planeWaveFun (γ : ℝ) (x : 𝕋) : ℂ := Complex.exp (Complex.I * ((γ * circleRep x : ℝ) : ℂ))

lemma measurable_planeWaveFun (γ : ℝ) : Measurable (planeWaveFun γ) := by
  unfold planeWaveFun
  have := measurable_circleRep
  fun_prop

lemma memLp_planeWaveFun (γ : ℝ) : MemLp (planeWaveFun γ) 2 μc :=
  MemLp.of_bound (measurable_planeWaveFun γ).aestronglyMeasurable 1
    (.of_forall fun _ => (Complex.norm_exp_I_mul_ofReal _).le)

/-- The plane wave `e^{iγx}` in `L²(0, 1)`. -/
def planeWave (γ : ℝ) : L² := (memLp_planeWaveFun γ).toLp

lemma twistedTranslation_planeWave (γ s : ℝ) :
    twistedTranslation γ s (planeWave γ) =
      Complex.exp (-(Complex.I * ((γ * s : ℝ) : ℂ))) • planeWave γ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_twistedTranslation γ s (planeWave γ),
    (measurePreserving_sub s).quasiMeasurePreserving.ae_eq_comp
      (memLp_planeWaveFun γ).coeFn_toLp,
    Lp.coeFn_smul (Complex.exp (-(Complex.I * ((γ * s : ℝ) : ℂ)))) (planeWave γ),
    (memLp_planeWaveFun γ).coeFn_toLp] with x h₁ h₂ h₃ h₄
  simp only [Function.comp_apply] at h₂
  rw [h₁, h₃, Pi.smul_apply, planeWave, h₂, h₄, smul_eq_mul, twistPhase, planeWaveFun,
    planeWaveFun, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma inner_planeWave_twistedTranslation (γ s : ℝ) (f : L²) :
    ⟪planeWave γ, twistedTranslation γ s f⟫_ℂ =
      Complex.exp (-(Complex.I * ((γ * s : ℝ) : ℂ))) * ⟪planeWave γ, f⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def, ← integral_const_mul]
  conv_rhs => rw [← integral_sub_right_eq_self (μ := μc) _ (s : 𝕋)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_twistedTranslation γ s f, (memLp_planeWaveFun γ).coeFn_toLp,
    (measurePreserving_sub s).quasiMeasurePreserving.ae_eq_comp
      (memLp_planeWaveFun γ).coeFn_toLp] with x h₁ h₂ h₃
  simp only [Function.comp_apply] at h₃
  rw [h₁, planeWave, h₂, h₃, RCLike.inner_apply, RCLike.inner_apply, twistPhase, planeWaveFun,
    planeWaveFun, ← Complex.exp_conj, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have key : Complex.exp (Complex.I * ((γ * (circleRep x - circleRep (x - s) - s) : ℝ) : ℂ)) *
      Complex.exp (-Complex.I * ((γ * circleRep x : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * ((γ * s : ℝ) : ℂ))) *
        Complex.exp (-Complex.I * ((γ * circleRep (x - s) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (f : 𝕋 → ℂ) (x - s) * key

lemma inner_planeWave_planeWave_eq (α β : ℝ) :
    ⟪planeWave β, planeWave α⟫_ℂ =
      ∫ a in (0 : ℝ)..1, Complex.exp (Complex.I * ((α - β : ℝ) : ℂ) * a) := by
  rw [L2.inner_def]
  have h₁ : ∫ x, ⟪(planeWave β : 𝕋 → ℂ) x, (planeWave α : 𝕋 → ℂ) x⟫_ℂ ∂μc =
      ∫ x, Complex.exp (Complex.I * (((α - β) * circleRep x : ℝ) : ℂ)) ∂μc := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_planeWaveFun α).coeFn_toLp, (memLp_planeWaveFun β).coeFn_toLp]
      with x hα hβ
    rw [planeWave, planeWave, hα, hβ, RCLike.inner_apply, planeWaveFun, planeWaveFun,
      ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h₁, ← volume_eq_haarAddCircle, ← UnitAddCircle.intervalIntegral_preimage 0, zero_add]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [(by simp [ae_iff] : ∀ᵐ a ∂(volume : Measure ℝ), a ≠ 1)] with a ha hmem
  rw [uIoc_of_le zero_le_one] at hmem
  rw [circleRep_coe, Int.fract_eq_self.mpr ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ha⟩]
  congr 1
  push_cast
  ring

lemma inner_planeWave_planeWave {α β : ℝ}
    (h : Complex.exp (Complex.I * α) ≠ Complex.exp (Complex.I * β)) :
    ⟪planeWave β, planeWave α⟫_ℂ ≠ 0 := by
  have hne : ((α - β : ℝ) : ℂ) ≠ 0 := by
    intro h0
    apply h
    rw [show (α : ℂ) = β by exact_mod_cast sub_eq_zero.mp (by exact_mod_cast h0)]
  have hc : Complex.I * ((α - β : ℝ) : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero hne
  rw [inner_planeWave_planeWave_eq, integral_exp_mul_complex hc]
  refine div_ne_zero ?_ hc
  rw [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, sub_ne_zero]
  intro h1
  apply h
  rw [show Complex.I * α = Complex.I * ((α - β : ℝ) : ℂ) + Complex.I * β by push_cast; ring,
    Complex.exp_add, h1, one_mul]

/-! ### A dense set of differentiable vectors -/

/-- `e^{2πinx} - 1`, which vanishes at both ends of `[0, 1]`. -/
def fourierDiff (n : ℤ) : L² := fourierLp 2 n - fourierLp 2 0

lemma coeFn_fourierDiff (n : ℤ) : fourierDiff n =ᵐ[μc] fun x => fourier n x - 1 := by
  filter_upwards [Lp.coeFn_sub (fourierLp 2 n) (fourierLp 2 0), coeFn_fourierLp 2 n,
    coeFn_fourierLp 2 0] with x h h₁ h₀
  rw [fourierDiff, h, Pi.sub_apply, h₁, h₀, fourier_zero]

lemma fourier_eq (n : ℤ) (x : 𝕋) :
    fourier n x = Complex.exp (Complex.I * ((2 * π * n * circleRep x : ℝ) : ℂ)) := by
  conv_lhs => rw [← coe_circleRep x]
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

lemma exp_two_pi_fract (n : ℤ) (y : ℝ) :
    Complex.exp (Complex.I * ((2 * π * n * Int.fract y : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((2 * π * n * y : ℝ) : ℂ)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-(n * ⌊y⌋), by rw [← Int.self_sub_floor]; push_cast; ring⟩

/-- The quasi-periodic extension `e^{iγ⌊y⌋} (e^{2πiny} - 1)` of `e^{2πiny} - 1` from `[0, 1)`. -/
def quasiWave (γ : ℝ) (n : ℤ) (y : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((γ * ⌊y⌋ : ℝ) : ℂ)) *
    (Complex.exp (Complex.I * ((2 * π * n * y : ℝ) : ℂ)) - 1)

lemma measurable_quasiWave (γ : ℝ) (n : ℤ) : Measurable (quasiWave γ n) := by
  unfold quasiWave
  fun_prop

lemma quasiWave_of_mem (γ : ℝ) (n : ℤ) {y : ℝ} (hy : y ∈ Ico (0 : ℝ) 1) :
    quasiWave γ n y = Complex.exp (Complex.I * ((2 * π * n * y : ℝ) : ℂ)) - 1 := by
  simp [quasiWave, Int.floor_eq_zero_iff.mpr hy]

lemma twistedTranslation_fourierDiff (γ s : ℝ) (n : ℤ) :
    twistedTranslation γ s (fourierDiff n) =ᵐ[μc] fun x => quasiWave γ n (circleRep x - s) := by
  filter_upwards [coeFn_twistedTranslation γ s (fourierDiff n),
    (measurePreserving_sub s).quasiMeasurePreserving.ae_eq_comp (coeFn_fourierDiff n)]
    with x h₁ h₂
  simp only [Function.comp_apply] at h₂
  have hx : circleRep (x - s) = Int.fract (circleRep x - s) := by
    rw [← circleRep_coe, AddCircle.coe_sub, coe_circleRep]
  rw [h₁, h₂, fourier_eq, twistPhase, quasiWave, hx, exp_two_pi_fract]
  congr 3
  rw [← Int.self_sub_floor]
  push_cast
  ring

lemma norm_exp_I_sub_exp_I_le (a b : ℝ) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤ |a - b| := by
  have h : Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b) =
      Complex.exp (Complex.I * b) * (Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

lemma norm_exp_two_pi_sub_one_le (n : ℤ) (y : ℝ) (j : ℤ) :
    ‖Complex.exp (Complex.I * ((2 * π * n * y : ℝ) : ℂ)) - 1‖ ≤ 2 * π * |(n : ℝ)| * |y - j| := by
  have h1 : Complex.exp (Complex.I * ((2 * π * n * j : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨n * j, by push_cast; ring⟩
  rw [← h1]
  refine (norm_exp_I_sub_exp_I_le _ _).trans_eq ?_
  rw [← mul_sub, abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]

/-- `quasiWave` is Lipschitz near `[0, 1)`, across the jumps of the phase. -/
lemma norm_quasiWave_sub_le (γ : ℝ) (n : ℤ) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) 1) (s : ℝ) :
    ‖quasiWave γ n (r - s) - quasiWave γ n r‖ ≤ 4 * π * |(n : ℝ)| * |s| := by
  rw [quasiWave_of_mem γ n hr]
  by_cases h : r - s ∈ Ico (0 : ℝ) 1
  · rw [quasiWave_of_mem γ n h, sub_sub_sub_cancel_right]
    refine (norm_exp_I_sub_exp_I_le _ _).trans ?_
    rw [show 2 * π * n * (r - s) - 2 * π * n * r = -(2 * π * n * s) by ring, abs_neg, abs_mul,
      abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    have : 0 ≤ π * |(n : ℝ)| * |s| := by positivity
    linarith
  · obtain ⟨j, hj₁, hj₂⟩ : ∃ j : ℤ, |r - s - j| ≤ |s| ∧ |r - j| ≤ |s| := by
      have hr0 := hr.1
      have hr1 := hr.2
      rcases not_and_or.mp (mem_Ico.not.mp h) with h' | h' <;> push Not at h'
      · refine ⟨0, ?_, ?_⟩ <;>
          rw [Int.cast_zero, sub_zero, abs_of_pos (by linarith : 0 < s), abs_le] <;>
          constructor <;> linarith
      · refine ⟨1, ?_, ?_⟩ <;> rw [Int.cast_one, abs_of_neg (by linarith : s < 0), abs_le] <;>
          constructor <;> linarith
    refine (norm_sub_le _ _).trans ?_
    rw [quasiWave, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    have e₁ := norm_exp_two_pi_sub_one_le n (r - s) j
    have e₂ := norm_exp_two_pi_sub_one_le n r j
    have hn : 0 ≤ 2 * π * |(n : ℝ)| := by positivity
    linarith [mul_le_mul_of_nonneg_left hj₁ hn, mul_le_mul_of_nonneg_left hj₂ hn]

/-- The derivative `-(2πn/ħ) i e^{2πinx}` of `t ↦ U_γ(t) (e^{2πinx} - 1)` at `0`, for every
`γ`. -/
def fourierDeriv (ħ : ℝ) (n : ℤ) : L² := (-(Complex.I * ((2 * π * n / ħ : ℝ) : ℂ))) • fourierLp 2 n

lemma hasDerivAt_quasiWave (γ ħ : ℝ) (n : ℤ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun t => quasiWave γ n (r - t / ħ))
      (-(Complex.I * ((2 * π * n / ħ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((2 * π * n * r : ℝ) : ℂ))) 0 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), r - t / ħ ∈ Ico (0 : ℝ) 1 := by
    have hcont : Continuous fun t : ℝ => r - t / ħ := by fun_prop
    have hc : Tendsto (fun t : ℝ => r - t / ħ) (𝓝 0) (𝓝 r) := by
      simpa using hcont.tendsto 0
    exact hc.eventually (Ico_mem_nhds hr.1 hr.2)
  have hd := (((((hasDerivAt_id' (0 : ℝ)).div_const ħ).const_sub r).const_mul
    (2 * π * n)).ofReal_comp.const_mul Complex.I).cexp.sub_const 1
  refine (hd.congr_of_eventuallyEq (hev.mono fun t ht => quasiWave_of_mem γ n ht)).congr_deriv ?_
  simp only [zero_div, sub_zero]
  push_cast
  ring

theorem hasDerivAt_twistedTranslation_fourierDiff (γ ħ : ℝ) (n : ℤ) :
    HasDerivAt (fun t => twistedTranslation γ (t / ħ) (fourierDiff n)) (fourierDeriv ħ n) 0 := by
  rw [hasDerivAt_iff_tendsto_slope, Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  set G : ℝ → 𝕋 → ℂ := fun t x =>
    (t⁻¹ : ℝ) • (quasiWave γ n (circleRep x - t / ħ) - quasiWave γ n (circleRep x)) -
      -(Complex.I * ((2 * π * n / ħ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((2 * π * n * circleRep x : ℝ) : ℂ))
  have hmeas : ∀ t, AEStronglyMeasurable (G t) μc := fun t => by
    have h1 := measurable_circleRep
    have h2 := measurable_quasiWave γ n
    exact Measurable.aestronglyMeasurable (by fun_prop)
  have hbound : ∀ t x, ‖G t x‖ ≤ 6 * π * |(n : ℝ)| * |ħ|⁻¹ := fun t x => by
    have h₁ : ‖(t⁻¹ : ℝ) • (quasiWave γ n (circleRep x - t / ħ) - quasiWave γ n (circleRep x))‖ ≤
        4 * π * |(n : ℝ)| * |ħ|⁻¹ := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      rcases eq_or_ne t 0 with rfl | ht
      · simp only [abs_zero, inv_zero, zero_mul]
        positivity
      have ht' : |t| ≠ 0 := abs_ne_zero.mpr ht
      calc |t|⁻¹ * ‖quasiWave γ n (circleRep x - t / ħ) - quasiWave γ n (circleRep x)‖
          ≤ |t|⁻¹ * (4 * π * |(n : ℝ)| * |t / ħ|) :=
            mul_le_mul_of_nonneg_left (norm_quasiWave_sub_le γ n (circleRep_mem x) _)
              (by positivity)
        _ = 4 * π * |(n : ℝ)| * |ħ|⁻¹ := by
            rw [abs_div]
            field_simp
    have h₂ : ‖-(Complex.I * ((2 * π * n / ħ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((2 * π * n * circleRep x : ℝ) : ℂ))‖ =
          2 * π * |(n : ℝ)| * |ħ|⁻¹ := by
      rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, norm_neg, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_two,
        abs_of_pos Real.pi_pos, div_eq_mul_inv]
    have := norm_sub_le ((t⁻¹ : ℝ) • (quasiWave γ n (circleRep x - t / ħ) -
      quasiWave γ n (circleRep x))) (-(Complex.I * ((2 * π * n / ħ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((2 * π * n * circleRep x : ℝ) : ℂ)))
    simp only [G]
    linarith
  have key := tendsto_eLpNorm_of_dominated (μ := μc) (p := 2) (l := 𝓝[≠] (0 : ℝ)) (f := G)
    (F := fun _ => 6 * π * |(n : ℝ)| * |ħ|⁻¹) ENNReal.ofNat_ne_top (.of_forall hmeas)
    (memLp_const _) (.of_forall fun t => .of_forall (hbound t)) ?_
  · refine key.congr' (.of_forall fun t => eLpNorm_congr_ae ?_)
    have hs : slope (fun t => twistedTranslation γ (t / ħ) (fourierDiff n)) 0 t =
        (t⁻¹ : ℝ) • (twistedTranslation γ (t / ħ) (fourierDiff n) -
          twistedTranslation γ (0 / ħ) (fourierDiff n)) := by
      rw [slope_def_module, sub_zero]
    rw [hs]
    filter_upwards [Lp.coeFn_smul (t⁻¹ : ℝ) (twistedTranslation γ (t / ħ) (fourierDiff n) -
        twistedTranslation γ (0 / ħ) (fourierDiff n)),
      Lp.coeFn_sub (twistedTranslation γ (t / ħ) (fourierDiff n))
        (twistedTranslation γ (0 / ħ) (fourierDiff n)),
      twistedTranslation_fourierDiff γ (t / ħ) n, twistedTranslation_fourierDiff γ (0 / ħ) n,
      Lp.coeFn_smul (-(Complex.I * ((2 * π * n / ħ : ℝ) : ℂ))) (fourierLp 2 n),
      coeFn_fourierLp 2 n] with x h₁ h₂ h₃ h₄ h₅ h₆
    simp only [G]
    rw [Pi.sub_apply, h₁, Pi.smul_apply, h₂, Pi.sub_apply, h₃, h₄, fourierDeriv, h₅,
      Pi.smul_apply, h₆, fourier_eq, smul_eq_mul, zero_div, sub_zero]
  · filter_upwards [ae_ne_zero] with x hx
    have hr : circleRep x ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨lt_of_le_of_ne (circleRep_mem x).1 fun h0 => hx ?_, (circleRep_mem x).2⟩
      rw [← coe_circleRep x, ← h0, AddCircle.coe_zero]
    have h := ((hasDerivAt_quasiWave γ ħ n hr).tendsto_slope).sub_const
      (-(Complex.I * ((2 * π * n / ħ : ℝ) : ℂ)) *
        Complex.exp (Complex.I * ((2 * π * n * circleRep x : ℝ) : ℂ)))
    rw [sub_self] at h
    refine h.congr fun t => ?_
    simp only [G, slope_def_module, sub_zero, zero_div]

/-! ### The switched propagator and its generator at `0` -/

/-- `U(t) = U_α(t)` for `t ≥ 0` and `U(t) = U_β(t)` for `t < 0`: the family `U_{0→t}` for
`t ≥ 0` and `U_{t→0}†` for `t < 0` of the Hamiltonian `H(t) = H_β` for `t < 0`, `H_α` for
`t ≥ 0`. -/
def switchedPropagator (ħ α β t : ℝ) : L² →L[ℂ] L² :=
  if 0 ≤ t then twistedTranslation α (t / ħ) else twistedTranslation β (t / ħ)

local notation "U" => switchedPropagator

variable {ħ α β : ℝ}

lemma switchedPropagator_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    U ħ α β t = twistedTranslation α (t / ħ) := by
  simp [switchedPropagator, ht]

lemma switchedPropagator_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    U ħ α β t = twistedTranslation β (t / ħ) := by
  rcases ht.lt_or_eq with h | rfl
  · simp [switchedPropagator, not_le.mpr h]
  · simp [switchedPropagator, twistedTranslation_zero]

theorem switchedPropagator_zero : U ħ α β 0 = 1 := by
  simp [switchedPropagator, twistedTranslation_zero]

theorem switchedPropagator_mem_unitary (t : ℝ) : U ħ α β t ∈ unitary (L² →L[ℂ] L²) := by
  unfold switchedPropagator
  split_ifs <;> exact twistedTranslation_mem_unitary _ _

variable (ħ α β) in
/-- `D`: the vectors `ψ` for which `t ↦ U(t) ψ` is differentiable at `0`. -/
def switchedDomain : Submodule ℂ L² where
  carrier := {ψ | DifferentiableAt ℝ (fun t => U ħ α β t ψ) 0}
  add_mem' {ψ φ} hψ hφ := by
    change DifferentiableAt ℝ (fun t => U ħ α β t (ψ + φ)) 0
    simp only [map_add]
    exact hψ.add hφ
  zero_mem' := by
    change DifferentiableAt ℝ (fun t => U ħ α β t 0) 0
    simp only [map_zero]
    exact differentiableAt_const _
  smul_mem' c ψ hψ := by
    change DifferentiableAt ℝ (fun t => U ħ α β t (c • ψ)) 0
    simp only [map_smul]
    exact hψ.const_smul c

lemma mem_switchedDomain {ψ : L²} :
    ψ ∈ switchedDomain ħ α β ↔ DifferentiableAt ℝ (fun t => U ħ α β t ψ) 0 :=
  Iff.rfl

variable (ħ α β) in
/-- `H₀ ψ = iħ U'(0) ψ` on `D`, the Hamiltonian at `0` that DR-SCEQ would require. -/
def switchedHamiltonian : L² →ₗ.[ℂ] L² where
  domain := switchedDomain ħ α β
  toFun :=
    { toFun := fun ψ => (Complex.I * ħ) • deriv (fun t => U ħ α β t ψ) 0
      map_add' := fun ψ φ => by
        simp only [Submodule.coe_add, map_add]
        rw [deriv_fun_add (mem_switchedDomain.mp ψ.2) (mem_switchedDomain.mp φ.2), smul_add]
      map_smul' := fun c ψ => by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        rw [deriv_fun_const_smul c (mem_switchedDomain.mp ψ.2), smul_comm] }

lemma switchedHamiltonian_apply (ψ : (switchedHamiltonian ħ α β).domain) :
    switchedHamiltonian ħ α β ψ = (Complex.I * ħ) • deriv (fun t => U ħ α β t ψ) 0 :=
  rfl

lemma fourierDiff_mem_switchedDomain (n : ℤ) : fourierDiff n ∈ switchedDomain ħ α β := by
  have h₁ : HasDerivWithinAt (fun t => U ħ α β t (fourierDiff n)) (fourierDeriv ħ n) (Ici 0) 0 :=
    (hasDerivAt_twistedTranslation_fourierDiff α ħ n).hasDerivWithinAt.congr
      (fun t ht => by rw [switchedPropagator_of_nonneg ht])
      (by rw [switchedPropagator_of_nonneg le_rfl])
  have h₂ : HasDerivWithinAt (fun t => U ħ α β t (fourierDiff n)) (fourierDeriv ħ n) (Iic 0) 0 :=
    (hasDerivAt_twistedTranslation_fourierDiff β ħ n).hasDerivWithinAt.congr
      (fun t ht => by rw [switchedPropagator_of_nonpos ht])
      (by rw [switchedPropagator_of_nonpos le_rfl])
  have h := h₂.union h₁
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
  exact h.differentiableAt

/-- **`D` is dense**: it contains `e^{2πinx} - 1` for all `n`, whose span is dense, since a
vector orthogonal to all of them has all Fourier coefficients equal. -/
theorem dense_switchedDomain : Dense (switchedDomain ħ α β : Set L²) := by
  have hS : (Submodule.span ℂ (range fourierDiff))ᗮ = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun φ hφ => ?_
    have h0 : ∀ n, ⟪fourierLp 2 n, φ⟫_ℂ = ⟪fourierLp 2 0, φ⟫_ℂ := fun n => by
      have := (Submodule.mem_orthogonal _ φ).mp hφ (fourierDiff n)
        (Submodule.subset_span ⟨n, rfl⟩)
      rwa [fourierDiff, inner_sub_left, sub_eq_zero] at this
    have hc : ∀ n, fourierBasis.repr φ n = ⟪fourierLp 2 0, φ⟫_ℂ := fun n => by
      rw [fourierBasis.repr_apply_apply, coe_fourierBasis, h0]
    have hsum := (lp.memℓp (fourierBasis.repr φ)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simp only [hc] at hsum
    have hc0 : ⟪fourierLp 2 0, φ⟫_ℂ = 0 := by
      simpa using (summable_const_iff _).mp hsum
    have hr : fourierBasis.repr φ = 0 := by
      ext n
      simp [hc, hc0]
    simpa using hr
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr hS)
  exact hd.mono (Submodule.span_le.mpr (range_subset_iff.mpr fourierDiff_mem_switchedDomain))

/-- **`H₀` is symmetric**, from `⟨U(t) ψ, U(t) φ⟩ = ⟨ψ, φ⟩`. -/
theorem switchedHamiltonian_symm (ψ φ : (switchedHamiltonian ħ α β).domain) :
    ⟪switchedHamiltonian ħ α β ψ, φ⟫_ℂ = ⟪(ψ : L²), switchedHamiltonian ħ α β φ⟫_ℂ := by
  have hA := (mem_switchedDomain.mp ψ.2).hasDerivAt
  have hB := (mem_switchedDomain.mp φ.2).hasDerivAt
  have hconst : (fun t => ⟪U ħ α β t ψ, U ħ α β t φ⟫_ℂ) = fun _ => ⟪(ψ : L²), φ⟫_ℂ :=
    funext fun t => by
      unfold switchedPropagator
      split_ifs <;> exact inner_twistedTranslation _ _ _ _
  have h := hA.inner ℂ hB
  rw [hconst, switchedPropagator_zero, one_apply_eq_self, one_apply_eq_self] at h
  have h0 := h.unique (hasDerivAt_const 0 _)
  rw [switchedHamiltonian_apply, switchedHamiltonian_apply, inner_smul_left, inner_smul_right]
  have hconj : (starRingEnd ℂ) (Complex.I * ħ) = -(Complex.I * ħ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rw [hconj]
  linear_combination (-(Complex.I * ħ)) * h0

/-- The derivative of `t ↦ e^{-iγt/ħ} c` at `0`. -/
lemma hasDerivAt_phase (γ : ℝ) (c : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(Complex.I * ((γ * (t / ħ) : ℝ) : ℂ))) * c)
      (-(Complex.I * ((γ / ħ : ℝ) : ℂ)) * c) 0 := by
  have hd := (((((hasDerivAt_id' (0 : ℝ)).div_const ħ).const_mul γ).ofReal_comp.const_mul
    Complex.I).neg.cexp.mul_const c)
  refine hd.congr_deriv ?_
  simp only [Pi.neg_apply, zero_div, mul_zero, Complex.ofReal_zero, neg_zero, Complex.exp_zero,
    one_mul]
  push_cast
  ring

/-- A derivative within `s` at `0` of `t ↦ e^{-iγt/ħ} c`. -/
lemma eq_of_hasDerivWithinAt_phase {f : ℝ → ℂ} {f' : ℂ} {s : Set ℝ}
    (hs : UniqueDiffWithinAt ℝ s 0) (h0 : (0 : ℝ) ∈ s) (hf : HasDerivWithinAt f f' s 0)
    {γ : ℝ} {c : ℂ} (h : ∀ t ∈ s, f t = Complex.exp (-(Complex.I * ((γ * (t / ħ) : ℝ) : ℂ))) * c) :
    f' = -(Complex.I * ((γ / ħ : ℝ) : ℂ)) * c :=
  hs.eq_deriv _ hf ((hasDerivAt_phase γ c).hasDerivWithinAt.congr (fun t ht => h t ht) (h 0 h0))

lemma inner_planeWave_switchedHamiltonian (hħ : ħ ≠ 0) (ψ : (switchedHamiltonian ħ α β).domain) :
    ⟪planeWave α, switchedHamiltonian ħ α β ψ⟫_ℂ = α * ⟪planeWave α, (ψ : L²)⟫_ℂ := by
  have hA := (mem_switchedDomain.mp ψ.2).hasDerivAt
  have hg : HasDerivAt (fun t => ⟪planeWave α, U ħ α β t ψ⟫_ℂ)
      ⟪planeWave α, deriv (fun t => U ħ α β t ψ) 0⟫_ℂ 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (planeWave α)).inner ℂ hA
  have heq := eq_of_hasDerivWithinAt_phase (uniqueDiffWithinAt_Ici 0) (mem_Ici.mpr le_rfl)
    hg.hasDerivWithinAt (γ := α) (c := ⟪planeWave α, (ψ : L²)⟫_ℂ)
    (fun t ht => by rw [switchedPropagator_of_nonneg ht, inner_planeWave_twistedTranslation])
  rw [switchedHamiltonian_apply, inner_smul_right, heq]
  have : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  push_cast
  field_simp
  linear_combination (-α * ⟪planeWave α, (ψ : L²)⟫_ℂ) * Complex.I_sq

/-- `e^{iαx}` lies in the domain of `H₀†`: `ψ ↦ ⟨e^{iαx}, H₀ ψ⟩ = α ⟨e^{iαx}, ψ⟩` is continuous
on `D`. -/
theorem planeWave_mem_adjoint_domain (hħ : ħ ≠ 0) :
    planeWave α ∈ (switchedHamiltonian ħ α β)†.domain := by
  rw [LinearPMap.mem_adjoint_domain_iff]
  have hc : Continuous fun ψ : (switchedHamiltonian ħ α β).domain =>
      (α : ℂ) * ⟪planeWave α, (ψ : L²)⟫_ℂ :=
    continuous_const.mul (continuous_const.inner continuous_subtype_val)
  refine hc.congr fun ψ => ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, innerₛₗ_apply_apply]
  exact (inner_planeWave_switchedHamiltonian hħ ψ).symm

/-- `e^{iαx}` is not in `D`: against `e^{iβx}`, `U(t) e^{iαx}` has the right derivative
`-iα/ħ ⟨e^{iβx}, e^{iαx}⟩` and the left derivative `-iβ/ħ ⟨e^{iβx}, e^{iαx}⟩`. -/
theorem planeWave_not_mem_switchedDomain (hħ : ħ ≠ 0)
    (h : Complex.exp (Complex.I * α) ≠ Complex.exp (Complex.I * β)) :
    planeWave α ∉ switchedDomain ħ α β := by
  intro hmem
  have hA := (mem_switchedDomain.mp hmem).hasDerivAt
  set c := ⟪planeWave β, planeWave α⟫_ℂ
  have hg : HasDerivAt (fun t => ⟪planeWave β, U ħ α β t (planeWave α)⟫_ℂ)
      ⟪planeWave β, deriv (fun t => U ħ α β t (planeWave α)) 0⟫_ℂ 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (planeWave β)).inner ℂ hA
  have h₁ := eq_of_hasDerivWithinAt_phase (uniqueDiffWithinAt_Ici 0) (mem_Ici.mpr le_rfl)
    hg.hasDerivWithinAt (γ := α) (c := c) (fun t ht => by
      rw [switchedPropagator_of_nonneg ht, twistedTranslation_planeWave, inner_smul_right])
  have h₂ := eq_of_hasDerivWithinAt_phase (uniqueDiffWithinAt_Iic 0) (mem_Iic.mpr le_rfl)
    hg.hasDerivWithinAt (γ := β) (c := c) (fun t ht => by
      rw [switchedPropagator_of_nonpos ht, inner_planeWave_twistedTranslation])
  rw [h₁] at h₂
  have h₃ := mul_left_cancel₀ Complex.I_ne_zero (neg_inj.mp
    (mul_right_cancel₀ (inner_planeWave_planeWave h) h₂))
  have h₄ : α = β := (div_left_inj' hħ).mp (Complex.ofReal_injective h₃)
  exact h (by rw [h₄])

/-- **The derived Hamiltonian is not self-adjoint.** -/
theorem not_isSelfAdjoint_switchedHamiltonian (hħ : ħ ≠ 0)
    (h : Complex.exp (Complex.I * α) ≠ Complex.exp (Complex.I * β)) :
    ¬ IsSelfAdjoint (switchedHamiltonian ħ α β) := by
  intro hsa
  have hmem := planeWave_mem_adjoint_domain (α := α) (β := β) hħ
  rw [LinearPMap.isSelfAdjoint_def.mp hsa] at hmem
  exact planeWave_not_mem_switchedDomain hħ h hmem

/-- **Theorem 2, time-dependent and unbounded: EVDIFF does not give a self-adjoint `H(t₀)`.**
For `e^{iα} ≠ e^{iβ}`, the unitaries `U(t)` (`e^{-itH_α/ħ}` for `t ≥ 0`, `e^{-itH_β/ħ}` for
`t < 0`) satisfy `U(0) = 1`, `t ↦ U(t) ψ` is differentiable at `0` for `ψ` in a dense subspace
`D`, and `H₀ = iħ U'(0)` is symmetric on `D`, but not self-adjoint. -/
theorem switchedHamiltonian_counterexample (hħ : ħ ≠ 0)
    (h : Complex.exp (Complex.I * α) ≠ Complex.exp (Complex.I * β)) :
    (∀ t, U ħ α β t ∈ unitary (L² →L[ℂ] L²)) ∧ U ħ α β 0 = 1 ∧
      Dense ((switchedHamiltonian ħ α β).domain : Set L²) ∧
      (∀ ψ φ : (switchedHamiltonian ħ α β).domain,
        ⟪switchedHamiltonian ħ α β ψ, φ⟫_ℂ = ⟪(ψ : L²), switchedHamiltonian ħ α β φ⟫_ℂ) ∧
      ¬ IsSelfAdjoint (switchedHamiltonian ħ α β) :=
  ⟨switchedPropagator_mem_unitary, switchedPropagator_zero, dense_switchedDomain,
    switchedHamiltonian_symm, not_isSelfAdjoint_switchedHamiltonian hħ h⟩

end UnitaryEntropy
