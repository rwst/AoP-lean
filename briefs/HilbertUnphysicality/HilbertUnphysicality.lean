/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Unphysicality of Hilbert spaces for quantum mechanics.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Theorem 1 of the brief says that the Hilbert-space formulation is inconsistent with three
physical conditions. The conditions are informal; what is checked here is the mathematics
behind each of the three arguments.

[B]COBS (continuity of measurable quantities):
* `not_continuous_of_unbounded`  an unbounded linear map on a normed space is not continuous;
* `numberExp_not_continuousAt`   the oscillator example (from `InconsistentConvergence`).

[B]WDQ (quantities well defined in all frames):
* `bounded_of_isSymmetric`, `not_isSymmetric_of_unbounded`  Hellinger–Toeplitz;
* `frameChange`, `strictMono_frameChange`  the change of coordinates `y(x) = tan(π/2 · erf x)`,
  with `Real.erf` from `ForMathlib`;
* `arctan_frameChange`, `cauchyDensity_frameChange_mul_deriv`  eq. (2), integrated and
  differential form: the Gaussian density `e^{-x²}/√π` becomes the Cauchy density
  `1/(π(1+y²))`;
* `integral_gaussDensity`, `integrable_sq_mul_gaussDensity`  `ψ` is normalized and in the
  domain of `X`;
* `integral_cauchyDensity`, `not_integrable_sq_mul_cauchyDensity`  `ϕ` is normalized and not in
  the domain of `Y`.

[B]STDIST (distinguishability of systems):
* `L2_euclidean_iso`  `L²(ℝⁿ⁺¹) ≃ₗᵢ L²(ℝᵐ⁺¹)` for all `n, m`, from the classification of
  separable Hilbert spaces (`nonempty_linearIsometryEquiv_of_separable`, in `ForMathlib`).
-/
public import ForMathlib.Analysis.InnerProductSpace.l2Space
public import ForMathlib.Analysis.SpecialFunctions.Gaussian.Erf
public import ForMathlib.MeasureTheory.Function.L2Space
public import InconsistentConvergence

open Real MeasureTheory Filter Topology Set

@[expose] public noncomputable section

namespace HilbertUnphysicality

/-! ### [B]COBS: unbounded observables are not continuous -/

/-- On normed spaces, a continuous linear map is bounded; so an unbounded one is not
continuous. -/
theorem not_continuous_of_unbounded {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →ₗ[𝕜] F) (hT : ∀ C : ℝ, ∃ x, C * ‖x‖ < ‖T x‖) : ¬ Continuous T := by
  intro hc
  let L : E →L[𝕜] F := ⟨T, hc⟩
  obtain ⟨x, hx⟩ := hT ‖L‖
  exact absurd (L.le_opNorm x) (not_le.mpr hx)

/-- The brief's example: for the oscillator, `√((j-1)/j)|0⟩ + √(1/j)|j⟩ → |0⟩` while `⟨N⟩`
stays at `1`, so `⟨N⟩` is not continuous at the ground state. -/
theorem numberExp_not_continuousAt :
    ¬ ContinuousAt InconsistentConvergence.numberExp InconsistentConvergence.ground :=
  InconsistentConvergence.not_continuousAt_numberExp

/-! ### [B]WDQ: Hellinger–Toeplitz -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Hellinger–Toeplitz: an everywhere-defined symmetric operator on a Hilbert space is
bounded. -/
theorem bounded_of_isSymmetric {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) :
    ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C * ‖x‖ :=
  ⟨‖(⟨T, hT.continuous⟩ : H →L[ℂ] H)‖, fun x => (⟨T, hT.continuous⟩ : H →L[ℂ] H).le_opNorm x⟩

/-- So an unbounded observable cannot be an everywhere-defined symmetric operator. -/
theorem not_isSymmetric_of_unbounded {T : H →ₗ[ℂ] H} (hT : ∀ C : ℝ, ∃ x, C * ‖x‖ < ‖T x‖) :
    ¬ T.IsSymmetric := fun h => not_continuous_of_unbounded T hT h.continuous

/-! ### [B]WDQ: the change of frame `y = tan(π/2 · erf x)` -/

/-- The change of coordinates `y(x) = tan(π/2 · erf x)` between the two frames. -/
def frameChange (x : ℝ) : ℝ := tan (π / 2 * erf x)

lemma mem_Ioo_erf (x : ℝ) : π / 2 * erf x ∈ Ioo (-(π / 2)) (π / 2) := by
  have h := abs_lt.mp (abs_erf_lt_one x)
  have hπ : 0 < π / 2 := by positivity
  constructor <;> nlinarith [h.1, h.2]

lemma cos_ne_zero_erf (x : ℝ) : cos (π / 2 * erf x) ≠ 0 :=
  (cos_pos_of_mem_Ioo (mem_Ioo_erf x)).ne'

/-- `y` is strictly increasing, so it is a genuine change of coordinates. -/
theorem strictMono_frameChange : StrictMono frameChange := fun a b hab =>
  strictMonoOn_tan (mem_Ioo_erf a) (mem_Ioo_erf b)
    (mul_lt_mul_of_pos_left (strictMono_erf hab) (by positivity))

/-- Eq. (2), integrated: `arctan(y)/π = erf(x)/2`. The Cauchy distribution function at
`y(x)` equals the Gaussian distribution function at `x`. -/
theorem arctan_frameChange (x : ℝ) : arctan (frameChange x) / π = erf x / 2 := by
  rw [frameChange, arctan_tan (mem_Ioo_erf x).1 (mem_Ioo_erf x).2]
  field_simp

/-- The density `|ψ(x)|² = e^{-x²}/√π` of the Gaussian packet. -/
def gaussDensity (x : ℝ) : ℝ := exp (-x ^ 2) / √π

/-- The density `|ϕ(y)|² = 1/(π(1+y²))` of the transformed packet. -/
def cauchyDensity (y : ℝ) : ℝ := 1 / (π * (1 + y ^ 2))

lemma hasDerivAt_frameChange (x : ℝ) :
    HasDerivAt frameChange
      (1 / cos (π / 2 * erf x) ^ 2 * (π / 2 * (2 / √π * exp (-x ^ 2)))) x :=
  (hasDerivAt_tan (cos_ne_zero_erf x)).comp x ((hasDerivAt_erf x).const_mul (π / 2))

/-- Eq. (2), differential form: `|ϕ(y(x))|² y'(x) = |ψ(x)|²`, i.e. the square of the wave
function transforms as a density. -/
theorem cauchyDensity_frameChange_mul_deriv (x : ℝ) :
    cauchyDensity (frameChange x) * deriv frameChange x = gaussDensity x := by
  rw [(hasDerivAt_frameChange x).deriv, cauchyDensity, frameChange, gaussDensity, one_div,
    ← inv_one_add_tan_sq (cos_ne_zero_erf x)]
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  have h1 : 0 < 1 + tan (π / 2 * erf x) ^ 2 := by positivity
  field_simp

/-- `ψ` is normalized: `∫ e^{-x²}/√π = 1`. -/
theorem integral_gaussDensity : ∫ x, gaussDensity x = 1 := by
  have hπ : 0 < √π := sqrt_pos.mpr pi_pos
  simp only [gaussDensity]
  rw [integral_div]
  have := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at this
  rw [this, div_self hπ.ne']

/-- `ψ` is in the domain of the position operator `X`: `∫ x² |ψ|² < ∞`. -/
theorem integrable_sq_mul_gaussDensity : Integrable fun x => x ^ 2 * gaussDensity x := by
  have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := 2) (by norm_num)).div_const
    (√π)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp [gaussDensity, mul_div_assoc]

/-- `ϕ` is normalized: `∫ 1/(π(1+y²)) = 1`. -/
theorem integral_cauchyDensity : ∫ y, cauchyDensity y = 1 := by
  have : (fun y : ℝ => cauchyDensity y) = fun y => (1 + y ^ 2)⁻¹ / π := by
    funext y
    simp [cauchyDensity]
    ring
  rw [this, integral_div, integral_univ_inv_one_add_sq, div_self pi_pos.ne']

/-- `ϕ` is *not* in the domain of the position operator `Y`: `∫ y² |ϕ|² = ∞`. -/
theorem not_integrable_sq_mul_cauchyDensity :
    ¬ Integrable fun y => y ^ 2 * cauchyDensity y := by
  intro h
  have hfin := h.measure_norm_ge_lt_top (ε := 1 / (2 * π)) (by positivity)
  have hsub : Ici (1 : ℝ) ⊆ {y | 1 / (2 * π) ≤ ‖y ^ 2 * cauchyDensity y‖} := by
    intro y hy
    simp only [mem_Ici] at hy
    simp only [mem_ofPred_eq, cauchyDensity, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), show y ^ 2 * (1 / (π * (1 + y ^ 2))) =
      y ^ 2 / (π * (1 + y ^ 2)) by ring, div_le_div_iff₀ (by positivity) (by positivity)]
    have hy2 : 1 ≤ y ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hy2 pi_pos.le]
  have := (measure_mono hsub).trans_lt hfin
  simp at this

/-! ### [B]STDIST: all separable infinite-dimensional Hilbert spaces are isomorphic -/

/-- [B]STDIST: the state spaces `L²(ℝⁿ⁺¹)` and `L²(ℝᵐ⁺¹)` are isometrically isomorphic, for
any numbers of degrees of freedom. -/
theorem L2_euclidean_iso (n m : ℕ) :
    Nonempty (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))) :=
  nonempty_linearIsometryEquiv_of_separable (L2.not_finiteDimensional_euclidean n)
    (L2.not_finiteDimensional_euclidean m)

end HilbertUnphysicality
