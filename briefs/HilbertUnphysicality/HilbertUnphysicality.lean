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

Theorem 5 of the brief says that the Hilbert-space formulation is inconsistent with three
physical conditions. The brief proves four mathematical propositions (Sec. 2) and argues each
part of Theorem 5 from one of them (Sec. 4). The propositions are checked here, and
Theorem 5 is stated and proved as `theorem5`, one conjunct per condition, each in its minimum
form.

Proposition 1 (unbounded self-adjoint operators):
* `not_continuous_of_unbounded`  an unbounded linear map on a normed space, such as `D(A)` with
  the inherited norm, is not continuous;
* `bounded_of_isSymmetric`, `not_isSymmetric_of_unbounded`  Hellinger–Toeplitz, so `D(A) ≠ H`;
* `domain_ne_top_of_unbounded`  the same for a partially defined symmetric operator.

Proposition 2, used for [B]COBS (continuity of measurable quantities):
* `numberDomain`, `expN`  the domain `D(N)` and the expectation `E_N(x) = ⟨x, N x⟩ / ‖x‖²` of
  the number operator;
* `expN_not_continuousWithinAt`, `not_continuousOn_expN`  `E_N` is not continuous at the ground
  state within `D(N) ∖ {0}`, so the minimum form of [B]COBS fails (from
  `InconsistentConvergence`);
* `numberOp`, `isSelfAdjoint_numberOp`, `coe_domain_numberOp`  `N` is the diagonal operator with
  entries `n` on `D(N)` (`lp.diagonal`, in `ForMathlib`), and is self-adjoint;
* `expN_eq_inner`  on `D(N)`, `expN x = Re ⟨x, N x⟩ / ‖x‖²`;
* `exists_lt_norm_numberOp`, `not_continuous_numberOp`  `N` is unbounded, so by Proposition 1
  not continuous on `D(N)`.

Proposition 3, used for [B]WDQ (quantities well defined in all frames):
* `frameChange`, `strictMono_frameChange`  the change of coordinates `y = f(x) = tan(π/2 · erf x)`,
  with `Real.erf` from `ForMathlib`;
* `surjective_frameChange`, `frameIso`, `hasDerivAt_frameIso_symm`  `f` is onto `ℝ`, an order
  isomorphism, and its inverse `g` has a positive derivative;
* `cauchyDensity_frameChange_mul_deriv`, `arctan_frameChange`  `Uψ = ϕ` at the level of
  densities, differential and integrated form: the Gaussian density `e^{-x²}/√π` becomes the
  Cauchy density `1/(π(1+y²))`;
* `integral_gaussDensity`, `integrable_sq_mul_gaussDensity`  `ψ` is normalized and in the
  domain of `X`;
* `integral_cauchyDensity`, `not_integrable_sq_mul_cauchyDensity`  `ϕ` is normalized and not in
  the domain of `Y`;
* `frameUnitary`  the unitary `(Uψ)(y) = ψ(g(y)) √g'(y)` of `L²(ℝ)` (`Lp.compDiffeo`, in
  `ForMathlib`), and `positionDomain`, the maximal domain `{ψ | xψ ∈ L²}` of `X` and of `Y`;
* `gaussState`, `gaussState_mem_positionDomain`, `frameUnitary_gaussState`,
  `frameUnitary_gaussState_not_mem`  `ψ ∈ D(X)`, `Uψ = ϕ` a.e., and `Uψ ∉ D(Y)`;
* `not_forall_frameUnitary_mem_positionDomain`  so the minimum form of [B]WDQ fails.

Proposition 4, used for [B]STDIST (distinguishability of systems):
* `L2_euclidean_iso`  `L²(ℝⁿ⁺¹) ≃ₗᵢ L²(ℝᵐ⁺¹)` for all `n, m`, from the classification of
  separable Hilbert spaces (`nonempty_linearIsometryEquiv_of_separable`, in `ForMathlib`);
* `born`, `CarriesQSTO`, `carriesQSTO`  every unitary induces bijections between rays, density
  operators and self-adjoint operators, and preserves the Born rule and the von Neumann entropy
  (from `ForPhyslib.QuantumMechanics.UnitaryEquivalence`);
* `exists_carriesQSTO`  so `L²(ℝⁿ⁺¹)` and `L²(ℝᵐ⁺¹)` carry the same QSTO:H model.

Theorem 5:
* `theorem5`  the three conjuncts above, for the oscillator, one spatial degree of freedom, and
  any two numbers of continuous degrees of freedom.

Sec. 5, the domain of the Schrödinger equation (an additional remark, not part of Theorem 5):
* `domain_numberOp_ne_top`, `harmonicState_not_mem_numberDomain`  `D(N) ≠ ℓ²`, by
  Hellinger–Toeplitz and by the explicit state `xₙ = 1/n`;
* `numberEvolution`  the oscillator's unitary evolution `e^{-i t N}`, defined on all of `ℓ²`
  (`lp.diagonalEvolution`, in `ForMathlib`);
* `hasDerivAt_numberEvolution`, `not_differentiableAt_numberEvolution`,
  `differentiableAt_numberEvolution_iff`  its orbit solves the Schrödinger equation exactly when
  the initial state lies in `D(N)`, and is differentiable nowhere otherwise;
* `not_memLp_sq_mul_frameUnitary_gaussState`  the potential `V(y) = y²` takes the state
  `ϕ ∈ L²(ℝ)` of Proposition 3 out of `L²`.
-/
public import ForMathlib.Analysis.InnerProductSpace.l2DiagonalEvolution
public import ForMathlib.Analysis.InnerProductSpace.l2Space
public import ForMathlib.Analysis.SpecialFunctions.Gaussian.Erf
public import ForMathlib.MeasureTheory.Function.L2Space
public import ForMathlib.MeasureTheory.Function.LpSpace.ChangeOfVariables
public import ForPhyslib.QuantumMechanics.UnitaryEquivalence
public import Mathlib.Analysis.PSeries
public import InconsistentConvergence

open Real MeasureTheory Filter Topology Set

@[expose] public noncomputable section

namespace HilbertUnphysicality

/-! ### Proposition 1: unbounded self-adjoint operators -/

section Prop1

/-- On normed spaces, a continuous linear map is bounded; so an unbounded one is not
continuous. -/
theorem not_continuous_of_unbounded {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →ₗ[𝕜] F) (hT : ∀ C : ℝ, ∃ x, C * ‖x‖ < ‖T x‖) : ¬ Continuous T := by
  intro hc
  let L : E →L[𝕜] F := ⟨T, hc⟩
  obtain ⟨x, hx⟩ := hT ‖L‖
  exact absurd (L.le_opNorm x) (not_le.mpr hx)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Hellinger–Toeplitz: an everywhere-defined symmetric operator on a Hilbert space is
bounded. -/
theorem bounded_of_isSymmetric {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) :
    ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C * ‖x‖ :=
  ⟨‖(⟨T, hT.continuous⟩ : H →L[ℂ] H)‖, fun x => (⟨T, hT.continuous⟩ : H →L[ℂ] H).le_opNorm x⟩

/-- So an unbounded observable cannot be an everywhere-defined symmetric operator. -/
theorem not_isSymmetric_of_unbounded {T : H →ₗ[ℂ] H} (hT : ∀ C : ℝ, ∃ x, C * ‖x‖ < ‖T x‖) :
    ¬ T.IsSymmetric := fun h => not_continuous_of_unbounded T hT h.continuous

/-- The same for a partially defined operator: a symmetric operator that is unbounded on its
domain is not defined on the whole space. -/
theorem domain_ne_top_of_unbounded {T : H →ₗ.[ℂ] H} (hT : T.IsFormalAdjoint T)
    (hu : ∀ C : ℝ, ∃ x : T.domain, C * ‖(x : H)‖ < ‖T x‖) : T.domain ≠ ⊤ := by
  intro htop
  let e : H ≃ₗ[ℂ] T.domain := (LinearEquiv.ofTop T.domain htop).symm
  have he (x : T.domain) : e x = x := Subtype.ext (by simp [e])
  refine not_isSymmetric_of_unbounded (T := T.toFun ∘ₗ e.toLinearMap) (fun C => ?_)
    fun x y => by simpa [e] using hT (e x) (e y)
  obtain ⟨x, hx⟩ := hu C
  exact ⟨x, by simpa [he] using hx⟩

end Prop1

/-! ### Proposition 2 ([B]COBS): the number operator -/

section COBS

open InconsistentConvergence

/-- The domain `D(N) = {x | ∑ n² |xₙ|² < ∞}` of the number operator on `ℓ²(ℕ)`. -/
def numberDomain : Set H := {x | Summable fun n : ℕ => (n : ℝ) ^ 2 * ‖x n‖ ^ 2}

/-- The expectation `E_N(x) = ⟨x, N x⟩ / ‖x‖²` of the number operator, with
`⟨x, N x⟩ = ∑ n |xₙ|²` on `D(N)`. -/
def expN (x : H) : ℝ := numberExp x / ‖x‖ ^ 2

lemma e_mem_numberDomain (j : ℕ) : e j ∈ numberDomain := by
  refine summable_of_ne_finset_zero (s := {0, j}) fun n hn => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  simp [e_apply_of_ne hn.1 hn.2]

lemma norm_e {j : ℕ} (hj : 1 ≤ j) : ‖e j‖ = 1 := by
  have hj0 : j ≠ 0 := by omega
  have hsq : ‖e j‖ ^ 2 = 1 := by
    rw [norm_sq_eq_tsum, tsum_pair (Ne.symm hj0)]
    · rw [e_apply_zero hj0, e_apply_self hj0, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, ampⱼ_sq, amp₀,
        sq_sqrt (div_nonneg (by simp [hj]) (Nat.cast_nonneg j))]
      have : (j : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    · intro n h0 hn
      simp [e_apply_of_ne h0 hn]
  nlinarith [norm_nonneg (e j)]

lemma ground_mem_numberDomain : ground ∈ numberDomain \ {0} := by
  refine ⟨summable_of_ne_finset_zero (s := ∅) fun n _ => ?_, ?_⟩
  · rcases eq_or_ne n 0 with rfl | hn <;> simp [level_apply, *]
  · intro h
    have := congrArg (fun x : H => x 0) h
    simp [level_apply] at this

/-- Proposition 2: for the oscillator, `xʲ = √((j-1)/j)|0⟩ + √(1/j)|j⟩ → |0⟩` within
`D(N) ∖ {0}`, while `E_N(xʲ) = 1` and `E_N(|0⟩) = 0`. So `E_N` is not continuous at the ground
state for the subspace topology. -/
theorem expN_not_continuousWithinAt :
    ¬ ContinuousWithinAt expN (numberDomain \ {0}) ground := by
  intro h
  have hmem : ∀ᶠ j in atTop, e j ∈ numberDomain \ {0} := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    refine ⟨e_mem_numberDomain j, fun h0 => ?_⟩
    simpa [show e j = 0 from h0] using norm_e hj
  have h0 : Tendsto (expN ∘ e) atTop (𝓝 0) := by
    have := h.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨tendsto_e, hmem⟩)
    simpa only [expN, numberExp_ground, zero_div] using this
  have h1 : Tendsto (expN ∘ e) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    simp [expN, numberExp_e hj, norm_e hj]
  exact zero_ne_one (tendsto_nhds_unique h0 h1)

/-- [B]COBS, minimum form, fails: `E_N` is not continuous on `D(N) ∖ {0}`. -/
theorem not_continuousOn_expN : ¬ ContinuousOn expN (numberDomain \ {0}) :=
  fun h => expN_not_continuousWithinAt (h _ ground_mem_numberDomain)

/-- The number operator `N`: the diagonal operator with entries `n` on its maximal domain. -/
def numberOp : H →ₗ.[ℂ] H := lp.diagonal fun n : ℕ => (n : ℝ)

/-- `N` is self-adjoint, so it is an observable of QSTO:H. -/
theorem isSelfAdjoint_numberOp : IsSelfAdjoint numberOp := lp.isSelfAdjoint_diagonal _

/-- The domain of `N` is `D(N)`. -/
theorem coe_domain_numberOp : (numberOp.domain : Set H) = numberDomain := by
  ext x
  change Memℓp _ 2 ↔ _
  rw [memℓp_gen_iff (by norm_num)]
  simp [numberDomain, mul_pow]

/-- On `D(N)`, `E_N(x) = ⟨x, N x⟩ / ‖x‖²`. -/
theorem expN_eq_inner (x : numberOp.domain) :
    expN x = (inner ℂ (x : H) (numberOp x)).re / ‖(x : H)‖ ^ 2 := by
  rw [expN, numberExp, lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  congr 2 with n
  change _ = (inner ℂ ((x : H) n) (((n : ℝ) : ℂ) * (x : H) n)).re
  rw [RCLike.inner_apply', mul_left_comm, Complex.conj_mul', ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `N` is unbounded on its domain. -/
theorem exists_lt_norm_numberOp (C : ℝ) :
    ∃ x : numberOp.domain, C * ‖(x : H)‖ < ‖numberOp x‖ := by
  refine lp.exists_lt_norm_diagonal _ (fun ⟨b, hb⟩ => ?_) C
  obtain ⟨n, hn⟩ := exists_nat_gt b
  have := hb ⟨n, rfl⟩
  simp only [Nat.abs_cast] at this
  linarith

/-- So, by Proposition 1, `N` is not continuous on `D(N)`. -/
theorem not_continuous_numberOp : ¬ Continuous numberOp.toFun :=
  not_continuous_of_unbounded _ exists_lt_norm_numberOp

end COBS

/-! ### Proposition 3 ([B]WDQ): the change of frame `y = tan(π/2 · erf x)` -/

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

/-- `Uψ = ϕ`, integrated: `arctan(y)/π = erf(x)/2`. The Cauchy distribution function at
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

lemma tendsto_frameChange_atTop : Tendsto frameChange atTop atTop := by
  refine tendsto_tan_pi_div_two.comp (tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩)
  · simpa using (tendsto_erf_atTop.const_mul (π / 2))
  · exact Eventually.of_forall fun x => (mem_Ioo_erf x).2

lemma frameChange_neg (x : ℝ) : frameChange (-x) = -frameChange x := by
  simp [frameChange, erf_neg, tan_neg]

lemma tendsto_frameChange_atBot : Tendsto frameChange atBot atBot := by
  have : frameChange = fun x => -frameChange (-x) := by
    funext x
    simp [frameChange_neg]
  rw [this]
  exact tendsto_neg_atTop_atBot.comp (tendsto_frameChange_atTop.comp tendsto_neg_atBot_atTop)

/-- `y` is onto `ℝ`, so the inverse `g = y⁻¹` is defined everywhere. -/
theorem surjective_frameChange : Function.Surjective frameChange :=
  (continuous_iff_continuousAt.mpr fun x => (hasDerivAt_frameChange x).continuousAt).surjective
    tendsto_frameChange_atTop tendsto_frameChange_atBot

/-- The change of frame as an order isomorphism of `ℝ`; its inverse is `g`. -/
def frameIso : ℝ ≃o ℝ :=
  strictMono_frameChange.orderIsoOfSurjective frameChange surjective_frameChange

lemma deriv_frameChange_pos (x : ℝ) :
    0 < 1 / cos (π / 2 * erf x) ^ 2 * (π / 2 * (2 / √π * exp (-x ^ 2))) :=
  mul_pos (one_div_pos.mpr (pow_pos (cos_pos_of_mem_Ioo (mem_Ioo_erf x)) 2)) (by positivity)

/-- The inverse change of frame `g = y⁻¹` has derivative `g'(y) = 1 / y'(g(y)) > 0`. -/
theorem hasDerivAt_frameIso_symm (y : ℝ) : ∃ g' > 0, HasDerivAt frameIso.symm g' y := by
  set x := frameIso.symm y
  refine ⟨_, inv_pos.mpr (deriv_frameChange_pos x),
    (hasDerivAt_frameChange x).of_local_left_inverse frameIso.symm.continuous.continuousAt
      (deriv_frameChange_pos x).ne' (Eventually.of_forall fun z => ?_)⟩
  exact frameIso.apply_symm_apply z

/-- `Uψ = ϕ` at the level of densities: `|ϕ(y(x))|² y'(x) = |ψ(x)|²`, i.e. the square of the wave
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

/-! #### The unitary between the two frames -/

section WDQ

/-- `L²(ℝ)`, the state space of one spatial degree of freedom, in either frame. -/
abbrev L2R := Lp ℂ 2 (volume : Measure ℝ)

/-- The maximal domain `{ψ | x ψ ∈ L²}` of the position operator. It is the domain of `X` on
`L²(ℝ, dx)` and of `Y` on `L²(ℝ, dy)`. -/
def positionDomain : Set L2R := {ψ | MemLp (fun x : ℝ => (x : ℂ) * ψ x) 2 volume}

lemma differentiable_frameChange : Differentiable ℝ frameChange := fun x =>
  (hasDerivAt_frameChange x).differentiableAt

lemma differentiable_frameIso_symm : Differentiable ℝ frameIso.symm := fun y =>
  (hasDerivAt_frameIso_symm y).elim fun _ h => h.2.differentiableAt

/-- The inverse change of frame `g = y⁻¹`, from the new coordinate to the old one. -/
def frameEquiv : ℝ ≃ ℝ := frameIso.symm.toEquiv

/-- The unitary `(Uψ)(y) = ψ(g(y)) √g'(y)` from `L²(ℝ, dx)` to `L²(ℝ, dy)` (Proposition 3). -/
def frameUnitary : L2R ≃ₗᵢ[ℂ] L2R :=
  Lp.compDiffeo (g := frameEquiv) differentiable_frameIso_symm differentiable_frameChange

lemma coeFn_frameUnitary (ψ : L2R) :
    frameUnitary ψ =ᵐ[volume] fun y => sqrtAbsDeriv frameEquiv y * ψ (frameEquiv y) :=
  Lp.coeFn_compDiffeo _ _ ψ

/-- `|g'(y)| |ψ(g(y))|² = |ϕ(y)|²`: the density identity, read in the new coordinate. -/
lemma abs_deriv_mul_gaussDensity (y : ℝ) :
    |deriv frameEquiv y| * gaussDensity (frameEquiv y) = cauchyDensity y := by
  set x := frameEquiv y
  have h1 : deriv frameChange x * deriv frameEquiv y = 1 :=
    deriv_symm_mul_deriv frameEquiv differentiable_frameIso_symm differentiable_frameChange y
  have hx : frameChange x = y := frameIso.apply_symm_apply y
  have hpos : 0 < deriv frameChange x :=
    (hasDerivAt_frameChange x).deriv ▸ deriv_frameChange_pos x
  have hg : 0 < deriv frameEquiv y := pos_of_mul_pos_right (h1 ▸ one_pos) hpos.le
  rw [abs_of_pos hg, ← cauchyDensity_frameChange_mul_deriv x, hx,
    show deriv frameEquiv y * (cauchyDensity y * deriv frameChange x) =
      cauchyDensity y * (deriv frameChange x * deriv frameEquiv y) by ring, h1, mul_one]

lemma measurable_gaussDensity : Measurable gaussDensity := by
  unfold gaussDensity
  fun_prop

lemma measurable_cauchyDensity : Measurable cauchyDensity := by
  unfold cauchyDensity
  fun_prop

/-- The Gaussian packet `ψ(x) = (e^{-x²}/√π)^{1/2}`. -/
def gaussFun (x : ℝ) : ℂ := (√(gaussDensity x) : ℝ)

/-- The transformed packet `ϕ(y) = (1/(π(1+y²)))^{1/2}`. -/
def cauchyFun (y : ℝ) : ℂ := (√(cauchyDensity y) : ℝ)

lemma norm_sq_ofReal_sqrt {a : ℝ} (ha : 0 ≤ a) : ‖((√a : ℝ) : ℂ)‖ ^ 2 = a := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt ha]

/-- Membership in the domain of the position operator: `xψ ∈ L²` iff `∫ x² |ψ|² < ∞`. -/
lemma memLp_mul_iff {ψ : ℝ → ℂ} (hψ : AEStronglyMeasurable ψ volume) :
    MemLp (fun x : ℝ => (x : ℂ) * ψ x) 2 volume ↔
      Integrable fun x => x ^ 2 * ‖ψ x‖ ^ 2 := by
  rw [memLp_two_iff_integrable_sq_norm (f := fun x : ℝ => (x : ℂ) * ψ x)
    ((Complex.continuous_ofReal.aestronglyMeasurable).mul hψ)]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

lemma memLp_gaussFun : MemLp gaussFun 2 volume := by
  have hm : AEStronglyMeasurable gaussFun volume := by
    unfold gaussFun
    exact (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp measurable_gaussDensity)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hi : Integrable gaussDensity :=
    Integrable.of_integral_ne_zero (by simp [integral_gaussDensity])
  refine hi.congr (ae_of_all _ fun x => ?_)
  simp only [gaussFun]
  rw [norm_sq_ofReal_sqrt (by unfold gaussDensity; positivity)]

/-- The Gaussian state `ψ ∈ L²(ℝ, dx)`. -/
def gaussState : L2R := memLp_gaussFun.toLp gaussFun

/-- `ψ ∈ D(X)`. -/
theorem gaussState_mem_positionDomain : gaussState ∈ positionDomain := by
  have h : (fun x : ℝ => (x : ℂ) * gaussState x) =ᵐ[volume] fun x => (x : ℂ) * gaussFun x := by
    filter_upwards [memLp_gaussFun.coeFn_toLp] with x hx
    rw [gaussState, hx]
  rw [positionDomain, mem_ofPred_eq, memLp_congr_ae h,
    memLp_mul_iff memLp_gaussFun.aestronglyMeasurable]
  refine integrable_sq_mul_gaussDensity.congr (ae_of_all _ fun x => ?_)
  simp only [gaussFun]
  rw [norm_sq_ofReal_sqrt (by unfold gaussDensity; positivity)]

/-- `Uψ = ϕ`: the frame change takes the Gaussian packet to the Cauchy packet. -/
theorem frameUnitary_gaussState : frameUnitary gaussState =ᵐ[volume] cauchyFun := by
  have hq := quasiMeasurePreserving_of_differentiable_symm frameEquiv
    differentiable_frameIso_symm.continuous differentiable_frameChange
  filter_upwards [coeFn_frameUnitary gaussState,
    hq.ae_eq_comp memLp_gaussFun.coeFn_toLp] with y h1 h2
  rw [h1, show gaussState (frameEquiv y) = gaussFun (frameEquiv y) from h2, sqrtAbsDeriv,
    gaussFun, cauchyFun, ← abs_deriv_mul_gaussDensity y, Real.sqrt_mul (abs_nonneg _)]
  simp

/-- `Uψ ∉ D(Y)`. -/
theorem frameUnitary_gaussState_not_mem : frameUnitary gaussState ∉ positionDomain := by
  intro h
  have hm : AEStronglyMeasurable cauchyFun volume := by
    unfold cauchyFun
    exact (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp measurable_cauchyDensity)).aestronglyMeasurable
  have h' : (fun y : ℝ => (y : ℂ) * frameUnitary gaussState y) =ᵐ[volume]
      fun y => (y : ℂ) * cauchyFun y := by
    filter_upwards [frameUnitary_gaussState] with y hy
    rw [hy]
  rw [positionDomain, mem_ofPred_eq, memLp_congr_ae h', memLp_mul_iff hm] at h
  refine not_integrable_sq_mul_cauchyDensity (h.congr (ae_of_all _ fun y => ?_))
  simp only [cauchyFun]
  rw [norm_sq_ofReal_sqrt (by unfold cauchyDensity; positivity)]

/-- [B]WDQ, minimum form, fails: for this change of frame, `ψ ∈ D(X)` does not imply
`Uψ ∈ D(Y)`. -/
theorem not_forall_frameUnitary_mem_positionDomain :
    ¬ ∀ ψ ∈ positionDomain, frameUnitary ψ ∈ positionDomain :=
  fun h => frameUnitary_gaussState_not_mem (h _ gaussState_mem_positionDomain)

end WDQ

/-! ### Proposition 4 ([B]STDIST): all separable infinite-dimensional Hilbert spaces are
isomorphic -/

/-- [B]STDIST: the state spaces `L²(ℝⁿ⁺¹)` and `L²(ℝᵐ⁺¹)` are isometrically isomorphic, for
any numbers of degrees of freedom. -/
theorem L2_euclidean_iso (n m : ℕ) :
    Nonempty (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (m + 1))))) :=
  nonempty_linearIsometryEquiv_of_separable (L2.not_finiteDimensional_euclidean n)
    (L2.not_finiteDimensional_euclidean m)

/-- The Born rule `p(ψ|ϕ) = ⟨ϕ|ψ⟩⟨ψ|ϕ⟩ / (⟨ψ|ψ⟩⟨ϕ|ϕ⟩)` of QSTO:H. -/
def born {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (ψ ϕ : E) : ℝ :=
  ‖inner ℂ ψ ϕ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖ϕ‖ ^ 2)

/-- A unitary preserves the Born rule. -/
lemma born_map {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (e : E ≃ₗᵢ[ℂ] F) (ψ ϕ : E) :
    born (e ψ) (e ϕ) = born ψ ϕ := by
  simp [born]

section STDIST

open QuantumMechanics

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The QSTO:H model on `E` is carried onto the one on `F` by `e`: `e` induces bijections between
the rays, the density operators (`ρ ↦ e ρ e⁻¹`) and the self-adjoint operators (`T ↦ e T e⁻¹`),
and it preserves the Born rule and the von Neumann entropy. -/
def CarriesQSTO (e : E ≃ₗᵢ[ℂ] F) : Prop :=
  Function.Bijective (mapRays e) ∧
  (∀ ψ ϕ, born (e ψ) (e ϕ) = born ψ ϕ) ∧
  Function.Bijective e.conjStarAlgEquiv ∧
  (∀ ρ, IsDensityOperator (e.conjStarAlgEquiv ρ) ↔ IsDensityOperator ρ) ∧
  (∀ ρ, IsDensityOperator ρ → vonNeumannEntropy (e.conjStarAlgEquiv ρ) = vonNeumannEntropy ρ) ∧
  Function.Bijective (conjLinearPMap e) ∧
  (∀ T, IsSelfAdjoint (conjLinearPMap e T) ↔ IsSelfAdjoint T)

/-- Every unitary carries the QSTO:H model. -/
theorem carriesQSTO (e : E ≃ₗᵢ[ℂ] F) : CarriesQSTO e :=
  ⟨(mapRays e).bijective, born_map e, e.conjStarAlgEquiv.bijective,
    fun _ => isDensityOperator_conjStarAlgEquiv_iff,
    fun _ hρ => hρ.vonNeumannEntropy_conjStarAlgEquiv, bijective_conjLinearPMap,
    fun _ => isSelfAdjoint_conjLinearPMap_iff⟩

end STDIST

/-- [B]STDIST: for any numbers `n + 1`, `m + 1` of degrees of freedom there is a unitary
`L²(ℝⁿ⁺¹) → L²(ℝᵐ⁺¹)`, and it carries the whole QSTO:H model. -/
theorem exists_carriesQSTO (n m : ℕ) :
    ∃ e : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))), CarriesQSTO e :=
  (L2_euclidean_iso n m).elim fun e => ⟨e, carriesQSTO e⟩

/-! ### Theorem 5 -/

open InconsistentConvergence in
/-- **Theorem 5.** QSTO:H is inconsistent with [B]COBS, [B]WDQ and [B]STDIST: for each
condition, a system to which QSTO:H applies fails its minimum form.
* [B]COBS, the harmonic oscillator: the number operator `N` is self-adjoint on `D(N)`, and the
  expectation `E_N(x) = ⟨x, N x⟩ / ‖x‖²` is not continuous on `D(N) ∖ {0}`;
* [B]WDQ, one spatial degree of freedom: the change of frame `U` takes the Gaussian packet `ψ`,
  which lies in the domain of `X`, to the Cauchy packet `ϕ`, which does not lie in the domain
  of `Y`;
* [B]STDIST, `n + 1` and `m + 1` continuous degrees of freedom: there is a unitary
  `L²(ℝⁿ⁺¹) → L²(ℝᵐ⁺¹)`, and it carries the whole QSTO:H model. -/
theorem theorem5 :
    (IsSelfAdjoint numberOp ∧ (numberOp.domain : Set H) = numberDomain ∧
      (∀ x : numberOp.domain, expN x = (inner ℂ (x : H) (numberOp x)).re / ‖(x : H)‖ ^ 2) ∧
      ¬ ContinuousOn expN (numberDomain \ {0})) ∧
    (gaussState ∈ positionDomain ∧ frameUnitary gaussState =ᵐ[volume] cauchyFun ∧
      frameUnitary gaussState ∉ positionDomain) ∧
    (∀ n m : ℕ, ∃ e : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))), CarriesQSTO e) :=
  ⟨⟨isSelfAdjoint_numberOp, coe_domain_numberOp, expN_eq_inner, not_continuousOn_expN⟩,
    ⟨gaussState_mem_positionDomain, frameUnitary_gaussState, frameUnitary_gaussState_not_mem⟩,
    exists_carriesQSTO⟩

/-! ### Sec. 5: the domain of the Schrödinger equation -/

section Schrodinger

open InconsistentConvergence

/-- `N` is not defined on the whole of `ℓ²`, by Hellinger–Toeplitz. -/
theorem domain_numberOp_ne_top : numberOp.domain ≠ ⊤ := by
  have hd : Dense (numberOp.domain : Set H) := lp.dense_diagonalDomain _
  have hT : numberOp.IsFormalAdjoint numberOp := by
    have h := LinearPMap.adjoint_isFormalAdjoint hd
    rwa [LinearPMap.isSelfAdjoint_def.mp isSelfAdjoint_numberOp] at h
  exact domain_ne_top_of_unbounded hT exists_lt_norm_numberOp

/-- An explicit state outside `D(N)`: `xₙ = 1/n` for `n ≥ 1`, with `x₀ = 0`. -/
def harmonicState : H :=
  ⟨fun n : ℕ => Complex.ofReal (n : ℝ)⁻¹, by
    change Memℓp (fun n : ℕ => Complex.ofReal (n : ℝ)⁻¹) 2
    rw [memℓp_gen_iff (by norm_num)]
    simp⟩

theorem harmonicState_not_mem_numberDomain : harmonicState ∉ numberDomain := by
  intro h
  have h1 := h.tendsto_atTop_zero
  refine one_ne_zero (tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) h1)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  change 1 = (n : ℝ) ^ 2 * ‖Complex.ofReal (n : ℝ)⁻¹‖ ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp

/-- The oscillator's unitary evolution `U t = e^{-i t N}` on `ℓ²`, in units with `ħω = 1` and
without the zero-point energy, which only adds a global phase. It is defined on all of `ℓ²`. -/
def numberEvolution (t : ℝ) : H ≃ₗᵢ[ℂ] H := lp.diagonalEvolution (fun n : ℕ => (n : ℝ)) t

/-- On `D(N)`, the orbit of `x` solves the Schrödinger equation `i d/dt (U t x) = N (U t x)`. -/
theorem hasDerivAt_numberEvolution {x : H} (hx : x ∈ numberOp.domain) (t : ℝ) :
    HasDerivAt (fun s => numberEvolution s x)
      (-(Complex.I • numberOp ⟨numberEvolution t x,
        (lp.diagonalEvolution_mem_diagonalDomain_iff _ t).2 hx⟩)) t :=
  lp.hasDerivAt_diagonalEvolution _ hx t

/-- Off `D(N)`, the orbit is differentiable nowhere, so the Schrödinger equation fails at every
time. -/
theorem not_differentiableAt_numberEvolution {x : H} (hx : x ∉ numberOp.domain) (t : ℝ) :
    ¬ DifferentiableAt ℝ (fun s => numberEvolution s x) t :=
  lp.not_differentiableAt_diagonalEvolution _ hx t

/-- The Schrödinger equation holds along the orbit of `x` exactly on the domain of `N`. -/
theorem differentiableAt_numberEvolution_iff {x : H} (t : ℝ) :
    DifferentiableAt ℝ (fun s => numberEvolution s x) t ↔ x ∈ numberOp.domain :=
  lp.differentiableAt_diagonalEvolution_iff _ t

/-- The potential `V(y) = y²` of the oscillator, up to constants, does not map `L²` into
itself: `ϕ = Uψ` is in `L²`, but `Vϕ` is not. For the linear potential `V(y) = y` this is
`frameUnitary_gaussState_not_mem`. -/
theorem not_memLp_sq_mul_frameUnitary_gaussState :
    ¬ MemLp (fun y : ℝ => (y : ℂ) ^ 2 * frameUnitary gaussState y) 2 volume := by
  intro h
  apply frameUnitary_gaussState_not_mem
  set ϕ := frameUnitary gaussState
  have hg : MemLp (fun y => ‖ϕ y‖ + ‖(y : ℂ) ^ 2 * ϕ y‖) 2 volume :=
    (Lp.memLp ϕ).norm.add h.norm
  show MemLp (fun y : ℝ => (y : ℂ) * ϕ y) 2 volume
  refine hg.of_le (Complex.continuous_ofReal.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable ϕ)) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs]
  have : |y| ≤ 1 + |y| ^ 2 := by nlinarith [abs_nonneg y]
  nlinarith [norm_nonneg (ϕ y)]

end Schrodinger

end HilbertUnphysicality
