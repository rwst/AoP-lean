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
* `positionOp`, `isSelfAdjoint_positionOp`  `X` and `Y` are multiplication by the coordinate on
  `positionDomain`, and self-adjoint (`L2.isSelfAdjoint_mulOp`, in `ForMathlib`);
* `conjLinearPMap_frameUnitary_positionOp`  `U X U⁻¹` is multiplication by `g(y)` on `U D(X)`
  (`Lp.compDiffeo_mulOp`, in `ForMathlib`);
* `isSelfAdjoint_conjLinearPMap_frameUnitary_positionOp`  it is self-adjoint;
* `conjLinearPMap_frameUnitary_positionOp_ne`  and it is not `Y`: `Uψ ∈ U D(X)`, `Uψ ∉ D(Y)`.

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
* `schrodinger_only_on_domain`  the same for every self-adjoint Hamiltonian that is unbounded on
  its domain, with the evolution `e^{-itH/ħ}` of Stone's theorem (`schrodingerPropagator`, in
  `ForPhyslib`), whatever the potential;
* `numberEvolution_eq_schrodingerPropagator`  `numberEvolution` is that evolution for `N`;
* `not_memLp_sq_mul_frameUnitary_gaussState`  the potential `V(y) = y²` takes the state
  `ϕ ∈ L²(ℝ)` of Proposition 3 out of `L²`.

Sec. 5 in position space, on `L²(ℝ)` with Mathlib's Fourier transform `fourierL2`:
* `momentumOp`, `mem_domain_momentumOp`  `P = 𝓕⁻¹ (2πξ) 𝓕` on `D(P) = {ψ | ξ 𝓕ψ ∈ L²}`;
* `isSelfAdjoint_momentumOp`, `isSelfAdjoint_freeHamiltonian`  `P` and `H₀` are self-adjoint;
* `roughState_not_mem_domain_momentumOp`, `domain_momentumOp_ne_top`  `𝓕⁻¹ ϕ ∉ D(P)`;
* `mem_domain_momentumOp_iff_memSobolev`, `roughState_not_memSobolev`  `D(P) = H¹(ℝ)`, so
  `𝓕⁻¹ ϕ` is not in `H¹`;
* `freeHamiltonian`, `freeEvolution`  `H₀ = P²/2 = 𝓕⁻¹ (2π²ξ²) 𝓕` and `e^{-itH₀}`, defined on
  all of `L²(ℝ)` (`L2.mulOp`, `L2.mulEvolution`, in `ForMathlib`);
* `hasDerivAt_freeEvolution`, `not_differentiableAt_freeEvolution`,
  `differentiableAt_freeEvolution_iff`  its orbit solves the free Schrödinger equation exactly
  when the initial state lies in `D(H₀)`, and is differentiable nowhere otherwise;
* `freeEvolution_eq_schrodingerPropagator`  `freeEvolution` is the evolution of Stone's theorem
  for `H₀`.

Sec. 5, the harmonic oscillator in position space (`m = ω = ħ = 1`), with the Hermite functions
`ψₙ` and their Hilbert basis of `L²(ℝ)` from TauCeti (`TauCeti.hermiteHilbertBasis`):
* `hermiteUnitary`, `oscillatorHamiltonian`  `H = P²/2 + X²/2` as the operator that is diagonal
  in the Hermite basis with entries `n + 1/2`;
* `isSelfAdjoint_oscillatorHamiltonian`, `oscillatorHamiltonian_hermiteFunctionLp`  `H` is
  self-adjoint, with the eigenvectors `ψₙ` and eigenvalues `n + 1/2`;
* `oscillatorHamiltonian_hermiteFunctionLp_ae`  `H ψₙ = (-ψₙ'' + x²ψₙ)/2` point by point;
* `eq_oscillatorHamiltonian`  `H` is the only self-adjoint operator with these eigenvectors and
  eigenvalues (`lp.eq_diagonal`, in `ForMathlib`);
* `exists_lt_norm_oscillatorHamiltonian`, `oscillator_schrodinger_only_on_domain`  `H` is
  unbounded, so with the potential `V(x) = x²/2` the Schrödinger equation holds only on
  `D(H) ≠ L²(ℝ)`.

Sec. 5, commutator relations (`ħ = 1` on `L²(ℝ)`):
* `not_exists_ccr_bounded`, `not_exists_ccr_symmetric`  `[X, P] = iħ` has no solution in
  bounded operators (Wielandt–Wintner, `commutator_ne_algebraMap` in `ForMathlib`), nor, by
  Hellinger–Toeplitz, in everywhere-defined symmetric ones;
* `commutatorXP`  `[X, P] = X P - P X` on its natural domain
  (`LinearPMap.compMax`, in `ForMathlib`);
* `domain_commutatorXP_ne_top`  `[X, P]` is not defined on all of `L²(ℝ)`;
* `positionOp_toTemperedDistribution`, `momentumOp_toTemperedDistribution`  in `𝓢'(ℝ)`, `X` is
  multiplication by `x` and `P = -i d/dx`;
* `commutatorXP_apply`  `[X, P] ψ = iψ` for every `ψ ∈ D([X, P])`, from the Leibniz rule in `𝓢'`
  (`TemperedDistribution.lineDerivOp_smulLeftCLM`, in `ForMathlib`);
* `toLp_mem_domain_commutatorXP`, `dense_domain_commutatorXP`  Schwartz functions lie in
  `D([X, P])`, so it is dense;
* `commutator_relations`  the above together.

Sec. 5, point-wise values (on `L²(ℝ)`):
* `exists_representative_apply_eq`, `exists_representatives_ne`  a vector `ψ` of `L²(ℝ)` has
  representatives with any prescribed value at any point, so two of them differ there
  (`MeasureTheory.update_ae_eq`, in `ForMathlib`);
* `exists_representative_density_eq`  so the density `|ψ(x)|²` takes any value `r ≥ 0` at `x`;
* `not_exists_continuous_eval`  even on Schwartz functions, `φ ↦ φ(x₀)` is not the restriction
  of a continuous linear functional on `L²(ℝ)`, so no choice of point values is continuous in `ψ`;
* `pointwise_values`  the above together.
-/
public import ForMathlib.Analysis.Distribution.TemperedDistribution
public import ForMathlib.Analysis.Normed.Algebra.Wielandt
public import ForMathlib.LinearAlgebra.LinearPMap
public import ForMathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Analysis.Distribution.Sobolev
public import ForMathlib.Analysis.InnerProductSpace.l2Space
public import ForMathlib.Analysis.SpecialFunctions.Gaussian.Erf
public import ForMathlib.MeasureTheory.Function.L2Space
public import ForMathlib.MeasureTheory.Function.LpSpace.ChangeOfVariables
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.HilbertBasis
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Oscillator
public import ForPhyslib.QuantumMechanics.Stone
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

omit [CompleteSpace H] in
/-- Sec. 5: the canonical commutation relation `[X, P] = iħ` has no solution in bounded
operators on a nonzero space (Wielandt–Wintner, in `ForMathlib`). -/
theorem not_exists_ccr_bounded [Nontrivial H] {ħ : ℝ} (hħ : ħ ≠ 0) :
    ¬ ∃ X P : H →L[ℂ] H, X * P - P * X = (Complex.I * ħ) • 1 := by
  rintro ⟨X, P, h⟩
  refine commutator_ne_algebraMap X P (c := Complex.I * ħ) (by simp [hħ]) ?_
  rw [h, Algebra.algebraMap_eq_smul_one]

/-- So, by Hellinger–Toeplitz, no everywhere-defined symmetric `X` and `P` satisfy it either:
the relation cannot hold on the whole of the Hilbert space. -/
theorem not_exists_ccr_symmetric [Nontrivial H] {ħ : ℝ} (hħ : ħ ≠ 0) :
    ¬ ∃ X P : H →ₗ[ℂ] H, X.IsSymmetric ∧ P.IsSymmetric ∧
      X ∘ₗ P - P ∘ₗ X = (Complex.I * ħ) • LinearMap.id := by
  rintro ⟨X, P, hX, hP, h⟩
  refine not_exists_ccr_bounded hħ ⟨⟨X, hX.continuous⟩, ⟨P, hP.continuous⟩, ?_⟩
  ext x
  exact LinearMap.congr_fun h x

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

/-! The position operators. `X` on `L²(ℝ, dx)` and `Y` on `L²(ℝ, dy)` are both multiplication by
the coordinate on `positionDomain`, while `U X U⁻¹` is multiplication by `g(y)` on `U D(X)`. -/

section PositionOperators

open QuantumMechanics

/-- The position operator `X`, multiplication by `x`, on its maximal domain. In the coordinate
`y` it is `Y`. -/
def positionOp : L2R →ₗ.[ℂ] L2R := L2.mulOp fun x : ℝ => x

theorem coe_domain_positionOp : (positionOp.domain : Set L2R) = positionDomain := rfl

lemma coeFn_positionOp (ψ : positionOp.domain) :
    positionOp ψ =ᵐ[volume] fun x => (x : ℂ) * (ψ : L2R) x :=
  L2.coeFn_mulOp _ ψ

/-- `X` and `Y` are self-adjoint on `positionDomain`. -/
theorem isSelfAdjoint_positionOp : IsSelfAdjoint positionOp :=
  L2.isSelfAdjoint_mulOp measurable_id

/-- `U X U⁻¹` is multiplication by `g(y)`, with domain `U D(X)` (Proposition 3). -/
theorem conjLinearPMap_frameUnitary_positionOp :
    conjLinearPMap frameUnitary positionOp = L2.mulOp fun y => frameEquiv y := by
  have hmem (ψ : L2R) :
      frameUnitary ψ ∈ L2.mulDomain (fun y => frameEquiv y) ↔ ψ ∈ positionOp.domain :=
    Lp.compDiffeo_mem_mulDomain_iff (a := fun x : ℝ => x) differentiable_frameIso_symm
      differentiable_frameChange measurable_id
  refine LinearPMap.ext (Submodule.ext fun ψ => ?_) fun ψ _ _ => ?_
  · rw [mem_domain_conjLinearPMap, ← hmem, LinearIsometryEquiv.apply_symm_apply]
    rfl
  · rw [conjLinearPMap_apply]
    refine (Lp.compDiffeo_mulOp (a := fun x : ℝ => x) differentiable_frameIso_symm
      differentiable_frameChange measurable_id _).trans ?_
    congr 1
    exact Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)

/-- `U X U⁻¹` is self-adjoint on `U D(X)`. -/
theorem isSelfAdjoint_conjLinearPMap_frameUnitary_positionOp :
    IsSelfAdjoint (conjLinearPMap frameUnitary positionOp) :=
  isSelfAdjoint_positionOp.conjLinearPMap

/-- `U X U⁻¹` is not `Y`: `Uψ` lies in `U D(X)` but not in `D(Y)`. -/
theorem conjLinearPMap_frameUnitary_positionOp_ne :
    conjLinearPMap frameUnitary positionOp ≠ positionOp := by
  intro h
  have hm : frameUnitary gaussState ∈ (conjLinearPMap frameUnitary positionOp).domain := by
    rw [mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_apply_apply]
    exact gaussState_mem_positionDomain
  rw [h] at hm
  exact frameUnitary_gaussState_not_mem hm

end PositionOperators

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

open InconsistentConvergence QuantumMechanics

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

/-- `numberEvolution` is the propagator `e^{-itN}` that Stone's theorem gives for `N`
(`schrodingerPropagator`, in `ForPhyslib`), with `ħ = 1`. -/
theorem numberEvolution_eq_schrodingerPropagator (t : ℝ) :
    ((numberEvolution t).toContinuousLinearEquiv : H →L[ℂ] H) =
      schrodingerPropagator one_ne_zero isSelfAdjoint_numberOp t := by
  refine SolvesSchrodinger.eq_schrodingerPropagator (U := fun t =>
    ((numberEvolution t).toContinuousLinearEquiv : H →L[ℂ] H)) (fun ψ s => ?_) one_ne_zero
    isSelfAdjoint_numberOp (ContinuousLinearMap.ext fun x => by simp [numberEvolution]) t
  refine ⟨(lp.diagonalEvolution_mem_diagonalDomain_iff _ s).2 ψ.2, ?_⟩
  rw [Complex.ofReal_one, mul_one, Complex.inv_I, neg_smul]
  exact hasDerivAt_numberEvolution ψ.2 s

/-- The remark for every Hamiltonian, with Stone's theorem (`schrodingerPropagator`, in
`ForPhyslib`): if `T` is self-adjoint and unbounded on its domain, then `D(T)` is not the whole
space; the evolution `e^{-itT/ħ}` is defined on the whole space, its orbits solve the
Schrödinger equation on `D(T)`, and off `D(T)` they are differentiable at no time. -/
theorem schrodinger_only_on_domain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ħ : ℝ} (hħ : ħ ≠ 0) {T : E →ₗ.[ℂ] E} (hT : IsSelfAdjoint T)
    (hu : ∀ C : ℝ, ∃ x : T.domain, C * ‖(x : E)‖ < ‖T x‖) :
    T.domain ≠ ⊤ ∧ SolvesSchrodinger ħ T (schrodingerPropagator hħ hT) ∧
      ∀ ψ ∉ T.domain, ∀ t, ¬ DifferentiableAt ℝ (fun s => schrodingerPropagator hħ hT s ψ) t := by
  refine ⟨domain_ne_top_of_unbounded ?_ hu, solvesSchrodinger_schrodingerPropagator hħ hT,
    fun ψ hψ t hd => hψ ((differentiableAt_schrodingerPropagator_iff hħ hT ψ t).1 hd)⟩
  have h := LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.mp hT] at h

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

/-! ### Sec. 5 in position space: the momentum operator and the free particle -/

section PositionSpace

open QuantumMechanics FourierTransform
open scoped SchwartzMap

/-- The Fourier transform, a unitary of `L²(ℝ)` (Plancherel), with Mathlib's convention
`𝓕ψ(ξ) = ∫ e^{-2πixξ} ψ(x) dx`. -/
abbrev fourierL2 : L2R ≃ₗᵢ[ℂ] L2R := Lp.fourierTransformₗᵢ ℝ ℂ

/-- The momentum operator `P = -i d/dx` (`ħ = 1`) on its maximal domain. The Fourier transform
takes `d/dx` to multiplication by `2πiξ`, so `P = 𝓕⁻¹ (2πξ) 𝓕`. -/
def momentumOp : L2R →ₗ.[ℂ] L2R :=
  conjLinearPMap fourierL2.symm (L2.mulOp fun ξ : ℝ => 2 * π * ξ)

/-- `ψ ∈ D(P)` iff `ξ 𝓕ψ ∈ L²`, that is, iff `𝓕ψ` lies in the domain of the position
operator. -/
theorem mem_domain_momentumOp {ψ : L2R} :
    ψ ∈ momentumOp.domain ↔ fourierL2 ψ ∈ positionDomain := by
  rw [momentumOp, mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_symm, L2.domain_mulOp,
    L2.mem_mulDomain]
  change _ ↔ MemLp (fun ξ : ℝ => (ξ : ℂ) * fourierL2 ψ ξ) 2 volume
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  constructor
  · intro h
    refine (h.const_mul (2 * π : ℂ)⁻¹).ae_eq (ae_of_all _ fun ξ => ?_)
    push_cast
    field_simp
  · intro h
    refine (h.const_mul (2 * π : ℂ)).ae_eq (ae_of_all _ fun ξ => ?_)
    push_cast
    ring

/-- A state outside `D(P)`: `𝓕⁻¹ ϕ` for the Cauchy packet `ϕ` of Proposition 3. -/
def roughState : L2R := fourierL2.symm (frameUnitary gaussState)

theorem roughState_not_mem_domain_momentumOp : roughState ∉ momentumOp.domain := by
  rw [mem_domain_momentumOp, roughState, LinearIsometryEquiv.apply_symm_apply]
  exact frameUnitary_gaussState_not_mem

/-- So `P` is not defined on the whole of `L²(ℝ)`. -/
theorem domain_momentumOp_ne_top : momentumOp.domain ≠ ⊤ := fun h =>
  roughState_not_mem_domain_momentumOp (h ▸ Submodule.mem_top)

/-- `P` is self-adjoint: it is unitarily equivalent to multiplication by `2πξ`. -/
theorem isSelfAdjoint_momentumOp : IsSelfAdjoint momentumOp :=
  (L2.isSelfAdjoint_mulOp (by fun_prop)).conjLinearPMap

open TemperedDistribution in
/-- `D(P)` is the Sobolev space `H¹(ℝ)`, which Mathlib defines through the Fourier transform
(`MemSobolev 1 2`, of the `L²` function as a tempered distribution). So `roughState` is a
vector of `L²(ℝ)` outside `H¹`, on which `P` is not defined. -/
theorem mem_domain_momentumOp_iff_memSobolev {ψ : L2R} :
    ψ ∈ momentumOp.domain ↔ MemSobolev 1 2 (ψ : 𝓢'(ℝ, ℂ)) := by
  rw [mem_domain_momentumOp, memSobolev_iff_exists_smulLeftCLM_fourier,
    Lp.fourier_toTemperedDistribution_eq]
  set g : L2R := 𝓕 ψ
  change MemLp (fun ξ : ℝ => (ξ : ℂ) * g ξ) 2 volume ↔ _
  set W : ℝ → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)
  set V : ℝ → ℂ := fun x => (((1 + ‖x‖ ^ 2) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
  have hW : W.HasTemperateGrowth := by fun_prop
  have hV : V.HasTemperateGrowth := by fun_prop
  have hpos (x : ℝ) : 0 < 1 + ‖x‖ ^ 2 := by positivity
  -- `|x| ≤ (1 + x²)^{1/2} ≤ 1 + |x|`.
  have hsqrt (x : ℝ) : (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) = √(1 + x ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hle (x : ℝ) : |x| ≤ √(1 + x ^ 2) := Real.abs_le_sqrt (by linarith [sq_nonneg x])
  have hge (x : ℝ) : √(1 + x ^ 2) ≤ 1 + |x| :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [abs_nonneg x, sq_abs x]⟩
  have hWn (x : ℝ) : ‖W x‖ = √(1 + x ^ 2) := by
    change ‖(((1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2) : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), hsqrt]
  constructor
  · intro h
    have hm : AEStronglyMeasurable (fun x => W x * g x) volume :=
      hW.1.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)
    have hWg : MemLp (fun x => W x * g x) 2 volume := by
      refine ((Lp.memLp g).norm.add h.norm).of_le hm (ae_of_all _ fun x => ?_)
      rw [norm_mul, hWn, Pi.add_apply, Real.norm_of_nonneg (by positivity), norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      nlinarith [hge x, norm_nonneg (g x)]
    refine ⟨hWg.toLp _, ?_⟩
    ext u
    simp only [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
      SchwartzMap.smulLeftCLM_apply_apply hW]
    refine integral_congr_ae ?_
    filter_upwards [hWg.coeFn_toLp] with x hx
    rw [hx, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  · rintro ⟨f', hf'⟩
    have hVW : W * V = fun _ => (1 : ℂ) := by
      funext x
      simp only [W, V, Pi.mul_apply, ← Complex.ofReal_mul]
      rw [← Real.rpow_add (hpos x)]
      norm_num
    have hVn (x : ℝ) : ‖V x‖ = (1 + ‖x‖ ^ 2) ^ (-(1 : ℝ) / 2) := by
      change ‖(((1 + ‖x‖ ^ 2) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hVb (x : ℝ) : ‖V x‖ ≤ 1 := by
      rw [hVn]
      exact Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (by positivity))
        (by norm_num)
    have hVmem : MemLp V ⊤ volume :=
      memLp_top_of_bound hV.1.continuous.aestronglyMeasurable 1 (ae_of_all _ hVb)
    have h1 : (g : 𝓢'(ℝ, ℂ)) = ((hVmem.toLp _ • f' : L2R) : 𝓢'(ℝ, ℂ)) := by
      rw [Lp.toTemperedDistribution_smul_eq hV hVmem, ← hf', smulLeftCLM_smulLeftCLM_apply hW hV,
        hVW, smulLeftCLM_const, one_smul]
    have hinj := LinearMap.ker_eq_bot.mp
      (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2))
    have hg : g = (hVmem.toLp _ • f' : L2R) := hinj h1
    refine (Lp.memLp f').of_le (Complex.continuous_ofReal.aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable g)) ?_
    rw [hg]
    filter_upwards [Lp.coeFn_lpSMul (r := 2) (hVmem.toLp _) f', hVmem.coeFn_toLp] with x h2 h3
    rw [h2, Pi.smul_apply', h3, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, ← mul_assoc]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [hVn, neg_div, Real.rpow_neg (hpos x).le, hsqrt]
    rw [← div_eq_mul_inv]
    exact div_le_one_of_le₀ (hle x) (Real.sqrt_nonneg _)

theorem roughState_not_memSobolev : ¬ TemperedDistribution.MemSobolev 1 2
    (roughState : 𝓢'(ℝ, ℂ)) :=
  fun h => roughState_not_mem_domain_momentumOp (mem_domain_momentumOp_iff_memSobolev.2 h)

lemma measurable_kinetic : Measurable fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2 := by fun_prop

/-- The free Hamiltonian `H₀ = P²/2` (mass `1`, `ħ = 1`), as `𝓕⁻¹ (2π²ξ²) 𝓕` on its maximal
domain. -/
def freeHamiltonian : L2R →ₗ.[ℂ] L2R :=
  conjLinearPMap fourierL2.symm (L2.mulOp fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2)

/-- `H₀` is self-adjoint: it is unitarily equivalent to multiplication by `2π²ξ²`. -/
theorem isSelfAdjoint_freeHamiltonian : IsSelfAdjoint freeHamiltonian :=
  (L2.isSelfAdjoint_mulOp measurable_kinetic).conjLinearPMap

/-- The free evolution `e^{-itH₀} = 𝓕⁻¹ e^{-2iπ²ξ²t} 𝓕`, defined on all of `L²(ℝ)`. -/
def freeEvolution (t : ℝ) : L2R ≃ₗᵢ[ℂ] L2R :=
  fourierL2.trans ((L2.mulEvolution measurable_kinetic t).trans fourierL2.symm)

lemma freeEvolution_apply (t : ℝ) (ψ : L2R) :
    freeEvolution t ψ = fourierL2.symm (L2.mulEvolution measurable_kinetic t (fourierL2 ψ)) :=
  rfl

lemma mem_domain_freeHamiltonian {ψ : L2R} :
    ψ ∈ freeHamiltonian.domain ↔ fourierL2 ψ ∈ L2.mulDomain fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2 := by
  rw [freeHamiltonian, mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_symm]
  rfl

lemma freeHamiltonian_apply (ψ : freeHamiltonian.domain) :
    freeHamiltonian ψ = fourierL2.symm (L2.mulOp (fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2)
      ⟨fourierL2 ψ, mem_domain_freeHamiltonian.1 ψ.2⟩) :=
  conjLinearPMap_apply ψ

lemma freeEvolution_mem_domain_iff (t : ℝ) {ψ : L2R} :
    freeEvolution t ψ ∈ freeHamiltonian.domain ↔ ψ ∈ freeHamiltonian.domain := by
  rw [mem_domain_freeHamiltonian, mem_domain_freeHamiltonian, freeEvolution_apply,
    LinearIsometryEquiv.apply_symm_apply, L2.mulEvolution_mem_mulDomain_iff]

/-- On `D(H₀)`, the orbit of `ψ` solves the free Schrödinger equation
`i d/dt (U t ψ) = H₀ (U t ψ)`. -/
theorem hasDerivAt_freeEvolution {ψ : L2R} (hψ : ψ ∈ freeHamiltonian.domain) (t : ℝ) :
    HasDerivAt (fun s => freeEvolution s ψ)
      (-(Complex.I • freeHamiltonian ⟨freeEvolution t ψ,
        (freeEvolution_mem_domain_iff t).2 hψ⟩)) t := by
  have h := ((fourierL2.symm.toContinuousLinearEquiv : L2R →L[ℂ] L2R).restrictScalars
    ℝ).hasFDerivAt.comp_hasDerivAt t
    (L2.hasDerivAt_mulEvolution measurable_kinetic (mem_domain_freeHamiltonian.1 hψ) t)
  convert h using 1
  · rfl
  rw [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, map_neg, map_smul, freeHamiltonian_apply]
  congr 4
  exact Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)

/-- Off `D(H₀)`, the orbit is differentiable nowhere. -/
theorem not_differentiableAt_freeEvolution {ψ : L2R} (hψ : ψ ∉ freeHamiltonian.domain)
    (t : ℝ) : ¬ DifferentiableAt ℝ (fun s => freeEvolution s ψ) t := by
  intro hd
  have h := ((fourierL2.toContinuousLinearEquiv : L2R →L[ℂ] L2R).restrictScalars
    ℝ).differentiableAt.comp t hd
  refine L2.not_differentiableAt_mulEvolution measurable_kinetic
    (mt mem_domain_freeHamiltonian.2 hψ) t ?_
  convert h using 1
  funext s
  simp [freeEvolution_apply]

/-- The free Schrödinger equation holds along the orbit of `ψ` exactly on the domain of `H₀`. -/
theorem differentiableAt_freeEvolution_iff {ψ : L2R} (t : ℝ) :
    DifferentiableAt ℝ (fun s => freeEvolution s ψ) t ↔ ψ ∈ freeHamiltonian.domain :=
  ⟨fun hd => by_contra fun hψ => not_differentiableAt_freeEvolution hψ t hd,
    fun hψ => (hasDerivAt_freeEvolution hψ t).differentiableAt⟩

/-- `freeEvolution` is the propagator `e^{-itH₀}` that Stone's theorem gives for `H₀`
(`schrodingerPropagator`, in `ForPhyslib`), with `ħ = 1`. -/
theorem freeEvolution_eq_schrodingerPropagator (t : ℝ) :
    ((freeEvolution t).toContinuousLinearEquiv : L2R →L[ℂ] L2R) =
      schrodingerPropagator one_ne_zero isSelfAdjoint_freeHamiltonian t := by
  refine SolvesSchrodinger.eq_schrodingerPropagator (U := fun t =>
    ((freeEvolution t).toContinuousLinearEquiv : L2R →L[ℂ] L2R)) (fun ψ s => ?_) one_ne_zero
    isSelfAdjoint_freeHamiltonian
    (ContinuousLinearMap.ext fun ψ => by simp [freeEvolution_apply]) t
  refine ⟨(freeEvolution_mem_domain_iff s).2 ψ.2, ?_⟩
  rw [Complex.ofReal_one, mul_one, Complex.inv_I, neg_smul]
  exact hasDerivAt_freeEvolution ψ.2 s

end PositionSpace

/-! ### Sec. 5: the harmonic oscillator in position space -/

section Oscillator

open QuantumMechanics TauCeti
open scoped lp

/-- The oscillator's energies `n + 1/2` (`m = ω = ħ = 1`). -/
def oscillatorEnergy (n : ℕ) : ℝ := n + 1 / 2

/-- The unitary `ℓ²(ℕ) ≃ L²(ℝ)` of the Hermite basis (`TauCeti.hermiteHilbertBasis`): it sends
the `n`-th basis sequence to the Hermite function `ψₙ`. -/
def hermiteUnitary : ℓ²(ℕ, ℂ) ≃ₗᵢ[ℂ] L2R := (hermiteHilbertBasis ℂ).repr.symm

lemma hermiteUnitary_single (n : ℕ) :
    hermiteUnitary (lp.single 2 n 1) = hermiteFunctionLp ℂ n := by
  rw [hermiteUnitary, HilbertBasis.repr_symm_single, coe_hermiteHilbertBasis]

/-- The oscillator Hamiltonian `H = P²/2 + X²/2` (`m = ω = ħ = 1`) on `L²(ℝ)`, as the operator
that is diagonal in the Hermite basis with entries `n + 1/2`, on its maximal domain. -/
def oscillatorHamiltonian : L2R →ₗ.[ℂ] L2R :=
  conjLinearPMap hermiteUnitary (lp.diagonal oscillatorEnergy)

/-- `H` is self-adjoint: it is unitarily equivalent to a real diagonal operator. -/
theorem isSelfAdjoint_oscillatorHamiltonian : IsSelfAdjoint oscillatorHamiltonian :=
  (lp.isSelfAdjoint_diagonal _).conjLinearPMap

lemma hermiteFunctionLp_mem_domain (n : ℕ) :
    hermiteFunctionLp ℂ n ∈ oscillatorHamiltonian.domain := by
  rw [oscillatorHamiltonian, mem_domain_conjLinearPMap, ← hermiteUnitary_single,
    LinearIsometryEquiv.symm_apply_apply]
  exact lp.single_mem_diagonalDomain _ n 1

/-- The Hermite functions are the eigenvectors of `H`, with eigenvalues `n + 1/2`. -/
theorem oscillatorHamiltonian_hermiteFunctionLp (n : ℕ) :
    oscillatorHamiltonian ⟨_, hermiteFunctionLp_mem_domain n⟩ =
      (oscillatorEnergy n : ℂ) • hermiteFunctionLp ℂ n := by
  refine (conjLinearPMap_apply (e := hermiteUnitary) (T := lp.diagonal oscillatorEnergy)
    ⟨_, hermiteFunctionLp_mem_domain n⟩).trans ?_
  rw [← LinearIsometryEquiv.eq_symm_apply, map_smul]
  conv_rhs => rw [← hermiteUnitary_single, LinearIsometryEquiv.symm_apply_apply]
  refine lp.ext <| funext fun i => ?_
  rw [lp.diagonal_apply, lp.coeFn_smul, Pi.smul_apply]
  simp only [← hermiteUnitary_single, LinearIsometryEquiv.symm_apply_apply]
  by_cases h : i = n
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- `H ψₙ` is the differential expression `(-ψ'' + x²ψ)/2` of the oscillator applied to the
Hermite function `ψₙ`, point by point (`TauCeti.hermiteFunction_oscillator`). -/
theorem oscillatorHamiltonian_hermiteFunctionLp_ae (n : ℕ) :
    oscillatorHamiltonian ⟨_, hermiteFunctionLp_mem_domain n⟩ =ᵐ[volume] fun x =>
      (((-deriv (deriv (hermiteFunction n)) x + x ^ 2 * hermiteFunction n x) / 2 : ℝ) : ℂ) := by
  rw [oscillatorHamiltonian_hermiteFunctionLp]
  filter_upwards [Lp.coeFn_smul (oscillatorEnergy n : ℂ) (hermiteFunctionLp ℂ n),
    coeFn_hermiteFunctionLp (𝕜 := ℂ) n] with x h1 h2
  rw [h1, Pi.smul_apply, h2, hermiteFunction_oscillator, oscillatorEnergy]
  simp only [Complex.coe_algebraMap, smul_eq_mul]
  push_cast
  ring

/-- `H` is the only self-adjoint operator on `L²(ℝ)` that has the Hermite functions as
eigenvectors with eigenvalues `n + 1/2`, as the differential expression does. -/
theorem eq_oscillatorHamiltonian {T : L2R →ₗ.[ℂ] L2R} (hT : IsSelfAdjoint T)
    (h : ∀ n, ∃ hn : hermiteFunctionLp ℂ n ∈ T.domain,
      T ⟨_, hn⟩ = (oscillatorEnergy n : ℂ) • hermiteFunctionLp ℂ n) :
    T = oscillatorHamiltonian := by
  have hT' : conjLinearPMap hermiteUnitary.symm T = lp.diagonal oscillatorEnergy := by
    refine lp.eq_diagonal _ hT.conjLinearPMap fun n => ?_
    obtain ⟨hn, he⟩ := h n
    have hm : lp.single 2 n (1 : ℂ) ∈ (conjLinearPMap hermiteUnitary.symm T).domain := by
      rwa [mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_symm, hermiteUnitary_single]
    refine ⟨hm, ?_⟩
    rw [conjLinearPMap_apply]
    simp_rw [LinearIsometryEquiv.symm_symm, hermiteUnitary_single, he, map_smul,
      ← hermiteUnitary_single, LinearIsometryEquiv.symm_apply_apply]
    rfl
  rw [← conjLinearPMap_symm_conjLinearPMap (e := hermiteUnitary.symm) T, hT']
  rfl

/-- `H` is unbounded on its domain. -/
theorem exists_lt_norm_oscillatorHamiltonian (C : ℝ) :
    ∃ ψ : oscillatorHamiltonian.domain, C * ‖(ψ : L2R)‖ < ‖oscillatorHamiltonian ψ‖ := by
  obtain ⟨n, hn⟩ := exists_nat_gt C
  refine ⟨⟨_, hermiteFunctionLp_mem_domain n⟩, ?_⟩
  rw [oscillatorHamiltonian_hermiteFunctionLp, norm_smul, norm_hermiteFunctionLp,
    Complex.norm_real, Real.norm_of_nonneg (by unfold oscillatorEnergy; positivity),
    oscillatorEnergy]
  linarith

/-- The remark of Sec. 5 for the potential `V(x) = x²/2`: `D(H) ≠ L²(ℝ)`, the evolution
`e^{-itH}` of Stone's theorem solves the Schrödinger equation on `D(H)`, and off `D(H)` its
orbit is differentiable nowhere. -/
theorem oscillator_schrodinger_only_on_domain :
    oscillatorHamiltonian.domain ≠ ⊤ ∧
      SolvesSchrodinger 1 oscillatorHamiltonian
        (schrodingerPropagator one_ne_zero isSelfAdjoint_oscillatorHamiltonian) ∧
      ∀ ψ ∉ oscillatorHamiltonian.domain, ∀ t, ¬ DifferentiableAt ℝ
        (fun s => schrodingerPropagator one_ne_zero isSelfAdjoint_oscillatorHamiltonian s ψ) t :=
  schrodinger_only_on_domain one_ne_zero isSelfAdjoint_oscillatorHamiltonian
    exists_lt_norm_oscillatorHamiltonian

end Oscillator

/-! ### Sec. 5: commutator relations -/

section Commutator

open QuantumMechanics FourierTransform LinearPMap LineDeriv TemperedDistribution
open scoped SchwartzMap

/-- The commutator `[X, P] = X P - P X` (`ħ = 1`), on its natural domain: the `ψ` in
`D(X) ∩ D(P)` with `Pψ ∈ D(X)` and `Xψ ∈ D(P)` (`LinearPMap.compMax`, in `ForMathlib`). -/
def commutatorXP : L2R →ₗ.[ℂ] L2R :=
  positionOp.compMax momentumOp - momentumOp.compMax positionOp

theorem domain_commutatorXP_le :
    commutatorXP.domain ≤ positionOp.domain ⊓ momentumOp.domain :=
  le_inf (inf_le_right.trans (compMax_domain_le _ _)) (inf_le_left.trans (compMax_domain_le _ _))

/-- `[X, P]` is not defined on the whole of `L²(ℝ)`, while the identity is: the Cauchy packet
`ϕ` of Proposition 3 is not in `D(X)`. -/
theorem domain_commutatorXP_ne_top : commutatorXP.domain ≠ ⊤ := by
  intro h
  have hm : frameUnitary gaussState ∈ commutatorXP.domain := h ▸ Submodule.mem_top
  exact frameUnitary_gaussState_not_mem (domain_commutatorXP_le hm).1

/-! The relation on the natural domain, computed in the tempered distributions `𝓢'(ℝ)`. -/

lemma injective_toTemperedDistribution :
    Function.Injective (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2) :=
  LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot

/-- In `𝓢'`, a multiplication operator acts by `smulLeftCLM`. -/
lemma toTemperedDistribution_mulOp {a : ℝ → ℝ} (ha : (fun x => (a x : ℂ)).HasTemperateGrowth)
    (ψ : (L2.mulOp a : L2R →ₗ.[ℂ] L2R).domain) :
    ((L2.mulOp a ψ : L2R) : 𝓢'(ℝ, ℂ)) =
      smulLeftCLM ℂ (fun x => (a x : ℂ)) ((ψ : L2R) : 𝓢'(ℝ, ℂ)) := by
  ext u
  simp only [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply_apply ha]
  refine integral_congr_ae ?_
  filter_upwards [L2.coeFn_mulOp a ψ] with x hx
  rw [hx, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

lemma hasTemperateGrowth_ofReal : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop

/-- In `𝓢'`, `X` is multiplication by `x`. -/
theorem positionOp_toTemperedDistribution (ψ : positionOp.domain) :
    ((positionOp ψ : L2R) : 𝓢'(ℝ, ℂ)) =
      smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) ((ψ : L2R) : 𝓢'(ℝ, ℂ)) :=
  toTemperedDistribution_mulOp hasTemperateGrowth_ofReal ψ

lemma mem_domain_momentumOp' {ψ : L2R} :
    ψ ∈ momentumOp.domain ↔ fourierL2 ψ ∈ (L2.mulOp fun ξ : ℝ => 2 * π * ξ).domain := by
  rw [momentumOp, mem_domain_conjLinearPMap, LinearIsometryEquiv.symm_symm]

lemma momentumOp_apply (ψ : momentumOp.domain) :
    momentumOp ψ = fourierL2.symm (L2.mulOp (fun ξ : ℝ => 2 * π * ξ)
      ⟨fourierL2 ψ, mem_domain_momentumOp'.1 ψ.2⟩) :=
  conjLinearPMap_apply ψ

/-- `2πξ 𝓕u = 𝓕(-i ∂u)` in `𝓢'(ℝ)`. -/
lemma smulLeftCLM_fourier (u : 𝓢'(ℝ, ℂ)) :
    smulLeftCLM ℂ (fun ξ : ℝ => ((2 * π * ξ : ℝ) : ℂ)) (𝓕 u) =
      𝓕 ((-Complex.I) • ∂_{(1 : ℝ)} u) := by
  have hi : (fun ξ : ℝ => ((inner ℝ ξ (1 : ℝ) : ℝ) : ℂ)).HasTemperateGrowth := by fun_prop
  have hf : (fun ξ : ℝ => ((2 * π * ξ : ℝ) : ℂ)) =
      (2 * π : ℂ) • fun ξ : ℝ => ((inner ℝ ξ (1 : ℝ) : ℝ) : ℂ) := by
    funext ξ
    simp
  rw [fourier_smul, TemperedDistribution.fourier_lineDerivOp_eq, hf, smulLeftCLM_smul hi,
    _root_.smul_apply, smul_smul]
  congr 1
  linear_combination (2 * π : ℂ) * Complex.I_sq

/-- In `𝓢'`, `P` is `-i d/dx`. -/
theorem momentumOp_toTemperedDistribution (ψ : momentumOp.domain) :
    ((momentumOp ψ : L2R) : 𝓢'(ℝ, ℂ)) = (-Complex.I) • ∂_{(1 : ℝ)} ((ψ : L2R) : 𝓢'(ℝ, ℂ)) := by
  rw [momentumOp_apply]
  change ((𝓕⁻ (L2.mulOp (fun ξ : ℝ => 2 * π * ξ) _ : L2R) : L2R) : 𝓢'(ℝ, ℂ)) = _
  rw [← Lp.fourierInv_toTemperedDistribution_eq, toTemperedDistribution_mulOp (by fun_prop)]
  change 𝓕⁻ (smulLeftCLM ℂ _ ((𝓕 (ψ : L2R) : L2R) : 𝓢'(ℝ, ℂ))) = _
  rw [← Lp.fourier_toTemperedDistribution_eq, smulLeftCLM_fourier, fourierInv_fourier_eq]

/-- The product rule `d/dx (x u) = u + x du/dx` in `𝓢'(ℝ)`, from the Leibniz rule
`TemperedDistribution.lineDerivOp_smulLeftCLM` in `ForMathlib`. -/
lemma lineDerivOp_smulLeftCLM_ofReal (u : 𝓢'(ℝ, ℂ)) :
    ∂_{(1 : ℝ)} (smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) u) =
      u + smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) (∂_{(1 : ℝ)} u) := by
  have hd : (fun x : ℝ => fderiv ℝ (fun x : ℝ => (x : ℂ)) x 1) = fun _ => (1 : ℂ) := by
    funext x
    rw [show (fun x : ℝ => (x : ℂ)) = ⇑Complex.ofRealCLM from rfl,
      Complex.ofRealCLM.hasFDerivAt.fderiv]
    simp
  rw [TemperedDistribution.lineDerivOp_smulLeftCLM hasTemperateGrowth_ofReal
    (by rw [hd]; fun_prop), hd, smulLeftCLM_const, one_smul]

/-- **`[X, P] = i`** on the natural domain of `[X, P]`: the commutation relation holds once it is
restricted to `D([X, P])`. -/
theorem commutatorXP_apply (ψ : commutatorXP.domain) : commutatorXP ψ = Complex.I • (ψ : L2R) := by
  obtain ⟨hP, hXP⟩ := mem_domain_compMax.1 ψ.2.1
  obtain ⟨hX, hPX⟩ := mem_domain_compMax.1 ψ.2.2
  have e : commutatorXP ψ = positionOp ⟨momentumOp ⟨ψ, hP⟩, hXP⟩ -
      momentumOp ⟨positionOp ⟨ψ, hX⟩, hPX⟩ := rfl
  apply injective_toTemperedDistribution
  rw [e, _root_.map_sub, _root_.map_smul]
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [positionOp_toTemperedDistribution, momentumOp_toTemperedDistribution,
    momentumOp_toTemperedDistribution, positionOp_toTemperedDistribution,
    lineDerivOp_smulLeftCLM_ofReal, _root_.map_smul]
  module

/-! The relation on Schwartz functions, a dense subspace of `D([X, P])`. -/

lemma toLp_mem_positionDomain (φ : 𝓢(ℝ, ℂ)) : φ.toLp 2 volume ∈ positionDomain := by
  refine ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) φ).memLp 2 volume).ae_eq ?_
  filter_upwards [φ.coeFn_toLp 2 volume] with x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_ofReal, hx, smul_eq_mul]

lemma positionOp_toLp (φ : 𝓢(ℝ, ℂ)) :
    positionOp ⟨φ.toLp 2 volume, toLp_mem_positionDomain φ⟩ =
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) φ).toLp 2 volume := by
  refine Lp.ext ?_
  filter_upwards [coeFn_positionOp ⟨φ.toLp 2 volume, toLp_mem_positionDomain φ⟩,
    φ.coeFn_toLp 2 volume,
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) φ).coeFn_toLp 2 volume] with x h1 h2 h3
  rw [h1, h3, h2, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_ofReal, smul_eq_mul]

lemma toLp_mem_domain_momentumOp (φ : 𝓢(ℝ, ℂ)) : φ.toLp 2 volume ∈ momentumOp.domain := by
  rw [mem_domain_momentumOp]
  change 𝓕 (φ.toLp 2) ∈ positionDomain
  rw [SchwartzMap.toLp_fourier_eq]
  exact toLp_mem_positionDomain _

lemma momentumOp_toLp (φ : 𝓢(ℝ, ℂ)) :
    momentumOp ⟨φ.toLp 2 volume, toLp_mem_domain_momentumOp φ⟩ =
      ((-Complex.I) • ∂_{(1 : ℝ)} φ).toLp 2 volume := by
  apply injective_toTemperedDistribution
  simp only [Lp.toTemperedDistributionCLM_apply]
  rw [momentumOp_toTemperedDistribution]
  simp only [Lp.toTemperedDistribution_toLp_eq, lineDerivOp_toTemperedDistributionCLM_eq,
    _root_.map_smul]

/-- Schwartz functions lie in the natural domain of `[X, P]`. -/
theorem toLp_mem_domain_commutatorXP (φ : 𝓢(ℝ, ℂ)) : φ.toLp 2 volume ∈ commutatorXP.domain := by
  refine ⟨mem_domain_compMax.2 ⟨toLp_mem_domain_momentumOp φ, ?_⟩,
    mem_domain_compMax.2 ⟨toLp_mem_positionDomain φ, ?_⟩⟩
  · rw [momentumOp_toLp]
    exact toLp_mem_positionDomain _
  · rw [positionOp_toLp]
    exact toLp_mem_domain_momentumOp _

/-- So `D([X, P])` is dense in `L²(ℝ)`, and `[X, P] = i` there. -/
theorem dense_domain_commutatorXP : Dense (commutatorXP.domain : Set L2R) :=
  (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) (μ := (volume : Measure ℝ))
    ENNReal.ofNat_ne_top).mono (by
      rintro _ ⟨φ, rfl⟩
      exact toLp_mem_domain_commutatorXP φ)

/-- The commutator relations of Sec. 5 together: `[X, P]` is not defined on all of `L²(ℝ)`, no
everywhere-defined symmetric operators satisfy `[X, P] = i` on a nonzero Hilbert space, and on
the natural domain of `[X, P]`, which is dense, the relation holds. -/
theorem commutator_relations :
    commutatorXP.domain ≠ ⊤ ∧
    ¬ (∃ X P : L2R →ₗ[ℂ] L2R, X.IsSymmetric ∧ P.IsSymmetric ∧
      X ∘ₗ P - P ∘ₗ X = (Complex.I * (1 : ℝ)) • LinearMap.id) ∧
    Dense (commutatorXP.domain : Set L2R) ∧
    ∀ ψ : commutatorXP.domain, commutatorXP ψ = Complex.I • (ψ : L2R) := by
  have : Nontrivial L2R := nontrivial_of_ne (frameUnitary gaussState) 0 fun h =>
    frameUnitary_gaussState_not_mem (by rw [h]; exact positionOp.domain.zero_mem)
  exact ⟨domain_commutatorXP_ne_top, not_exists_ccr_symmetric one_ne_zero,
    dense_domain_commutatorXP, commutatorXP_apply⟩

end Commutator

/-! ### Sec. 5: point-wise values -/

section PointwiseValues

open scoped SchwartzMap

/-- A vector of `L²(ℝ)` has a representative with any value `c` at any point `x`: changing a
function at one point does not change its class. -/
theorem exists_representative_apply_eq (ψ : L2R) (x : ℝ) (c : ℂ) :
    ∃ f : ℝ → ℂ, f =ᵐ[volume] ψ ∧ f x = c :=
  MeasureTheory.exists_ae_eq_apply_eq _ x c

/-- So the value of `ψ` at a point is not well defined: two representatives differ there. -/
theorem exists_representatives_ne (ψ : L2R) (x : ℝ) :
    ∃ f g : ℝ → ℂ, f =ᵐ[volume] ψ ∧ g =ᵐ[volume] ψ ∧ f x ≠ g x := by
  obtain ⟨f, hf, hfx⟩ := exists_representative_apply_eq ψ x 0
  obtain ⟨g, hg, hgx⟩ := exists_representative_apply_eq ψ x 1
  exact ⟨f, g, hf, hg, by rw [hfx, hgx]; exact zero_ne_one⟩

/-- Nor is the probability density `|ψ(x)|²`: it takes any value `r ≥ 0` at `x`. -/
theorem exists_representative_density_eq (ψ : L2R) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    ∃ f : ℝ → ℂ, f =ᵐ[volume] ψ ∧ ‖f x‖ ^ 2 = r := by
  obtain ⟨f, hf, hfx⟩ := exists_representative_apply_eq ψ x (√r : ℝ)
  refine ⟨f, hf, ?_⟩
  rw [hfx, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hr]

/-- Point evaluation at `x₀` is not continuous in the `L²` norm, even on Schwartz functions: no
continuous linear functional on `L²(ℝ)` agrees with `φ ↦ φ(x₀)` there. The witnesses are bumps
of value `1` at `x₀` and support of length `2r`, so of norm at most `√(2r)`. -/
theorem not_exists_continuous_eval (x₀ : ℝ) :
    ¬ ∃ ℓ : L2R →L[ℂ] ℂ, ∀ φ : 𝓢(ℝ, ℂ), ℓ (φ.toLp 2 volume) = φ x₀ := by
  rintro ⟨ℓ, hℓ⟩
  set r : ℝ := 1 / (4 * (‖ℓ‖ ^ 2 + 1)) with hr
  have hr0 : 0 < r := by positivity
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩
  have hb : HasCompactSupport (Complex.ofRealCLM ∘ b) := b.hasCompactSupport.comp_left rfl
  let φ : 𝓢(ℝ, ℂ) := hb.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hφ : φ x₀ = 1 := by
    simp [φ, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hr0).le)]
  have hint : ∫ x, ‖φ x‖ ^ (2 : ℝ) ≤ 2 * r := by
    calc ∫ x, ‖φ x‖ ^ (2 : ℝ) ≤ ∫ x, (Metric.ball x₀ r).indicator 1 x := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => by positivity) ?_
            (ae_of_all _ fun x => ?_)
          · exact (integrable_indicator_iff measurableSet_ball).2
              (integrableOn_const measure_ball_lt_top.ne)
          · by_cases hx : x ∈ Metric.ball x₀ r
            · rw [indicator_of_mem hx]
              have h0 := b.nonneg' x
              simp [φ, abs_of_nonneg h0]
              exact b.le_one
            · rw [indicator_of_notMem hx]
              have : b x = 0 := by
                rwa [← Function.notMem_support, b.support_eq]
              simp [φ, this]
      _ = 2 * r := by
          rw [integral_indicator_one measurableSet_ball, Measure.real, Real.volume_ball,
            ENNReal.toReal_ofReal (by positivity)]
  have hN := SchwartzMap.norm_toLp' (f := φ) (p := 2) (μ := volume) two_ne_zero
    ENNReal.ofNat_ne_top
  rw [ENNReal.toReal_ofNat, show (2⁻¹ : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow] at hN
  have hN2 : ‖φ.toLp 2 volume‖ ^ 2 ≤ 2 * r := by
    rw [hN, Real.sq_sqrt (integral_nonneg fun _ => by positivity)]
    exact hint
  have h1 : (1 : ℝ) ≤ ‖ℓ‖ * ‖φ.toLp 2 volume‖ := by
    have := ℓ.le_opNorm (φ.toLp 2 volume)
    rwa [hℓ, hφ, norm_one] at this
  have hr1 : r * (4 * (‖ℓ‖ ^ 2 + 1)) = 1 := by
    rw [hr]
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hN2 (sq_nonneg ‖ℓ‖), mul_self_le_mul_self zero_le_one h1,
    norm_nonneg ℓ, norm_nonneg (φ.toLp 2 volume)]

/-- The point-wise values of Sec. 5 together: every value at every point is taken by a
representative of every `ψ ∈ L²(ℝ)`, and point evaluation does not extend continuously from
Schwartz functions to `L²(ℝ)`. -/
theorem pointwise_values :
    (∀ (ψ : L2R) (x : ℝ) (c : ℂ), ∃ f : ℝ → ℂ, f =ᵐ[volume] ψ ∧ f x = c) ∧
    ∀ x₀ : ℝ, ¬ ∃ ℓ : L2R →L[ℂ] ℂ, ∀ φ : 𝓢(ℝ, ℂ), ℓ (φ.toLp 2 volume) = φ x₀ :=
  ⟨exists_representative_apply_eq, not_exists_continuous_eval⟩

end PointwiseValues

end HilbertUnphysicality
