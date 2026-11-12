/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import HilbertUnphysicality
public import ForMathlib.Analysis.InnerProductSpace.SelfAdjointExtension
public import ForMathlib.Analysis.Fourier.LpSpace

/-!
# Unphysicality of Hilbert spaces: real potentials

The remark of Sec. 5 of the brief, that the Schrödinger equation holds only on `D(H)`, for
`H = P²/2 + V(x)` on `L²(ℝ)` with an arbitrary real potential `V` that is square integrable near
each point of an open set `U` whose complement is null (`V ∈ L²_loc(U)`). This covers every
continuous potential (`U = ℝ`), whatever its growth or sign (`|x|^β`, `-x⁴`, `eˣ`), and
potentials with isolated singularities (`U = ℝ ∖ {0}`), however strong (`1/x²`, `-1/x²`).

For such `V`, the operator sum `H₀ + V` on `D(H₀) ∩ D(V)` is densely defined (it contains the
smooth functions with compact support in `U`), symmetric, unbounded, and commutes with complex
conjugation. By von Neumann's theorem it has a self-adjoint extension `H`, and every self-adjoint
extension satisfies the remark. The extension need not be unique: for `-x⁴` or `-1/x²` the
self-adjoint realizations differ by boundary conditions at infinity or at `0`, and the remark
holds for each of them.

Commutation with conjugation rests on `𝓕 f̄ = R (𝓕 f)‾` (`R` the reflection), since `H₀` is the
Fourier transform of multiplication by the even function `2π²ξ²`.

This module is separate from the main file of the brief because von Neumann's theorem is
reached through `ForMathlib.Analysis.InnerProductSpace.SelfAdjointExtension`, whose TauCeti import
clashes with Physlib's unbounded operators in files that load private imports, such as the
comparator's exporter. No certified statement depends on it.

## Main results

* `commutesWithConj_schrodingerHamiltonian`: `H₀ + V` commutes with complex conjugation;
* `dense_domain_schrodingerHamiltonian`: `D(H₀) ∩ D(V)` is dense for `V ∈ L²_loc(U)`;
* `exists_lt_norm_schrodingerHamiltonian_of_locallyIntegrableOn`: `H₀ + V` is unbounded;
* `exists_isSelfAdjoint_le_schrodingerHamiltonian`: `H₀ + V` has a self-adjoint extension;
* `realPotential_schrodinger_only_on_domain`: the remark of Sec. 5 for every self-adjoint
  extension of `H₀ + V`;
* `continuous_schrodinger_only_on_domain`, `continuousOn_schrodinger_only_on_domain`: the cases
  of a continuous potential and of one continuous off `0`.
-/

open Real MeasureTheory FourierTransform QuantumMechanics LinearPMap Complex
open SchwartzMap LineDeriv
open scoped ENNReal ContDiff InnerProductSpace

@[expose] public noncomputable section

namespace HilbertUnphysicality

/-! ### Commutation with complex conjugation -/

/-- The reflection `ψ ↦ ψ ∘ (-·)` of `L²(ℝ)`. -/
abbrev reflectL2 : L2R →+ L2R :=
  Lp.compMeasurePreserving (fun x : ℝ => -x) (Measure.measurePreserving_neg volume)

lemma fourierL2_conjugate (ψ : L2R) :
    fourierL2 (L2.conjugate ψ) = reflectL2 (L2.conjugate (fourierL2 ψ)) :=
  Lp.fourier_conjugate ψ

lemma fourierL2_symm_reflectL2_conjugate (g : L2R) :
    fourierL2.symm (reflectL2 (L2.conjugate g)) = L2.conjugate (fourierL2.symm g) := by
  apply fourierL2.injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourierL2_conjugate,
    LinearIsometryEquiv.apply_symm_apply]

lemma kinetic_neg (ξ : ℝ) : 2 * π ^ 2 * (-ξ) ^ 2 = 2 * π ^ 2 * ξ ^ 2 := by ring

/-- `H₀` commutes with complex conjugation. -/
theorem commutesWithConj_freeHamiltonian :
    freeHamiltonian.CommutesWithConj L2.conjugate := by
  intro ψ
  have hR := Measure.measurePreserving_neg (volume : Measure ℝ)
  have hf := mem_domain_freeHamiltonian.1 ψ.2
  have hc := L2.conjugate_mem_mulDomain _ hf
  have hRc := L2.compMeasurePreserving_mem_mulDomain hR kinetic_neg hc
  have e := fourierL2_conjugate ψ
  have hmem : L2.conjugate (ψ : L2R) ∈ freeHamiltonian.domain :=
    mem_domain_freeHamiltonian.2 (e ▸ hRc)
  refine ⟨hmem, ?_⟩
  rw [freeHamiltonian_apply, freeHamiltonian_apply]
  have h1 : L2.mulOp (fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2)
      ⟨fourierL2 (L2.conjugate (ψ : L2R)), mem_domain_freeHamiltonian.1 hmem⟩ =
      L2.mulOp (fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2) ⟨_, hRc⟩ :=
    congrArg _ (Subtype.ext e)
  rw [h1, L2.mulOp_compMeasurePreserving hR kinetic_neg ⟨_, hc⟩,
    L2.mulOp_conjugate _ ⟨_, hf⟩, fourierL2_symm_reflectL2_conjugate]

/-- Multiplication by a real potential commutes with complex conjugation. -/
theorem commutesWithConj_mulOp (V : ℝ → ℝ) :
    (L2.mulOp V : L2R →ₗ.[ℂ] L2R).CommutesWithConj L2.conjugate := fun ψ =>
  ⟨L2.conjugate_mem_mulDomain V ψ.2, L2.mulOp_conjugate V ψ⟩

/-- **`H₀ + V` is real**: it commutes with complex conjugation. -/
theorem commutesWithConj_schrodingerHamiltonian (V : ℝ → ℝ) :
    (schrodingerHamiltonian V).CommutesWithConj L2.conjugate :=
  commutesWithConj_freeHamiltonian.add (commutesWithConj_mulOp V)

/-- `H₀ + V` is symmetric. -/
theorem isFormalAdjoint_schrodingerHamiltonian {V : ℝ → ℝ} (hV : Measurable V) :
    (schrodingerHamiltonian V).IsFormalAdjoint (schrodingerHamiltonian V) :=
  isSelfAdjoint_freeHamiltonian.isFormalAdjoint.add (L2.isSelfAdjoint_mulOp hV).isFormalAdjoint

/-! ### Test functions -/

section TestFunctions

variable {V : ℝ → ℝ} {U : Set ℝ} (hV : Measurable V)
  (hloc : LocallyIntegrableOn (fun x => V x ^ 2) U volume)
include hV hloc

/-- A Schwartz function with compact support in `U` lies in `D(V)` for `V ∈ L²_loc(U)`. -/
lemma toLp_mem_mulDomain_of_tsupport_subset (φ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) : φ.toLp 2 volume ∈ L2.mulDomain V := by
  rw [L2.mem_mulDomain]
  have hK : IsCompact (tsupport φ) := hc
  have hVK : IntegrableOn (fun x => V x ^ 2) (tsupport φ) volume :=
    hloc.integrableOn_compact_subset hs hK
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuous φ.continuous
  have hm : AEStronglyMeasurable (fun x => (V x : ℂ) * φ x) volume :=
    (hV.complex_ofReal.mul φ.continuous.measurable).aestronglyMeasurable
  have hmem : MemLp (fun x => (V x : ℂ) * φ x) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine ((hVK.integrable_indicator hK.measurableSet).const_mul (M ^ 2)).mono'
      (hm.norm.pow 2) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_pow, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hx : x ∈ tsupport φ
    · rw [Set.indicator_of_mem hx]
      have h0 : 0 ≤ ‖φ x‖ := norm_nonneg _
      have h1 : ‖φ x‖ ≤ M := hM x
      have h2 : |V x| ^ 2 = V x ^ 2 := sq_abs _
      nlinarith [sq_nonneg (V x), mul_le_mul h1 h1 h0 (h0.trans h1)]
    · rw [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, norm_zero]
      simp
  exact hmem.ae_eq (by filter_upwards [φ.coeFn_toLp 2 volume] with x hx; rw [hx])

lemma toLp_mem_domain_schrodingerHamiltonian (φ : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ U) : φ.toLp 2 volume ∈ (schrodingerHamiltonian V).domain :=
  ⟨toLp_mem_domain_freeHamiltonian φ, toLp_mem_mulDomain_of_tsupport_subset hV hloc φ hc hs⟩

variable (hU : IsOpen U) (hUc : volume Uᶜ = 0)
include hU hUc

/-- **`D(H₀) ∩ D(V)` is dense** for `V ∈ L²_loc(U)`: a vector orthogonal to it is orthogonal to
every smooth function with compact support in `U`, so vanishes almost everywhere on `U`. -/
theorem dense_domain_schrodingerHamiltonian :
    Dense ((schrodingerHamiltonian V).domain : Set L2R) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr ((Submodule.eq_bot_iff _).mpr fun g hg => ?_))
  have hzero := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp g).locallyIntegrable (by norm_num)).locallyIntegrableOn U)
    fun φ hφ hφc hφU => by
      have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ φ) := hφc.comp_left rfl
      have h₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ φ) := by fun_prop
      set ψ : 𝓢(ℝ, ℂ) := h₁.toSchwartzMap h₂
      have hψU : tsupport ψ ⊆ U :=
        (tsupport_comp_subset (g := Complex.ofRealCLM) (map_zero _) φ).trans hφU
      have h0 := (Submodule.mem_orthogonal _ g).1 hg _
        (toLp_mem_domain_schrodingerHamiltonian hV hloc ψ h₁ hψU)
      rw [L2.inner_def] at h0
      rw [← h0]
      refine integral_congr_ae ?_
      filter_upwards [ψ.coeFn_toLp 2 volume] with x hx
      rw [hx]
      change (φ x : ℂ) * g x = _
      simp only [RCLike.inner_apply]
      rw [show ψ x = (φ x : ℂ) from rfl, Complex.conj_ofReal, mul_comm]
  have hU' : ∀ᵐ x ∂volume, x ∈ U := by
    rw [ae_iff]
    exact hUc
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hzero, hU'] with x h1 h2
  rw [h1 h2, Pi.zero_apply]

end TestFunctions

/-! ### Unboundedness -/

/-- An `L²` norm bound from a pointwise bound by three functions. -/
lemma norm_le_add_add_of_ae_le {u v₁ v₂ v₃ : L2R}
    (h : ∀ᵐ x ∂volume, ‖u x‖ ≤ ‖v₁ x‖ + ‖v₂ x‖ + ‖v₃ x‖) : ‖u‖ ≤ ‖v₁‖ + ‖v₂‖ + ‖v₃‖ := by
  have m1 := (Lp.memLp v₁).norm
  have m2 := (Lp.memLp v₂).norm
  have m3 := (Lp.memLp v₃).norm
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, Lp.norm_def,
    ← ENNReal.toReal_add (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _),
    ← ENNReal.toReal_add (by simp [Lp.eLpNorm_ne_top]) (Lp.eLpNorm_ne_top _)]
  refine ENNReal.toReal_mono (by simp [Lp.eLpNorm_ne_top]) ?_
  calc eLpNorm (u : ℝ → ℂ) 2 volume
      ≤ eLpNorm (fun x => ‖v₁ x‖ + ‖v₂ x‖ + ‖v₃ x‖) 2 volume :=
        eLpNorm_mono_ae_real (Lp.aestronglyMeasurable _) h
    _ ≤ eLpNorm (fun x => ‖v₁ x‖ + ‖v₂ x‖) 2 volume + eLpNorm (fun x => ‖v₃ x‖) 2 volume :=
        eLpNorm_add_le one_le_two
    _ ≤ eLpNorm (fun x => ‖v₁ x‖) 2 volume + eLpNorm (fun x => ‖v₂ x‖) 2 volume +
          eLpNorm (fun x => ‖v₃ x‖) 2 volume := by
        gcongr
        exact eLpNorm_add_le one_le_two
    _ = _ := by
        rw [eLpNorm_norm _ (Lp.aestronglyMeasurable _), eLpNorm_norm _ (Lp.aestronglyMeasurable _),
          eLpNorm_norm _ (Lp.aestronglyMeasurable _)]

/-- Two `L²` functions with the same pointwise norms have the same norm. -/
lemma norm_eq_of_ae_norm_eq {u v : L2R} (h : ∀ᵐ x ∂volume, ‖u x‖ = ‖v x‖) : ‖u‖ = ‖v‖ := by
  have h2 : ‖u‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [L2.norm_sq_eq_integral, L2.norm_sq_eq_integral]
    exact integral_congr_ae (by filter_upwards [h] with x hx; rw [hx])
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- The derivatives of a modulated function `e^{itx} f(x)`. -/
lemma deriv_deriv_exp_mul {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : ℝ) :
    deriv (deriv fun y : ℝ => cexp (↑(t * y) * I) * f y) x =
      cexp (↑(t * x) * I) * (-(t : ℂ) ^ 2 * f x + 2 * t * I * deriv f x +
        deriv (deriv f) x) := by
  obtain ⟨hf1, hf'⟩ := contDiff_infty_iff_deriv.1 hf
  obtain ⟨hf2, -⟩ := contDiff_infty_iff_deriv.1 hf'
  have he (y : ℝ) : HasDerivAt (fun y : ℝ => cexp (↑(t * y) * I))
      (cexp (↑(t * y) * I) * (t * I)) y := by
    have h : HasDerivAt (fun y : ℝ => (↑(t * y) : ℂ) * I) (t * I) y := by
      simpa using (((hasDerivAt_id y).const_mul t).ofReal_comp).mul_const I
    exact h.cexp
  have h1 : deriv (fun y : ℝ => cexp (↑(t * y) * I) * f y) =
      fun y => cexp (↑(t * y) * I) * (t * I * f y + deriv f y) := by
    funext y
    exact ((he y).mul (hf1 y).hasDerivAt).deriv.trans (by ring)
  rw [h1]
  have h2 := (he x).mul (((hf1 x).hasDerivAt.const_mul (t * I)).add (hf2 x).hasDerivAt)
  refine h2.deriv.trans ?_
  simp only [Pi.add_apply]
  linear_combination cexp (↑(t * x) * I) * (t : ℂ) ^ 2 * f x * I_sq

section RealPotential

variable {V : ℝ → ℝ} {U : Set ℝ} (hV : Measurable V)
  (hloc : LocallyIntegrableOn (fun x => V x ^ 2) U volume) (hU : IsOpen U)
  (hUc : volume Uᶜ = 0)
include hV hloc hU hUc

/-- **`H₀ + V` is unbounded on its domain** for `V ∈ L²_loc(U)`: for a bump `f` with support in
`U`, the modulated functions `e^{itx} f` have `‖V e^{itx} f‖ = ‖V f‖` and `‖e^{itx} f‖ = ‖f‖`, while
`‖H₀ e^{itx} f‖ ≥ (t² ‖f‖ - 2 t ‖f'‖ - ‖f''‖) / 2`. -/
theorem exists_lt_norm_schrodingerHamiltonian_of_locallyIntegrableOn (c : ℝ) :
    ∃ ψ : (schrodingerHamiltonian V).domain,
      c * ‖(ψ : L2R)‖ < ‖schrodingerHamiltonian V ψ‖ := by
  -- a bump `f` with support in `U`
  obtain ⟨a, ha⟩ : U.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    simp at hUc
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU a ha
  set β : ContDiffBump a := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set f : ℝ → ℂ := Complex.ofRealCLM ∘ β
  have hfs : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hfc : HasCompactSupport f := β.hasCompactSupport.comp_left rfl
  have hfU : tsupport f ⊆ U := by
    refine (tsupport_comp_subset (by simp) _).trans ?_
    rw [β.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show r / 2 < r by linarith)).trans hrU
  -- the modulated bumps
  set g : ℝ → ℝ → ℂ := fun t y => cexp (↑(t * y) * I) * f y
  have hgs (t : ℝ) : ContDiff ℝ ∞ (g t) := by
    have he : ContDiff ℝ ∞ (fun y : ℝ => cexp (Complex.ofRealCLM (t * y) * I)) :=
      Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)
    exact he.mul hfs
  have hgc (t : ℝ) : HasCompactSupport (g t) := hfc.mul_left
  have hgU (t : ℝ) : tsupport (g t) ⊆ U := (tsupport_mul_subset_right).trans hfU
  set Φ : ℝ → 𝓢(ℝ, ℂ) := fun t => (hgc t).toSchwartzMap (hgs t)
  have hΦ (t : ℝ) (y : ℝ) : Φ t y = g t y := rfl
  have hnorm_g (t : ℝ) (y : ℝ) : ‖g t y‖ = ‖f y‖ := by
    simp only [g, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hdom (t : ℝ) := toLp_mem_domain_schrodingerHamiltonian hV hloc (Φ t) (hgc t) (hgU t)
  -- the `L²` functions `f`, `f'`, `f''`, and the norms
  set F : 𝓢(ℝ, ℂ) := hfc.toSchwartzMap hfs
  set F₁ : 𝓢(ℝ, ℂ) := ∂_{(1 : ℝ)} F
  set F₂ : 𝓢(ℝ, ℂ) := ∂_{(1 : ℝ)} F₁
  have hF₁ (y : ℝ) : F₁ y = deriv f y := by
    rw [lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
    rfl
  have hF₁' : (F₁ : ℝ → ℂ) = deriv f := funext hF₁
  have hF₂ (y : ℝ) : F₂ y = deriv (deriv f) y := by
    rw [lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv, hF₁']
  have hD (t : ℝ) (y : ℝ) : (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Φ t))) y = deriv (deriv (g t)) y := by
    rw [lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
    congr 1
  set n₀ := ‖F.toLp 2 volume‖
  set n₁ := ‖F₁.toLp 2 volume‖
  set n₂ := ‖F₂.toLp 2 volume‖
  have hFV := toLp_mem_mulDomain_of_tsupport_subset hV hloc F hfc hfU
  set B := ‖L2.mulOp V ⟨F.toLp 2 volume, hFV⟩‖
  have hF (y : ℝ) : F y = f y := rfl
  have hn₀ : 0 < n₀ := by
    refine norm_pos_iff.2 fun h => ?_
    have h' : (F : ℝ → ℂ) =ᵐ[volume] 0 :=
      (F.coeFn_toLp 2 volume).symm.trans (Lp.eq_zero_iff_ae_eq_zero.1 h)
    have h'' := congrFun ((Continuous.ae_eq_iff_eq volume F.continuous continuous_zero).1 h') a
    rw [hF] at h''
    have h1 : β a = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))
    simp [f, h1] at h''
  have hΦn (t : ℝ) : ‖(Φ t).toLp 2 volume‖ = n₀ :=
    norm_eq_of_ae_norm_eq (by
      filter_upwards [(Φ t).coeFn_toLp 2 volume, F.coeFn_toLp 2 volume] with y h1 h2
      rw [h1, h2, hΦ, hnorm_g, hF])
  have hVn (t : ℝ) : ‖L2.mulOp V ⟨(Φ t).toLp 2 volume, (hdom t).2⟩‖ = B :=
    norm_eq_of_ae_norm_eq (by
      filter_upwards [L2.coeFn_mulOp V ⟨_, (hdom t).2⟩, L2.coeFn_mulOp V ⟨_, hFV⟩,
        (Φ t).coeFn_toLp 2 volume, F.coeFn_toLp 2 volume] with y h1 h2 h3 h4
      rw [h1, h2, h3, h4, norm_mul, norm_mul, hΦ, hnorm_g, hF])
  have hH (t : ℝ) : ‖freeHamiltonian ⟨(Φ t).toLp 2 volume, (hdom t).1⟩‖ =
      1 / 2 * ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Φ t))).toLp 2 volume‖ := by
    rw [freeHamiltonian_toLp, show ((-(1 / 2) : ℂ) • ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Φ t))).toLp 2 volume
      = (-(1 / 2) : ℂ) • (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Φ t))).toLp 2 volume from rfl, norm_smul]
    norm_num
  -- `t² ‖f‖ ≤ ‖(e^{itx} f)''‖ + 2 |t| ‖f'‖ + ‖f''‖`
  have hlow (t : ℝ) : t ^ 2 * n₀ ≤
      ‖(∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Φ t))).toLp 2 volume‖ + 2 * |t| * n₁ + n₂ := by
    have h := norm_le_add_add_of_ae_le (u := ((t : ℂ) ^ 2) • F.toLp 2 volume)
      (v₁ := (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Φ t))).toLp 2 volume)
      (v₂ := ((2 * t : ℝ) : ℂ) • F₁.toLp 2 volume) (v₃ := F₂.toLp 2 volume) (by
        filter_upwards [Lp.coeFn_smul ((t : ℂ) ^ 2) (F.toLp 2 volume), F.coeFn_toLp 2 volume,
          (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} (Φ t))).coeFn_toLp 2 volume,
          Lp.coeFn_smul (((2 * t : ℝ) : ℂ)) (F₁.toLp 2 volume), F₁.coeFn_toLp 2 volume,
          F₂.coeFn_toLp 2 volume] with y h1 h2 h3 h4 h5 h6
        rw [h1, Pi.smul_apply, h2, h3, h4, Pi.smul_apply, h5, h6, hD, deriv_deriv_exp_mul hfs,
          hF, hF₁, hF₂, smul_eq_mul, smul_eq_mul, norm_mul (cexp _),
          Complex.norm_exp_ofReal_mul_I, one_mul]
        set A := -(t : ℂ) ^ 2 * f y + 2 * t * I * deriv f y + deriv (deriv f) y
        have e : (t : ℂ) ^ 2 * f y = -A + ((2 * t : ℝ) : ℂ) * deriv f y * I +
            deriv (deriv f) y := by
          simp only [A]
          push_cast
          ring
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) le_rfl)
        rw [norm_neg, norm_mul _ I, Complex.norm_I, mul_one])
    rw [norm_smul, norm_smul, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, abs_mul, abs_two] at h
    linarith
  -- choose `t` large
  set K := n₁ + n₂ + B + |c| * n₀ + 1
  set t : ℝ := 2 * K / n₀ + 1
  have hK : 0 < K := by positivity
  have ht1 : 1 ≤ t := by
    have : 0 ≤ 2 * K / n₀ := by positivity
    linarith
  have htn : t * n₀ = 2 * K + n₀ := by
    simp only [t]
    field_simp
  refine ⟨⟨(Φ t).toLp 2 volume, hdom t⟩, ?_⟩
  change c * ‖(Φ t).toLp 2 volume‖ < ‖freeHamiltonian ⟨(Φ t).toLp 2 volume, (hdom t).1⟩ +
    L2.mulOp V ⟨(Φ t).toLp 2 volume, (hdom t).2⟩‖
  have h1 := norm_sub_norm_le (freeHamiltonian ⟨(Φ t).toLp 2 volume, (hdom t).1⟩)
    (-L2.mulOp V ⟨(Φ t).toLp 2 volume, (hdom t).2⟩)
  rw [sub_neg_eq_add, norm_neg, hVn, hH] at h1
  have h2 := hlow t
  rw [abs_of_pos (by linarith)] at h2
  rw [hΦn]
  have hn₁ : 0 ≤ n₁ := norm_nonneg _
  have hn₂ : 0 ≤ n₂ := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  have hc : c * n₀ ≤ |c| * n₀ := mul_le_mul_of_nonneg_right (le_abs_self c) hn₀.le
  have e1 : t ^ 2 * n₀ = t * K + t * K + t * n₀ := by linear_combination t * htn
  have e2 : t * K = t * n₁ + t * (n₂ + B + |c| * n₀ + 1) := by
    simp only [K]
    ring
  have e3 := mul_le_mul_of_nonneg_right ht1 (by positivity : (0 : ℝ) ≤ n₂ + B + |c| * n₀ + 1)
  have e4 : 0 ≤ t * n₀ := by positivity
  linarith

/-! ### Self-adjoint realizations -/

/-- **Real potentials have self-adjoint realizations.** For `V ∈ L²_loc(U)`, the operator sum
`H₀ + V` on `D(H₀) ∩ D(V)` has a self-adjoint extension, by von Neumann's theorem. -/
theorem exists_isSelfAdjoint_le_schrodingerHamiltonian :
    ∃ H, schrodingerHamiltonian V ≤ H ∧ IsSelfAdjoint H :=
  exists_isSelfAdjoint_le_of_commutesWithConj L2.inner_conjugate_conjugate
    L2.conjugate_conjugate (dense_domain_schrodingerHamiltonian hV hloc hU hUc)
    (isFormalAdjoint_schrodingerHamiltonian hV) (commutesWithConj_schrodingerHamiltonian V)

/-- The remark of Sec. 5 for every real potential `V ∈ L²_loc(U)`: `H₀ + V` has a self-adjoint
extension, and for every self-adjoint extension `H`, `D(H) ≠ L²(ℝ)`, the evolution `e^{-itH}` of
Stone's theorem solves the Schrödinger equation on `D(H)`, and off `D(H)` its orbit is
differentiable nowhere. -/
theorem realPotential_schrodinger_only_on_domain :
    (∃ H, schrodingerHamiltonian V ≤ H ∧ IsSelfAdjoint H) ∧
      ∀ H (hH : IsSelfAdjoint H), schrodingerHamiltonian V ≤ H →
        H.domain ≠ ⊤ ∧ SolvesSchrodinger 1 H (schrodingerPropagator one_ne_zero hH) ∧
        ∀ ψ ∉ H.domain, ∀ t, ¬ DifferentiableAt ℝ
          (fun s => schrodingerPropagator one_ne_zero hH s ψ) t := by
  refine ⟨exists_isSelfAdjoint_le_schrodingerHamiltonian hV hloc hU hUc, fun H hH hle => ?_⟩
  refine schrodinger_only_on_domain one_ne_zero hH fun c => ?_
  obtain ⟨ψ, hψ⟩ := exists_lt_norm_schrodingerHamiltonian_of_locallyIntegrableOn hV hloc hU hUc c
  refine ⟨⟨ψ, hle.1 ψ.2⟩, ?_⟩
  rw [← hle.2 (x := ψ) (y := ⟨ψ, hle.1 ψ.2⟩) rfl]
  exact hψ

end RealPotential

/-- The remark of Sec. 5 for every continuous potential, whatever its growth or sign. -/
theorem continuous_schrodinger_only_on_domain {V : ℝ → ℝ} (hV : Continuous V) :
    (∃ H, schrodingerHamiltonian V ≤ H ∧ IsSelfAdjoint H) ∧
      ∀ H (hH : IsSelfAdjoint H), schrodingerHamiltonian V ≤ H →
        H.domain ≠ ⊤ ∧ SolvesSchrodinger 1 H (schrodingerPropagator one_ne_zero hH) ∧
        ∀ ψ ∉ H.domain, ∀ t, ¬ DifferentiableAt ℝ
          (fun s => schrodingerPropagator one_ne_zero hH s ψ) t :=
  realPotential_schrodinger_only_on_domain hV.measurable
    ((hV.pow 2).locallyIntegrable.locallyIntegrableOn _) isOpen_univ (by simp)

/-- The remark of Sec. 5 for every measurable potential that is continuous off `0`, however
singular at `0`, such as `±1/x²`. -/
theorem continuousOn_schrodinger_only_on_domain {V : ℝ → ℝ} (hV : Measurable V)
    (hc : ContinuousOn V {0}ᶜ) :
    (∃ H, schrodingerHamiltonian V ≤ H ∧ IsSelfAdjoint H) ∧
      ∀ H (hH : IsSelfAdjoint H), schrodingerHamiltonian V ≤ H →
        H.domain ≠ ⊤ ∧ SolvesSchrodinger 1 H (schrodingerPropagator one_ne_zero hH) ∧
        ∀ ψ ∉ H.domain, ∀ t, ¬ DifferentiableAt ℝ
          (fun s => schrodingerPropagator one_ne_zero hH s ψ) t :=
  realPotential_schrodinger_only_on_domain hV
    ((hc.pow 2).locallyIntegrableOn (measurableSet_singleton 0).compl) isOpen_compl_singleton
    (by simp)

end HilbertUnphysicality
