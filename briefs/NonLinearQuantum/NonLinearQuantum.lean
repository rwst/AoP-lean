/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Non-linear representations in quantum mechanics.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

The brief exhibits a non-linear map `m : ℂ² → ℂ²` that sends every ray to itself and
preserves the Born rule, so the linear structure of `H` is not fixed by the physics.

Formalized here (two-state system, `H = EuclideanSpace ℂ (Fin 2)`, `|z⁺⟩ = e₀`, `|z⁻⟩ = e₁`):
* `nlMap_smul`      eq. (3): `m (k • v) = k • m v` for every `k : ℂ`;
* `nlMap_mem_ray`   each ray is mapped to itself, by a phase factor;
* `nlMap_not_add`   eq. (4): `m` is not additive (so not linear) for `θ ∈ (0, 2π)`;
* `inner_nlMap`     eq. (5): how the inner product changes;
* `born_nlMap`      eq. (6): the Born rule is preserved;
* `nlHomeomorph`    `m` is a homeomorphism of `H`, with inverse the map for `-θ`;
* `contDiffAt_nlMap` `m` is smooth away from `0`;
* `not_differentiableAt_nlMap_zero`  `m` is *not* differentiable at `0`, so the brief's
  remark that `m` is a diffeomorphism of `H` holds only on `H ∖ {0}`.
-/
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Complex ComplexConjugate

@[expose] public noncomputable section

namespace NonLinearQuantum

/-- The two-state Hilbert space `ℂ²`. -/
abbrev H := EuclideanSpace ℂ (Fin 2)

/-- `|z⁺⟩`. -/
abbrev zp : H := EuclideanSpace.single 0 1

/-- `|z⁻⟩`. -/
abbrev zm : H := EuclideanSpace.single 1 1

/-- The Born rule `p(v | w) = ⟨w|v⟩⟨v|w⟩ / (⟨v|v⟩⟨w|w⟩)`. -/
def born (v w : H) : ℝ := ‖inner ℂ v w‖ ^ 2 / (‖v‖ ^ 2 * ‖w‖ ^ 2)

/-- `p(z⁺ | v) = |c₊|² / (|c₊|² + |c₋|²)`; it is `0` at `v = 0`. -/
def probUp (v : H) : ℝ := ‖v 0‖ ^ 2 / ‖v‖ ^ 2

/-- The phase factor `exp (iθ p(z⁺ | v))`. -/
def phase (θ : ℝ) (v : H) : ℂ := exp ((θ * probUp v : ℝ) * I)

/-- The brief's map, eq. (2). At `v = 0` it gives `0` without a case split. -/
def nlMap (θ : ℝ) (v : H) : H := phase θ v • v

lemma norm_phase (θ : ℝ) (v : H) : ‖phase θ v‖ = 1 := norm_exp_ofReal_mul_I _

lemma probUp_smul {k : ℂ} (hk : k ≠ 0) (v : H) : probUp (k • v) = probUp v := by
  have hk' : ‖k‖ ^ 2 ≠ 0 := by positivity
  simp only [probUp, PiLp.smul_apply, smul_eq_mul, norm_mul, norm_smul, mul_pow]
  rw [mul_div_mul_left _ _ hk']

lemma probUp_phase_smul (θ : ℝ) (v : H) : probUp (phase θ v • v) = probUp v :=
  probUp_smul (fun h => by simpa [h] using norm_phase θ v) v

lemma phase_phase_smul (θ θ' : ℝ) (v : H) : phase θ' (phase θ v • v) = phase θ' v := by
  rw [phase, probUp_phase_smul, phase]

/-- Eq. (3): rays are mapped to rays, `m (k v) = k m(v)`. -/
theorem nlMap_smul (θ : ℝ) (k : ℂ) (v : H) : nlMap θ (k • v) = k • nlMap θ v := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [nlMap]
  · simp only [nlMap, phase, probUp_smul hk, smul_comm k]

/-- Each ray is mapped to itself: `m v` differs from `v` by a phase. -/
theorem nlMap_mem_ray (θ : ℝ) (v : H) : ∃ c : ℂ, ‖c‖ = 1 ∧ nlMap θ v = c • v :=
  ⟨phase θ v, norm_phase θ v, rfl⟩

lemma norm_nlMap (θ : ℝ) (v : H) : ‖nlMap θ v‖ = ‖v‖ := by
  simp [nlMap, norm_smul, norm_phase]

/-- Eq. (5): `⟨m v | m w⟩ = e^{-iθ p(z⁺|v)} e^{iθ p(z⁺|w)} ⟨v|w⟩`. -/
theorem inner_nlMap (θ : ℝ) (v w : H) :
    inner ℂ (nlMap θ v) (nlMap θ w) = conj (phase θ v) * phase θ w * inner ℂ v w := by
  simp only [nlMap, inner_smul_left, inner_smul_right]
  ring

/-- Eq. (6): the Born rule is preserved. -/
theorem born_nlMap (θ : ℝ) (v w : H) : born (nlMap θ v) (nlMap θ w) = born v w := by
  simp only [born, inner_nlMap, norm_nlMap, norm_mul, RCLike.norm_conj, norm_phase, one_mul]

lemma probUp_zp : probUp zp = 1 := by simp [probUp]

lemma probUp_zm : probUp zm = 0 := by simp [probUp]

lemma probUp_zp_add_zm : probUp (zp + zm) = 1 / 2 := by
  simp [probUp, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  norm_num

/-- Eq. (4): `m(|z⁺⟩ + |z⁻⟩) ≠ m(|z⁺⟩) + m(|z⁻⟩)` for `θ ∈ (0, 2π)`. -/
theorem nlMap_not_add {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    nlMap θ (zp + zm) ≠ nlMap θ zp + nlMap θ zm := by
  intro h
  have h1 := congrArg (· 1) h
  simp only [nlMap, phase, probUp_zp, probUp_zm, probUp_zp_add_zm, PiLp.add_apply,
    PiLp.smul_apply, PiLp.single_apply] at h1
  norm_num at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hn' : θ / 2 = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hlo : (0 : ℝ) < n := by
    by_contra hc
    nlinarith [hθ.1, Real.pi_pos, (show (n : ℝ) ≤ 0 by linarith)]
  have hhi : (n : ℝ) < 1 := by nlinarith [hθ.2, Real.pi_pos]
  have : (0 : ℤ) < n := by exact_mod_cast hlo
  have : n < (1 : ℤ) := by exact_mod_cast hhi
  omega

/-- `m` is not linear. -/
theorem not_isLinearMap_nlMap {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ¬ IsLinearMap ℂ (nlMap θ) := fun h => nlMap_not_add hθ (h.map_add _ _)

/-- The map for `-θ` undoes the map for `θ`. -/
lemma nlMap_neg_nlMap (θ : ℝ) (v : H) : nlMap (-θ) (nlMap θ v) = v := by
  rw [nlMap, nlMap, phase_phase_smul]
  simp only [smul_smul, phase, ← Complex.exp_add]
  push_cast
  simp

lemma probUp_contDiffAt {v : H} (hv : v ≠ 0) : ContDiffAt ℝ ⊤ probUp v := by
  have h0 : ContDiff ℝ ⊤ fun x : H => ‖x 0‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) 0).contDiff
  exact h0.contDiffAt.div (contDiff_norm_sq ℝ).contDiffAt (by positivity)

/-- `m` is smooth on `H ∖ {0}`. -/
theorem contDiffAt_nlMap (θ : ℝ) {v : H} (hv : v ≠ 0) : ContDiffAt ℝ ⊤ (nlMap θ) v := by
  have hp : ContDiffAt ℝ ⊤ (phase θ) v :=
    Complex.contDiff_exp.contDiffAt.comp v
      (((ofRealCLM.contDiff.contDiffAt.comp v
        (contDiffAt_const.mul (probUp_contDiffAt hv)))).mul contDiffAt_const)
  exact hp.smul contDiffAt_id

lemma continuous_nlMap (θ : ℝ) : Continuous (nlMap θ) := by
  refine continuous_iff_continuousAt.mpr fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · have h0 : nlMap θ 0 = 0 := by simp [nlMap]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_nlMap] using (continuous_norm.tendsto (0 : H))
  · exact (contDiffAt_nlMap θ hv).continuousAt

/-- `m` is a homeomorphism of `H`. -/
def nlHomeomorph (θ : ℝ) : H ≃ₜ H where
  toFun := nlMap θ
  invFun := nlMap (-θ)
  left_inv := nlMap_neg_nlMap θ
  right_inv v := by simpa using nlMap_neg_nlMap (-θ) v
  continuous_toFun := continuous_nlMap θ
  continuous_invFun := continuous_nlMap (-θ)

/-- `m` is not differentiable at `0`. Along each real line, `m (t • v) = t • m v`, so a
derivative at `0` would have to be `m` itself, which is not additive. -/
theorem not_differentiableAt_nlMap_zero {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ¬ DifferentiableAt ℝ (nlMap θ) 0 := by
  intro hd
  have key : ∀ v : H, fderiv ℝ (nlMap θ) 0 v = nlMap θ v := by
    intro v
    have h0 : HasFDerivAt (nlMap θ) (fderiv ℝ (nlMap θ) 0) ((0 : ℝ) • v) := by
      simpa using hd.hasFDerivAt
    have hline := h0.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const v)
    rw [one_smul] at hline
    refine hline.unique ?_
    convert (hasDerivAt_id (0 : ℝ)).smul_const (nlMap θ v) using 1
    · funext t
      simp only [Function.comp_apply, id]
      rw [← Complex.coe_smul, nlMap_smul, Complex.coe_smul]
    · simp
  apply nlMap_not_add hθ
  rw [← key, ← key, ← key, map_add]

/-- Theorem 1 of the brief, mathematical content: there is a homeomorphism of `H` that maps
every ray to itself, preserves the Born rule and is not additive. -/
theorem exists_nonlinear_born_preserving {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ∃ m : H ≃ₜ H,
      (∀ (k : ℂ) v, m (k • v) = k • m v) ∧
      (∀ v, ∃ c : ℂ, ‖c‖ = 1 ∧ m v = c • v) ∧
      (∀ v w, born (m v) (m w) = born v w) ∧
      ¬ (∀ v w, m (v + w) = m v + m w) :=
  ⟨nlHomeomorph θ, nlMap_smul θ, nlMap_mem_ray θ, born_nlMap θ,
    fun h => nlMap_not_add hθ (h _ _)⟩

end NonLinearQuantum
