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
* `born_nlMap`      eq. (6): the Born rule is preserved; by `born_smul` this holds for every map
  that keeps each ray, so it does not depend on the choice of phase;
* `nlHomeomorph`    `m` is a homeomorphism of `H`, with inverse the map for `-θ`;
* `contDiffAt_nlMap` `m` is smooth away from `0`;
* `not_differentiableAt_nlMap_zero`  `m` is *not* differentiable at `0`, so the brief's
  remark that `m` is a diffeomorphism of `H` holds only on `H ∖ {0}`.

Theorem 1 in a precise form. Carrying the structure of `H` over along `m` gives `Twisted θ`, the
brief's `m(H)`, on the same carrier:
* `toTwisted_smul`, `born_toTwisted`   the same scalar multiplication, so the same rays, and the
  same Born rule;
* `not_map_add_toTwisted`   a different addition;
* `twistedIsometry`   `m` is a linear isometry `H ≃ₗᵢ m(H)`, so the brief's `H ≢ m(H)` is false;
* `exists_second_linear_structure`   the four together: the linear structure of `H` is not
  fixed by the rays and the Born rule, though it is fixed up to isomorphism;
* `map_add_of_map_smul`   in dimension one every map that commutes with scalars is additive, so
  the statement needs `dim H ≥ 2`.
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

/-- The Born rule `p(v | w) = ⟨w|v⟩⟨v|w⟩ / (⟨v|v⟩⟨w|w⟩)`, on any complex inner product space. -/
def born {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v w : E) : ℝ :=
  ‖inner ℂ v w‖ ^ 2 / (‖v‖ ^ 2 * ‖w‖ ^ 2)

/-- The Born rule only sees rays: `p(c v | d w) = p(v | w)` for `c, d ≠ 0`. So every map that
sends each vector into its own ray preserves the Born rule. -/
lemma born_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {c d : ℂ}
    (hc : c ≠ 0) (hd : d ≠ 0) (v w : E) : born (c • v) (d • w) = born v w := by
  have h : ‖c‖ ^ 2 * ‖d‖ ^ 2 ≠ 0 := by positivity
  simp only [born, inner_smul_left, inner_smul_right, norm_mul, RCLike.norm_conj, norm_smul,
    mul_pow]
  rw [← mul_div_mul_left (‖inner ℂ v w‖ ^ 2) (‖v‖ ^ 2 * ‖w‖ ^ 2) h]
  ring

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

/-- Eq. (6): the Born rule is preserved. This needs only that `m` keeps each ray. -/
theorem born_nlMap (θ : ℝ) (v w : H) : born (nlMap θ v) (nlMap θ w) = born v w :=
  born_smul (exp_ne_zero _) (exp_ne_zero _) v w

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

/-! ### A second linear structure with the same rays and Born rule -/

/-- The brief's `m(H)`: the carrier of `H`, with the vector space structure and the inner product
carried over along `m`. Scalar multiplication, rays and the Born rule are those of `H`; addition
is not. -/
def Twisted (_θ : ℝ) : Type := H

/-- The identity of the carrier, from `H` to `Twisted θ`. -/
def toTwisted (θ : ℝ) : H ≃ Twisted θ := Equiv.refl H

/-- `m⁻¹`, from `Twisted θ` to `H`. The structure of `Twisted θ` is carried over along it. -/
def twistedEquiv (θ : ℝ) : Twisted θ ≃ H :=
  (toTwisted θ).symm.trans (nlHomeomorph θ).symm.toEquiv

instance (θ : ℝ) : AddCommGroup (Twisted θ) := (twistedEquiv θ).addCommGroup

instance (θ : ℝ) : Module ℂ (Twisted θ) := (twistedEquiv θ).addEquiv.module ℂ

instance (θ : ℝ) : InnerProductSpace.Core ℂ (Twisted θ) where
  inner a b := inner ℂ (twistedEquiv θ a) (twistedEquiv θ b)
  conj_inner_symm _ _ := inner_conj_symm _ _
  re_inner_nonneg _ := inner_self_nonneg
  add_left a b c := by
    show inner ℂ (twistedEquiv θ ((twistedEquiv θ).symm _)) _ = _
    rw [Equiv.apply_symm_apply, inner_add_left]
    rfl
  smul_left a b r := by
    show inner ℂ (twistedEquiv θ ((twistedEquiv θ).symm _)) _ = _
    rw [Equiv.apply_symm_apply, inner_smul_left]
    rfl
  definite a h := by
    rw [← (twistedEquiv θ).symm_apply_apply a, inner_self_eq_zero.mp h]
    rfl

instance (θ : ℝ) : NormedAddCommGroup (Twisted θ) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance (θ : ℝ) : InnerProductSpace ℂ (Twisted θ) := InnerProductSpace.ofCore _

lemma nlMap_nlMap_neg (θ : ℝ) (v : H) : nlMap θ (nlMap (-θ) v) = v := by
  simpa using nlMap_neg_nlMap (-θ) v

lemma toTwisted_add (θ : ℝ) (v w : H) :
    toTwisted θ v + toTwisted θ w = toTwisted θ (nlMap θ (nlMap (-θ) v + nlMap (-θ) w)) := rfl

lemma inner_toTwisted (θ : ℝ) (v w : H) :
    inner ℂ (toTwisted θ v) (toTwisted θ w) = inner ℂ (nlMap (-θ) v) (nlMap (-θ) w) := rfl

/-- Scalar multiplication on `Twisted θ` is that of `H`, by eq. (3); so are the rays. -/
theorem toTwisted_smul (θ : ℝ) (k : ℂ) (v : H) : toTwisted θ (k • v) = k • toTwisted θ v := by
  show _ = toTwisted θ (nlMap θ (k • nlMap (-θ) v))
  rw [nlMap_smul, nlMap_nlMap_neg]

/-- `m` is a linear isometry from `H` onto `Twisted θ`: as vector spaces, `H ≅ m(H)`. -/
def twistedIsometry (θ : ℝ) : H ≃ₗᵢ[ℂ] Twisted θ :=
  ((twistedEquiv θ).addEquiv.linearEquiv ℂ).symm.isometryOfInner fun v w => by
    show inner ℂ (twistedEquiv θ ((twistedEquiv θ).symm v))
      (twistedEquiv θ ((twistedEquiv θ).symm w)) = _
    simp only [Equiv.apply_symm_apply]

lemma twistedIsometry_apply (θ : ℝ) (v : H) : twistedIsometry θ v = toTwisted θ (nlMap θ v) :=
  rfl

lemma norm_toTwisted (θ : ℝ) (v : H) : ‖toTwisted θ v‖ = ‖v‖ :=
  calc ‖toTwisted θ v‖ = ‖twistedIsometry θ (nlMap (-θ) v)‖ := by
        rw [twistedIsometry_apply, nlMap_nlMap_neg]
    _ = ‖v‖ := by rw [LinearIsometryEquiv.norm_map, norm_nlMap]

/-- The Born rule of `Twisted θ` is that of `H`. -/
theorem born_toTwisted (θ : ℝ) (v w : H) : born (toTwisted θ v) (toTwisted θ w) = born v w :=
  calc born (toTwisted θ v) (toTwisted θ w) = born (nlMap (-θ) v) (nlMap (-θ) w) := by
        simp only [born, inner_toTwisted, norm_toTwisted, norm_nlMap]
    _ = born v w := born_nlMap _ v w

/-- Addition on `Twisted θ` is not that of `H`, by eq. (4). -/
theorem not_map_add_toTwisted {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ¬ ∀ v w : H, toTwisted θ (v + w) = toTwisted θ v + toTwisted θ w := by
  intro h
  have h' := h (nlMap θ zp) (nlMap θ zm)
  rw [toTwisted_add, nlMap_neg_nlMap, nlMap_neg_nlMap] at h'
  exact nlMap_not_add hθ ((toTwisted θ).injective h').symm

/-- Theorem 1, as "the linear structure is not fixed by the state space and the Born rule": the
carrier of `H` has a second complex inner product space structure, `Twisted θ`, with the same
scalar multiplication (so the same rays) and the same Born rule, but a different addition. The
two structures are isomorphic, so `H ≅ m(H)` as inner product spaces. -/
theorem exists_second_linear_structure {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    (∀ (k : ℂ) (v : H), toTwisted θ (k • v) = k • toTwisted θ v) ∧
    (∀ v w : H, born (toTwisted θ v) (toTwisted θ w) = born v w) ∧
    ¬ (∀ v w : H, toTwisted θ (v + w) = toTwisted θ v + toTwisted θ w) ∧
    Nonempty (H ≃ₗᵢ[ℂ] Twisted θ) :=
  ⟨toTwisted_smul θ, born_toTwisted θ, not_map_add_toTwisted hθ, ⟨twistedIsometry θ⟩⟩

/-- In dimension one there is no second linear structure: every map that commutes with scalar
multiplication is additive, so carrying the structure along it changes nothing. -/
theorem map_add_of_map_smul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (hE : Module.finrank ℂ E = 1) {f : E → E} (hf : ∀ (k : ℂ) v, f (k • v) = k • f v)
    (v w : E) : f (v + w) = f v + f w := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
  obtain ⟨b, hb⟩ := exists_ne (0 : E)
  have hspan := (finrank_eq_one_iff_of_nonzero' b hb).mp hE
  obtain ⟨c, rfl⟩ := hspan v
  obtain ⟨d, rfl⟩ := hspan w
  rw [← add_smul, hf, hf, hf, add_smul]

end NonLinearQuantum
