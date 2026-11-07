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

The brief exhibits a non-linear bijection `m` of a two-dimensional Hilbert space that sends every
ray to itself and preserves the Fubini–Study distance, hence the Born rule, and argues from it
that linearity is a choice of representation (Theorem 4, checked by reading).

Formalized here, on any complex inner product space `E` with an orthonormal pair `v, w` (the
brief's `H` is the case `dim E = 2`); `m = nlMap v θ`, `m x = exp (iθ p(v | x)) • x`:
* `nlMap_smul_add_smul`, `eq_nlMap`   eq. (2); in dimension two it determines `m`;
* `nlMap_spec`   Proposition 1: `m` is bijective, with inverse the map for `-θ`, sends each ray
  to itself (`mk_nlMap`), preserves the Fubini–Study distance (`fsDist_nlMap`), and
  `m (v + w) ≠ m v + m w` for `θ ∈ (0, 2π)` (`nlMap_not_add`);
* `swapOp`, `isSelfAdjoint_swapOp`, `swapOp_mem_unitary`, `not_map_add_transport_swapOp`
  Corollary 3: the swap `A (a v + b w) = b v + a w` is self-adjoint and unitary, but
  `m ∘ A ∘ m⁻¹` is not additive;
* `born_eq_cos_sq_fsDist`   the Born rule is the squared cosine of the Fubini–Study distance
  (Theorem 4, proof);
* `inner_nlMap_ne`   `m` does not preserve the inner product (Conclusion);
* `not_map_add_transport_projOp`   the projector `|v⟩⟨v|` moved over through `m` is not
  additive either, so density operators are not literally "left unchanged" (Theorem 4, proof).

The structure of `E` carried over along `m` (the brief's `m(H)`):
* `toTwisted_smul`, `born_toTwisted`   the same scalar multiplication, so the same rays, and the
  same Born rule;
* `not_map_add_toTwisted`   a different addition;
* `twistedIsometry`   `m` is a linear isometry `E ≃ₗᵢ m(E)`;
* `exists_second_linear_structure`   the four together;
* `map_add_of_map_smul`   in dimension one every map that commutes with scalars is additive, so
  an orthonormal pair, i.e. `dim E ≥ 2`, is needed.

Also: `nlHomeomorph` (`m` is a homeomorphism), `contDiffAt_nlMap` (smooth away from `0`) and
`not_differentiableAt_nlMap_zero` (not differentiable at `0`).
-/
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.LinearAlgebra.Projectivization.Basic

open Complex ComplexConjugate

@[expose] public noncomputable section

namespace NonLinearQuantum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ### The Born rule and the Fubini–Study distance -/

/-- The Born rule `p(x | y) = ⟨y|x⟩⟨x|y⟩ / (⟨x|x⟩⟨y|y⟩)`. -/
def born (x y : E) : ℝ :=
  ‖inner ℂ x y‖ ^ 2 / (‖x‖ ^ 2 * ‖y‖ ^ 2)

/-- The Born rule only sees rays: `p(c x | d y) = p(x | y)` for `c, d ≠ 0`. So every map that
sends each vector into its own ray preserves the Born rule. -/
lemma born_smul {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (x y : E) :
    born (c • x) (d • y) = born x y := by
  have h : ‖c‖ ^ 2 * ‖d‖ ^ 2 ≠ 0 := by positivity
  simp only [born, inner_smul_left, inner_smul_right, norm_mul, RCLike.norm_conj, norm_smul,
    mul_pow]
  rw [← mul_div_mul_left (‖inner ℂ x y‖ ^ 2) (‖x‖ ^ 2 * ‖y‖ ^ 2) h]
  ring

lemma born_smul_right {k : ℂ} (hk : k ≠ 0) (x y : E) : born x (k • y) = born x y := by
  simpa using born_smul one_ne_zero hk x y

/-- The Fubini–Study geodesic distance `arccos (|⟨x, y⟩| / (‖x‖ ‖y‖))`. -/
def fsDist (x y : E) : ℝ :=
  Real.arccos (‖inner ℂ x y‖ / (‖x‖ * ‖y‖))

/-- The Born rule is the squared cosine of the Fubini–Study distance. -/
theorem born_eq_cos_sq_fsDist (x y : E) : born x y = Real.cos (fsDist x y) ^ 2 := by
  have h0 : 0 ≤ ‖inner ℂ x y‖ / (‖x‖ * ‖y‖) := by positivity
  have h1 : ‖inner ℂ x y‖ / (‖x‖ * ‖y‖) ≤ 1 :=
    div_le_one_of_le₀ (norm_inner_le_norm x y) (by positivity)
  rw [fsDist, Real.cos_arccos (by linarith) h1, born, div_pow, mul_pow]

/-! ### The map -/

variable (v : E)

/-- The phase factor `exp (iθ p(v | x))`. -/
def phase (θ : ℝ) (x : E) : ℂ := exp ((θ * born v x : ℝ) * I)

/-- The brief's map `m`, eq. (2), with `r(x) = p(v | x)`. At `x = 0` it gives `0` without a case
split. -/
def nlMap (θ : ℝ) (x : E) : E := phase v θ x • x

lemma norm_phase (θ : ℝ) (x : E) : ‖phase v θ x‖ = 1 := norm_exp_ofReal_mul_I _

lemma phase_smul {k : ℂ} (hk : k ≠ 0) (θ : ℝ) (x : E) : phase v θ (k • x) = phase v θ x := by
  rw [phase, born_smul_right hk, phase]

lemma phase_ne_zero (θ : ℝ) (x : E) : phase v θ x ≠ 0 := exp_ne_zero _

lemma phase_phase_smul (θ θ' : ℝ) (x : E) : phase v θ' (phase v θ x • x) = phase v θ' x :=
  phase_smul v (phase_ne_zero v θ x) θ' x

/-- `m (k x) = k m(x)` for every `k : ℂ`. -/
theorem nlMap_smul (θ : ℝ) (k : ℂ) (x : E) : nlMap v θ (k • x) = k • nlMap v θ x := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [nlMap]
  · simp only [nlMap, phase_smul v hk, smul_comm k]

/-- Each ray is mapped to itself: `m x` differs from `x` by a phase. -/
theorem nlMap_mem_ray (θ : ℝ) (x : E) : ∃ c : ℂ, ‖c‖ = 1 ∧ nlMap v θ x = c • x :=
  ⟨phase v θ x, norm_phase v θ x, rfl⟩

lemma norm_nlMap (θ : ℝ) (x : E) : ‖nlMap v θ x‖ = ‖x‖ := by
  simp [nlMap, norm_smul, norm_phase]

lemma nlMap_ne_zero (θ : ℝ) {x : E} (hx : x ≠ 0) : nlMap v θ x ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_nlMap, norm_ne_zero_iff]
  exact hx

/-- `[m(x)] = [x]` in the projective space. -/
theorem mk_nlMap (θ : ℝ) {x : E} (hx : x ≠ 0) :
    Projectivization.mk ℂ (nlMap v θ x) (nlMap_ne_zero v θ hx) = Projectivization.mk ℂ x hx :=
  (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨phase v θ x, rfl⟩

/-- `⟨m x, m y⟩ = e^{-iθ r(x)} e^{iθ r(y)} ⟨x, y⟩`. -/
theorem inner_nlMap (θ : ℝ) (x y : E) :
    inner ℂ (nlMap v θ x) (nlMap v θ y) = conj (phase v θ x) * phase v θ y * inner ℂ x y := by
  simp only [nlMap, inner_smul_left, inner_smul_right]
  ring

/-- `m` preserves the Fubini–Study distance. -/
theorem fsDist_nlMap (θ : ℝ) (x y : E) : fsDist (nlMap v θ x) (nlMap v θ y) = fsDist x y := by
  simp only [fsDist, inner_nlMap, norm_nlMap, norm_mul, RCLike.norm_conj, norm_phase, one_mul]

/-- `m` preserves the Born rule. This needs only that `m` keeps each ray. -/
theorem born_nlMap (θ : ℝ) (x y : E) : born (nlMap v θ x) (nlMap v θ y) = born x y :=
  born_smul (exp_ne_zero _) (exp_ne_zero _) x y

/-- The map for `-θ` undoes the map for `θ`. -/
lemma nlMap_neg_nlMap (θ : ℝ) (x : E) : nlMap v (-θ) (nlMap v θ x) = x := by
  rw [nlMap, nlMap, phase_phase_smul, smul_smul, phase, phase, ← Complex.exp_add]
  have h : ((-θ * born v x : ℝ) : ℂ) * I + ((θ * born v x : ℝ) : ℂ) * I = 0 := by
    push_cast
    ring
  rw [h, Complex.exp_zero, one_smul]

lemma nlMap_nlMap_neg (θ : ℝ) (x : E) : nlMap v θ (nlMap v (-θ) x) = x := by
  simpa using nlMap_neg_nlMap v (-θ) x

lemma born_contDiffAt {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ⊤ (born v) x := by
  rcases eq_or_ne v 0 with rfl | hv
  · have h : born (0 : E) = fun _ => 0 := by
      funext y
      simp [born]
    rw [h]
    exact contDiffAt_const
  let _ : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have hn : ContDiff ℝ ⊤ fun y : E => ‖inner ℂ v y‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp ((innerSL ℂ v).restrictScalars ℝ).contDiff
  exact hn.contDiffAt.div (contDiff_const.mul (contDiff_norm_sq ℝ)).contDiffAt (by positivity)

/-- `m` is smooth on `E ∖ {0}`. -/
theorem contDiffAt_nlMap (θ : ℝ) {x : E} (hx : x ≠ 0) : ContDiffAt ℝ ⊤ (nlMap v θ) x := by
  have hp : ContDiffAt ℝ ⊤ (phase v θ) x :=
    Complex.contDiff_exp.contDiffAt.comp x
      (((ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul (born_contDiffAt v hx)))).mul contDiffAt_const)
  exact hp.smul contDiffAt_id

lemma continuous_nlMap (θ : ℝ) : Continuous (nlMap v θ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : nlMap v θ 0 = 0 := by simp [nlMap]
    rw [ContinuousAt, h0, tendsto_zero_iff_norm_tendsto_zero]
    simpa [norm_nlMap] using (continuous_norm.tendsto (0 : E))
  · exact (contDiffAt_nlMap v θ hx).continuousAt

/-- `m` is a homeomorphism of `E`, with inverse the map for `-θ`. -/
def nlHomeomorph (θ : ℝ) : E ≃ₜ E where
  toFun := nlMap v θ
  invFun := nlMap v (-θ)
  left_inv := nlMap_neg_nlMap v θ
  right_inv := nlMap_nlMap_neg v θ
  continuous_toFun := continuous_nlMap v θ
  continuous_invFun := continuous_nlMap v (-θ)

/-! ### An orthonormal pair -/

variable {v} {w : E}

lemma norm_left (hvw : Orthonormal ℂ ![v, w]) : ‖v‖ = 1 := by simpa using hvw.1 0

lemma norm_right (hvw : Orthonormal ℂ ![v, w]) : ‖w‖ = 1 := by simpa using hvw.1 1

lemma inner_left_right (hvw : Orthonormal ℂ ![v, w]) : inner ℂ v w = 0 := by
  simpa using hvw.2 (show (0 : Fin 2) ≠ 1 by decide)

lemma inner_right_left (hvw : Orthonormal ℂ ![v, w]) : inner ℂ w v = 0 := by
  rw [← inner_conj_symm, inner_left_right hvw, map_zero]

lemma inner_left_left (hvw : Orthonormal ℂ ![v, w]) : inner ℂ v v = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_left hvw]
  simp

lemma inner_right_right (hvw : Orthonormal ℂ ![v, w]) : inner ℂ w w = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_right hvw]
  simp

lemma norm_smul_add_smul_sq (hvw : Orthonormal ℂ ![v, w]) (a b : ℂ) :
    ‖a • v + b • w‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (a • v) (b • w)
    (by simp [inner_smul_left, inner_smul_right, inner_left_right hvw])
  simp only [norm_smul, norm_left hvw, norm_right hvw, mul_one] at h
  rw [sq, sq, sq]
  exact h

/-- `r(a v + b w) = |a|² / (|a|² + |b|²)`. -/
lemma born_smul_add_smul (hvw : Orthonormal ℂ ![v, w]) (a b : ℂ) :
    born v (a • v + b • w) = ‖a‖ ^ 2 / (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  simp [born, inner_add_right, inner_smul_right, inner_left_right hvw, norm_left hvw,
    norm_smul_add_smul_sq hvw]

lemma born_left (hvw : Orthonormal ℂ ![v, w]) : born v v = 1 := by
  simpa using born_smul_add_smul hvw 1 0

lemma born_right (hvw : Orthonormal ℂ ![v, w]) : born v w = 0 := by
  simpa using born_smul_add_smul hvw 0 1

lemma born_add (hvw : Orthonormal ℂ ![v, w]) : born v (v + w) = 1 / 2 := by
  have h := born_smul_add_smul hvw 1 1
  simp only [one_smul, norm_one] at h
  rw [h]
  norm_num

/-- Eq. (2): `m(a v + b w) = exp (iθ |a|² / (|a|² + |b|²)) (a v + b w)`. -/
theorem nlMap_smul_add_smul (hvw : Orthonormal ℂ ![v, w]) (θ : ℝ) (a b : ℂ) :
    nlMap v θ (a • v + b • w) =
      exp ((θ * (‖a‖ ^ 2 / (‖a‖ ^ 2 + ‖b‖ ^ 2)) : ℝ) * I) • (a • v + b • w) := by
  rw [nlMap, phase, born_smul_add_smul hvw]

/-- In dimension two, `x = ⟨v, x⟩ v + ⟨w, x⟩ w`. -/
lemma eq_inner_smul_add_inner_smul (hE : Module.finrank ℂ E = 2)
    (hvw : Orthonormal ℂ ![v, w]) (x : E) : x = inner ℂ v x • v + inner ℂ w x • w := by
  set b := basisOfOrthonormalOfCardEqFinrank hvw (by simp [hE])
  have hb : ⇑b = ![v, w] := coe_basisOfOrthonormalOfCardEqFinrank hvw _
  obtain ⟨c, d, rfl⟩ : ∃ c d : ℂ, x = c • v + d • w :=
    ⟨b.repr x 0, b.repr x 1, by
      conv_lhs => rw [← b.sum_repr x]
      simp [Fin.sum_univ_two, hb]⟩
  simp [inner_add_right, inner_smul_right, inner_left_right hvw, inner_right_left hvw,
    norm_left hvw, norm_right hvw]

/-- In dimension two, eq. (2) determines `m`. -/
theorem eq_nlMap (hE : Module.finrank ℂ E = 2) (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    {m : E → E}
    (hm : ∀ a b : ℂ, m (a • v + b • w) =
      exp ((θ * (‖a‖ ^ 2 / (‖a‖ ^ 2 + ‖b‖ ^ 2)) : ℝ) * I) • (a • v + b • w)) :
    m = nlMap v θ := by
  funext x
  rw [eq_inner_smul_add_inner_smul hE hvw x, hm, nlMap_smul_add_smul hvw]

lemma nlMap_left (hvw : Orthonormal ℂ ![v, w]) (θ : ℝ) : nlMap v θ v = exp (θ * I) • v := by
  simp [nlMap, phase, born_left hvw]

lemma nlMap_right (hvw : Orthonormal ℂ ![v, w]) (θ : ℝ) : nlMap v θ w = w := by
  simp [nlMap, phase, born_right hvw]

lemma nlMap_add (hvw : Orthonormal ℂ ![v, w]) (θ : ℝ) :
    nlMap v θ (v + w) = exp ((θ / 2 : ℝ) * I) • (v + w) := by
  rw [nlMap, phase, born_add hvw, show θ * (1 / 2) = θ / 2 by ring]

lemma exp_mul_I_ne_one {t : ℝ} (h0 : 0 < t) (h1 : t < 2 * Real.pi) : exp (t * I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hn' : t = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hlo : (0 : ℝ) < n := by
    by_contra hc
    nlinarith [Real.pi_pos, (show (n : ℝ) ≤ 0 by linarith)]
  have hhi : (n : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have : (0 : ℤ) < n := by exact_mod_cast hlo
  have : n < (1 : ℤ) := by exact_mod_cast hhi
  omega

lemma exp_half_mul_I_ne_one {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    exp ((θ / 2 : ℝ) * I) ≠ 1 :=
  exp_mul_I_ne_one (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `m(v + w) ≠ m(v) + m(w)` for `θ ∈ (0, 2π)`. -/
theorem nlMap_not_add (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) : nlMap v θ (v + w) ≠ nlMap v θ v + nlMap v θ w := by
  rw [nlMap_add hvw, nlMap_left hvw, nlMap_right hvw]
  intro h
  have h1 := congrArg (inner ℂ w) h
  simp only [inner_add_right, inner_smul_right, inner_right_left hvw, inner_right_right hvw,
    mul_zero, zero_add, mul_one] at h1
  exact exp_half_mul_I_ne_one hθ h1

/-- `m` is not linear. -/
theorem not_isLinearMap_nlMap (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) : ¬ IsLinearMap ℂ (nlMap v θ) :=
  fun h => nlMap_not_add hvw hθ (h.map_add _ _)

/-- Proposition 1: `m` is bijective, with inverse the map for `-θ`, is not additive, sends each
ray to itself, and preserves the Fubini–Study distance. -/
theorem nlMap_spec (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    Function.Bijective (nlMap v θ) ∧
    nlMap v θ (v + w) ≠ nlMap v θ v + nlMap v θ w ∧
    (∀ x (hx : x ≠ 0),
      Projectivization.mk ℂ (nlMap v θ x) (nlMap_ne_zero v θ hx) = Projectivization.mk ℂ x hx) ∧
    (∀ x y, fsDist (nlMap v θ x) (nlMap v θ y) = fsDist x y) ∧
    (∀ x, nlMap v (-θ) (nlMap v θ x) = x ∧ nlMap v θ (nlMap v (-θ) x) = x) :=
  ⟨(nlHomeomorph v θ).bijective, nlMap_not_add hvw hθ, fun _ hx => mk_nlMap v θ hx,
    fsDist_nlMap v θ, fun x => ⟨nlMap_neg_nlMap v θ x, nlMap_nlMap_neg v θ x⟩⟩

/-- Conclusion: `m` does not preserve the inner product, `⟨m w, m (v + w)⟩ ≠ ⟨w, v + w⟩`. -/
theorem inner_nlMap_ne (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    inner ℂ (nlMap v θ w) (nlMap v θ (v + w)) ≠ inner ℂ w (v + w) := by
  rw [nlMap_right hvw, nlMap_add hvw, inner_smul_right]
  have h : inner ℂ w (v + w) = 1 := by
    rw [inner_add_right, inner_right_left hvw, inner_right_right hvw, zero_add]
  rw [h, mul_one]
  exact exp_half_mul_I_ne_one hθ

/-- `m` is not differentiable at `0`. Along each real line, `m (t • x) = t • m x`, so a
derivative at `0` would have to be `m` itself, which is not additive. -/
theorem not_differentiableAt_nlMap_zero (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) : ¬ DifferentiableAt ℝ (nlMap v θ) 0 := by
  intro hd
  have key : ∀ x : E, fderiv ℝ (nlMap v θ) 0 x = nlMap v θ x := by
    intro x
    have h0 : HasFDerivAt (nlMap v θ) (fderiv ℝ (nlMap v θ) 0) ((0 : ℝ) • x) := by
      simpa using hd.hasFDerivAt
    have hline := h0.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const x)
    rw [one_smul] at hline
    refine hline.unique ?_
    convert (hasDerivAt_id (0 : ℝ)).smul_const (nlMap v θ x) using 1
    · funext t
      simp only [Function.comp_apply, id]
      rw [← Complex.coe_smul, nlMap_smul, Complex.coe_smul]
    · simp
  apply nlMap_not_add hvw hθ
  rw [← key, ← key, ← key, map_add]

/-! ### Operators moved over through `m` -/

variable (v w) in
/-- The swap `A (a v + b w) = b v + a w`, as `A x = ⟨w, x⟩ v + ⟨v, x⟩ w`. -/
def swapOp : E →L[ℂ] E := (innerSL ℂ w).smulRight v + (innerSL ℂ v).smulRight w

lemma swapOp_apply (x : E) : swapOp v w x = inner ℂ w x • v + inner ℂ v x • w := rfl

lemma swapOp_left (hvw : Orthonormal ℂ ![v, w]) : swapOp v w v = w := by
  simp [swapOp_apply, inner_right_left hvw, norm_left hvw]

lemma swapOp_right (hvw : Orthonormal ℂ ![v, w]) : swapOp v w w = v := by
  simp [swapOp_apply, inner_left_right hvw, norm_right hvw]

theorem isSelfAdjoint_swapOp [CompleteSpace E] : IsSelfAdjoint (swapOp v w) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, swapOp_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem swapOp_mem_unitary [CompleteSpace E] (hE : Module.finrank ℂ E = 2)
    (hvw : Orthonormal ℂ ![v, w]) : swapOp v w ∈ unitary (E →L[ℂ] E) := by
  have hsq : swapOp v w * swapOp v w = 1 := by
    ext x
    show swapOp v w (swapOp v w x) = x
    rw [swapOp_apply x, map_add,
      map_smul, map_smul, swapOp_left hvw, swapOp_right hvw, add_comm]
    exact (eq_inner_smul_add_inner_smul hE hvw x).symm
  rw [Unitary.mem_iff, isSelfAdjoint_swapOp.star_eq, and_self]
  exact hsq

lemma transport_swapOp_left (hvw : Orthonormal ℂ ![v, w]) (θ : ℝ) :
    nlMap v θ (swapOp v w (nlMap v (-θ) v)) = exp (-θ * I) • w := by
  rw [nlMap_left hvw, map_smul, swapOp_left hvw, nlMap_smul, nlMap_right hvw]
  push_cast
  rfl

lemma transport_swapOp_right (hvw : Orthonormal ℂ ![v, w]) (θ : ℝ) :
    nlMap v θ (swapOp v w (nlMap v (-θ) w)) = exp (θ * I) • v := by
  rw [nlMap_right hvw, swapOp_right hvw, nlMap_left hvw]

lemma transport_swapOp_add (hvw : Orthonormal ℂ ![v, w]) (θ : ℝ) :
    nlMap v θ (swapOp v w (nlMap v (-θ) (v + w))) = v + w := by
  rw [nlMap_add hvw, map_smul, map_add, swapOp_left hvw, swapOp_right hvw, add_comm w,
    nlMap_smul, nlMap_add hvw, smul_smul, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

/-- Corollary 3: the swap is self-adjoint and unitary, but `m ∘ A ∘ m⁻¹` is not additive. -/
theorem not_map_add_transport_swapOp (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    nlMap v θ (swapOp v w (nlMap v (-θ) (v + w))) ≠
      nlMap v θ (swapOp v w (nlMap v (-θ) v)) + nlMap v θ (swapOp v w (nlMap v (-θ) w)) := by
  rw [transport_swapOp_add hvw, transport_swapOp_left hvw, transport_swapOp_right hvw]
  intro h
  have h1 := congrArg (inner ℂ v) h
  simp only [inner_add_right, inner_smul_right, inner_left_left hvw, inner_left_right hvw,
    mul_zero, zero_add, add_zero, mul_one] at h1
  exact exp_mul_I_ne_one hθ.1 hθ.2 h1.symm

variable (v) in
/-- The projector `|v⟩⟨v|`, `x ↦ ⟨v, x⟩ v`. -/
def projOp : E →L[ℂ] E := (innerSL ℂ v).smulRight v

lemma projOp_apply (x : E) : projOp v x = inner ℂ v x • v := rfl

/-- The pure density operator `|v⟩⟨v|` moved over through `m` is not additive. -/
theorem not_map_add_transport_projOp (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    nlMap v θ (projOp v (nlMap v (-θ) (v + w))) ≠
      nlMap v θ (projOp v (nlMap v (-θ) v)) + nlMap v θ (projOp v (nlMap v (-θ) w)) := by
  have hl : nlMap v θ (projOp v (nlMap v (-θ) v)) = v := by
    rw [nlMap_left hvw, map_smul, projOp_apply, inner_left_left hvw, one_smul, nlMap_smul,
      nlMap_left hvw, smul_smul, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  have hr : nlMap v θ (projOp v (nlMap v (-θ) w)) = 0 := by
    rw [nlMap_right hvw, projOp_apply, inner_left_right hvw, zero_smul]
    simp [nlMap]
  have ha : nlMap v θ (projOp v (nlMap v (-θ) (v + w))) = exp ((θ / 2 : ℝ) * I) • v := by
    rw [nlMap_add hvw, map_smul, projOp_apply, inner_add_right, inner_left_left hvw,
      inner_left_right hvw, add_zero, one_smul, nlMap_smul, nlMap_left hvw, smul_smul,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hl, hr, ha, add_zero]
  intro h
  have h1 := congrArg (inner ℂ v) h
  simp only [inner_smul_right, inner_left_left hvw, mul_one] at h1
  exact exp_half_mul_I_ne_one hθ h1

/-! ### A second linear structure with the same rays and Born rule -/

/-- The brief's `m(H)`: the carrier of `E`, with the vector space structure and the inner product
carried over along `m`. Scalar multiplication, rays and the Born rule are those of `E`; addition
is not. -/
def Twisted (_v : E) (_θ : ℝ) : Type _ := E

variable (v) in
/-- The identity of the carrier, from `E` to `Twisted v θ`. -/
def toTwisted (θ : ℝ) : E ≃ Twisted v θ := Equiv.refl E

variable (v) in
/-- `m⁻¹`, from `Twisted v θ` to `E`. The structure of `Twisted v θ` is carried over along it. -/
def twistedEquiv (θ : ℝ) : Twisted v θ ≃ E :=
  (toTwisted v θ).symm.trans (nlHomeomorph v θ).symm.toEquiv

instance (θ : ℝ) : AddCommGroup (Twisted v θ) := (twistedEquiv v θ).addCommGroup

instance (θ : ℝ) : Module ℂ (Twisted v θ) := (twistedEquiv v θ).addEquiv.module ℂ

instance (θ : ℝ) : InnerProductSpace.Core ℂ (Twisted v θ) where
  inner a b := inner ℂ (twistedEquiv v θ a) (twistedEquiv v θ b)
  conj_inner_symm _ _ := inner_conj_symm _ _
  re_inner_nonneg _ := inner_self_nonneg
  add_left a b c := by
    show inner ℂ (twistedEquiv v θ ((twistedEquiv v θ).symm _)) _ = _
    rw [Equiv.apply_symm_apply, inner_add_left]
    rfl
  smul_left a b r := by
    show inner ℂ (twistedEquiv v θ ((twistedEquiv v θ).symm _)) _ = _
    rw [Equiv.apply_symm_apply, inner_smul_left]
    rfl
  definite a h := by
    rw [← (twistedEquiv v θ).symm_apply_apply a, inner_self_eq_zero.mp h]
    rfl

instance (θ : ℝ) : NormedAddCommGroup (Twisted v θ) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance (θ : ℝ) : InnerProductSpace ℂ (Twisted v θ) := InnerProductSpace.ofCore _

variable (v)

lemma toTwisted_add (θ : ℝ) (x y : E) :
    toTwisted v θ x + toTwisted v θ y =
      toTwisted v θ (nlMap v θ (nlMap v (-θ) x + nlMap v (-θ) y)) := rfl

lemma inner_toTwisted (θ : ℝ) (x y : E) :
    inner ℂ (toTwisted v θ x) (toTwisted v θ y) = inner ℂ (nlMap v (-θ) x) (nlMap v (-θ) y) :=
  rfl

/-- Scalar multiplication on `Twisted v θ` is that of `E`, since `m` commutes with scalars; so
are the rays. -/
theorem toTwisted_smul (θ : ℝ) (k : ℂ) (x : E) :
    toTwisted v θ (k • x) = k • toTwisted v θ x := by
  show _ = toTwisted v θ (nlMap v θ (k • nlMap v (-θ) x))
  rw [nlMap_smul, nlMap_nlMap_neg]

/-- `m` is a linear isometry from `E` onto `Twisted v θ`: as inner product spaces, `E ≅ m(E)`. -/
def twistedIsometry (θ : ℝ) : E ≃ₗᵢ[ℂ] Twisted v θ :=
  ((twistedEquiv v θ).addEquiv.linearEquiv ℂ).symm.isometryOfInner fun x y => by
    show inner ℂ (twistedEquiv v θ ((twistedEquiv v θ).symm x))
      (twistedEquiv v θ ((twistedEquiv v θ).symm y)) = _
    simp only [Equiv.apply_symm_apply]

lemma twistedIsometry_apply (θ : ℝ) (x : E) :
    twistedIsometry v θ x = toTwisted v θ (nlMap v θ x) :=
  rfl

lemma norm_toTwisted (θ : ℝ) (x : E) : ‖toTwisted v θ x‖ = ‖x‖ :=
  calc ‖toTwisted v θ x‖ = ‖twistedIsometry v θ (nlMap v (-θ) x)‖ := by
        rw [twistedIsometry_apply, nlMap_nlMap_neg]
    _ = ‖x‖ := by rw [LinearIsometryEquiv.norm_map, norm_nlMap]

/-- The Born rule of `Twisted v θ` is that of `E`. -/
theorem born_toTwisted (θ : ℝ) (x y : E) :
    born (toTwisted v θ x) (toTwisted v θ y) = born x y :=
  calc born (toTwisted v θ x) (toTwisted v θ y) = born (nlMap v (-θ) x) (nlMap v (-θ) y) := by
        simp only [born, inner_toTwisted, norm_toTwisted, norm_nlMap]
    _ = born x y := born_nlMap _ _ x y

variable {v}

/-- Addition on `Twisted v θ` is not that of `E`. -/
theorem not_map_add_toTwisted (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    ¬ ∀ x y : E, toTwisted v θ (x + y) = toTwisted v θ x + toTwisted v θ y := by
  intro h
  have h' := h (nlMap v θ v) (nlMap v θ w)
  rw [toTwisted_add, nlMap_neg_nlMap, nlMap_neg_nlMap] at h'
  exact nlMap_not_add hvw hθ ((toTwisted v θ).injective h').symm

/-- The carrier of `E` has a second complex inner product space structure, `Twisted v θ`, with
the same scalar multiplication (so the same rays) and the same Born rule, but a different
addition. The two structures are isomorphic, so `E ≅ m(E)` as inner product spaces. -/
theorem exists_second_linear_structure (hvw : Orthonormal ℂ ![v, w]) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) :
    (∀ (k : ℂ) (x : E), toTwisted v θ (k • x) = k • toTwisted v θ x) ∧
    (∀ x y : E, born (toTwisted v θ x) (toTwisted v θ y) = born x y) ∧
    ¬ (∀ x y : E, toTwisted v θ (x + y) = toTwisted v θ x + toTwisted v θ y) ∧
    Nonempty (E ≃ₗᵢ[ℂ] Twisted v θ) :=
  ⟨toTwisted_smul v θ, born_toTwisted v θ, not_map_add_toTwisted hvw hθ,
    ⟨twistedIsometry v θ⟩⟩

/-- In dimension one there is no second linear structure: every map that commutes with scalar
multiplication is additive, so carrying the structure along it changes nothing. -/
theorem map_add_of_map_smul {F : Type*} [AddCommGroup F] [Module ℂ F]
    (hF : Module.finrank ℂ F = 1) {f : F → F} (hf : ∀ (k : ℂ) x, f (k • x) = k • f x)
    (x y : F) : f (x + y) = f x + f y := by
  have : Nontrivial F := Module.nontrivial_of_finrank_eq_succ hF
  obtain ⟨b, hb⟩ := exists_ne (0 : F)
  have hspan := (finrank_eq_one_iff_of_ne_zero' b hb).mp hF
  obtain ⟨c, rfl⟩ := hspan x
  obtain ⟨d, rfl⟩ := hspan y
  rw [← add_smul, hf, hf, hf, add_smul]

end NonLinearQuantum
