/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Stone

/-!
# The forward Hamiltonian of a unitary evolution, and a local Stone theorem

An evolution that runs forward from time `t₀` gives unitaries `F τ = U(t₀ + τ, t₀)` for `τ ≥ 0`,
with `F 0 = 1`. Its forward Hamiltonian is `H₀ ψ = iħ ∂₊ F τ ψ` at `τ = 0`, from the right
derivative only, on the vectors where that derivative exists. For a time-independent evolution
`F τ = e^{-iτH/ħ}` it is the self-adjoint `H`, by Stone's theorem. For a time-dependent one it is
always symmetric, but in general not self-adjoint.

## i. Overview

Symmetry comes from `⟨F τ ψ, F τ φ⟩ = ⟨ψ, φ⟩`: the right derivative at `0` of the left side is
`⟨ψ', φ⟩ + ⟨ψ, φ'⟩ = 0`.

Self-adjointness is the condition that `F` is tangent to a one-parameter unitary group:
`F τ ψ - e^{-iτH/ħ} ψ = o(τ)` as `τ → 0⁺`, for a self-adjoint `H` and every `ψ` in its domain.
If it holds, `H` is a restriction of `H₀` (both derivatives exist on the domain of `H`, and they
agree), and a symmetric extension of a self-adjoint operator is the operator itself (`H ≤ H₀ ≤
H₀† ≤ H† = H`). Conversely, if `H₀` is self-adjoint, take `H = H₀`. The tangent group is then
unique: `H = H₀`.

A sufficient condition on `F` alone: a dense subspace `D`, invariant under every `F t`, on which
the orbits are differentiable, and on which the generators near `0` differ from the one at `0`
by bounded operators, `‖∂F(t)ψ - (∂F|₀)(F t ψ)‖ ≤ C ‖ψ‖`. Then `H₀` restricted to `D` is
essentially self-adjoint. A vector `y` with `⟨y, ∂F|₀ x⟩ = a ⟨y, x⟩` on `D` gives
`f(τ) = ⟨y, F τ ψ⟩` with `f' = a f + O(C)`; `f` is bounded, so for `a` large `|⟨y, ψ⟩|` is at
most `‖y‖ ‖ψ‖ / 2`, and by density `y = 0`. After scaling, these are the deficiency vectors at
`±i`. No self-adjointness at any time is assumed.

If moreover the bound tends to `0` as `t → 0⁺`, the forward Hamiltonian is self-adjoint, not just
essentially self-adjoint. Duhamel: against `e^{-isA/ħ} z`, `A` the closure, the inner product
with `F s ψ` moves only through the generator difference, so `‖F τ ψ - e^{-iτA/ħ} ψ‖ ≤ ε τ ‖ψ‖`
on `D`, and by density on all of `E`. `F` is then tangent to the group of `A`.

## ii. Key results

- `QuantumMechanics.forwardHamiltonian`: `iħ ∂₊ F τ ψ` at `τ = 0`.
- `QuantumMechanics.forwardHamiltonian_isSymmetric`: it is symmetric.
- `QuantumMechanics.IsSelfAdjoint.eq_of_le_of_isSymmetric`: a symmetric extension of a
  self-adjoint operator is the operator itself.
- `QuantumMechanics.forwardHamiltonian_eq_of_isLittleO`: if `F` is tangent to `e^{-iτH/ħ}`, the
  forward Hamiltonian is `H`.
- `QuantumMechanics.isSelfAdjoint_forwardHamiltonian_iff`: the forward Hamiltonian is
  self-adjoint iff `F` is tangent to a one-parameter unitary group.
- `QuantumMechanics.isEssentiallySelfAdjoint_forwardHamiltonian`: an invariant dense subspace
  on which the generator varies by bounded operators is a core, and the forward Hamiltonian is
  essentially self-adjoint.
- `QuantumMechanics.norm_sub_schrodingerPropagator_le`: Duhamel estimate for an approximate
  solution of the Schrödinger equation.
- `QuantumMechanics.isSelfAdjoint_forwardHamiltonian`: if the generator differences also tend to
  `0`, the forward Hamiltonian is self-adjoint, the closure of its restriction to `D`.
-/

@[expose] public noncomputable section

namespace QuantumMechanics

open Filter Topology Set Asymptotics
open scoped InnerProductSpace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A symmetric extension of a self-adjoint operator is the operator itself: `H ≤ K ≤ K† ≤ H† =
H`. -/
theorem IsSelfAdjoint.eq_of_le_of_isSymmetric [CompleteSpace E] {H K : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) (hK : K.IsSymmetric) (hle : H ≤ K) : K = H := by
  have hdense : Dense (K.domain : Set E) := hH.dense_domain.mono hle.1
  have h1 : K ≤ K† := LinearPMap.IsFormalAdjoint.le_adjoint hdense hK
  have h2 : K† ≤ H† := LinearPMap.adjoint_antitone (Or.inl hH.dense_domain) hle
  rw [LinearPMap.isSelfAdjoint_def.mp hH] at h2
  exact le_antisymm (h1.trans h2) hle

variable (F : ℝ → E →L[ℂ] E)

/-- The vectors `ψ` for which `τ ↦ F τ ψ` has a right derivative at `0`. -/
def forwardDomain : Submodule ℂ E where
  carrier := {ψ | DifferentiableWithinAt ℝ (fun τ => F τ ψ) (Ici 0) 0}
  add_mem' {ψ φ} hψ hφ := by
    change DifferentiableWithinAt ℝ (fun τ => F τ (ψ + φ)) (Ici 0) 0
    simp only [map_add]
    exact hψ.add hφ
  zero_mem' := by
    change DifferentiableWithinAt ℝ (fun τ => F τ 0) (Ici 0) 0
    simp only [map_zero]
    exact differentiableWithinAt_const 0
  smul_mem' c ψ hψ := by
    change DifferentiableWithinAt ℝ (fun τ => F τ (c • ψ)) (Ici 0) 0
    simp only [map_smul]
    exact hψ.const_smul c

variable {F} in
lemma mem_forwardDomain {ψ : E} :
    ψ ∈ forwardDomain F ↔ DifferentiableWithinAt ℝ (fun τ => F τ ψ) (Ici 0) 0 :=
  Iff.rfl

/-- **The forward Hamiltonian** `H₀ ψ = iħ ∂₊ F τ ψ` at `τ = 0`, from the right derivative only. -/
def forwardHamiltonian (ħ : ℝ) : E →ₗ.[ℂ] E where
  domain := forwardDomain F
  toFun :=
    { toFun := fun ψ => (Complex.I * ħ) • derivWithin (fun τ => F τ ψ) (Ici 0) 0
      map_add' := fun ψ φ => by
        simp only [Submodule.coe_add, map_add]
        rw [derivWithin_fun_add (mem_forwardDomain.mp ψ.2) (mem_forwardDomain.mp φ.2), smul_add]
      map_smul' := fun c ψ => by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        rw [derivWithin_fun_const_smul c (mem_forwardDomain.mp ψ.2), smul_comm] }

variable {F}

lemma forwardHamiltonian_apply (ħ : ℝ) (ψ : (forwardHamiltonian F ħ).domain) :
    forwardHamiltonian F ħ ψ = (Complex.I * ħ) • derivWithin (fun τ => F τ ψ) (Ici 0) 0 :=
  rfl

lemma forwardHamiltonian_of_hasDerivWithinAt (ħ : ℝ) {ψ v : E}
    (h : HasDerivWithinAt (fun τ => F τ ψ) v (Ici 0) 0) :
    ∃ hψ : ψ ∈ forwardDomain F, forwardHamiltonian F ħ ⟨ψ, hψ⟩ = (Complex.I * ħ) • v :=
  ⟨h.differentiableWithinAt, by
    rw [forwardHamiltonian_apply, h.derivWithin (uniqueDiffWithinAt_Ici 0)]⟩

lemma hasDerivWithinAt_forwardHamiltonian {ħ : ℝ} (hħ : ħ ≠ 0)
    (ψ : (forwardHamiltonian F ħ).domain) :
    HasDerivWithinAt (fun τ => F τ ψ) ((Complex.I * ħ)⁻¹ • forwardHamiltonian F ħ ψ) (Ici 0) 0 := by
  have : Complex.I * ħ ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)
  rw [forwardHamiltonian_apply, smul_smul, inv_mul_cancel₀ this, one_smul]
  exact (mem_forwardDomain.mp ψ.2).hasDerivWithinAt

/-- **The forward Hamiltonian is symmetric**, from `⟨F τ ψ, F τ φ⟩ = ⟨ψ, φ⟩`. -/
theorem forwardHamiltonian_isSymmetric (ħ : ℝ) (hF0 : F 0 = 1)
    (hF : ∀ τ, 0 ≤ τ → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) :
    (forwardHamiltonian F ħ).IsSymmetric := by
  intro ψ φ
  have hA := (mem_forwardDomain.mp ψ.2).hasDerivWithinAt
  have hB := (mem_forwardDomain.mp φ.2).hasDerivWithinAt
  have h := (hA.inner ℂ hB).congr (f₁ := fun _ => ⟪(ψ : E), φ⟫_ℂ)
    (fun τ hτ => (hF τ hτ ψ φ).symm) (by simp [hF0])
  have h0 := (uniqueDiffWithinAt_Ici 0).eq_deriv _ h (hasDerivWithinAt_const _ _ _)
  rw [hF0, one_apply_eq_self, one_apply_eq_self] at h0
  rw [forwardHamiltonian_apply, forwardHamiltonian_apply, inner_smul_left, inner_smul_right]
  have hconj : (starRingEnd ℂ) (Complex.I * ħ) = -(Complex.I * ħ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rw [hconj]
  linear_combination (-(Complex.I * ħ)) * h0

/-- If `F ψ - V ψ = o(τ)` and `F 0 = V 0`, both have the same right derivative at `0`. -/
lemma hasDerivWithinAt_of_isLittleO {f g : ℝ → E} {v : E} (hg : HasDerivWithinAt g v (Ici 0) 0)
    (h0 : f 0 = g 0) (ho : (fun τ => f τ - g τ) =o[𝓝[≥] 0] fun τ => τ) :
    HasDerivWithinAt f v (Ici 0) 0 := by
  have hd : HasDerivWithinAt (fun τ => f τ - g τ) 0 (Ici 0) 0 := by
    rw [hasDerivWithinAt_iff_isLittleO]
    simpa [h0] using ho
  simpa using hd.fun_add hg

variable [CompleteSpace E]

/-- **Tangent to a unitary group.** If `F τ ψ - e^{-iτH/ħ} ψ = o(τ)` on the domain of a
self-adjoint `H`, and `F` is unitary with `F 0 = 1`, the forward Hamiltonian is `H`. -/
theorem forwardHamiltonian_eq_of_isLittleO {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ τ, 0 ≤ τ → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H)
    (ho : ∀ ψ ∈ H.domain,
      (fun τ => F τ ψ - schrodingerPropagator hħ hH τ ψ) =o[𝓝[≥] 0] fun τ => τ) :
    forwardHamiltonian F ħ = H := by
  have hV0 := schrodingerPropagator_zero hħ hH
  have key : ∀ ψ : H.domain, ∃ h : (ψ : E) ∈ forwardDomain F,
      forwardHamiltonian F ħ ⟨ψ, h⟩ = H ψ := fun ψ => by
    obtain ⟨hmem, hd⟩ := solvesSchrodinger_schrodingerPropagator hħ hH ψ 0
    have hψ : (⟨schrodingerPropagator hħ hH 0 ψ, hmem⟩ : H.domain) = ψ := by
      ext; simp [hV0]
    rw [hψ] at hd
    have hF := hasDerivWithinAt_of_isLittleO hd.hasDerivWithinAt (by simp [hF0, hV0])
      (ho ψ ψ.2)
    obtain ⟨h, hH'⟩ := forwardHamiltonian_of_hasDerivWithinAt ħ hF
    refine ⟨h, ?_⟩
    have : Complex.I * ħ ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)
    rw [hH', smul_smul, mul_inv_cancel₀ this, one_smul]
  refine IsSelfAdjoint.eq_of_le_of_isSymmetric hH (forwardHamiltonian_isSymmetric ħ hF0 hF)
    ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, fun ψ φ hψφ => ?_⟩
  obtain ⟨h, hH'⟩ := key ψ
  rw [← hH']
  exact congrArg _ (Subtype.ext hψφ)

/-- **Local Stone theorem.** The forward Hamiltonian of a unitary `F` with `F 0 = 1` is
self-adjoint iff `F` is tangent at `0` to a one-parameter unitary group: `F τ ψ - e^{-iτH/ħ} ψ =
o(τ)` as `τ → 0⁺` for a self-adjoint `H` and every `ψ` in its domain. -/
theorem isSelfAdjoint_forwardHamiltonian_iff {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ τ, 0 ≤ τ → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) :
    IsSelfAdjoint (forwardHamiltonian F ħ) ↔
      ∃ (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H), ∀ ψ ∈ H.domain,
        (fun τ => F τ ψ - schrodingerPropagator hħ hH τ ψ) =o[𝓝[≥] 0] fun τ => τ := by
  refine ⟨fun hH => ⟨_, hH, fun ψ hψ => ?_⟩, fun ⟨H, hH, ho⟩ => ?_⟩
  · obtain ⟨hmem, hd⟩ := solvesSchrodinger_schrodingerPropagator hħ hH ⟨ψ, hψ⟩ 0
    have hψ' : (⟨schrodingerPropagator hħ hH 0 ψ, hmem⟩ : (forwardHamiltonian F ħ).domain) =
        ⟨ψ, hψ⟩ := by
      ext; simp [schrodingerPropagator_zero]
    rw [hψ'] at hd
    have h := (hasDerivWithinAt_forwardHamiltonian hħ ⟨ψ, hψ⟩).sub hd.hasDerivWithinAt
    rw [sub_self, hasDerivWithinAt_iff_isLittleO] at h
    simpa [hF0, schrodingerPropagator_zero] using h
  · rw [forwardHamiltonian_eq_of_isLittleO hħ hF0 hF hH ho]
    exact hH

/-! ### An invariant core -/

omit [CompleteSpace E] in
/-- **A deficiency vector against an orbit.** If `⟨y, B x⟩ = a ⟨y, x⟩` on `D` with `a ≥ 0`, and
`η' = B η + e` along an orbit in `D`, then `e^{-aτ} ⟨y, η τ⟩` moves only through `e`, so
`⟨y, η 0⟩` is bounded by `e^{-aT} ‖η T‖ + T sup ‖e‖`. -/
lemma norm_inner_le_of_hasDerivAt {B : E → E} {D : Submodule ℂ E} {a : ℝ} (ha : 0 ≤ a) {y : E}
    (hy : ∀ x ∈ D, ⟪y, B x⟫_ℂ = a * ⟪y, x⟫_ℂ) {η e : ℝ → E} {T R K : ℝ} (hT : 0 ≤ T)
    (hη : ∀ τ ∈ Icc 0 T, η τ ∈ D) (hd : ∀ τ ∈ Icc 0 T, HasDerivAt η (B (η τ) + e τ) τ)
    (he : ∀ τ ∈ Icc 0 T, ‖e τ‖ ≤ R) (hK : ‖η T‖ ≤ K) :
    ‖⟪y, η 0⟫_ℂ‖ ≤ (Real.exp (-a * T) * K + R * T) * ‖y‖ := by
  set g : ℝ → ℂ := fun τ => (Real.exp (-a * τ) : ℂ) * ⟪y, η τ⟫_ℂ
  have hg : ∀ τ ∈ Icc 0 T,
      HasDerivWithinAt g ((Real.exp (-a * τ) : ℂ) * ⟪y, e τ⟫_ℂ) (Icc 0 T) τ := by
    intro τ hτ
    have h1 : HasDerivAt (fun τ : ℝ => (Real.exp (-a * τ) : ℂ))
        ((Real.exp (-a * τ) * -a : ℝ) : ℂ) τ := by
      have h := ((hasDerivAt_id τ).const_mul (-a)).exp.ofReal_comp
      simpa using h
    have h2 := (hasDerivAt_const τ y).inner ℂ (hd τ hτ)
    refine ((h1.mul h2).hasDerivWithinAt).congr_deriv ?_
    rw [inner_zero_left, add_zero, inner_add_right, hy _ (hη τ hτ)]
    push_cast
    ring
  have hbound : ∀ τ ∈ Ico 0 T, ‖(Real.exp (-a * τ) : ℂ) * ⟪y, e τ⟫_ℂ‖ ≤ R * ‖y‖ := by
    intro τ hτ
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hexp : Real.exp (-a * τ) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hτ.1])
    calc Real.exp (-a * τ) * ‖⟪y, e τ⟫_ℂ‖ ≤ 1 * (‖y‖ * R) := by
          refine mul_le_mul hexp ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _) zero_le_one
          exact mul_le_mul_of_nonneg_left (he τ (Ico_subset_Icc_self hτ)) (norm_nonneg _)
      _ = R * ‖y‖ := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hg hbound T (right_mem_Icc.mpr hT)
  have hg0 : g 0 = ⟪y, η 0⟫_ℂ := by simp [g]
  have hgT : ‖g T‖ ≤ Real.exp (-a * T) * K * ‖y‖ := by
    simp only [g, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    calc ‖⟪y, η T⟫_ℂ‖ ≤ ‖y‖ * ‖η T‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * K := mul_le_mul_of_nonneg_left hK (norm_nonneg _)
      _ = K * ‖y‖ := mul_comm _ _
  rw [← hg0]
  calc ‖g 0‖ ≤ ‖g T‖ + ‖g T - g 0‖ := by
        simpa using norm_sub_le (g T) (g T - g 0)
    _ ≤ Real.exp (-a * T) * K * ‖y‖ + R * ‖y‖ * (T - 0) := add_le_add hgT hmv
    _ = (Real.exp (-a * T) * K + R * T) * ‖y‖ := by ring

omit [CompleteSpace E] in
/-- **No deficiency vectors for large `|a|`.** Let `F t` be contractions with `F 0 = 1`, `D` a
dense subspace invariant under every `F t`, on which `t ↦ F t ψ` is differentiable, and suppose
that near `0` the derivative of the orbit differs from `B = ∂F|₀` at the current point by at most
`C ‖ψ‖`. Then for `|a|` large no `y ≠ 0` has `⟨y, B x⟩ = a ⟨y, x⟩` on `D`. -/
lemma exists_eq_zero_of_inner_deriv (hF0 : F 0 = 1) (hF : ∀ t x, ‖F t x‖ ≤ ‖x‖)
    {D : Submodule ℂ E} (hD : Dense (D : Set E)) (hinv : ∀ t, ∀ x ∈ D, F t x ∈ D)
    (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x) {C T : ℝ} (hT : 0 < T)
    (hC : ∀ t ∈ Icc (-T) T, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ C * ‖x‖) :
    ∃ μ > 0, ∀ a : ℝ, μ ≤ |a| → ∀ y : E,
      (∀ x ∈ D, ⟪y, deriv (fun s => F s x) 0⟫_ℂ = a * ⟪y, x⟫_ℂ) → y = 0 := by
  set B : E → E := fun x => deriv (fun s => F s x) 0
  set S : ℝ := T / (4 * |C| * T + 1)
  have hden : 0 < 4 * |C| * T + 1 := by positivity
  have hS : 0 < S := div_pos hT hden
  have hST : S ≤ T := div_le_self hT.le (by nlinarith [abs_nonneg C])
  have hCS : |C| * S ≤ 1 / 4 := by
    rw [show |C| * S = |C| * T / (4 * |C| * T + 1) by simp only [S]; ring, div_le_iff₀ hden]
    nlinarith [mul_nonneg (abs_nonneg C) hT.le]
  refine ⟨4 / S, div_pos four_pos hS, fun a ha y hy => ?_⟩
  have hexp : Real.exp (-|a| * S) ≤ 1 / 4 := by
    have h4 : 4 ≤ |a| * S := by rwa [div_le_iff₀ hS] at ha
    rw [neg_mul, Real.exp_neg, inv_eq_one_div]
    refine one_div_le_one_div_of_le four_pos ?_
    linarith [Real.add_one_le_exp (|a| * S)]
  -- `|⟨y, x⟩| ≤ ‖x‖ ‖y‖ / 2` on `D`, from the orbit forward (`a ≥ 0`) or backward (`a < 0`).
  have hD2 : ∀ x ∈ D, ‖⟪y, x⟫_ℂ‖ ≤ 1 / 2 * ‖x‖ * ‖y‖ := by
    intro x hx
    have hR : ∀ τ ∈ Icc (-T) T, ‖deriv (fun s => F s x) τ - B (F τ x)‖ ≤ |C| * ‖x‖ :=
      fun τ hτ => (hC τ hτ x hx).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _))
    have hfin : (Real.exp (-|a| * S) * ‖x‖ + |C| * ‖x‖ * S) * ‖y‖ ≤ 1 / 2 * ‖x‖ * ‖y‖ := by
      have : Real.exp (-|a| * S) * ‖x‖ + |C| * ‖x‖ * S ≤ 1 / 2 * ‖x‖ := by
        nlinarith [norm_nonneg x]
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    rcases le_or_gt 0 a with h0 | h0
    · have h := norm_inner_le_of_hasDerivAt (B := B) (D := D) h0 (y := y) hy
        (η := fun τ => F τ x) (e := fun τ => deriv (fun s => F s x) τ - B (F τ x))
        (K := ‖x‖) hS.le (fun τ _ => hinv τ x hx)
        (fun τ _ => by simpa using ((hdiff x hx) τ).hasDerivAt)
        (fun τ hτ => hR τ ⟨by linarith [hτ.1], hτ.2.trans hST⟩) (hF S x)
      rw [abs_of_nonneg h0] at hfin
      simpa [hF0] using h.trans hfin
    · have hy' : ∀ x ∈ D, ⟪y, -B x⟫_ℂ = ((-a : ℝ) : ℂ) * ⟪y, x⟫_ℂ := fun x hx => by
        rw [inner_neg_right, hy x hx]
        push_cast
        ring
      have h := norm_inner_le_of_hasDerivAt (B := fun x => -B x) (D := D)
        (by linarith : (0 : ℝ) ≤ -a) hy'
        (η := fun τ => F (-τ) x) (e := fun τ => -(deriv (fun s => F s x) (-τ) - B (F (-τ) x)))
        (K := ‖x‖) hS.le (fun τ _ => hinv (-τ) x hx)
        (fun τ _ => by
          have h := ((hdiff x hx) (-τ)).hasDerivAt.scomp τ (hasDerivAt_neg τ)
          refine h.congr_deriv ?_
          simp only [neg_one_smul]
          abel)
        (fun τ hτ => by
          rw [norm_neg]
          exact hR (-τ) ⟨by linarith [hτ.2, hST], by linarith [hτ.1]⟩) (hF (-S) x)
      rw [abs_of_neg h0] at hfin
      simpa [hF0] using h.trans hfin
  -- By density it holds for `x = y`, so `‖y‖² ≤ ‖y‖² / 2`.
  have hall : ∀ x, ‖⟪y, x⟫_ℂ‖ ≤ 1 / 2 * ‖x‖ * ‖y‖ := by
    have hcl : IsClosed {x : E | ‖⟪y, x⟫_ℂ‖ ≤ 1 / 2 * ‖x‖ * ‖y‖} :=
      isClosed_le (continuous_const.inner continuous_id).norm
        ((continuous_const.mul continuous_norm).mul continuous_const)
    intro x
    have hx : x ∈ closure (D : Set E) := hD.closure_eq ▸ Set.mem_univ x
    exact closure_minimal (fun x hx => hD2 x hx) hcl hx
  have hyy := hall y
  have hnorm : ‖⟪y, y⟫_ℂ‖ = ‖y‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hnorm] at hyy
  have : ‖y‖ = 0 := by nlinarith [norm_nonneg y]
  exact norm_eq_zero.mp this

omit [CompleteSpace E] in
lemma domRestrict_forwardHamiltonian_apply {ħ : ℝ} {D : Submodule ℂ E}
    (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x) {x : E}
    (hx : x ∈ ((forwardHamiltonian F ħ).domRestrict D).domain) :
    (forwardHamiltonian F ħ).domRestrict D ⟨x, hx⟩ =
      (Complex.I * ħ) • deriv (fun s => F s x) 0 := by
  change (Complex.I * ħ) • derivWithin (fun τ => F τ x) (Ici 0) 0 = _
  congr 1
  exact ((hdiff x hx.1) 0).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)

/-- **An invariant core.** Let `F t` be unitaries with `F 0 = 1`, for instance
`F t = U(t₀ + t, t₀)`, and `D` a dense subspace invariant under every `F t`, on which
`t ↦ F t ψ` is differentiable. Suppose that near `t = 0` the derivative of the orbit differs from
`∂F|₀` applied to the current point by at most `C ‖ψ‖`: the generators at nearby times differ
from the one at `0` by bounded operators. Then the forward Hamiltonian restricted to `D` is
essentially self-adjoint, and so is the forward Hamiltonian, with the same closure. -/
theorem isEssentiallySelfAdjoint_forwardHamiltonian {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t, F t ∈ unitary (E →L[ℂ] E)) {D : Submodule ℂ E} (hD : Dense (D : Set E))
    (hinv : ∀ t, ∀ x ∈ D, F t x ∈ D) (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x)
    {C T : ℝ} (hT : 0 < T)
    (hC : ∀ t ∈ Icc (-T) T, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ C * ‖x‖) :
    ((forwardHamiltonian F ħ).domRestrict D).IsEssentiallySelfAdjoint ∧
      (forwardHamiltonian F ħ).IsEssentiallySelfAdjoint ∧
      (forwardHamiltonian F ħ).closure = ((forwardHamiltonian F ħ).domRestrict D).closure := by
  have hDle : D ≤ (forwardHamiltonian F ħ).domain := fun x hx =>
    mem_forwardDomain.mpr ((hdiff x hx) 0).differentiableWithinAt
  have hsym₀ : (forwardHamiltonian F ħ).IsSymmetric := forwardHamiltonian_isSymmetric ħ hF0
    fun τ _ => ContinuousLinearMap.inner_map_map_of_mem_unitary (hF τ)
  have hdense₀ : (forwardHamiltonian F ħ).HasDenseDomain := hD.mono hDle
  have hdenseD : ((forwardHamiltonian F ħ).domRestrict D).HasDenseDomain := by
    rw [LinearPMap.hasDenseDomain_def, LinearPMap.domRestrict_domain, inf_eq_left.mpr hDle]
    exact hD
  have hsymD : ((forwardHamiltonian F ħ).domRestrict D).IsSymmetric :=
    hsym₀.of_le LinearPMap.domRestrict_le
  obtain ⟨μ, hμ, hzero⟩ := exists_eq_zero_of_inner_deriv hF0
    (fun t x => (ContinuousLinearMap.norm_map_of_mem_unitary (hF t) x).le) hD hinv hdiff hT hC
  -- Scale by `κ = 1 / (μ |ħ|)`: the deficiency vectors of `κ H₀|_D` at `±i` are those of `∂F|₀`
  -- at `±μ`.
  set κ : ℝ := 1 / (μ * |ħ|) with hκdef
  have hκ : 0 < κ := by positivity
  have hdef : ∀ sgn : ℝ, (sgn = 1 ∨ sgn = -1) →
      ((κ : ℂ) • (forwardHamiltonian F ħ).domRestrict D).defectNumber (sgn * Complex.I) = 0 := by
    intro sgn hsgn
    show Module.rank ℂ ↥(((κ : ℂ) • (forwardHamiltonian F ħ).domRestrict D -
      (sgn * Complex.I) • 1).toFun.rangeᗮ) = 0
    refine Submodule.rank_eq_zero.mpr ((Submodule.eq_bot_iff _).mpr fun y hy => ?_)
    refine hzero (sgn / (κ * ħ)) ?_ y fun x hx => ?_
    · have h1 : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> simp
      have habs : |ħ| ≠ 0 := abs_ne_zero.mpr hħ
      have : |sgn / (κ * ħ)| = μ := by
        rw [abs_div, abs_mul, h1, abs_of_pos hκ, hκdef]
        field_simp
      exact this.ge
    · have hxD : x ∈ ((forwardHamiltonian F ħ).domRestrict D).domain := by
        rw [LinearPMap.domRestrict_domain]
        exact ⟨hx, hDle hx⟩
      have hxS : x ∈ ((κ : ℂ) • (forwardHamiltonian F ħ).domRestrict D -
          (sgn * Complex.I) • (1 : E →ₗ.[ℂ] E)).domain := by
        rw [LinearPMap.sub_domain]
        exact ⟨hxD, Submodule.mem_top⟩
      have hz : ⟪y, (κ : ℂ) • ((forwardHamiltonian F ħ).domRestrict D ⟨x, hxD⟩) -
          (sgn * Complex.I) • x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal' _ y).mp hy _ ⟨⟨x, hxS⟩, rfl⟩
      rw [domRestrict_forwardHamiltonian_apply hdiff, inner_sub_right, inner_smul_right,
        inner_smul_right, inner_smul_right, sub_eq_zero] at hz
      have hħ' : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
      have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
      push_cast
      field_simp
      linear_combination (-Complex.I) * hz + (⟪y, deriv (fun s => F s x) 0⟫_ℂ * κ * ħ -
        sgn * ⟪y, x⟫_ℂ) * Complex.I_sq
  have hSess : ((κ : ℂ) • (forwardHamiltonian F ħ).domRestrict D).IsEssentiallySelfAdjoint :=
    (hsymD.smul (Complex.conj_ofReal κ)).isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdenseD
      (by simpa using hdef 1 (Or.inl rfl)) (by simpa using hdef (-1) (Or.inr rfl))
  -- Undo the scaling.
  have hHDess : ((forwardHamiltonian F ħ).domRestrict D).IsEssentiallySelfAdjoint := by
    rw [LinearPMap.isEssentiallySelfAdjoint_def] at hSess ⊢
    have hκ0 : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    rw [LinearPMap.closure_smul _ hκ0] at hSess
    have h := ProbabilisticTheory.QuantumMechanics.Essential.isSelfAdjoint_smul_real hSess κ⁻¹
      (inv_ne_zero hκ.ne')
    rwa [smul_smul, Complex.ofReal_inv, inv_mul_cancel₀ hκ0, one_smul] at h
  -- A symmetric extension has the same closure.
  have hle : ((forwardHamiltonian F ħ).domRestrict D).closure ≤
      (forwardHamiltonian F ħ).closure :=
    (hsym₀.isClosable hdense₀).closure_mono LinearPMap.domRestrict_le
  have heq : (forwardHamiltonian F ħ).closure =
      ((forwardHamiltonian F ħ).domRestrict D).closure :=
    IsSelfAdjoint.eq_of_le_of_isSymmetric hHDess (hsym₀.closure hdense₀) hle
  refine ⟨hHDess, ?_, heq⟩
  rw [LinearPMap.isEssentiallySelfAdjoint_def, heq]
  exact hHDess

/-! ### Self-adjointness -/

/-- **Duhamel estimate.** An approximate solution `η' = (iħ)⁻¹ H η + e` of the Schrödinger
equation for a self-adjoint `H`, with `‖e‖ ≤ R` on `[0, τ]`, stays within `R τ` of the exact
solution: `‖η τ - e^{-iτH/ħ} η 0‖ ≤ R τ`. Against `e^{-isH/ħ} z`, `z` in the domain, the inner
product with `η s` moves only through `e`. -/
lemma norm_sub_schrodingerPropagator_le {ħ : ℝ} (hħ : ħ ≠ 0) {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H) {η e : ℝ → E} {τ R : ℝ} (hτ : 0 ≤ τ)
    (hd : ∀ s ∈ Icc 0 τ, ∃ h : η s ∈ H.domain,
      HasDerivAt η ((Complex.I * ħ)⁻¹ • H ⟨η s, h⟩ + e s) s)
    (he : ∀ s ∈ Icc 0 τ, ‖e s‖ ≤ R) :
    ‖η τ - schrodingerPropagator hħ hH τ (η 0)‖ ≤ R * τ := by
  have hU := schrodingerPropagator_mem_unitary hħ hH
  have hsym := LinearPMap.IsSelfAdjoint.isSymmetric hH
  have hR : 0 ≤ R := (norm_nonneg _).trans (he 0 (left_mem_Icc.mpr hτ))
  have hc : (starRingEnd ℂ) ((Complex.I * ħ)⁻¹) = -(Complex.I * ħ)⁻¹ := by
    rw [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul, inv_neg]
  have hz : ∀ z ∈ H.domain, ‖⟪schrodingerPropagator hħ hH τ z,
      η τ - schrodingerPropagator hħ hH τ (η 0)⟫_ℂ‖ ≤ R * τ * ‖z‖ := by
    intro z hz
    have hf : ∀ s ∈ Icc 0 τ, HasDerivWithinAt (fun s => ⟪schrodingerPropagator hħ hH s z, η s⟫_ℂ)
        ⟪schrodingerPropagator hħ hH s z, e s⟫_ℂ (Icc 0 τ) s := by
      intro s hs
      obtain ⟨hmem, hU'⟩ := solvesSchrodinger_schrodingerPropagator hħ hH ⟨z, hz⟩ s
      obtain ⟨hη, hη'⟩ := hd s hs
      refine ((hU'.inner ℂ hη').hasDerivWithinAt).congr_deriv ?_
      have h3 : ⟪H ⟨_, hmem⟩, η s⟫_ℂ = ⟪schrodingerPropagator hħ hH s z, H ⟨η s, hη⟩⟫_ℂ :=
        hsym ⟨_, hmem⟩ ⟨_, hη⟩
      rw [inner_add_right, inner_smul_right, inner_smul_left, h3, hc]
      ring
    have hbound : ∀ s ∈ Ico 0 τ, ‖⟪schrodingerPropagator hħ hH s z, e s⟫_ℂ‖ ≤ R * ‖z‖ := by
      intro s hs
      refine (norm_inner_le_norm _ _).trans ?_
      rw [ContinuousLinearMap.norm_map_of_mem_unitary (hU s), mul_comm]
      exact mul_le_mul_of_nonneg_right (he s (Ico_subset_Icc_self hs)) (norm_nonneg _)
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound τ (right_mem_Icc.mpr hτ)
    rw [schrodingerPropagator_zero, one_apply_eq_self,
      ← ContinuousLinearMap.inner_map_map_of_mem_unitary (hU τ) z (η 0), ← inner_sub_right,
      sub_zero] at hmv
    linarith
  -- By density this holds for every `z`, in particular for `z = U τ† w`.
  set w := η τ - schrodingerPropagator hħ hH τ (η 0)
  have hall : ∀ z, ‖⟪schrodingerPropagator hħ hH τ z, w⟫_ℂ‖ ≤ R * τ * ‖z‖ := by
    have hcl : IsClosed {z : E | ‖⟪schrodingerPropagator hħ hH τ z, w⟫_ℂ‖ ≤ R * τ * ‖z‖} :=
      isClosed_le ((schrodingerPropagator hħ hH τ).continuous.inner continuous_const).norm
        (continuous_const.mul continuous_norm)
    intro z
    have hzc : z ∈ closure (H.domain : Set E) := hH.dense_domain.closure_eq ▸ Set.mem_univ z
    exact closure_minimal (fun z hz' => hz z hz') hcl hzc
  have hww := hall (star (schrodingerPropagator hħ hH τ) w)
  have hnorm : ‖⟪w, w⟫_ℂ‖ = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [← mul_apply_eq_comp, Unitary.mul_star_self_of_mem (hU τ),
    one_apply_eq_self, ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.star_mem (hU τ)),
    hnorm] at hww
  nlinarith [norm_nonneg w, mul_nonneg hR hτ]

/-- **Self-adjointness.** Under the hypotheses of `isEssentiallySelfAdjoint_forwardHamiltonian`,
suppose moreover that the generators at times `t → 0⁺` approach the one at `0` on `D`:
`‖∂F(t)ψ - (∂F|₀)(F t ψ)‖ ≤ ε ‖ψ‖` for `t ∈ [0, δ]`. Then `F` is tangent at `0` to the unitary
group of the closure, by the Duhamel estimate on `D` and density, and the forward Hamiltonian is
self-adjoint: it is the closure of its restriction to `D`. -/
theorem isSelfAdjoint_forwardHamiltonian {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t, F t ∈ unitary (E →L[ℂ] E)) {D : Submodule ℂ E} (hD : Dense (D : Set E))
    (hinv : ∀ t, ∀ x ∈ D, F t x ∈ D) (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x)
    {C T : ℝ} (hT : 0 < T)
    (hC : ∀ t ∈ Icc (-T) T, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ C * ‖x‖)
    (hω : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc 0 δ, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ ε * ‖x‖) :
    IsSelfAdjoint (forwardHamiltonian F ħ) ∧
      forwardHamiltonian F ħ = ((forwardHamiltonian F ħ).domRestrict D).closure := by
  obtain ⟨-, hess, hcl⟩ :=
    isEssentiallySelfAdjoint_forwardHamiltonian hħ hF0 hF hD hinv hdiff hT hC
  have hA : IsSelfAdjoint (forwardHamiltonian F ħ).closure :=
    LinearPMap.isEssentiallySelfAdjoint_def.mp hess
  have hDle : D ≤ (forwardHamiltonian F ħ).domain := fun x hx =>
    mem_forwardDomain.mpr ((hdiff x hx) 0).differentiableWithinAt
  have hF' : ∀ τ, 0 ≤ τ → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ :=
    fun τ _ => ContinuousLinearMap.inner_map_map_of_mem_unitary (hF τ)
  -- On `D`, `(iħ)⁻¹` times the closure is `∂F|₀`.
  have hgen : ∀ x ∈ D, ∃ h : x ∈ (forwardHamiltonian F ħ).closure.domain,
      (Complex.I * ħ)⁻¹ • (forwardHamiltonian F ħ).closure ⟨x, h⟩ = deriv (fun s => F s x) 0 := by
    intro x hx
    have hle := (forwardHamiltonian F ħ).le_closure
    refine ⟨hle.1 (hDle hx), ?_⟩
    have hIħ : Complex.I * ħ ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)
    rw [← hle.2 (x := ⟨x, hDle hx⟩) rfl, forwardHamiltonian_apply, smul_smul,
      inv_mul_cancel₀ hIħ, one_smul]
    exact ((hdiff x hx) 0).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
  -- The Duhamel estimate on `D`, then on all of `E` by density.
  have hbound : ∀ ε > 0, ∃ δ > 0, ∀ τ ∈ Icc 0 δ, ∀ ψ,
      ‖F τ ψ - schrodingerPropagator hħ hA τ ψ‖ ≤ ε * τ * ‖ψ‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hω'⟩ := hω ε hε
    refine ⟨δ, hδ, fun τ hτ => ?_⟩
    have hDτ : ∀ x ∈ D, ‖F τ x - schrodingerPropagator hħ hA τ x‖ ≤ ε * τ * ‖x‖ := by
      intro x hx
      have h := norm_sub_schrodingerPropagator_le hħ hA (η := fun s => F s x)
        (e := fun s => deriv (fun s => F s x) s - deriv (fun s' => F s' (F s x)) 0)
        (R := ε * ‖x‖) hτ.1
        (fun s _ => by
          obtain ⟨h, hh⟩ := hgen (F s x) (hinv s x hx)
          refine ⟨h, ?_⟩
          rw [hh]
          simpa using ((hdiff x hx) s).hasDerivAt)
        (fun s hs => hω' s ⟨hs.1, hs.2.trans hτ.2⟩ x hx)
      rw [hF0, one_apply_eq_self] at h
      linarith
    have hcl' : IsClosed {ψ : E | ‖F τ ψ - schrodingerPropagator hħ hA τ ψ‖ ≤ ε * τ * ‖ψ‖} :=
      isClosed_le ((F τ).continuous.sub (schrodingerPropagator hħ hA τ).continuous).norm
        (continuous_const.mul continuous_norm)
    intro ψ
    have hψ : ψ ∈ closure (D : Set E) := hD.closure_eq ▸ Set.mem_univ ψ
    exact closure_minimal (fun x hx => hDτ x hx) hcl' hψ
  have ho : ∀ ψ ∈ (forwardHamiltonian F ħ).closure.domain,
      (fun τ => F τ ψ - schrodingerPropagator hħ hA τ ψ) =o[𝓝[≥] 0] fun τ => τ := by
    intro ψ _
    refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
    obtain ⟨δ, hδ, hb⟩ := hbound (c / (‖ψ‖ + 1)) (by positivity)
    filter_upwards [Icc_mem_nhdsGE hδ] with τ hτ
    refine (hb τ hτ ψ).trans ?_
    rw [Real.norm_of_nonneg hτ.1, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hc.le hτ.1]
  exact ⟨(isSelfAdjoint_forwardHamiltonian_iff hħ hF0 hF').mpr ⟨_, hA, ho⟩,
    (forwardHamiltonian_eq_of_isLittleO hħ hF0 hF' hA ho).trans hcl⟩

end QuantumMechanics
