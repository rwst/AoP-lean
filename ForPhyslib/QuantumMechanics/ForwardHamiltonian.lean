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

## ii. Key results

- `QuantumMechanics.forwardHamiltonian`: `iħ ∂₊ F τ ψ` at `τ = 0`.
- `QuantumMechanics.forwardHamiltonian_isSymmetric`: it is symmetric.
- `QuantumMechanics.IsSelfAdjoint.eq_of_le_of_isSymmetric`: a symmetric extension of a
  self-adjoint operator is the operator itself.
- `QuantumMechanics.forwardHamiltonian_eq_of_isLittleO`: if `F` is tangent to `e^{-iτH/ħ}`, the
  forward Hamiltonian is `H`.
- `QuantumMechanics.isSelfAdjoint_forwardHamiltonian_iff`: the forward Hamiltonian is
  self-adjoint iff `F` is tangent to a one-parameter unitary group.
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

end QuantumMechanics
