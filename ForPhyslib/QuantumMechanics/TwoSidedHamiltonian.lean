/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.ForwardHamiltonian

/-!
# The backward and two-sided Hamiltonians of a unitary evolution

Besides the forward Hamiltonian `iħ ∂₊ F τ ψ` (`QuantumMechanics.forwardHamiltonian`), a unitary
family `F τ = U(t₀ + τ, t₀)` with `F 0 = 1` has a backward Hamiltonian `iħ ∂₋ F τ ψ`, from the
left derivative at `τ = 0`, and a two-sided Hamiltonian `iħ ∂ F τ ψ`, from the derivative. This
file proves for both the statements proved for the forward one: symmetry, the local Stone theorem
(self-adjoint iff tangent to a one-parameter unitary group, now from the left resp. from both
sides), and the invariant-core criteria for essential self-adjointness and self-adjointness.

## i. Overview

The backward Hamiltonian of `F` is the forward Hamiltonian of the reflected family
`τ ↦ F (-τ)` for `-ħ`, and `e^{-iτH/(-ħ)} = e^{-i(-τ)H/ħ}`. The backward statements are the
forward ones for the reflected family, with the conditions moved from `τ ≥ 0` to `τ ≤ 0`.

The two-sided Hamiltonian is the infimum of the two one-sided ones: its domain is the set of
vectors on which both one-sided derivatives exist and agree. It is symmetric as a restriction
of the forward Hamiltonian. It is self-adjoint iff `F` is tangent to a one-parameter unitary group
from both sides; then all three Hamiltonians coincide.

Under the invariant-core hypotheses, which are already symmetric in time, the restriction of
the forward Hamiltonian to the core lies below all three. Each of them is therefore essentially
self-adjoint, with the same closure. If the generator differences tend to `0` from the left,
the backward Hamiltonian is self-adjoint; from both sides, all three are, and they are equal.

## ii. Key results

- `QuantumMechanics.backwardHamiltonian`, `QuantumMechanics.twoSidedHamiltonian`.
- `QuantumMechanics.backwardHamiltonian_eq_forwardHamiltonian`: backward is forward for the
  reflected family.
- `QuantumMechanics.twoSidedHamiltonian_eq_inf`: two-sided is forward `⊓` backward.
- `QuantumMechanics.backwardHamiltonian_isSymmetric`,
  `QuantumMechanics.twoSidedHamiltonian_isSymmetric`.
- `QuantumMechanics.isSelfAdjoint_backwardHamiltonian_iff`,
  `QuantumMechanics.isSelfAdjoint_twoSidedHamiltonian_iff`: local Stone theorems.
- `QuantumMechanics.isEssentiallySelfAdjoint_twoSidedHamiltonian`: an invariant core makes all
  three essentially self-adjoint, with one closure.
- `QuantumMechanics.isSelfAdjoint_backwardHamiltonian`,
  `QuantumMechanics.isSelfAdjoint_twoSidedHamiltonian`: self-adjointness when the generator
  differences vanish from the left, resp. from both sides.
-/

@[expose] public noncomputable section

namespace QuantumMechanics

open Filter Topology Set Asymptotics
open scoped InnerProductSpace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A right derivative of `τ ↦ f (-τ)` at `0` is minus a left derivative of `f`. -/
lemma hasDerivWithinAt_Ici_comp_neg_iff {f : ℝ → E} {v : E} :
    HasDerivWithinAt (fun τ => f (-τ)) v (Ici 0) 0 ↔ HasDerivWithinAt f (-v) (Iic 0) 0 := by
  have hm : MapsTo (fun τ : ℝ => -τ) (Ici 0) (Iic 0) := fun τ hτ => by
    simpa using (mem_Ici.mp hτ)
  have hm' : MapsTo (fun τ : ℝ => -τ) (Iic 0) (Ici 0) := fun τ hτ => by
    simpa using (mem_Iic.mp hτ)
  constructor
  · intro h
    have := h.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt hm' (by simp)
    simpa [Function.comp_def] using this
  · intro h
    have := h.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt hm (by simp)
    simpa [Function.comp_def] using this

lemma differentiableWithinAt_Ici_comp_neg_iff {f : ℝ → E} :
    DifferentiableWithinAt ℝ (fun τ => f (-τ)) (Ici 0) 0 ↔
      DifferentiableWithinAt ℝ f (Iic 0) 0 :=
  ⟨fun h => ⟨_, (hasDerivWithinAt_Ici_comp_neg_iff.mp h.hasDerivWithinAt).hasFDerivWithinAt⟩,
    fun h => ⟨_, ((hasDerivWithinAt_Ici_comp_neg_iff (v := -derivWithin f (Iic 0) 0)).mpr
      (by rw [neg_neg]; exact h.hasDerivWithinAt)).hasFDerivWithinAt⟩⟩

variable (F : ℝ → E →L[ℂ] E)

/-- The vectors `ψ` for which `τ ↦ F τ ψ` has a left derivative at `0`. -/
def backwardDomain : Submodule ℂ E where
  carrier := {ψ | DifferentiableWithinAt ℝ (fun τ => F τ ψ) (Iic 0) 0}
  add_mem' {ψ φ} hψ hφ := by
    change DifferentiableWithinAt ℝ (fun τ => F τ (ψ + φ)) (Iic 0) 0
    simp only [map_add]
    exact hψ.add hφ
  zero_mem' := by
    change DifferentiableWithinAt ℝ (fun τ => F τ 0) (Iic 0) 0
    simp only [map_zero]
    exact differentiableWithinAt_const 0
  smul_mem' c ψ hψ := by
    change DifferentiableWithinAt ℝ (fun τ => F τ (c • ψ)) (Iic 0) 0
    simp only [map_smul]
    exact hψ.const_smul c

/-- **The backward Hamiltonian** `iħ ∂₋ F τ ψ` at `τ = 0`, from the left derivative only. -/
def backwardHamiltonian (ħ : ℝ) : E →ₗ.[ℂ] E where
  domain := backwardDomain F
  toFun :=
    { toFun := fun ψ => (Complex.I * ħ) • derivWithin (fun τ => F τ ψ) (Iic 0) 0
      map_add' := fun ψ φ => by
        simp only [Submodule.coe_add, map_add]
        rw [derivWithin_fun_add ψ.2 φ.2, smul_add]
      map_smul' := fun c ψ => by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        rw [derivWithin_fun_const_smul c ψ.2, smul_comm] }

/-- The vectors `ψ` for which `τ ↦ F τ ψ` is differentiable at `0`. -/
def twoSidedDomain : Submodule ℂ E where
  carrier := {ψ | DifferentiableAt ℝ (fun τ => F τ ψ) 0}
  add_mem' {ψ φ} hψ hφ := by
    change DifferentiableAt ℝ (fun τ => F τ (ψ + φ)) 0
    simp only [map_add]
    exact hψ.add hφ
  zero_mem' := by
    change DifferentiableAt ℝ (fun τ => F τ 0) 0
    simp only [map_zero]
    exact differentiableAt_const 0
  smul_mem' c ψ hψ := by
    change DifferentiableAt ℝ (fun τ => F τ (c • ψ)) 0
    simp only [map_smul]
    exact hψ.const_smul c

/-- **The two-sided Hamiltonian** `iħ ∂ F τ ψ` at `τ = 0`. -/
def twoSidedHamiltonian (ħ : ℝ) : E →ₗ.[ℂ] E where
  domain := twoSidedDomain F
  toFun :=
    { toFun := fun ψ => (Complex.I * ħ) • deriv (fun τ => F τ ψ) 0
      map_add' := fun ψ φ => by
        simp only [Submodule.coe_add, map_add]
        rw [deriv_fun_add ψ.2 φ.2, smul_add]
      map_smul' := fun c ψ => by
        simp only [Submodule.coe_smul, map_smul, RingHom.id_apply]
        rw [deriv_fun_const_smul c ψ.2, smul_comm] }

variable {F}

lemma mem_backwardDomain {ψ : E} :
    ψ ∈ backwardDomain F ↔ DifferentiableWithinAt ℝ (fun τ => F τ ψ) (Iic 0) 0 :=
  Iff.rfl

lemma mem_twoSidedDomain {ψ : E} :
    ψ ∈ twoSidedDomain F ↔ DifferentiableAt ℝ (fun τ => F τ ψ) 0 :=
  Iff.rfl

lemma backwardHamiltonian_apply (ħ : ℝ) (ψ : (backwardHamiltonian F ħ).domain) :
    backwardHamiltonian F ħ ψ = (Complex.I * ħ) • derivWithin (fun τ => F τ ψ) (Iic 0) 0 :=
  rfl

lemma twoSidedHamiltonian_apply (ħ : ℝ) (ψ : (twoSidedHamiltonian F ħ).domain) :
    twoSidedHamiltonian F ħ ψ = (Complex.I * ħ) • deriv (fun τ => F τ ψ) 0 :=
  rfl

/-- **Reflection.** The backward Hamiltonian of `F` for `ħ` is the forward Hamiltonian of
`τ ↦ F (-τ)` for `-ħ`. -/
theorem backwardHamiltonian_eq_forwardHamiltonian (ħ : ℝ) :
    backwardHamiltonian F ħ = forwardHamiltonian (fun τ => F (-τ)) (-ħ) := by
  have hdom : backwardDomain F = forwardDomain fun τ => F (-τ) := by
    ext ψ
    exact differentiableWithinAt_Ici_comp_neg_iff.symm
  refine LinearPMap.ext hdom fun ψ hb hf => ?_
  rw [backwardHamiltonian_apply, forwardHamiltonian_apply]
  have h := (mem_forwardDomain.mp hf).hasDerivWithinAt
  have h' := (hasDerivWithinAt_Ici_comp_neg_iff (f := fun τ => F τ ψ)).mp h
  rw [h'.derivWithin (uniqueDiffWithinAt_Iic 0)]
  push_cast
  rw [smul_neg, mul_neg, neg_smul]

lemma twoSidedHamiltonian_le_forwardHamiltonian (ħ : ℝ) :
    twoSidedHamiltonian F ħ ≤ forwardHamiltonian F ħ :=
  ⟨fun _ hψ => mem_forwardDomain.mpr (mem_twoSidedDomain.mp hψ).differentiableWithinAt,
    fun ψ φ h => by
      have hd : DifferentiableAt ℝ (fun τ => F τ ψ) 0 := ψ.2
      rw [twoSidedHamiltonian_apply, forwardHamiltonian_apply, ← h,
        hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)]⟩

lemma twoSidedHamiltonian_le_backwardHamiltonian (ħ : ℝ) :
    twoSidedHamiltonian F ħ ≤ backwardHamiltonian F ħ :=
  ⟨fun _ hψ => mem_backwardDomain.mpr (mem_twoSidedDomain.mp hψ).differentiableWithinAt,
    fun ψ φ h => by
      have hd : DifferentiableAt ℝ (fun τ => F τ ψ) 0 := ψ.2
      rw [twoSidedHamiltonian_apply, backwardHamiltonian_apply, ← h,
        hd.hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 0)]⟩

/-- **The two-sided Hamiltonian is the infimum of the one-sided ones**: it is defined exactly
where both one-sided derivatives exist and agree. -/
theorem twoSidedHamiltonian_eq_inf {ħ : ℝ} (hħ : ħ ≠ 0) :
    twoSidedHamiltonian F ħ = forwardHamiltonian F ħ ⊓ backwardHamiltonian F ħ := by
  refine le_antisymm (le_inf (twoSidedHamiltonian_le_forwardHamiltonian ħ)
    (twoSidedHamiltonian_le_backwardHamiltonian ħ)) ⟨fun ψ ⟨hf, hb, heq⟩ => ?_, fun ψ φ h => ?_⟩
  · have hIħ : Complex.I * ħ ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)
    rw [forwardHamiltonian_apply, backwardHamiltonian_apply] at heq
    have hR := (mem_forwardDomain.mp hf).hasDerivWithinAt
    have hL := (mem_backwardDomain.mp hb).hasDerivWithinAt
    rw [smul_right_injective E hIħ heq] at hR
    have h := hL.union hR
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
    exact h.differentiableAt
  · exact ((twoSidedHamiltonian_le_forwardHamiltonian ħ).2 h.symm).symm

/-- **The backward Hamiltonian is symmetric**, from `⟨F τ ψ, F τ φ⟩ = ⟨ψ, φ⟩` for `τ ≤ 0`. -/
theorem backwardHamiltonian_isSymmetric (ħ : ℝ) (hF0 : F 0 = 1)
    (hF : ∀ τ, τ ≤ 0 → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) :
    (backwardHamiltonian F ħ).IsSymmetric := by
  rw [backwardHamiltonian_eq_forwardHamiltonian]
  exact forwardHamiltonian_isSymmetric (-ħ) (by simpa using hF0)
    fun τ hτ => hF (-τ) (by linarith)

/-- **The two-sided Hamiltonian is symmetric**, as a restriction of the forward one. -/
theorem twoSidedHamiltonian_isSymmetric (ħ : ℝ) (hF0 : F 0 = 1)
    (hF : ∀ τ, 0 ≤ τ → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) :
    (twoSidedHamiltonian F ħ).IsSymmetric :=
  (forwardHamiltonian_isSymmetric ħ hF0 hF).of_le (twoSidedHamiltonian_le_forwardHamiltonian ħ)

lemma tendsto_neg_nhdsWithin_Ici_Iic :
    Tendsto (fun τ : ℝ => -τ) (𝓝[≥] 0) (𝓝[≤] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨(continuous_neg.tendsto' (0 : ℝ) 0 neg_zero).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun τ hτ => by simpa using hτ⟩

lemma tendsto_neg_nhdsWithin_Iic_Ici :
    Tendsto (fun τ : ℝ => -τ) (𝓝[≤] 0) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨(continuous_neg.tendsto' (0 : ℝ) 0 neg_zero).mono_left
    nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun τ hτ => by simpa using hτ⟩

omit [InnerProductSpace ℂ E] in
/-- `f (-τ) = o(τ)` from the right iff `f τ = o(τ)` from the left. -/
lemma isLittleO_Ici_comp_neg_iff {f : ℝ → E} :
    (fun τ => f (-τ)) =o[𝓝[≥] 0] (fun τ => τ) ↔ f =o[𝓝[≤] 0] fun τ => τ := by
  constructor
  · intro h
    have := (h.comp_tendsto tendsto_neg_nhdsWithin_Iic_Ici)
    simpa [Function.comp_def] using isLittleO_neg_right.mp this
  · intro h
    exact isLittleO_neg_right.mp (h.comp_tendsto tendsto_neg_nhdsWithin_Ici_Iic)

variable [CompleteSpace E]

/-- `e^{-iτH/(-ħ)} = e^{-i(-τ)H/ħ}`, by uniqueness of the propagator. -/
lemma schrodingerPropagator_neg {ħ : ℝ} (hħ : ħ ≠ 0) {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H)
    (τ : ℝ) :
    schrodingerPropagator (neg_ne_zero.mpr hħ) hH τ = schrodingerPropagator hħ hH (-τ) := by
  refine (SolvesSchrodinger.eq_schrodingerPropagator
    (U := fun τ => schrodingerPropagator hħ hH (-τ)) (fun ψ t => ?_) (neg_ne_zero.mpr hħ) hH
    (by simp [schrodingerPropagator_zero]) τ).symm
  obtain ⟨hmem, hd⟩ := solvesSchrodinger_schrodingerPropagator hħ hH ψ (-t)
  refine ⟨hmem, ?_⟩
  have h := hd.scomp t (hasDerivAt_neg t)
  simp only [Function.comp_def] at h
  convert h using 1
  rw [neg_one_smul, Complex.ofReal_neg, mul_neg, inv_neg, neg_smul]

/-- **Tangent from the left.** If `F τ ψ - e^{-iτH/ħ} ψ = o(τ)` as `τ → 0⁻` on the domain of a
self-adjoint `H`, the backward Hamiltonian is `H`. -/
theorem backwardHamiltonian_eq_of_isLittleO {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ τ, τ ≤ 0 → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) {H : E →ₗ.[ℂ] E}
    (hH : IsSelfAdjoint H)
    (ho : ∀ ψ ∈ H.domain,
      (fun τ => F τ ψ - schrodingerPropagator hħ hH τ ψ) =o[𝓝[≤] 0] fun τ => τ) :
    backwardHamiltonian F ħ = H := by
  rw [backwardHamiltonian_eq_forwardHamiltonian]
  refine forwardHamiltonian_eq_of_isLittleO (neg_ne_zero.mpr hħ) (by simpa using hF0)
    (fun τ hτ => hF (-τ) (by linarith)) hH fun ψ hψ => ?_
  simp_rw [schrodingerPropagator_neg hħ hH]
  exact isLittleO_Ici_comp_neg_iff.mpr (ho ψ hψ)

/-- **Local Stone theorem, backward.** The backward Hamiltonian of a unitary `F` with `F 0 = 1`
is self-adjoint iff `F` is tangent from the left to a one-parameter unitary group. -/
theorem isSelfAdjoint_backwardHamiltonian_iff {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ τ, τ ≤ 0 → ∀ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) :
    IsSelfAdjoint (backwardHamiltonian F ħ) ↔
      ∃ (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H), ∀ ψ ∈ H.domain,
        (fun τ => F τ ψ - schrodingerPropagator hħ hH τ ψ) =o[𝓝[≤] 0] fun τ => τ := by
  rw [backwardHamiltonian_eq_forwardHamiltonian, isSelfAdjoint_forwardHamiltonian_iff
    (F := fun τ => F (-τ)) (neg_ne_zero.mpr hħ) (by simpa using hF0)
    (fun τ hτ => hF (-τ) (by linarith))]
  refine exists_congr fun H => exists_congr fun hH => forall₂_congr fun ψ _ => ?_
  simp_rw [schrodingerPropagator_neg hħ hH]
  exact isLittleO_Ici_comp_neg_iff (f := fun τ => F τ ψ - schrodingerPropagator hħ hH τ ψ)

/-- **Tangent from both sides.** If `F τ ψ - e^{-iτH/ħ} ψ = o(τ)` as `τ → 0` on the domain of a
self-adjoint `H`, the forward, backward and two-sided Hamiltonians are all `H`. -/
theorem twoSidedHamiltonian_eq_of_isLittleO {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ τ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H)
    (ho : ∀ ψ ∈ H.domain,
      (fun τ => F τ ψ - schrodingerPropagator hħ hH τ ψ) =o[𝓝 0] fun τ => τ) :
    forwardHamiltonian F ħ = H ∧ backwardHamiltonian F ħ = H ∧ twoSidedHamiltonian F ħ = H := by
  have hR := forwardHamiltonian_eq_of_isLittleO hħ hF0 (fun τ _ => hF τ) hH
    fun ψ hψ => (ho ψ hψ).mono nhdsWithin_le_nhds
  have hL := backwardHamiltonian_eq_of_isLittleO hħ hF0 (fun τ _ => hF τ) hH
    fun ψ hψ => (ho ψ hψ).mono nhdsWithin_le_nhds
  exact ⟨hR, hL, by rw [twoSidedHamiltonian_eq_inf hħ, hR, hL, inf_idem]⟩

/-- **Local Stone theorem, two-sided.** The two-sided Hamiltonian of a unitary `F` with
`F 0 = 1` is self-adjoint iff `F` is tangent at `0` to a one-parameter unitary group:
`F τ ψ - e^{-iτH/ħ} ψ = o(τ)` as `τ → 0`, for a self-adjoint `H` and every `ψ` in its domain. -/
theorem isSelfAdjoint_twoSidedHamiltonian_iff {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ τ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ) :
    IsSelfAdjoint (twoSidedHamiltonian F ħ) ↔
      ∃ (H : E →ₗ.[ℂ] E) (hH : IsSelfAdjoint H), ∀ ψ ∈ H.domain,
        (fun τ => F τ ψ - schrodingerPropagator hħ hH τ ψ) =o[𝓝 0] fun τ => τ := by
  refine ⟨fun hH => ⟨_, hH, fun ψ hψ => ?_⟩, fun ⟨H, hH, ho⟩ => ?_⟩
  · obtain ⟨hmem, hd⟩ := solvesSchrodinger_schrodingerPropagator hħ hH ⟨ψ, hψ⟩ 0
    have hψ' : (⟨schrodingerPropagator hħ hH 0 ψ, hmem⟩ : (twoSidedHamiltonian F ħ).domain) =
        ⟨ψ, hψ⟩ := by
      ext; simp [schrodingerPropagator_zero]
    rw [hψ'] at hd
    have hIħ : Complex.I * ħ ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)
    have hF' : HasDerivAt (fun τ => F τ ψ)
        ((Complex.I * ħ)⁻¹ • twoSidedHamiltonian F ħ ⟨ψ, hψ⟩) 0 := by
      rw [twoSidedHamiltonian_apply, smul_smul, inv_mul_cancel₀ hIħ, one_smul]
      exact (mem_twoSidedDomain.mp hψ).hasDerivAt
    have h := hF'.sub hd
    rw [sub_self, hasDerivAt_iff_isLittleO] at h
    simpa [hF0, schrodingerPropagator_zero] using h
  · rw [(twoSidedHamiltonian_eq_of_isLittleO hħ hF0 hF hH ho).2.2]
    exact hH

/-! ### An invariant core -/

/-- A symmetric extension of an essentially self-adjoint operator is essentially self-adjoint,
with the same closure. -/
lemma isEssentiallySelfAdjoint_of_le {L K : E →ₗ.[ℂ] E} (hL : L.IsEssentiallySelfAdjoint)
    (hK : K.IsSymmetric) (hKd : K.HasDenseDomain) (hle : L ≤ K) :
    K.IsEssentiallySelfAdjoint ∧ K.closure = L.closure := by
  have hA : IsSelfAdjoint L.closure := LinearPMap.isEssentiallySelfAdjoint_def.mp hL
  have heq : K.closure = L.closure := IsSelfAdjoint.eq_of_le_of_isSymmetric hA
    (hK.closure hKd) ((hK.isClosable hKd).closure_mono hle)
  exact ⟨by rw [LinearPMap.isEssentiallySelfAdjoint_def, heq]; exact hA, heq⟩

omit [CompleteSpace E] in
lemma domRestrict_forwardHamiltonian_le_twoSidedHamiltonian {ħ : ℝ} {D : Submodule ℂ E}
    (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x) :
    (forwardHamiltonian F ħ).domRestrict D ≤ twoSidedHamiltonian F ħ := by
  refine ⟨fun x hx => (hdiff x hx.1) 0, fun ψ φ h => ?_⟩
  obtain ⟨x, hx⟩ := ψ
  rw [domRestrict_forwardHamiltonian_apply hdiff, twoSidedHamiltonian_apply, ← h]

omit [CompleteSpace E] in
lemma domRestrict_backwardHamiltonian_eq {ħ : ℝ} {D : Submodule ℂ E}
    (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x) :
    (backwardHamiltonian F ħ).domRestrict D = (forwardHamiltonian F ħ).domRestrict D := by
  have hDb : D ≤ backwardDomain F := fun x hx => ((hdiff x hx) 0).differentiableWithinAt
  have hDf : D ≤ forwardDomain F := fun x hx => ((hdiff x hx) 0).differentiableWithinAt
  refine LinearPMap.ext ?_ fun x hb hf => ?_
  · rw [LinearPMap.domRestrict_domain, LinearPMap.domRestrict_domain]
    exact (inf_eq_left.mpr hDb).trans (inf_eq_left.mpr hDf).symm
  · rw [domRestrict_forwardHamiltonian_apply hdiff]
    change (Complex.I * ħ) • derivWithin (fun τ => F τ x) (Iic 0) 0 = _
    congr 1
    exact ((hdiff x hb.1) 0).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iic 0)

/-- **An invariant core, all three Hamiltonians.** Under the hypotheses of
`isEssentiallySelfAdjoint_forwardHamiltonian`, which are symmetric in time, the backward and the
two-sided Hamiltonians are essentially self-adjoint too, with the closure of the forward one. -/
theorem isEssentiallySelfAdjoint_twoSidedHamiltonian {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t, F t ∈ unitary (E →L[ℂ] E)) {D : Submodule ℂ E} (hD : Dense (D : Set E))
    (hinv : ∀ t, ∀ x ∈ D, F t x ∈ D) (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x)
    {C T : ℝ} (hT : 0 < T)
    (hC : ∀ t ∈ Icc (-T) T, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ C * ‖x‖) :
    (backwardHamiltonian F ħ).IsEssentiallySelfAdjoint ∧
      (twoSidedHamiltonian F ħ).IsEssentiallySelfAdjoint ∧
      (backwardHamiltonian F ħ).closure = (forwardHamiltonian F ħ).closure ∧
      (twoSidedHamiltonian F ħ).closure = (forwardHamiltonian F ħ).closure := by
  obtain ⟨hHD, -, hcl⟩ :=
    isEssentiallySelfAdjoint_forwardHamiltonian hħ hF0 hF hD hinv hdiff hT hC
  have hF' : ∀ τ x y, ⟪F τ x, F τ y⟫_ℂ = ⟪x, y⟫_ℂ :=
    fun τ => ContinuousLinearMap.inner_map_map_of_mem_unitary (hF τ)
  have hle := domRestrict_forwardHamiltonian_le_twoSidedHamiltonian (ħ := ħ) hdiff
  have hDle : D ≤ twoSidedDomain F := fun x hx => (hdiff x hx) 0
  have hb2 := twoSidedHamiltonian_le_backwardHamiltonian (F := F) ħ
  have h2 := isEssentiallySelfAdjoint_of_le hHD
    (twoSidedHamiltonian_isSymmetric ħ hF0 fun τ _ => hF' τ) (hD.mono hDle) hle
  have hb := isEssentiallySelfAdjoint_of_le hHD
    (backwardHamiltonian_isSymmetric ħ hF0 fun τ _ => hF' τ) (hD.mono (hDle.trans hb2.1))
    (hle.trans hb2)
  exact ⟨hb.1, h2.1, hb.2.trans hcl.symm, h2.2.trans hcl.symm⟩

/-- **Self-adjointness, backward.** Under the hypotheses of
`isEssentiallySelfAdjoint_forwardHamiltonian`, suppose that the generators at times `t → 0⁻`
approach the one at `0` on `D`. Then the backward Hamiltonian is self-adjoint: it is the closure
of the restriction of the forward one to `D`. -/
theorem isSelfAdjoint_backwardHamiltonian {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t, F t ∈ unitary (E →L[ℂ] E)) {D : Submodule ℂ E} (hD : Dense (D : Set E))
    (hinv : ∀ t, ∀ x ∈ D, F t x ∈ D) (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x)
    {C T : ℝ} (hT : 0 < T)
    (hC : ∀ t ∈ Icc (-T) T, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ C * ‖x‖)
    (hω : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (-δ) 0, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ ε * ‖x‖) :
    IsSelfAdjoint (backwardHamiltonian F ħ) ∧
      backwardHamiltonian F ħ = ((forwardHamiltonian F ħ).domRestrict D).closure := by
  -- The reflected family `G t = F (-t)` satisfies the forward hypotheses.
  have hG : ∀ t, ∀ x ∈ D, ‖deriv (fun s => F (-s) x) t - deriv (fun s => F (-s) (F (-t) x)) 0‖ =
      ‖deriv (fun s => F s x) (-t) - deriv (fun s => F s (F (-t) x)) 0‖ := fun t x _ => by
    rw [deriv_comp_neg (f := fun s => F s x), deriv_comp_neg (f := fun s => F s (F (-t) x)),
      neg_zero, neg_sub_neg, norm_sub_rev]
  have h := isSelfAdjoint_forwardHamiltonian (F := fun t => F (-t)) (neg_ne_zero.mpr hħ)
    (by simpa using hF0) (fun t => hF (-t)) hD (fun t x hx => hinv (-t) x hx)
    (fun x hx => (hdiff x hx).comp differentiable_neg) hT
    (fun t ht x hx => by
      rw [hG t x hx]
      exact hC (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ x hx)
    (fun ε hε => by
      obtain ⟨δ, hδ, hω'⟩ := hω ε hε
      exact ⟨δ, hδ, fun t ht x hx => by
        rw [hG t x hx]
        exact hω' (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ x hx⟩)
  rw [← backwardHamiltonian_eq_forwardHamiltonian, domRestrict_backwardHamiltonian_eq hdiff] at h
  exact h

/-- **Self-adjointness, two-sided.** Under the hypotheses of
`isEssentiallySelfAdjoint_forwardHamiltonian`, suppose that the generators at times `t → 0`
approach the one at `0` on `D`, from both sides. Then the forward, backward and two-sided
Hamiltonians coincide and are self-adjoint: the closure of the restriction to `D`. -/
theorem isSelfAdjoint_twoSidedHamiltonian {ħ : ℝ} (hħ : ħ ≠ 0) (hF0 : F 0 = 1)
    (hF : ∀ t, F t ∈ unitary (E →L[ℂ] E)) {D : Submodule ℂ E} (hD : Dense (D : Set E))
    (hinv : ∀ t, ∀ x ∈ D, F t x ∈ D) (hdiff : ∀ x ∈ D, Differentiable ℝ fun t => F t x)
    {C T : ℝ} (hT : 0 < T)
    (hC : ∀ t ∈ Icc (-T) T, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ C * ‖x‖)
    (hω : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Icc (-δ) δ, ∀ x ∈ D,
      ‖deriv (fun s => F s x) t - deriv (fun s => F s (F t x)) 0‖ ≤ ε * ‖x‖) :
    IsSelfAdjoint (twoSidedHamiltonian F ħ) ∧
      forwardHamiltonian F ħ = twoSidedHamiltonian F ħ ∧
      backwardHamiltonian F ħ = twoSidedHamiltonian F ħ ∧
      twoSidedHamiltonian F ħ = ((forwardHamiltonian F ħ).domRestrict D).closure := by
  obtain ⟨hRsa, hR⟩ := isSelfAdjoint_forwardHamiltonian hħ hF0 hF hD hinv hdiff hT hC
    fun ε hε => by
      obtain ⟨δ, hδ, hω'⟩ := hω ε hε
      exact ⟨δ, hδ, fun t ht => hω' t ⟨by linarith [ht.1], ht.2⟩⟩
  obtain ⟨-, hL⟩ := isSelfAdjoint_backwardHamiltonian hħ hF0 hF hD hinv hdiff hT hC
    fun ε hε => by
      obtain ⟨δ, hδ, hω'⟩ := hω ε hε
      exact ⟨δ, hδ, fun t ht => hω' t ⟨ht.1, by linarith [ht.2]⟩⟩
  have h2 : twoSidedHamiltonian F ħ = forwardHamiltonian F ħ := by
    rw [twoSidedHamiltonian_eq_inf hħ, hL, ← hR, inf_idem]
  refine ⟨h2 ▸ hRsa, h2.symm, ?_, h2.trans hR⟩
  rw [h2, hL, ← hR]

end QuantumMechanics
