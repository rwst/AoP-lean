/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.Stone
public import UnitaryEntropy.MomentumDomain

/-!
# The twisted translations are `e^{-itH_α/ħ}`

This continues `UnitaryEntropy.MomentumDomain`. On `L²(0, 1)`, let `H_α` be the momentum
`-i d/dx` with the boundary condition `ψ(1) = e^{iα} ψ(0)` (`momentum`). Its graph consists of
the pairs `(ψ, -i g)` with `ψ(x) = c + ∫₀ˣ g`, `g ∈ L²(0, 1)` and `c + ∫₀¹ g = e^{iα} c`
(`IsMomentumPair`). Then `H_α` is self-adjoint, and `U_α(t) = e^{-itH_α/ħ}`: the twisted
translation by `t/ħ` solves the Schrödinger equation for `H_α`, so it is the exponential of
`-itH_α/ħ` given by the spectral theorem.

The switched propagator of `UnitaryEntropy.MomentumExtensions` is `U_α(t)` for `t ≥ 0` and
`U_β(t)` for `t < 0`. Its right derivative at `0` exists exactly on the domain of `H_α`, its left
derivative exactly on the domain of `H_β`, and `H₀ = iħ U'(0)` is a restriction of both.

## Proof

Let `eₙ = e^{i(α + 2πn)x}`, the eigenbasis of `U_α` (`twistedBasis`). Integration by parts
(`inner_planeWave_neg_I_smul`) shows that `(ψ, h)` is in the graph of `H_α` iff
`⟨eₙ, h⟩ = (α + 2πn) ⟨eₙ, ψ⟩` for all `n` (`isMomentumPair_iff`). So `H_α` is diagonal in the
basis `eₙ`, with the real eigenvalues `α + 2πn`, and is self-adjoint. `U_α(t)` is diagonal in the
same basis, with the eigenvalues `e^{-i(α + 2πn)t/ħ}`. So it maps the domain of `H_α` to itself,
and `hasDerivAt_twistedTranslation_of_inner` gives `d/dt U_α(t) ψ = (iħ)⁻¹ H_α U_α(t) ψ`. A
solution of the Schrödinger equation with `U(0) = 1` is `e^{-itH/ħ}`
(`QuantumMechanics.SolvesSchrodinger.eq_schrodingerPropagator`).

## Main results

* `momentum`, `isMomentumPair_iff`: `H_α`, and its graph in the eigenbasis.
* `isSelfAdjoint_momentum`: `H_α` is self-adjoint.
* `solvesSchrodinger_twistedTranslation`: `U_α(t)` solves the Schrödinger equation for `H_α`.
* `twistedTranslation_eq_schrodingerPropagator`: `U_α(t) = e^{-itH_α/ħ}`.
* `exists_hasDerivWithinAt_iff`: `t ↦ U_α(t) ψ` has a derivative at `0`, even a one-sided one,
  exactly for `ψ` in the domain of `H_α`.
* `switchedHamiltonian_le_momentum_left`, `switchedHamiltonian_le_momentum_right`: `H₀ ⊆ H_α`
  and `H₀ ⊆ H_β`.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy

open MeasureTheory Filter Topology Set AddCircle QuantumMechanics
open scoped ENNReal InnerProductSpace ComplexConjugate Real LinearPMap

/-- The circle `ℝ/ℤ`. -/
local notation "𝕋" => AddCircle (1 : ℝ)

/-- Haar probability measure on `ℝ/ℤ`, which is Lebesgue measure on `[0, 1)`. -/
local notation "μc" => (haarAddCircle : Measure 𝕋)

/-- `L²(0, 1)`, as `L²` of the circle. -/
local notation "L²" => Lp ℂ 2 μc

local notation "U" => switchedPropagator

variable {ħ α β : ℝ}

/-! ### The momentum `H_α` -/

/-- `(ψ, h)` is in the graph of `H_α = -i d/dx` with `ψ(1) = e^{iα} ψ(0)`: `ψ(x) = c + ∫₀ˣ g`
with `g ∈ L²(0, 1)`, `c + ∫₀¹ g = e^{iα} c`, and `h = -i g`. -/
def IsMomentumPair (α : ℝ) (ψ h : L²) : Prop :=
  ∃ (c : ℂ) (g : L²), c + ∫ u in (0 : ℝ)..1, g (u : 𝕋) = Complex.exp (Complex.I * α) * c ∧
    ψ = c • planeWave 0 + primitive g ∧ h = (-Complex.I) • g

/-- **The graph of `H_α` in its eigenbasis**: `(ψ, h)` is in it iff
`⟨eₙ, h⟩ = (α + 2πn) ⟨eₙ, ψ⟩` for all `n`. -/
theorem isMomentumPair_iff {ψ h : L²} :
    IsMomentumPair α ψ h ↔ ∀ n : ℤ, ⟪twistedBasis α n, h⟫_ℂ =
      ((α + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis α n, ψ⟫_ℂ := by
  constructor
  · rintro ⟨c, g, hbc, rfl, rfl⟩ n
    have h₁ := inner_planeWave_neg_I_smul (α + 2 * π * n) g
    rw [← twistedBasis_apply, exp_twistedBasis_eigenvalue] at h₁
    have h₂ := mul_inner_twistedBasis_planeWave_zero α n
    have he : Complex.exp (-(Complex.I * α)) * Complex.exp (Complex.I * α) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    rw [h₁, inner_add_right, inner_smul_right]
    linear_combination (-c) * h₂ - Complex.I * Complex.exp (-(Complex.I * α)) * hbc -
      Complex.I * c * he
  · intro hr
    set g : L² := Complex.I • h
    have hg : h = (-Complex.I) • g := by
      rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    have hf : ∀ n : ℤ, ((α + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis α n, ψ - primitive g⟫_ℂ =
        -(Complex.I * Complex.exp (-(Complex.I * α)) * ∫ u in (0 : ℝ)..1, g (u : 𝕋)) :=
      fun n => by
        have h₁ := inner_planeWave_neg_I_smul (α + 2 * π * n) g
        rw [← twistedBasis_apply, exp_twistedBasis_eigenvalue, ← hg, hr n] at h₁
        rw [inner_sub_right]
        linear_combination h₁
    obtain ⟨k, hk, hc⟩ := exists_smul_of_mul_inner_twistedBasis hf
    exact ⟨k, g, by rw [hc]; ring, sub_eq_iff_eq_add.mp hk, hg⟩

variable (α) in
/-- The graph of `H_α`. -/
def momentumGraph : Submodule ℂ (L² × L²) where
  carrier := {p | IsMomentumPair α p.1 p.2}
  add_mem' {p q} hp hq := isMomentumPair_iff.mpr fun n => by
    rw [Prod.fst_add, Prod.snd_add, inner_add_right, inner_add_right, isMomentumPair_iff.mp hp n,
      isMomentumPair_iff.mp hq n, mul_add]
  zero_mem' := isMomentumPair_iff.mpr fun n => by simp
  smul_mem' c p hp := isMomentumPair_iff.mpr fun n => by
    rw [Prod.smul_fst, Prod.smul_snd, inner_smul_right, inner_smul_right,
      isMomentumPair_iff.mp hp n, mul_left_comm]

lemma momentumGraph_isGraph :
    ∀ (p : L² × L²) (_ : p ∈ momentumGraph α) (_ : p.1 = 0), p.2 = 0 := by
  rintro ⟨ψ, h⟩ hp (rfl : ψ = 0)
  refine (twistedBasis α).ext_inner fun n => ?_
  rw [isMomentumPair_iff.mp hp n, inner_zero_right, mul_zero]

variable (α) in
/-- **The momentum `H_α = -i d/dx` with the boundary condition `ψ(1) = e^{iα} ψ(0)`.** -/
def momentum : L² →ₗ.[ℂ] L² := (momentumGraph α).toLinearPMap

lemma mem_graph_momentum {ψ h : L²} :
    (ψ, h) ∈ (momentum α).graph ↔ IsMomentumPair α ψ h := by
  rw [momentum, Submodule.toLinearPMap_graph_eq _ momentumGraph_isGraph]
  rfl

/-- `H_α eₙ = (α + 2πn) eₙ`, coordinatewise. -/
lemma inner_twistedBasis_momentum (ψ : (momentum α).domain) (n : ℤ) :
    ⟪twistedBasis α n, momentum α ψ⟫_ℂ =
      ((α + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis α n, (ψ : L²)⟫_ℂ :=
  isMomentumPair_iff.mp (mem_graph_momentum.mp ((momentum α).mem_graph ψ)) n

/-- If `⟨eₙ, h⟩ = (α + 2πn) ⟨eₙ, ψ⟩` for all `n`, then `ψ` is in the domain of `H_α` and
`H_α ψ = h`. -/
lemma momentum_of_inner {ψ h : L²}
    (hr : ∀ n : ℤ, ⟪twistedBasis α n, h⟫_ℂ =
      ((α + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis α n, ψ⟫_ℂ) :
    ∃ hψ : ψ ∈ (momentum α).domain, momentum α ⟨ψ, hψ⟩ = h := by
  obtain ⟨⟨y, hy⟩, hy₁, hy₂⟩ :=
    ((momentum α).mem_graph_iff).mp (mem_graph_momentum.mpr (isMomentumPair_iff.mpr hr))
  dsimp only at hy₁ hy₂
  subst hy₁
  exact ⟨hy, hy₂⟩

/-- `eₙ` is an eigenvector of `H_α`, with eigenvalue `α + 2πn`. -/
lemma momentum_twistedBasis (n : ℤ) :
    ∃ h : twistedBasis α n ∈ (momentum α).domain,
      momentum α ⟨_, h⟩ = ((α + 2 * π * n : ℝ) : ℂ) • twistedBasis α n :=
  momentum_of_inner fun m => by
    rw [inner_smul_right, orthonormal_iff_ite.mp (twistedBasis α).orthonormal]
    split_ifs with h
    · rw [h]
    · simp

lemma dense_domain_momentum : Dense ((momentum α).domain : Set L²) :=
  (Submodule.dense_iff_topologicalClosure_eq_top.mpr (twistedBasis α).dense_span).mono
    (Submodule.span_le.mpr (by rintro _ ⟨n, rfl⟩; exact (momentum_twistedBasis n).1))

lemma isFormalAdjoint_momentum : (momentum α).IsFormalAdjoint (momentum α) := fun ψ φ => by
  rw [← (twistedBasis α).tsum_inner_mul_inner, ← (twistedBasis α).tsum_inner_mul_inner]
  refine tsum_congr fun n => ?_
  rw [← inner_conj_symm, inner_twistedBasis_momentum, inner_twistedBasis_momentum, map_mul,
    Complex.conj_ofReal, inner_conj_symm]
  ring

/-- **`H_α` is self-adjoint.** -/
theorem isSelfAdjoint_momentum : IsSelfAdjoint (momentum α) := by
  rw [LinearPMap.isSelfAdjoint_def]
  refine le_antisymm (LinearPMap.le_of_le_graph fun p hp => ?_)
    (isFormalAdjoint_momentum.le_adjoint dense_domain_momentum)
  obtain ⟨y, hy₁, hy₂⟩ := (LinearPMap.mem_graph_iff _).mp hp
  rw [← Prod.mk.eta (p := p), ← hy₁, ← hy₂, mem_graph_momentum, isMomentumPair_iff]
  intro n
  obtain ⟨he, hHe⟩ := momentum_twistedBasis (α := α) n
  have h := LinearPMap.adjoint_isFormalAdjoint dense_domain_momentum y ⟨_, he⟩
  rw [hHe, inner_smul_right] at h
  rw [← inner_conj_symm, h, map_mul, Complex.conj_ofReal, inner_conj_symm]

/-! ### `U_α(t) = e^{-itH_α/ħ}` -/

lemma twistedTranslation_add_apply (γ a b : ℝ) (f : L²) :
    twistedTranslation γ (a + b) f = twistedTranslation γ a (twistedTranslation γ b f) := by
  refine (twistedBasis γ).ext_inner fun n => ?_
  rw [inner_twistedBasis_twistedTranslation, inner_twistedBasis_twistedTranslation,
    inner_twistedBasis_twistedTranslation, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `U_α(t)` maps the domain of `H_α` to itself and commutes with `H_α`. -/
lemma momentum_twistedTranslation (s : ℝ) (ψ : (momentum α).domain) :
    ∃ h : twistedTranslation α s ψ ∈ (momentum α).domain,
      momentum α ⟨_, h⟩ = twistedTranslation α s (momentum α ψ) :=
  momentum_of_inner fun n => by
    rw [inner_twistedBasis_twistedTranslation, inner_twistedBasis_twistedTranslation,
      inner_twistedBasis_momentum]
    ring

lemma hasDerivAt_twistedTranslation_momentum (ψ : (momentum α).domain) :
    HasDerivAt (fun t => twistedTranslation α (t / ħ) ψ) ((Complex.I * ħ)⁻¹ • momentum α ψ) 0 :=
  hasDerivAt_twistedTranslation_of_inner fun n => by
    rw [inner_smul_right, inner_twistedBasis_momentum, mul_inv, Complex.inv_I]
    push_cast
    ring

variable (ħ α) in
/-- **`U_α(t)` solves the Schrödinger equation for `H_α`**: for `ψ` in the domain of `H_α`,
`d/dt U_α(t) ψ = (iħ)⁻¹ H_α U_α(t) ψ`. -/
theorem solvesSchrodinger_twistedTranslation :
    SolvesSchrodinger ħ (momentum α) fun t => twistedTranslation α (t / ħ) := fun ψ t => by
  obtain ⟨hmem, -⟩ := momentum_twistedTranslation (t / ħ) ψ
  refine ⟨hmem, ?_⟩
  have h := HasDerivAt.comp_sub_const t t
    (by rw [sub_self]; exact hasDerivAt_twistedTranslation_momentum (ħ := ħ) ⟨_, hmem⟩)
  refine h.congr_of_eventuallyEq (.of_forall fun s => ?_)
  change twistedTranslation α (s / ħ) ψ =
    twistedTranslation α ((s - t) / ħ) (twistedTranslation α (t / ħ) ψ)
  rw [← twistedTranslation_add_apply, sub_div, sub_add_cancel]

/-- **`U_α(t) = e^{-itH_α/ħ}`**, with the exponential of the spectral theorem. -/
theorem twistedTranslation_eq_schrodingerPropagator (hħ : ħ ≠ 0) (t : ℝ) :
    twistedTranslation α (t / ħ) = schrodingerPropagator hħ (isSelfAdjoint_momentum (α := α)) t :=
  (solvesSchrodinger_twistedTranslation ħ α).eq_schrodingerPropagator hħ isSelfAdjoint_momentum
    (by simp only [zero_div, twistedTranslation_zero]) t

/-! ### One-sided derivatives and the switched Hamiltonian -/

/-- If `t ↦ U_γ(t) ψ` has derivative `v` at `0` within `s`, then `ψ` is in the domain of `H_γ`
and `H_γ ψ = iħ v`. -/
lemma momentum_of_hasDerivWithinAt (hħ : ħ ≠ 0) {γ : ℝ} {s : Set ℝ}
    (hs : UniqueDiffWithinAt ℝ s 0) (h0 : (0 : ℝ) ∈ s) {ψ v : L²}
    (h : HasDerivWithinAt (fun t => twistedTranslation γ (t / ħ) ψ) v s 0) :
    ∃ hψ : ψ ∈ (momentum γ).domain, momentum γ ⟨ψ, hψ⟩ = (Complex.I * ħ) • v := by
  have hħc : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ
  refine momentum_of_inner fun n => ?_
  rw [inner_smul_right, inner_twistedBasis_of_hasDerivWithinAt hs h0 h n, Complex.ofReal_div]
  field_simp
  linear_combination (-((γ + 2 * π * n : ℝ) : ℂ) * ⟪twistedBasis γ n, ψ⟫_ℂ) * Complex.I_sq

/-- **The derivative of `t ↦ U_γ(t) ψ` at `0`**, even a one-sided one, exists exactly for `ψ` in
the domain of `H_γ`. -/
theorem exists_hasDerivWithinAt_iff (hħ : ħ ≠ 0) {γ : ℝ} {s : Set ℝ}
    (hs : UniqueDiffWithinAt ℝ s 0) (h0 : (0 : ℝ) ∈ s) {ψ : L²} :
    (∃ v, HasDerivWithinAt (fun t => twistedTranslation γ (t / ħ) ψ) v s 0) ↔
      ψ ∈ (momentum γ).domain :=
  ⟨fun ⟨_, h⟩ => (momentum_of_hasDerivWithinAt hħ hs h0 h).1,
    fun hψ => ⟨_, (hasDerivAt_twistedTranslation_momentum ⟨ψ, hψ⟩).hasDerivWithinAt⟩⟩

/-- **`H₀ ⊆ H_α`**: the generator of the switched propagator at `0` is a restriction of `H_α`. -/
theorem switchedHamiltonian_le_momentum_left (hħ : ħ ≠ 0) :
    switchedHamiltonian ħ α β ≤ momentum α := by
  have key : ∀ ψ : (switchedHamiltonian ħ α β).domain, ∃ h : (ψ : L²) ∈ (momentum α).domain,
      momentum α ⟨ψ, h⟩ = switchedHamiltonian ħ α β ψ := fun ψ => by
    rw [switchedHamiltonian_apply]
    exact momentum_of_hasDerivWithinAt hħ (uniqueDiffWithinAt_Ici 0) (mem_Ici.mpr le_rfl)
      ((mem_switchedDomain.mp ψ.2).hasDerivAt.hasDerivWithinAt.congr
        (fun t ht => by rw [switchedPropagator_of_nonneg ht])
        (by rw [switchedPropagator_of_nonneg le_rfl]))
  refine ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, fun ψ φ hψφ => ?_⟩
  obtain ⟨h, hH⟩ := key ψ
  rw [← hH]
  exact congrArg _ (Subtype.ext hψφ)

/-- **`H₀ ⊆ H_β`**: the generator of the switched propagator at `0` is a restriction of `H_β`. -/
theorem switchedHamiltonian_le_momentum_right (hħ : ħ ≠ 0) :
    switchedHamiltonian ħ α β ≤ momentum β := by
  have key : ∀ ψ : (switchedHamiltonian ħ α β).domain, ∃ h : (ψ : L²) ∈ (momentum β).domain,
      momentum β ⟨ψ, h⟩ = switchedHamiltonian ħ α β ψ := fun ψ => by
    rw [switchedHamiltonian_apply]
    exact momentum_of_hasDerivWithinAt hħ (uniqueDiffWithinAt_Iic 0) (mem_Iic.mpr le_rfl)
      ((mem_switchedDomain.mp ψ.2).hasDerivAt.hasDerivWithinAt.congr
        (fun t ht => by rw [switchedPropagator_of_nonpos ht])
        (by rw [switchedPropagator_of_nonpos le_rfl]))
  refine ⟨fun ψ hψ => (key ⟨ψ, hψ⟩).1, fun ψ φ hψφ => ?_⟩
  obtain ⟨h, hH⟩ := key ψ
  rw [← hH]
  exact congrArg _ (Subtype.ext hψφ)

end UnitaryEntropy
