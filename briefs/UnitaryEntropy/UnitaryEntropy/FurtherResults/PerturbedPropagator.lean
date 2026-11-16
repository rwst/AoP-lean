/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.InnerProductSpace.StronglyContinuousUnitary
public import ForMathlib.Analysis.Normed.Operator.LinearPMapGraph
public import ForMathlib.Analysis.Normed.Operator.StronglyContinuous
public import ForPhyslib.QuantumMechanics.Howland
public import ForPhyslib.QuantumMechanics.VonNeumannEntropy

import UnitaryEntropy.Propagator
import UnitaryEntropy.Unbounded

/-!
# Further results: the propagator of an unbounded `H(t) = H₀ + V(t)`

Not part of the brief. This file formalizes Sec. 3 of `further-results.tex` in the brief's
directory. The proof of the brief's Theorem 2 (⇒) assumes that "the Schrödinger equation gives
rise to a differentiable unitary propagator". For bounded `H(t)` this is proved in
`UnitaryEntropy.Propagator`. Here it is proved for a class of unbounded, time-dependent
Hamiltonians, with hypotheses of the kind used in Kato's theory of hyperbolic evolution equations:
the domain `Y = D(H₀)` is invariant, and the perturbation is strongly continuous on it in the
graph norm.

Setting: a complex Hilbert space `E` of any dimension, `ħ ≠ 0`, a self-adjoint, in general
unbounded `H₀`, and a regular perturbation `V` (`IsRegularPerturbation`): every `V t` is bounded
and self-adjoint, `t ↦ V t x` is continuous, `V t` maps the domain `D(H₀)` into itself, and
`t ↦ H₀ V t x` is continuous for `x ∈ D(H₀)`. The Hamiltonian is `H(t) = H₀ + V t` on `D(H₀)`.
`SolvesPerturbed ħ H₀ V U` says that for `ψ ∈ D(H₀)` every `U t ψ` is in `D(H₀)` and
`d/dt U t ψ = (iħ)⁻¹ H(t) U t ψ`.

Main results:
* `existsUnique_propagator`  exactly one family of bounded operators `U` with `U 0 = 1` solves the
  equation; it is unitary and strongly continuous, and `U t†` preserves `D(H₀)`
  (`exists_propagator`, `eq_of_solvesPerturbed`);
* `twoParam`, `solvesPerturbed_twoParam`, `eq_twoParam`  the two-parameter propagator
  `U(t, s) = U t U s†` is the unique solution from time `s`;
* `unitaryPropagator`  it is a strongly continuous unitary propagator, so Howland's quasi-energy
  operator exists for it;
* `twoParam_conserves_vonNeumannEntropy`  DR-INFO: the evolution preserves density operators and
  the von Neumann entropy, and the past is reconstructed;
* `differentiableAt_twoParam_proj`  EVDIFF on the dense set `D(H₀)` of pure states.

Proof: the interaction picture. With `W t = e^{-itH₀/ħ}` (`schrodingerPropagator`), the
interaction-picture perturbation `V_I(t) = W(-t) V t W t` (`interactionOp`) is bounded,
self-adjoint and strongly continuous, so `U_I' = (iħ)⁻¹ V_I U_I` has a unitary solution
(`UnitaryEntropy.exists_propagator_of_continuous_apply`). The same equation is solved on the graph
of `H₀`, a Banach space on which `V_I(t)` acts boundedly by the closed graph theorem
(`LinearPMap.graphLift`, `interactionGraph`). By uniqueness on `E` the two solutions agree, so
`U_I t` maps `D(H₀)` into itself, and so does its inverse, which is the solution on the graph run
backwards (`exists_interactionPropagator`). Then `U t = W t U_I t`, and the product rule for
strongly continuous families (`ContinuousLinearMap.hasDerivAt_apply_apply`) gives the equation.
Uniqueness: for two solutions, `⟪U t φ, Ũ t ψ⟫` has derivative `0` on `D(H₀)`, as `H(t)` is
symmetric there.

The general constant-domain theorem of Kato, for `H(t)` not of the form `H₀ + V(t)` with bounded
`V(t)`, is not formalized. The comparator lane, which certifies the main file of the brief, does
not depend on this module.

## References

- T. Kato, *Linear evolution equations of "hyperbolic" type*, J. Fac. Sci. Univ. Tokyo 17
  (1970), 241–258.
- A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Springer (1983), Ch. 5.
-/

@[expose] public noncomputable section

namespace UnitaryEntropy.FurtherResults

open InnerProductSpace QuantumMechanics QuantumMechanics.Wigner Filter Topology
open LinearPMap (fst_mem_domain graphMk graphFst graphLift continuous_graphLift_apply)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ħ : ℝ} {H₀ : E →ₗ.[ℂ] E}

/-! ## The free propagator -/

section Free

variable [CompleteSpace E] (hħ : ħ ≠ 0) (hH₀ : IsSelfAdjoint H₀)

/-- The free propagator `e^{-itH₀/ħ}` as a strongly continuous unitary group. -/
lemma exists_freeGroup : ∃ W : StronglyContinuousUnitaryGroup E,
    W.toFun = schrodingerPropagator hħ hH₀ :=
  exists_stronglyContinuousUnitaryGroup_of_solvesSchrodinger hħ hH₀
    (schrodingerPropagator_zero hħ hH₀) (solvesSchrodinger_schrodingerPropagator hħ hH₀)

local notation "W" => schrodingerPropagator hħ hH₀

include hħ hH₀ in
lemma free_mem_unitary (t : ℝ) : W t ∈ unitary (E →L[ℂ] E) :=
  schrodingerPropagator_mem_unitary hħ hH₀ t

include hħ hH₀ in
lemma free_add (s t : ℝ) : W (s + t) = W s * W t := by
  obtain ⟨V, hV⟩ := exists_freeGroup hħ hH₀
  rw [← hV]
  exact V.map_add s t

include hħ hH₀ in
lemma free_continuous_apply (x : E) : Continuous fun t => W t x := by
  obtain ⟨V, hV⟩ := exists_freeGroup hħ hH₀
  rw [← hV]
  exact V.continuous_apply x

include hħ hH₀ in
lemma free_neg (t : ℝ) : W (-t) = star (W t) := by
  have h1 : W (-t) * W t = 1 := by
    rw [← free_add hħ hH₀, neg_add_cancel, schrodingerPropagator_zero]
  have h2 := (Unitary.mem_iff.mp (free_mem_unitary hħ hH₀ t)).2
  calc W (-t) = W (-t) * (W t * star (W t)) := by rw [h2, mul_one]
    _ = star (W t) := by rw [← mul_assoc, h1, one_mul]

include hħ hH₀ in
lemma free_mem_domain {x : E} (hx : x ∈ H₀.domain) (t : ℝ) : W t x ∈ H₀.domain :=
  (solvesSchrodinger_schrodingerPropagator hħ hH₀ ⟨x, hx⟩ t).1

include hħ hH₀ in
/-- `e^{-itH₀/ħ}` commutes with `H₀` on its domain. -/
lemma free_commute (x : H₀.domain) (t : ℝ) :
    H₀ ⟨W t x, free_mem_domain hħ hH₀ x.2 t⟩ = W t (H₀ x) := by
  set c : ℂ := (Complex.I * ħ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ))
  obtain ⟨_, h₁⟩ := solvesSchrodinger_schrodingerPropagator hħ hH₀ x t
  obtain ⟨h0, h₂⟩ := solvesSchrodinger_schrodingerPropagator hħ hH₀ x 0
  have hx0 : (⟨W 0 x, h0⟩ : H₀.domain) = x := by
    ext
    simp [schrodingerPropagator_zero]
  rw [hx0] at h₂
  have h₃ : HasDerivAt (fun s => W t (W (s - t) x)) (W t (c • H₀ x)) t := by
    have := HasDerivAt.comp_sub_const t t (by rwa [sub_self])
    exact ((W t).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t this
  have heq : (fun s => W t (W (s - t) x)) = fun s => W s x := by
    ext s
    change (W t * W (s - t)) x = W s x
    rw [← free_add hħ hH₀, add_sub_cancel]
  rw [heq] at h₃
  have := h₁.unique h₃
  rw [map_smul] at this
  exact smul_right_injective E hc this

end Free

/-! ## The graph space of `H₀` -/

variable [CompleteSpace E] in
/-- The graph of a self-adjoint `H₀` is closed, so it is a Banach space. -/
lemma isClosed_graph (hH₀ : IsSelfAdjoint H₀) : IsClosed (H₀.graph : Set (E × E)) := hH₀.isClosed

/-! ## The interaction picture -/

variable [CompleteSpace E] in
/-- **Regular perturbation** of `H₀`: a strongly continuous family of bounded self-adjoint
operators `V t` that maps the domain of `H₀` into itself, with `t ↦ H₀ (V t x)` continuous for
every `x` in the domain. Then `V t` is bounded in the graph norm of `H₀` (closed graph theorem)
and strongly continuous there. -/
structure IsRegularPerturbation (H₀ : E →ₗ.[ℂ] E) (V : ℝ → E →L[ℂ] E) : Prop where
  isSelfAdjoint : ∀ t, IsSelfAdjoint (V t)
  continuous_apply : ∀ x, Continuous (V · x)
  mem_domain : ∀ t, ∀ x ∈ H₀.domain, V t x ∈ H₀.domain
  continuous_domain : ∀ x : H₀.domain, Continuous fun t => H₀ ⟨V t x, mem_domain t x x.2⟩

/-- `U` solves the Schrödinger equation `d/dt U t ψ = (iħ)⁻¹ (H₀ + V t) U t ψ` on the domain of
`H₀`: for `ψ` in the domain, every `U t ψ` is in the domain and `t ↦ U t ψ` has that
derivative. -/
def SolvesPerturbed (ħ : ℝ) (H₀ : E →ₗ.[ℂ] E) (V : ℝ → E →L[ℂ] E) (U : ℝ → E →L[ℂ] E) :
    Prop :=
  ∀ (ψ : H₀.domain) (t : ℝ), ∃ h : U t ψ ∈ H₀.domain,
    HasDerivAt (fun s => U s ψ) ((Complex.I * ħ)⁻¹ • (H₀ ⟨U t ψ, h⟩ + V t (U t ψ))) t

section Interaction

variable [CompleteSpace E] (hħ : ħ ≠ 0) (hH₀ : IsSelfAdjoint H₀) {V : ℝ → E →L[ℂ] E}

local notation "W" => schrodingerPropagator hħ hH₀

/-- The perturbation in the interaction picture, `e^{itH₀/ħ} V t e^{-itH₀/ħ}`. -/
def interactionOp (V : ℝ → E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := W (-t) * V t * W t

include hħ hH₀ in
lemma interactionOp_isSelfAdjoint (hV : IsRegularPerturbation H₀ V) (t : ℝ) :
    IsSelfAdjoint (interactionOp hħ hH₀ V t) := by
  rw [interactionOp, free_neg hħ hH₀]
  exact (hV.isSelfAdjoint t).conjugate' _

include hħ hH₀ in
lemma continuous_free_neg_apply (x : E) : Continuous fun t => W (-t) x :=
  (free_continuous_apply hħ hH₀ x).comp continuous_neg

include hħ hH₀ in
lemma interactionOp_continuous_apply (hV : IsRegularPerturbation H₀ V) (x : E) :
    Continuous fun t => interactionOp hħ hH₀ V t x :=
  ContinuousLinearMap.continuous_apply_apply (continuous_free_neg_apply hħ hH₀)
    (ContinuousLinearMap.continuous_apply_apply hV.continuous_apply
      (free_continuous_apply hħ hH₀ x))

include hħ hH₀ in
lemma free_neg_mem_domain {x : E} (hx : x ∈ H₀.domain) (t : ℝ) : W (-t) x ∈ H₀.domain :=
  free_mem_domain hħ hH₀ hx (-t)

include hħ hH₀ in
/-- A family of free propagators is strongly continuous on the graph. -/
lemma continuous_graphLift_free [CompleteSpace H₀.graph] {f : ℝ → ℝ} (hf : Continuous f)
    (y : H₀.graph) :
    Continuous fun t => graphLift (W (f t)) (fun _ hx => free_mem_domain hħ hH₀ hx (f t)) y :=
  continuous_graphLift_apply _ (fun x => (free_continuous_apply hħ hH₀ x).comp hf)
    (fun x => by
      simp_rw [free_commute hħ hH₀]
      exact (free_continuous_apply hħ hH₀ _).comp hf) y

variable [CompleteSpace H₀.graph]

/-- The interaction-picture perturbation on the graph of `H₀`. -/
def interactionGraph (hV : IsRegularPerturbation H₀ V) (t : ℝ) : H₀.graph →L[ℂ] H₀.graph :=
  graphLift (W (-t)) (fun _ hx => free_neg_mem_domain hħ hH₀ hx t) ∘L
    graphLift (V t) (hV.mem_domain t) ∘L
      graphLift (W t) (fun _ hx => free_mem_domain hħ hH₀ hx t)

lemma graphFst_interactionGraph (hV : IsRegularPerturbation H₀ V) (t : ℝ) (y : H₀.graph) :
    graphFst (interactionGraph hħ hH₀ hV t y) = interactionOp hħ hH₀ V t (graphFst y) := rfl

lemma interactionGraph_continuous_apply (hV : IsRegularPerturbation H₀ V) (y : H₀.graph) :
    Continuous fun t => interactionGraph hħ hH₀ hV t y := by
  refine ContinuousLinearMap.continuous_apply_apply
    (continuous_graphLift_free hħ hH₀ continuous_neg) ?_
  exact ContinuousLinearMap.continuous_apply_apply
    (continuous_graphLift_apply _ hV.continuous_apply hV.continuous_domain)
    (continuous_graphLift_free hħ hH₀ continuous_id y)

end Interaction

/-! ## Existence -/

section Existence

variable [CompleteSpace E] (hħ : ħ ≠ 0) (hH₀ : IsSelfAdjoint H₀) {V : ℝ → E →L[ℂ] E}

local notation "W" => schrodingerPropagator hħ hH₀

include hħ hH₀ in
/-- **The interaction-picture propagator.** `d/dt U_I t = (iħ)⁻¹ V_I(t) U_I t` has a unitary
solution with `U_I 0 = 1`, and `U_I t` and `U_I t†` map the domain of `H₀` into itself. The
equation is solved twice: on `E` and on the graph of `H₀`, a Banach space on which `V_I(t)` is
again strongly continuous. By uniqueness on `E` the two solutions agree on the domain. -/
theorem exists_interactionPropagator (hV : IsRegularPerturbation H₀ V) :
    ∃ U : ℝ → E →L[ℂ] E, U 0 = 1 ∧
      (∀ ψ t, HasDerivAt (U · ψ) ((Complex.I * ħ)⁻¹ • interactionOp hħ hH₀ V t (U t ψ)) t) ∧
      (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧ (∀ t, ∀ x ∈ H₀.domain, U t x ∈ H₀.domain) ∧
      ∀ t, ∀ x ∈ H₀.domain, star (U t) x ∈ H₀.domain := by
  have : CompleteSpace H₀.graph := (isClosed_graph hH₀).completeSpace_coe
  set c : ℂ := (Complex.I * ħ)⁻¹
  obtain ⟨U, hU₀, hU, hUu⟩ := exists_propagator_of_continuous_apply
    (interactionOp_continuous_apply hħ hH₀ hV) (interactionOp_isSelfAdjoint hħ hH₀ hV) ħ 0
  have hK : ∀ y, Continuous fun t => (c • interactionGraph hħ hH₀ hV t) y := fun y =>
    (interactionGraph_continuous_apply hħ hH₀ hV y).const_smul c
  obtain ⟨UG, hUG₀, hUG⟩ := exists_hasDerivAt_apply hK 0
  have hL : ∀ x, Continuous fun t =>
      ((c • interactionOp hħ hH₀ V t).restrictScalars ℝ : E →L[ℝ] E) x := fun x =>
    (interactionOp_continuous_apply hħ hH₀ hV x).const_smul c
  -- The two solutions agree on the first coordinate.
  have hmatch : ∀ (y : H₀.graph) t, U t (graphFst y) = graphFst (UG t y) := fun y => by
    refine congrFun (eq_of_hasDerivAt_clm_apply_of_continuous_apply hL (fun t => hU _ t)
      (fun t => ?_) (by rw [hU₀, hUG₀]; rfl))
    exact ((graphFst : H₀.graph →L[ℂ] E).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hUG y t)
  have hdom : ∀ t, ∀ x ∈ H₀.domain, U t x ∈ H₀.domain := fun t x hx => by
    have := hmatch (graphMk ⟨x, hx⟩) t
    rw [show graphFst (graphMk ⟨x, hx⟩) = x from rfl] at this
    rw [this]
    exact fst_mem_domain _
  refine ⟨U, hU₀, hU, hUu, hdom, fun t x hx => ?_⟩
  obtain ⟨u, hu⟩ := isUnit_of_hasDerivAt_apply hK hUG₀ hUG t
  set z : H₀.graph := (↑u⁻¹ : H₀.graph →L[ℂ] H₀.graph) (graphMk ⟨x, hx⟩)
  have hz : U t (graphFst z) = x := by
    rw [hmatch, ← hu, show (u : H₀.graph →L[ℂ] H₀.graph) z = graphMk ⟨x, hx⟩ by
      change ((u : H₀.graph →L[ℂ] H₀.graph) * ↑u⁻¹) _ = _
      rw [Units.mul_inv]
      rfl]
    rfl
  have h1 := (Unitary.mem_iff.mp (hUu t)).1
  have : star (U t) x = graphFst z := by
    rw [← hz]
    change (star (U t) * U t) _ = _
    rw [h1]
    rfl
  rw [this]
  exact fst_mem_domain z

end Existence

/-! ## The propagator -/

section Propagator

variable [CompleteSpace E] (hħ : ħ ≠ 0) (hH₀ : IsSelfAdjoint H₀) {V : ℝ → E →L[ℂ] E}

local notation "W" => schrodingerPropagator hħ hH₀

include hħ hH₀ in
/-- **Existence.** For a regular perturbation `V` of a self-adjoint `H₀`, the Schrödinger
equation for `H₀ + V t` has a strongly continuous unitary solution `U` with `U 0 = 1`, and
`U t†` maps the domain of `H₀` into itself. `U t = e^{-itH₀/ħ} U_I t`. -/
theorem exists_propagator (hV : IsRegularPerturbation H₀ V) :
    ∃ U : ℝ → E →L[ℂ] E, U 0 = 1 ∧ (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧
      SolvesPerturbed ħ H₀ V U ∧ (∀ t, ∀ x ∈ H₀.domain, star (U t) x ∈ H₀.domain) ∧
      ∀ x, Continuous (U · x) := by
  obtain ⟨UI, h₀, hd, hu, hdom, hsdom⟩ := exists_interactionPropagator hħ hH₀ hV
  refine ⟨fun t => W t * UI t, ?_, fun t => mul_mem (free_mem_unitary hħ hH₀ t) (hu t),
    fun ψ t => ?_, fun t x hx => ?_, fun x => ?_⟩
  · simp [h₀, schrodingerPropagator_zero]
  · obtain ⟨hm, hW⟩ := solvesSchrodinger_schrodingerPropagator hħ hH₀ ⟨UI t ψ, hdom t ψ ψ.2⟩ t
    refine ⟨hm, ?_⟩
    have h := ContinuousLinearMap.hasDerivAt_apply_apply
      (A := fun s => (W s).restrictScalars ℝ) (free_continuous_apply hħ hH₀) (hd ψ t) hW
    have hWV : W t (interactionOp hħ hH₀ V t (UI t ψ)) = V t (W t (UI t ψ)) := by
      change (W t * W (-t)) (V t (W t (UI t ψ))) = _
      rw [← free_add hħ hH₀, add_neg_cancel, schrodingerPropagator_zero]
      rfl
    convert h using 1
    · rfl
    change _ = W t ((Complex.I * ħ)⁻¹ • interactionOp hħ hH₀ V t (UI t ψ)) + _
    rw [map_smul, hWV, smul_add, add_comm]
    rfl
  · rw [star_mul]
    change star (UI t) (star (W t) x) ∈ _
    rw [← free_neg hħ hH₀]
    exact hsdom t _ (free_neg_mem_domain hħ hH₀ hx t)
  · exact ContinuousLinearMap.continuous_apply_apply (free_continuous_apply hħ hH₀)
      (continuous_iff_continuousAt.mpr fun t => (hd x t).continuousAt)

include hH₀ in
/-- A vector orthogonal to the dense domain of a self-adjoint operator is zero. -/
lemma eq_zero_of_inner_domain {z : E} (h : ∀ φ ∈ H₀.domain, ⟪φ, z⟫_ℂ = 0) :
    z = 0 := by
  have := Continuous.ext_on hH₀.dense_domain (continuous_id.inner continuous_const)
    continuous_const h
  exact inner_self_eq_zero.mp (congrFun this z)

include hH₀ in
/-- **Uniqueness.** A family of bounded operators that solves the Schrödinger equation for
`H₀ + V t` and agrees at one time with a unitary solution is that solution:
`⟪U t φ, Ũ t ψ⟫` is constant for `φ, ψ` in the domain, as `H₀ + V t` is symmetric there. -/
theorem eq_of_solvesPerturbed (hV : IsRegularPerturbation H₀ V) {U Ũ : ℝ → E →L[ℂ] E}
    (hU : SolvesPerturbed ħ H₀ V U) (hUu : ∀ t, U t ∈ unitary (E →L[ℂ] E))
    (hŨ : SolvesPerturbed ħ H₀ V Ũ) {s : ℝ} (h : Ũ s = U s) : Ũ = U := by
  have hsym := LinearPMap.IsSelfAdjoint.isSymmetric hH₀
  have hconst : ∀ (φ ψ : H₀.domain) t, ⟪U t φ, Ũ t ψ⟫_ℂ = ⟪U s φ, Ũ s ψ⟫_ℂ := by
    intro φ ψ
    have hf : ∀ t, HasDerivAt (fun t => ⟪U t φ, Ũ t ψ⟫_ℂ) 0 t := by
      intro t
      obtain ⟨h₁, d₁⟩ := hU φ t
      obtain ⟨h₂, d₂⟩ := hŨ ψ t
      have hVs : ⟪V t (U t φ), Ũ t ψ⟫_ℂ = ⟪U t φ, V t (Ũ t ψ)⟫_ℂ :=
        (hV.isSelfAdjoint t).isSymmetric _ _
      have hHs := hsym ⟨_, h₁⟩ ⟨_, h₂⟩
      convert d₁.inner ℂ d₂ using 1
      rw [inner_smul_left, inner_smul_right, starRingEnd_apply, star_inv_I_mul, inner_add_left,
        inner_add_right, hHs, hVs]
      ring
    intro t
    exact is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
      (fun t => (hf t).deriv) t s
  funext t
  have hdom : ∀ ψ : H₀.domain, Ũ t ψ = U t ψ := fun ψ => by
    set w := Ũ t ψ - U t ψ
    have hw : star (U t) w = 0 := eq_zero_of_inner_domain hH₀ fun φ hφ => by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        inner_sub_right, hconst ⟨φ, hφ⟩ ψ t, h, ContinuousLinearMap.inner_map_map_of_mem_unitary (hUu s),
        ContinuousLinearMap.inner_map_map_of_mem_unitary (hUu t), sub_self]
    have := congrArg (U t) hw
    rw [map_zero] at this
    change (U t * star (U t)) w = 0 at this
    rw [(Unitary.mem_iff.mp (hUu t)).2] at this
    exact sub_eq_zero.mp this
  exact ContinuousLinearMap.ext fun x => congrFun (Continuous.ext_on hH₀.dense_domain
    (Ũ t).continuous (U t).continuous fun ξ hξ => hdom ⟨ξ, hξ⟩) x

end Propagator

/-! ## The two-parameter propagator and information conservation -/

section TwoParameter

variable [CompleteSpace E] (hħ : ħ ≠ 0) (hH₀ : IsSelfAdjoint H₀) {V : ℝ → E →L[ℂ] E}
  (hV : IsRegularPerturbation H₀ V)

/-- The propagator `U t` of `H₀ + V t` with `U 0 = 1` (`exists_propagator`). -/
def propagator : ℝ → E →L[ℂ] E := (exists_propagator hħ hH₀ hV).choose

lemma propagator_zero : propagator hħ hH₀ hV 0 = 1 := (exists_propagator hħ hH₀ hV).choose_spec.1

lemma propagator_mem_unitary (t : ℝ) : propagator hħ hH₀ hV t ∈ unitary (E →L[ℂ] E) :=
  (exists_propagator hħ hH₀ hV).choose_spec.2.1 t

lemma solvesPerturbed_propagator : SolvesPerturbed ħ H₀ V (propagator hħ hH₀ hV) :=
  (exists_propagator hħ hH₀ hV).choose_spec.2.2.1

lemma star_propagator_mem_domain (t : ℝ) {x : E} (hx : x ∈ H₀.domain) :
    star (propagator hħ hH₀ hV t) x ∈ H₀.domain :=
  (exists_propagator hħ hH₀ hV).choose_spec.2.2.2.1 t x hx

lemma propagator_continuous_apply (x : E) : Continuous fun t => propagator hħ hH₀ hV t x :=
  (exists_propagator hħ hH₀ hV).choose_spec.2.2.2.2 x

include hħ hH₀ hV in
/-- **Existence and uniqueness** of the propagator of `H₀ + V t`: exactly one family of bounded
operators `U` with `U 0 = 1` solves the Schrödinger equation on the domain of `H₀`. It is
unitary and strongly continuous. -/
theorem existsUnique_propagator :
    ∃! U : ℝ → E →L[ℂ] E, U 0 = 1 ∧ SolvesPerturbed ħ H₀ V U :=
  ⟨propagator hħ hH₀ hV, ⟨propagator_zero hħ hH₀ hV, solvesPerturbed_propagator hħ hH₀ hV⟩,
    fun _ hŨ => eq_of_solvesPerturbed hH₀ hV (solvesPerturbed_propagator hħ hH₀ hV)
      (propagator_mem_unitary hħ hH₀ hV) hŨ.2
      (by rw [hŨ.1, propagator_zero])⟩

/-- The two-parameter propagator `U(t, s) = U t U s†`, from time `s` to time `t`. -/
def twoParam (t s : ℝ) : E →L[ℂ] E := propagator hħ hH₀ hV t * star (propagator hħ hH₀ hV s)

lemma twoParam_mem_unitary (t s : ℝ) : twoParam hħ hH₀ hV t s ∈ unitary (E →L[ℂ] E) :=
  mul_mem (propagator_mem_unitary hħ hH₀ hV t)
    (Unitary.star_mem (propagator_mem_unitary hħ hH₀ hV s))

lemma twoParam_self (t : ℝ) : twoParam hħ hH₀ hV t t = 1 :=
  (Unitary.mem_iff.mp (propagator_mem_unitary hħ hH₀ hV t)).2

lemma twoParam_comp (t r s : ℝ) :
    twoParam hħ hH₀ hV t r * twoParam hħ hH₀ hV r s = twoParam hħ hH₀ hV t s := by
  have h := (Unitary.mem_iff.mp (propagator_mem_unitary hħ hH₀ hV r)).1
  simp only [twoParam]
  rw [mul_assoc, ← mul_assoc (star _), h, one_mul]

/-- `t ↦ U(t, s)` solves the Schrödinger equation for `H₀ + V t` with initial time `s`, and it is
the only solution with `U(s, s) = 1`. -/
theorem solvesPerturbed_twoParam (s : ℝ) :
    SolvesPerturbed ħ H₀ V (fun t => twoParam hħ hH₀ hV t s) := fun ψ t =>
  solvesPerturbed_propagator hħ hH₀ hV ⟨_, star_propagator_mem_domain hħ hH₀ hV s ψ.2⟩ t

theorem eq_twoParam {Ũ : ℝ → E →L[ℂ] E} {s : ℝ} (h₀ : Ũ s = 1)
    (hŨ : SolvesPerturbed ħ H₀ V Ũ) : Ũ = fun t => twoParam hħ hH₀ hV t s :=
  eq_of_solvesPerturbed hH₀ hV (solvesPerturbed_twoParam hħ hH₀ hV s)
    (fun t => twoParam_mem_unitary hħ hH₀ hV t s) hŨ (by rw [h₀, twoParam_self])

/-- The propagator of `H₀ + V t` is a strongly continuous unitary propagator, so Howland's
quasi-energy operator `K = -iħ ∂ₜ + H₀ + V t` is defined for it
(`QuantumMechanics.UnitaryPropagator.exists_howlandGenerator`). -/
def unitaryPropagator : UnitaryPropagator E where
  toFun := twoParam hħ hH₀ hV
  mem_unitary := twoParam_mem_unitary hħ hH₀ hV
  map_self := twoParam_self hħ hH₀ hV
  map_comp := twoParam_comp hħ hH₀ hV
  continuous_apply x := ContinuousLinearMap.continuous_apply_apply
    (A := fun p : ℝ × ℝ => propagator hħ hH₀ hV p.1)
    (fun y => (propagator_continuous_apply hħ hH₀ hV y).comp continuous_fst)
    ((ContinuousLinearMap.continuous_star_apply_of_mem_unitary (propagator_mem_unitary hħ hH₀ hV)
      (propagator_continuous_apply hħ hH₀ hV) x).comp continuous_snd)

/-- **DR-INFO** for `H₀ + V t`: the evolution `ρ ↦ U(t₁, t₀) ρ U(t₁, t₀)†` maps density operators
to density operators, the past is reconstructed by `U(t₁, t₀)†`, and the von Neumann entropy is
conserved. -/
theorem twoParam_conserves_vonNeumannEntropy {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    (t₀ t₁ : ℝ) :
    IsDensityOperator (twoParam hħ hH₀ hV t₁ t₀ * ρ * star (twoParam hħ hH₀ hV t₁ t₀)) ∧
      star (twoParam hħ hH₀ hV t₁ t₀) *
          (twoParam hħ hH₀ hV t₁ t₀ * ρ * star (twoParam hħ hH₀ hV t₁ t₀)) *
          twoParam hħ hH₀ hV t₁ t₀ = ρ ∧
      vonNeumannEntropy (twoParam hħ hH₀ hV t₁ t₀ * ρ * star (twoParam hħ hH₀ hV t₁ t₀)) =
        vonNeumannEntropy ρ := by
  have hu := (Unitary.mem_iff.mp (twoParam_mem_unitary hħ hH₀ hV t₁ t₀)).1
  refine ⟨hρ.conj hu, ?_, hρ.vonNeumannEntropy_conj hu⟩
  set P := twoParam hħ hH₀ hV t₁ t₀
  calc star P * (P * ρ * star P) * P = (star P * P) * ρ * (star P * P) := by noncomm_ring
    _ = ρ := by rw [hu, one_mul, mul_one]

/-- **EVDIFF on a dense set of states** for `H₀ + V t`: for a unit vector `ψ` in the domain of
`H₀`, the evolved pure state `U(t, t₀) |ψ⟩⟨ψ| U(t, t₀)†` is differentiable in `t`, in operator
norm, at every time. -/
theorem differentiableAt_twoParam_proj {ψ : E} (hψ : ψ ∈ H₀.domain) (t₀ t : ℝ) :
    DifferentiableAt ℝ (fun s => twoParam hħ hH₀ hV s t₀ * proj ψ *
      star (twoParam hħ hH₀ hV s t₀)) t := by
  obtain ⟨_, hd⟩ := solvesPerturbed_twoParam hħ hH₀ hV t₀ ⟨ψ, hψ⟩ t
  have h := differentiableAt_proj_of_hasDerivAt hd
  simp_rw [mul_proj_mul_star]
  exact h

end TwoParameter

end UnitaryEntropy.FurtherResults
