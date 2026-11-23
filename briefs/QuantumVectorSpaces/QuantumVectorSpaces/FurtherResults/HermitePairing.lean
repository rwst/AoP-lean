/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.FurtherResults.HermiteStepSpaces

/-!
# Further results: an explicit `S^{1/2}_{1/2}(ℝ²) ≅ S^1_1(ℝ)`, in step form

Not part of the brief. This file makes explicit, on the coefficient side, the example
`S^{1/2}_{1/2}(ℝ²) ≅ S^1_1(ℝ)` of Sec. 5 of `further-results.tex` in the brief's directory
(R. Stephan, *Further results on the brief "Physical vector spaces for quantum mechanics"*): the
topology of `S^μ_μ(ℝⁿ)` remembers only the product `μ n`.

The coefficient space of `S^{1/2}_{1/2}(ℝ²)` has the weights `exp (t (a + b))` on `(a, b) ∈ ℕ²`,
that of `S^1_1(ℝ)` the weights `exp (t √j)` on `j ∈ ℕ` (`stepSpace` of `HermiteStepSpaces`, with
`f d = d` on `ℕ²` and `f d = √d = d ^ (1 / (2 ⬝ 1))` on `ℕ`). Mathlib's pairing `Nat.pair`
enumerates `ℕ²` in square shells, `max a b ^ 2 ≤ Nat.pair a b < (max a b + 1) ^ 2`, so
`√(Nat.pair a b)` and `a + b` agree up to a factor `2` and an additive constant `1`. Relabelling
the coefficients along `Nat.pair`, which sends `h_a ⊗ h_b` to `h_{Nat.pair a b}`, is therefore a
linear bijection between the two coefficient spaces that maps every step ball into a step ball,
and so is its inverse.

The existence of such a bijection is also an instance of
`HermiteSpace.exists_isStepBounded_equiv_gelfandShilov_iff` (`½ ⬝ 2 = 1 ⬝ 1`); this file gives
the map.

## Main definitions

* `HermiteSpace.pairEquiv`: `ℕ¹ ≃ ℕ²`, `(j) ↦ Nat.unpair j`.
* `HermiteSpace.pairingEquiv 𝕜`: the relabelling from the coefficient space of
  `S^{1/2}_{1/2}(ℝ²)` onto that of `S^1_1(ℝ)`.

## Main statements

* `HermiteSpace.pairingEquiv_apply_pair`: `(T c)_{Nat.pair a b} = c_{(a, b)}`.
* `HermiteSpace.isStepBounded_pairingEquiv`, `HermiteSpace.isStepBounded_pairingEquiv_symm`: both
  directions map every step ball `B_t` into a multiple of some step ball `B_s`.
-/

@[expose] public section

open DualPowerSeriesSpace (IsStepBounded union relabel isStepBounded_of_coe_eq union_le_union)

noncomputable section

namespace QuantumVectorSpaces.FurtherResults

namespace HermiteSpace

/-- The relabelling `ℕ¹ ≃ ℕ²` along `Nat.unpair`. -/
def pairEquiv : (Fin 1 → ℕ) ≃ (Fin 2 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).trans (Nat.pairEquiv.symm.trans (finTwoArrowEquiv ℕ).symm)

theorem pairEquiv_apply (j : Fin 1 → ℕ) :
    pairEquiv j = ![(Nat.unpair (j 0)).1, (Nat.unpair (j 0)).2] := rfl

theorem pairEquiv_symm_apply (a b : ℕ) : pairEquiv.symm ![a, b] = fun _ => Nat.pair a b := rfl

theorem degree_fin_one (j : Fin 1 → ℕ) : degree j = j 0 := Fin.sum_univ_one j

theorem degree_pairEquiv (j : Fin 1 → ℕ) :
    degree (pairEquiv j) = (Nat.unpair (j 0)).1 + (Nat.unpair (j 0)).2 := by
  rw [pairEquiv_apply, degree, Fin.sum_univ_two]
  rfl

/-- `√(Nat.pair a b) ≤ a + b + 1`. -/
theorem sqrt_degree_le (j : Fin 1 → ℕ) :
    √(degree j : ℝ) ≤ 1 * (degree (pairEquiv j) : ℝ) + 1 := by
  rw [degree_fin_one, degree_pairEquiv, one_mul]
  set a := (Nat.unpair (j 0)).1
  set b := (Nat.unpair (j 0)).2
  have h := Nat.pair_lt_max_add_one_sq a b
  rw [Nat.pair_unpair] at h
  have hm : max a b ≤ a + b := max_le (Nat.le_add_right a b) (Nat.le_add_left b a)
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h' : j 0 ≤ (a + b + 1) ^ 2 :=
    h.le.trans (Nat.pow_le_pow_left (Nat.add_le_add_right hm 1) 2)
  exact_mod_cast h'

/-- `a + b ≤ 2 √(Nat.pair a b)`. -/
theorem degree_le_sqrt (j : Fin 1 → ℕ) :
    (degree (pairEquiv j) : ℝ) ≤ 2 * √(degree j : ℝ) + 0 := by
  rw [degree_fin_one, degree_pairEquiv, add_zero]
  set a := (Nat.unpair (j 0)).1
  set b := (Nat.unpair (j 0)).2
  have h := Nat.max_sq_add_min_le_pair a b
  rw [Nat.pair_unpair] at h
  have hmax : ((max a b : ℕ) : ℝ) ≤ √(j 0 : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast (Nat.le_add_right _ _).trans h
  have hab : a + b ≤ 2 * max a b := by omega
  calc ((a + b : ℕ) : ℝ) ≤ 2 * ((max a b : ℕ) : ℝ) := by exact_mod_cast hab
    _ ≤ 2 * √(j 0 : ℝ) := by gcongr

/-- `√d` is the Gelfand–Shilov exponent `d ^ (1 / (2μ))` for `μ = 1`. -/
theorem sqrt_eq_rpow : (fun d : ℕ => √(d : ℝ)) = fun d : ℕ => (d : ℝ) ^ (1 / (2 * (1 : ℝ))) :=
  funext fun d => by rw [mul_one, Real.sqrt_eq_rpow]

variable (𝕜 : Type*) [RCLike 𝕜]

theorem union_pairEquiv :
    union 𝕜 (degreeWeight (fun d => (d : ℝ)) 2 ∘ pairEquiv) =
      stepSpace 𝕜 (fun d => √(d : ℝ)) 1 :=
  le_antisymm (union_le_union one_pos sqrt_degree_le) (union_le_union two_pos degree_le_sqrt)

/-- Relabelling along `pairEquiv`. -/
def pairRelabel :
    stepSpace 𝕜 (fun d => (d : ℝ)) 2 ≃ₗ[𝕜]
      union 𝕜 (degreeWeight (fun d => (d : ℝ)) 2 ∘ pairEquiv) :=
  relabel 𝕜 (degreeWeight (fun d => (d : ℝ)) 2) pairEquiv

/-- **The explicit isomorphism `S^{1/2}_{1/2}(ℝ²) ≅ S^1_1(ℝ)` on coefficients**: relabelling
along `Nat.pair`. -/
def pairingEquiv :
    stepSpace 𝕜 (fun d => (d : ℝ)) 2 ≃ₗ[𝕜] stepSpace 𝕜 (fun d => √(d : ℝ)) 1 :=
  (pairRelabel 𝕜).trans (LinearEquiv.ofEq _ _ (union_pairEquiv 𝕜))

variable {𝕜}

theorem pairingEquiv_apply (c : stepSpace 𝕜 (fun d => (d : ℝ)) 2) (j : Fin 1 → ℕ) :
    (pairingEquiv 𝕜 c : (Fin 1 → ℕ) → 𝕜) j = (c : (Fin 2 → ℕ) → 𝕜) (pairEquiv j) := rfl

/-- The coefficient of `h_a ⊗ h_b` becomes the coefficient of `h_{Nat.pair a b}`. -/
theorem pairingEquiv_apply_pair (c : stepSpace 𝕜 (fun d => (d : ℝ)) 2) (a b : ℕ) :
    (pairingEquiv 𝕜 c : (Fin 1 → ℕ) → 𝕜) (fun _ => Nat.pair a b) =
      (c : (Fin 2 → ℕ) → 𝕜) ![a, b] := by
  rw [pairingEquiv_apply, ← pairEquiv_symm_apply, Equiv.apply_symm_apply]

/-- The relabelling maps every step ball into a multiple of a step ball. -/
theorem isStepBounded_pairingEquiv :
    IsStepBounded (degreeWeight (fun d => (d : ℝ)) 2) (degreeWeight (fun d => √(d : ℝ)) 1)
      (pairingEquiv 𝕜).toLinearMap := by
  rw [pairingEquiv, LinearEquiv.coe_trans]
  exact (DualPowerSeriesSpace.isStepBounded_relabel pairEquiv).comp
    (isStepBounded_of_coe_eq one_pos sqrt_degree_le _
      (LinearEquiv.coe_ofEq_apply (union_pairEquiv 𝕜)))

/-- So does its inverse. -/
theorem isStepBounded_pairingEquiv_symm :
    IsStepBounded (degreeWeight (fun d => √(d : ℝ)) 1) (degreeWeight (fun d => (d : ℝ)) 2)
      (pairingEquiv 𝕜).symm.toLinearMap := by
  rw [pairingEquiv, LinearEquiv.trans_symm, LinearEquiv.coe_trans, LinearEquiv.ofEq_symm]
  exact (isStepBounded_of_coe_eq two_pos degree_le_sqrt _
      (LinearEquiv.coe_ofEq_apply (union_pairEquiv 𝕜).symm)).comp
    (DualPowerSeriesSpace.isStepBounded_relabel_symm pairEquiv)

end HermiteSpace

end QuantumVectorSpaces.FurtherResults

end
