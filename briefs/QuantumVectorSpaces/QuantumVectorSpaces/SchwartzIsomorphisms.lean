/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces.Isomorphisms
public import ForMathlib.Algebra.Lie.Subalgebra

/-!
# Schwartz spaces of different dimension are not Lie isomorphic

Example 3 claims that `𝓢(ℝⁿ)` and `𝓢(ℝᵐ)`, with the defining observables `Xⁱ`, `Pᵢ`, `I`, "are
isomorphic as quantum vector spaces if and only if `n = m`". For Lie isomorphisms (`LieIso`) this
holds, for any nonzero values of `ħ`: the observables `Xⁱ`, `Pᵢ`, `I` are linearly independent
and span a Lie algebra of dimension `2n + 1`, which a Lie isomorphism preserves.

## Main results

* `card_obsN`  there are `2n + 1` defining observables;
* `linearIndependent_obsN`  they are linearly independent, by taking commutators with `Pₖ` and
  `Xᵏ`;
* `finrank_lieAlgebra_obsN`  their Lie algebra is their linear span, of dimension `2n + 1`;
* `nonempty_lieIso_schwartzN_iff`  `𝓢(ℝⁿ)` and `𝓢(ℝᵐ)` are Lie isomorphic if and only if
  `n = m`.
-/

open Complex SchwartzMap
open scoped ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing

@[expose] public noncomputable section

namespace QuantumVectorSpaces

variable (n : ℕ)

set_option hygiene false in
/-- The Schwartz space `𝓢(ℝⁿ)` of complex functions. -/
local notation "𝓢ₙ" => 𝓢(EuclideanSpace ℝ (Fin n), ℂ)

/-- The defining observables `Xⁱ`, `Pᵢ`, `I` as a sum type. -/
def ObsN.equiv : ObsN n ≃ (Fin n ⊕ Fin n) ⊕ Unit where
  toFun
    | .pos i => .inl (.inl i)
    | .mom i => .inl (.inr i)
    | .one => .inr ()
  invFun
    | .inl (.inl i) => .pos i
    | .inl (.inr i) => .mom i
    | .inr _ => .one
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with (i | i) | _ <;> rfl

/-- There are `2n + 1` defining observables. -/
lemma card_obsN : Fintype.card (ObsN n) = 2 * n + 1 := by
  rw [Fintype.card_congr (ObsN.equiv n)]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

lemma sum_obsN {M : Type*} [AddCommMonoid M] (F : ObsN n → M) :
    ∑ a, F a = ∑ i, F (.pos i) + ∑ i, F (.mom i) + F .one := by
  rw [← (ObsN.equiv n).symm.sum_comp]
  simp [Fintype.sum_sum_type, ObsN.equiv]

/-- `𝓢(ℝⁿ)` is nontrivial: it contains a bump function. -/
instance : Nontrivial 𝓢ₙ := by
  let f : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport fun x => (f x : ℂ) :=
    f.hasCompactSupport.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ fun x => (f x : ℂ) := ofRealCLM.contDiff.comp (f.contDiff (n := (⊤ : ℕ∞)))
  refine ⟨h1.toSchwartzMap h2, 0, fun h => ?_⟩
  have h0 := congrArg (fun g : 𝓢ₙ => g 0) h
  change ((f 0 : ℝ) : ℂ) = 0 at h0
  rw [f.one_of_mem_closedBall (Metric.mem_closedBall_self f.rIn_pos.le)] at h0
  exact one_ne_zero (ofReal_eq_zero.1 h0)

variable {n} {ħ : ℝ}

/-- For `ħ ≠ 0`, the defining observables `Xⁱ`, `Pᵢ`, `I` are linearly independent: the
commutator with `Pₖ` of a combination picks out the coefficient of `Xᵏ`, the commutator with
`Xᵏ` that of `Pₖ`. -/
theorem linearIndependent_obsN (hħ : ħ ≠ 0) : LinearIndependent ℂ (obsN n ħ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hIħ : (I * ħ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.2 hħ)
  have hc (T : Module.End ℂ 𝓢ₙ) : ∑ a, g a • (obsN n ħ a * T - T * obsN n ħ a) = 0 := by
    have h : (∑ a, g a • obsN n ħ a) * T - T * ∑ a, g a • obsN n ħ a = 0 := by simp [hg]
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib] at h
    simpa [smul_mul_assoc, mul_smul_comm, smul_sub] using h
  have hpos (k : Fin n) : g (.pos k) = 0 := by
    have h := hc (momOpN n ħ k)
    rw [sum_obsN] at h
    simp only [obsN, posOpN_comm_momOpN, momOpN_comm, one_mul, mul_one, sub_self, smul_zero,
      Finset.sum_const_zero, add_zero, smul_ite, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, smul_smul] at h
    exact (mul_eq_zero.1 ((smul_eq_zero.1 h).resolve_right one_ne_zero)).resolve_right hIħ
  have hmom (k : Fin n) : g (.mom k) = 0 := by
    have hpm (i : Fin n) : momOpN n ħ i * posOpN n k - posOpN n k * momOpN n ħ i =
        -(if k = i then (I * ħ) • (1 : Module.End ℂ 𝓢ₙ) else 0) := by
      rw [← posOpN_comm_momOpN, neg_sub]
    have h := hc (posOpN n k)
    rw [sum_obsN] at h
    simp only [obsN, posOpN_comm, hpm, one_mul, mul_one, sub_self, smul_zero,
      Finset.sum_const_zero, zero_add, add_zero, smul_neg, Finset.sum_neg_distrib, smul_ite,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, smul_smul, neg_eq_zero] at h
    exact (mul_eq_zero.1 ((smul_eq_zero.1 h).resolve_right one_ne_zero)).resolve_right hIħ
  have hone : g .one = 0 := by
    rw [sum_obsN] at hg
    simp only [hpos, hmom, zero_smul, Finset.sum_const_zero, zero_add, obsN] at hg
    exact (smul_eq_zero.1 hg).resolve_right one_ne_zero
  intro a
  cases a with
  | pos k => exact hpos k
  | mom k => exact hmom k
  | one => exact hone

/-- The Lie algebra of `Xⁱ`, `Pᵢ`, `I` is their linear span, since their commutators are
multiples of `I`. -/
lemma toSubmodule_lieAlgebra_obsN :
    (lieAlgebra (obsN n ħ)).toSubmodule = Submodule.span ℂ (Set.range (obsN n ħ)) := by
  refine LieSubalgebra.coe_lieSpan_eq_span_of_forall_lie_mem ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [LieRing.of_associative_ring_bracket, obsN_comm, ← Finsupp.range_linearCombination]
  exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)

/-- Changing `ħ` rescales the momenta. -/
lemma momOpN_eq_smul (hħ : ħ ≠ 0) (ħ' : ℝ) (i : Fin n) :
    momOpN n ħ' i = ((ħ' / ħ : ℝ) : ℂ) • momOpN n ħ i := by
  ext f : 1
  simp only [momOpN, LinearMap.smul_apply, ContinuousLinearMap.toLinearMap_smul,
    ContinuousLinearMap.coe_coe, smul_smul]
  have hħc : (ħ : ℂ) ≠ 0 := ofReal_ne_zero.2 hħ
  congr 1
  push_cast
  field_simp

/-- For nonzero `ħ` and `ħ'`, the defining observables span the same space. -/
lemma span_obsN_le (hħ : ħ ≠ 0) (ħ' : ℝ) :
    Submodule.span ℂ (Set.range (obsN n ħ')) ≤ Submodule.span ℂ (Set.range (obsN n ħ)) := by
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  cases a with
  | pos i => exact Submodule.subset_span ⟨.pos i, rfl⟩
  | mom i =>
    rw [obsN, momOpN_eq_smul hħ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨.mom i, rfl⟩)
  | one => exact Submodule.subset_span ⟨.one, rfl⟩

/-- For `ħ ≠ 0`, the Lie algebra of `Xⁱ`, `Pᵢ`, `I` has dimension `2n + 1`. -/
theorem finrank_lieAlgebra_obsN (hħ : ħ ≠ 0) :
    Module.finrank ℂ (lieAlgebra (obsN n ħ)).toSubmodule = 2 * n + 1 := by
  rw [toSubmodule_lieAlgebra_obsN, finrank_span_eq_card (linearIndependent_obsN hħ), card_obsN]

/-- Example 3: for nonzero `ħ` and `ħ'`, `𝓢(ℝⁿ)` and `𝓢(ℝᵐ)` with `Xⁱ`, `Pᵢ`, `I` are Lie
isomorphic if and only if `n = m`. -/
theorem nonempty_lieIso_schwartzN_iff {m : ℕ} {ħ' : ℝ} (hħ : ħ ≠ 0) (hħ' : ħ' ≠ 0) :
    Nonempty (LieIso (l2CoreN n) (obsN n ħ) (l2CoreN m) (obsN m ħ')) ↔ n = m := by
  refine ⟨fun ⟨e⟩ => ?_, ?_⟩
  · have h := e.finrank_lieAlgebra
    rw [finrank_lieAlgebra_obsN hħ, finrank_lieAlgebra_obsN hħ'] at h
    omega
  · rintro rfl
    refine ⟨⟨LinearEquiv.refl ℂ _, fun _ _ => rfl, fun A => ?_⟩⟩
    rw [LinearEquiv.conj_refl, ← LieSubalgebra.mem_toSubmodule, ← LieSubalgebra.mem_toSubmodule,
      toSubmodule_lieAlgebra_obsN, toSubmodule_lieAlgebra_obsN,
      le_antisymm (span_obsN_le hħ ħ') (span_obsN_le hħ' ħ)]

end QuantumVectorSpaces
