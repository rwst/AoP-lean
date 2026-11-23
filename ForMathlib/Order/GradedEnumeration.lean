/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Basic.Countable.Defs
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.OrderIsoNat

/-!
# Enumerations by degree

Let `ι` be a countably infinite type with a degree `deg : ι → ℕ` whose sublevel sets
`{i | deg i ≤ d}` are finite. Then `ι` can be enumerated as `e 0, e 1, …` with nondecreasing
degree. For multi-indices `ι = Fin n → ℕ` with `deg k = ∑ i, k i` this lists the eigenvalues of
the `n`-dimensional harmonic oscillator in increasing order.

The position of an element in such an enumeration is controlled by counting: `e j` comes after
every element of smaller degree, and before every element of larger degree.

## Main statements

* `exists_equiv_nat_monotone`: an enumeration `e : ℕ ≃ ι` with `deg ∘ e` monotone exists.
* `succ_le_card_of_monotone`, `card_le_of_monotone`: the counting bounds.
-/

@[expose] public section

open Function

variable {ι : Type*} {deg : ι → ℕ}

/-- **Enumeration by degree.** A countably infinite type whose degree has finite sublevel sets
can be enumerated with nondecreasing degree. -/
theorem exists_equiv_nat_monotone [Countable ι] [Infinite ι]
    (hdeg : ∀ d, {i | deg i ≤ d}.Finite) : ∃ e : ℕ ≃ ι, Monotone (deg ∘ e) := by
  classical
  let _ := Encodable.ofCountable ι
  -- `B d` exceeds the code of every element of degree at most `d`
  let B : ℕ → ℕ := fun d => (hdeg d).toFinset.sup fun i => Encodable.encode i + 1
  let T : ℕ → ℕ := fun d => ∑ c ∈ Finset.range d, B c
  let φ : ι → ℕ := fun i => T (deg i) + Encodable.encode i
  have hT : Monotone T := fun c d hcd =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hcd)
  have hlt : ∀ i j, deg i < deg j → φ i < φ j := fun i j h => by
    have hB : Encodable.encode i < B (deg i) :=
      Nat.lt_of_succ_le (Finset.le_sup (f := fun i => Encodable.encode i + 1)
        ((hdeg (deg i)).mem_toFinset.mpr (le_refl (deg i))))
    have := hT (Nat.succ_le_of_lt h)
    rw [show T (deg i).succ = T (deg i) + B (deg i) from Finset.sum_range_succ _ _] at this
    simp only [φ]
    omega
  have hφ : Injective φ := fun i j h => by
    rcases lt_trichotomy (deg i) (deg j) with hij | hij | hij
    · exact absurd h (hlt i j hij).ne
    · exact Encodable.encode_injective (by simpa [φ, hij] using h)
    · exact absurd h (hlt j i hij).ne'
  have : Infinite (Set.range φ) := (Set.infinite_range_of_injective hφ).to_subtype
  let o := Nat.Subtype.orderIsoOfNat (Set.range φ)
  let E := Equiv.ofInjective φ hφ
  refine ⟨o.toEquiv.trans E.symm, fun a b hab => ?_⟩
  by_contra h
  have key := hlt _ _ (not_le.mp h)
  simp only [Equiv.trans_apply, E, Equiv.apply_ofInjective_symm] at key
  exact (not_le.mpr (o.lt_iff_lt.mp (Subtype.coe_lt_coe.mp key))) hab

variable (e : ℕ ≃ ι) (he : Monotone (deg ∘ e))
include he

/-- If `s` contains every element of degree at most `deg (e j)`, it has more than `j`
elements. -/
theorem succ_le_card_of_monotone {s : Finset ι} {j : ℕ} (hs : ∀ i, deg i ≤ deg (e j) → i ∈ s) :
    j + 1 ≤ s.card := by
  rw [← Finset.card_range (j + 1)]
  exact Finset.card_le_card_of_injOn e
    (fun i hi => hs _ (he (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
    (e.injective.injOn)

/-- If every element of `s` has degree less than `deg (e j)`, then `s` has at most `j`
elements. -/
theorem card_le_of_monotone {s : Finset ι} {j : ℕ} (hs : ∀ i ∈ s, deg i < deg (e j)) :
    s.card ≤ j := by
  rw [← Finset.card_range j]
  refine Finset.card_le_card_of_injOn e.symm (fun i hi => ?_) e.symm.injective.injOn
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra h
  have := he (not_lt.mp h)
  simp only [comp_apply, Equiv.apply_symm_apply] at this
  exact (not_le.mpr (hs i hi)) this

end
