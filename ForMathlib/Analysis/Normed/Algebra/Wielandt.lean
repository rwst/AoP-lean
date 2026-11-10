/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# The Wielandt–Wintner theorem

In a nontrivial normed algebra over `ℝ` or `ℂ`, no commutator `a * b - b * a` is a nonzero
scalar. In particular, the canonical commutation relation `[X, P] = iħ` has no solution in
bounded operators on a nonzero normed space.

The proof is Wielandt's: from `[a, b] = c` follows `[a, b ^ (n + 1)] = (n + 1) c b ^ n`, so
no power of `b` vanishes, and `(n + 1) ‖c‖ ≤ 2 ‖a‖ ‖b‖` for every `n`.

## Main results

* `commutator_pow_succ`: `[a, b] = c` implies `[a, b ^ (n + 1)] = (n + 1) c b ^ n`, in any
  algebra;
* `pow_ne_zero_of_commutator_eq_algebraMap`: if moreover `c ≠ 0`, no power of `b` vanishes;
* `commutator_ne_algebraMap`: the Wielandt–Wintner theorem.
-/

@[expose] public section

variable {𝕜 A : Type*}

theorem commutator_pow_succ [CommRing 𝕜] [Ring A] [Algebra 𝕜 A] {a b : A} {c : 𝕜}
    (h : a * b - b * a = algebraMap 𝕜 A c) (n : ℕ) :
    a * b ^ (n + 1) - b ^ (n + 1) * a = ((n + 1 : 𝕜) * c) • b ^ n := by
  induction n with
  | zero => simp [h, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have e : a * b ^ (n + 1 + 1) - b ^ (n + 1 + 1) * a =
        (a * b ^ (n + 1) - b ^ (n + 1) * a) * b + b ^ (n + 1) * (a * b - b * a) := by
      rw [pow_succ b (n + 1)]
      noncomm_ring
    rw [e, ih, h, smul_mul_assoc, ← pow_succ, ← Algebra.commutes, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, ← add_smul]
    push_cast
    ring_nf

theorem pow_ne_zero_of_commutator_eq_algebraMap [Field 𝕜] [CharZero 𝕜] [Ring A] [Nontrivial A]
    [Algebra 𝕜 A] {a b : A} {c : 𝕜} (h : a * b - b * a = algebraMap 𝕜 A c) (hc : c ≠ 0) (n : ℕ) :
    b ^ n ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    have key := commutator_pow_succ h n
    rw [hn, mul_zero, zero_mul, sub_zero, eq_comm, smul_eq_zero] at key
    exact key.elim (mul_ne_zero (by exact_mod_cast n.succ_ne_zero) hc) ih

/-- **Wielandt–Wintner**: in a nontrivial normed algebra over `ℝ` or `ℂ`, a commutator is
never a nonzero scalar. -/
theorem commutator_ne_algebraMap [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [Nontrivial A]
    (a b : A) {c : 𝕜} (hc : c ≠ 0) : a * b - b * a ≠ algebraMap 𝕜 A c := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖a‖ * ‖b‖ / ‖c‖)
  have hb : 0 < ‖b ^ n‖ := norm_pos_iff.2 (pow_ne_zero_of_commutator_eq_algebraMap h hc n)
  have hnb : ‖b ^ (n + 1)‖ ≤ ‖b ^ n‖ * ‖b‖ := by
    rw [pow_succ]
    exact norm_mul_le _ _
  have key : ((n : ℝ) + 1) * ‖c‖ * ‖b ^ n‖ ≤ 2 * ‖a‖ * ‖b‖ * ‖b ^ n‖ :=
    calc ((n : ℝ) + 1) * ‖c‖ * ‖b ^ n‖ = ‖((n + 1 : 𝕜) * c) • b ^ n‖ := by
          rw [norm_smul, norm_mul]
          norm_cast
      _ = ‖a * b ^ (n + 1) - b ^ (n + 1) * a‖ := by rw [commutator_pow_succ h]
      _ ≤ ‖a * b ^ (n + 1)‖ + ‖b ^ (n + 1) * a‖ := norm_sub_le _ _
      _ ≤ ‖a‖ * ‖b ^ (n + 1)‖ + ‖b ^ (n + 1)‖ * ‖a‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖a‖ * (‖b ^ n‖ * ‖b‖) + ‖b ^ n‖ * ‖b‖ * ‖a‖ := by gcongr
      _ = 2 * ‖a‖ * ‖b‖ * ‖b ^ n‖ := by ring
  have h1 := le_of_mul_le_mul_right key hb
  have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
  rw [div_lt_iff₀ hc'] at hn
  nlinarith
