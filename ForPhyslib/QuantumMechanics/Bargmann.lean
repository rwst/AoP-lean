/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.MeasureTheory.Integral.IntervalIntegral.LocalCocycle
public import ForPhyslib.QuantumMechanics.Kadison
public import ForPhyslib.QuantumMechanics.Wigner.OneParameter

/-!
# Bargmann's theorem for `ℝ`: lifting a continuous evolution to a unitary group

A time evolution of density operators that is, for every `t ≥ 0`, conjugation by a unitary
or an anti-unitary, with `Φ 0 = id`, `Φ (s + t) = Φ s ∘ Φ t` and `t ↦ Φ t ρ` continuous at `0⁺`
on pure states, is conjugation by a strongly continuous unitary one-parameter group. This is
Bargmann's theorem for the group `ℝ`, with no dimension hypothesis and no measurability.

## i. Overview

The anti-unitary case is excluded by `Φ t = Φ (t / 2) ∘ Φ (t / 2)`. The remaining unitaries
`u t` are determined up to a phase (`exists_eq_smul_of_proj_eq`: an operator that commutes with
every pure state is a scalar), and everything phase-free about them is continuous. The pure
states `|u t ψ⟩⟨u t ψ|` are continuous at every `t ≥ 0`, not only at `0⁺`, because
`u (t₀ - h)` is `u h⋆ u t₀` up to phase; by polarization, so is `t ↦ |u t x⟩⟨u t y|`.

Fix a unit vector `e`. Near `0` the phase can be chosen with `⟪e, U t e⟫ > 0`, and then
`U t x = ⟪U t e, e⟫⁻¹ |u t x⟩⟨u t e| e` is strongly continuous. Its multiplier
`ω a b = ⟪e, U a U b e⟫ / ⟪e, U (a + b) e⟫`, with `U a U b = ω a b U (a + b)`, is continuous,
near `1`, of modulus one and satisfies the cocycle identity. By the real-analysis lemma
`Real.exists_eq_exp_of_localCocycle` it is a coboundary,
`ω a b = exp (i (f a + f b - f (a + b)))`, so `V t = exp (-i f t) U t` is a local homomorphism on
`[0, ε]`. It extends to `t ≥ 0` by `V (t / n) ^ n` and to `ℝ` by `V (-t) = V t⋆`, and the group
law carries continuity from `0` to every `t`.

## ii. Key results

- `QuantumMechanics.StronglyContinuousUnitaryGroup`: strongly continuous unitary groups.
- `QuantumMechanics.exists_eq_smul_of_proj_eq`: two unitaries with the same action on pure
  states differ by a phase.
- `QuantumMechanics.continuousWithinAt_rankOne`: phase-free continuity at every `t ≥ 0`.
- `QuantumMechanics.exists_map_add_of_local`: a local homomorphism on `[0, ε]` extends to
  `t ≥ 0`.
- `QuantumMechanics.multiplier_spec`, `QuantumMechanics.multiplier_cocycle`: the multiplier of
  the normalized section.
- `QuantumMechanics.exists_stronglyContinuousUnitaryGroup_of_proj`: the lift, phase-free form.
- `QuantumMechanics.exists_stronglyContinuousUnitaryGroup`: the lift for an evolution of density
  operators.

## iii. Table of contents

- A. Pure states determine a unitary up to a phase
- B. Continuity of the pure-state evolution at every `t ≥ 0`
- C. Extending a local homomorphism
- D. The normalized local section
- E. The multiplier is a continuous local 2-cocycle
- F. The lift

## iv. References

- V. Bargmann, *On unitary ray representations of continuous groups*, Ann. of Math. 59 (1954),
  1–46.
- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), 327–349, §7–8.
- G. Cassinelli, E. De Vito, P. J. Lahti, A. Levrero, *The Theory of Symmetry Actions in Quantum
  Mechanics*, Springer (2004), §3.5.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace Topology ComplexConjugate
open InnerProductSpace QuantumMechanics.Wigner Set Filter

/-- A strongly continuous one-parameter group of unitaries: `U 0 = 1`, `U (s + t) = U s U t` and
`t ↦ U t x` is continuous for every `x`. -/
structure QuantumMechanics.StronglyContinuousUnitaryGroup (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  /-- The unitary at time `t`. -/
  toFun : ℝ → E →L[ℂ] E
  mem_unitary : ∀ t, toFun t ∈ unitary (E →L[ℂ] E)
  map_zero : toFun 0 = 1
  map_add : ∀ s t, toFun (s + t) = toFun s * toFun t
  continuous_apply : ∀ x, Continuous fun t => toFun t x

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace StronglyContinuousUnitaryGroup

instance : CoeFun (StronglyContinuousUnitaryGroup E) fun _ => ℝ → E →L[ℂ] E := ⟨toFun⟩

/-- The trivial group `t ↦ 1`. -/
instance : Inhabited (StronglyContinuousUnitaryGroup E) :=
  ⟨{ toFun := fun _ => 1
     mem_unitary := fun _ => one_mem _
     map_zero := rfl
     map_add := fun _ _ => (mul_one 1).symm
     continuous_apply := fun _ => continuous_const }⟩

end StronglyContinuousUnitaryGroup

/-!
## A. Pure states determine a unitary up to a phase
-/

lemma mul_rankOne_mul_star (A : E →L[ℂ] E) (x y : E) :
    A * rankOne ℂ x y * star A = rankOne ℂ (A x) (A y) := by
  ext z
  simp [rankOne_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

omit [CompleteSpace E] in
lemma rankOne_smul_smul {c : ℂ} (hc : ‖c‖ = 1) (x y : E) :
    rankOne ℂ (c • x) (c • y) = rankOne ℂ x y := by
  ext z
  simp only [rankOne_apply, inner_smul_left, smul_smul]
  congr 1
  rw [mul_comm, ← mul_assoc, Complex.mul_conj', hc]
  simp

omit [CompleteSpace E] in
lemma proj_smul_eq {c : ℂ} (hc : ‖c‖ = 1) (x : E) : proj (c • x) = proj x :=
  rankOne_smul_smul hc x x

omit [CompleteSpace E] in
/-- The polarization identity for rank-one operators. -/
lemma rankOne_eq_polarization (x y : E) :
    rankOne ℂ x y = (4⁻¹ : ℂ) • (proj (x + y) - proj (x - y) +
      Complex.I • proj (x + Complex.I • y) - Complex.I • proj (x - Complex.I • y)) := by
  ext z
  simp only [rankOne_apply, smul_apply, add_apply,
    sub_apply, inner_add_left, inner_sub_left, inner_smul_left,
    Complex.conj_I]
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

omit [CompleteSpace E] in
/-- An operator commuting with every pure state commutes with every `|w⟩⟨w|`. -/
lemma commute_proj_of_unit {z : E →L[ℂ] E}
    (h : ∀ ψ : E, ‖ψ‖ = 1 → z * proj ψ = proj ψ * z) (w : E) : z * proj w = proj w * z := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [proj]
  · have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
    have hψ : ‖(‖w‖⁻¹ : ℂ) • w‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    have hw2 : w = (‖w‖ : ℂ) • ((‖w‖⁻¹ : ℂ) • w) := by
      rw [smul_smul, mul_inv_cancel₀ hw', one_smul]
    rw [hw2, proj_smul, mul_smul_comm, smul_mul_assoc, h _ hψ]

omit [CompleteSpace E] in
/-- An operator commuting with every pure state is a scalar. -/
lemma exists_eq_smul_one_of_commute_proj {z : E →L[ℂ] E}
    (h : ∀ ψ : E, ‖ψ‖ = 1 → z * proj ψ = proj ψ * z) : ∃ a : ℂ, z = a • 1 := by
  have hall : ∀ w : E, ⟪w, w⟫_ℂ • z w = ⟪w, z w⟫_ℂ • w := fun w => by
    have h1 := congrArg (fun A : E →L[ℂ] E => A w) (commute_proj_of_unit h w)
    simpa only [mul_apply_eq_comp, proj_apply, map_smul] using h1
  have hdep : ∀ w : E, ¬ LinearIndependent ℂ ![w, z.toLinearMap w] := fun w hli => by
    rcases eq_or_ne w 0 with rfl | hw
    · exact hli.ne_zero 0 rfl
    · refine (LinearIndependent.pair_iff' hw).mp hli ((⟪w, w⟫_ℂ)⁻¹ * ⟪w, z w⟫_ℂ) ?_
      rw [mul_smul, ← hall w, smul_smul,
        inv_mul_cancel₀ (inner_self_ne_zero (𝕜 := ℂ) |>.mpr hw), one_smul]
      rfl
  obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  exact ⟨a, ContinuousLinearMap.ext fun x => by
    simpa using congrArg (fun f : E →ₗ[ℂ] E => f x) ha⟩

/-- **Two unitaries with the same action on pure states differ by a phase.** -/
theorem exists_eq_smul_of_proj_eq {u v : E →L[ℂ] E} (hu : u ∈ unitary (E →L[ℂ] E))
    (hv : v ∈ unitary (E →L[ℂ] E)) (h : ∀ ψ : E, ‖ψ‖ = 1 → proj (u ψ) = proj (v ψ)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ v = c • u := by
  set z := star u * v with hz_def
  have hz : z ∈ unitary (E →L[ℂ] E) := mul_mem (Unitary.star_mem hu) hv
  have hcomm : ∀ ψ : E, ‖ψ‖ = 1 → z * proj ψ = proj ψ * z := fun ψ hψ => by
    have h1 : u * proj ψ * star u = v * proj ψ * star v := by
      rw [mul_proj_mul_star, mul_proj_mul_star, h ψ hψ]
    have h2 : proj ψ = z * proj ψ * star z := by
      have : star u * (u * proj ψ * star u) * u = proj ψ := by
        rw [← mul_assoc, ← mul_assoc, Unitary.star_mul_self_of_mem hu, one_mul, mul_assoc,
          Unitary.star_mul_self_of_mem hu, mul_one]
      calc proj ψ = star u * (u * proj ψ * star u) * u := this.symm
        _ = star u * (v * proj ψ * star v) * u := by rw [h1]
        _ = z * proj ψ * star z := by rw [hz_def, star_mul, star_star]; simp only [mul_assoc]
    calc z * proj ψ = z * proj ψ * star z * z := by
          rw [mul_assoc (z * proj ψ), Unitary.star_mul_self_of_mem hz, mul_one]
      _ = proj ψ * z := by rw [← h2]
  obtain ⟨a, ha⟩ := exists_eq_smul_one_of_commute_proj hcomm
  have hva : v = a • u := by
    calc v = u * z := by rw [hz_def, ← mul_assoc, Unitary.mul_star_self_of_mem hu, one_mul]
      _ = a • u := by rw [ha, mul_smul_comm, mul_one]
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨1, norm_one, ContinuousLinearMap.ext fun x => Subsingleton.elim _ _⟩
  · obtain ⟨ψ, hψ⟩ := exists_norm_eq E zero_le_one
    refine ⟨a, ?_, hva⟩
    have h1 := ContinuousLinearMap.norm_map_of_mem_unitary hv ψ
    rw [hva, smul_apply, norm_smul,
      ContinuousLinearMap.norm_map_of_mem_unitary hu, hψ, mul_one] at h1
    exact h1

/-!
## B. Continuity of the pure-state evolution at every `t ≥ 0`

Let `u t` be unitaries with `|u 0 ψ⟩⟨u 0 ψ| = |ψ⟩⟨ψ|` and
`|u (s + t) ψ⟩⟨u (s + t) ψ| = |u s (u t ψ)⟩⟨u s (u t ψ)|` for `s, t ≥ 0`, and let
`t ↦ |u t ψ⟩⟨u t ψ|` be continuous at `0⁺`. The phases of `u t` are arbitrary; only these
phase-free objects enter.
-/

section Continuity

variable {u : ℝ → E →L[ℂ] E} (hu : ∀ t, u t ∈ unitary (E →L[ℂ] E))
  (h0 : ∀ ψ : E, ‖ψ‖ = 1 → proj (u 0 ψ) = proj ψ)
  (hadd : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ψ : E, ‖ψ‖ = 1 → proj (u (s + t) ψ) = proj (u s (u t ψ)))
  (hcont : ∀ ψ : E, ‖ψ‖ = 1 → ContinuousWithinAt (fun t => proj (u t ψ)) (Ici 0) 0)
include hu h0 hadd hcont

/-- Continuity at `0⁺` gives continuity at every `t₀ ≥ 0`: on the right because
`u (t₀ + h)` is `u t₀ u h` up to phase, on the left because `u (t₀ - h)` is `u h⋆ u t₀`. -/
theorem continuousWithinAt_proj {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {ψ : E} (hψ : ‖ψ‖ = 1) :
    ContinuousWithinAt (fun t => proj (u t ψ)) (Ici 0) t₀ := by
  have hφ : ‖u t₀ ψ‖ = 1 := by rw [ContinuousLinearMap.norm_map_of_mem_unitary (hu t₀), hψ]
  rw [Metric.continuousWithinAt_iff]
  intro η hη
  obtain ⟨δ₁, hδ₁, H₁⟩ := Metric.continuousWithinAt_iff.mp (hcont ψ hψ) η hη
  obtain ⟨δ₂, hδ₂, H₂⟩ := Metric.continuousWithinAt_iff.mp (hcont _ hφ) η hη
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {t} ht hdist => ?_⟩
  have ht' : (0 : ℝ) ≤ t := ht
  rw [Real.dist_eq] at hdist
  rcases le_total t₀ t with h | h
  · have e1 : proj (u t ψ) = u t₀ * proj (u (t - t₀) ψ) * star (u t₀) := by
      rw [mul_proj_mul_star, ← hadd t₀ ht₀ (t - t₀) (sub_nonneg.2 h) ψ hψ, add_sub_cancel]
    have e2 : proj (u t₀ ψ) = u t₀ * proj (u 0 ψ) * star (u t₀) := by
      rw [mul_proj_mul_star, ← hadd t₀ ht₀ 0 le_rfl ψ hψ, add_zero]
    rw [dist_eq_norm, e1, e2, ← sub_mul, ← mul_sub,
      CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (hu t₀)),
      CStarRing.norm_mem_unitary_mul _ (hu t₀), ← dist_eq_norm]
    refine H₁ (show (0 : ℝ) ≤ t - t₀ by linarith) ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith)]
    rw [abs_of_nonneg (by linarith)] at hdist
    exact lt_of_lt_of_le hdist (min_le_left _ _)
  · have hh : 0 ≤ t₀ - t := sub_nonneg.2 h
    have e1 : proj (u (t₀ - t) (u t ψ)) = proj (u t₀ ψ) := by
      rw [← hadd _ hh t ht' ψ hψ, sub_add_cancel]
    have e2 : u (t₀ - t) * (proj (u t ψ) - proj (u t₀ ψ)) * star (u (t₀ - t)) =
        proj (u t₀ ψ) - proj (u (t₀ - t) (u t₀ ψ)) := by
      rw [mul_sub, sub_mul, mul_proj_mul_star, mul_proj_mul_star, e1]
    rw [dist_eq_norm, ← CStarRing.norm_mem_unitary_mul _ (hu (t₀ - t)),
      ← CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem (hu (t₀ - t))), e2,
      ← dist_eq_norm, dist_comm, ← h0 _ hφ]
    refine H₂ hh ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hh]
    rw [abs_of_nonpos (by linarith)] at hdist
    exact lt_of_lt_of_le (by linarith) (min_le_right _ _)

/-- The same for `|u t w⟩⟨u t w|` with `w` of any norm. -/
theorem continuousWithinAt_proj_apply {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (w : E) :
    ContinuousWithinAt (fun t => proj (u t w)) (Ici 0) t₀ := by
  rcases eq_or_ne w 0 with rfl | hw
  · simpa using continuousWithinAt_const
  · have hw' : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
    have hψ : ‖(‖w‖⁻¹ : ℂ) • w‖ = 1 := by
      rw [norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    have hw2 : w = (‖w‖ : ℂ) • ((‖w‖⁻¹ : ℂ) • w) := by
      rw [smul_smul, mul_inv_cancel₀ hw', one_smul]
    have : (fun t => proj (u t w)) =
        fun t => ((‖(‖w‖ : ℂ)‖ ^ 2 : ℝ) : ℂ) • proj (u t ((‖w‖⁻¹ : ℂ) • w)) := by
      funext t
      conv_lhs => rw [hw2, map_smul, proj_smul]
    rw [this]
    exact (continuousWithinAt_proj hu h0 hadd hcont ht₀ hψ).const_smul
      (((‖(‖w‖ : ℂ)‖ ^ 2 : ℝ) : ℂ))

/-- **The phase-free continuity.** `t ↦ |u t x⟩⟨u t y|` is continuous at every `t₀ ≥ 0`, by
polarization. -/
theorem continuousWithinAt_rankOne {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (x y : E) :
    ContinuousWithinAt (fun t => rankOne ℂ (u t x) (u t y)) (Ici 0) t₀ := by
  have : (fun t => rankOne ℂ (u t x) (u t y)) = fun t => (4⁻¹ : ℂ) •
      (proj (u t (x + y)) - proj (u t (x - y)) + Complex.I • proj (u t (x + Complex.I • y)) -
        Complex.I • proj (u t (x - Complex.I • y))) := by
    funext t
    rw [rankOne_eq_polarization]
    simp only [map_add, map_sub, map_smul]
  rw [this]
  have hc := fun w => continuousWithinAt_proj_apply hu h0 hadd hcont ht₀ w
  exact ((((hc _).sub (hc _)).add ((hc _).const_smul Complex.I)).sub
    ((hc _).const_smul Complex.I)).const_smul (4⁻¹ : ℂ)

end Continuity

/-- If `t ↦ A t x` is continuous for every `x` and every `A t` is unitary, so is
`t ↦ A t⋆ x`. -/
theorem continuousWithinAt_star_apply {A : ℝ → E →L[ℂ] E} (hA : ∀ t, A t ∈ unitary (E →L[ℂ] E))
    {s : Set ℝ} {t₀ : ℝ} (h : ∀ x, ContinuousWithinAt (fun t => A t x) s t₀) (x : E) :
    ContinuousWithinAt (fun t => star (A t) x) s t₀ := by
  set y := star (A t₀) x
  have hy : A t₀ y = x := by
    rw [← mul_apply_eq_comp, Unitary.mul_star_self_of_mem (hA t₀),
      one_apply_eq_self]
  have key : ∀ t, ‖star (A t) x - y‖ = ‖A t y - A t₀ y‖ := fun t => by
    rw [← ContinuousLinearMap.norm_map_of_mem_unitary (hA t), map_sub,
      ← mul_apply_eq_comp, Unitary.mul_star_self_of_mem (hA t),
      one_apply_eq_self, hy, norm_sub_rev]
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  exact (tendsto_congr key).mpr (tendsto_iff_norm_sub_tendsto_zero.mp (h y))

/-!
## C. Extending a local homomorphism
-/

/-- **A local homomorphism on `[0, ε]` extends to `t ≥ 0`**, by `W t = V (t / n) ^ n` for any `n`
with `t / n ≤ ε`. -/
theorem exists_map_add_of_local {M : Type*} [Monoid M] {ε : ℝ} (hε : 0 < ε) {V : ℝ → M}
    (h0 : V 0 = 1) (hV : ∀ a ∈ Icc 0 ε, ∀ b ∈ Icc 0 ε, V (a + b) = V a * V b) :
    ∃ W : ℝ → M, (∀ s ≥ 0, ∀ t ≥ 0, W (s + t) = W s * W t) ∧ ∀ t ∈ Icc 0 ε, W t = V t := by
  have hpow : ∀ s ∈ Icc 0 ε, ∀ k : ℕ, k * s ≤ ε → V s ^ k = V (k * s) := by
    intro s hs k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      have hks : (k : ℝ) * s ≤ ε := le_trans (by push_cast; nlinarith [hs.1]) hk
      rw [pow_succ, ih hks, ← hV _ ⟨by positivity [hs.1], hks⟩ s hs]
      congr 1
      push_cast
      ring
  have hwd : ∀ t ≥ 0, ∀ n m : ℕ, 0 < n → 0 < m → t / n ≤ ε → t / m ≤ ε →
      V (t / n) ^ n = V (t / m) ^ m := by
    intro t ht n m hn hm h1 h2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hs : t / (n * m) ∈ Icc 0 ε := by
      refine ⟨by positivity, le_trans ?_ h1⟩
      exact div_le_div_of_nonneg_left ht hn' (le_mul_of_one_le_right hn'.le (by exact_mod_cast hm))
    have hk1 : (m : ℝ) * (t / (n * m)) = t / n := by field_simp
    have hk2 : (n : ℝ) * (t / (n * m)) = t / m := by field_simp
    have e1 : V (t / n) = V (t / (n * m)) ^ m := by
      rw [hpow _ hs m (hk1 ▸ h1), hk1]
    have e2 : V (t / m) = V (t / (n * m)) ^ n := by
      rw [hpow _ hs n (hk2 ▸ h2), hk2]
    rw [e1, e2, ← pow_mul, ← pow_mul, Nat.mul_comm n m]
  set N : ℝ → ℕ := fun t => ⌈t / ε⌉₊ + 1
  have hN : ∀ t ≥ 0, t / N t ≤ ε := fun t ht => by
    have h1 : t / ε ≤ ⌈t / ε⌉₊ := Nat.le_ceil _
    have h2 : (0 : ℝ) < N t := by positivity
    rw [div_le_iff₀ h2]
    have : t ≤ ε * ⌈t / ε⌉₊ := by rwa [div_le_iff₀' hε] at h1
    simp only [N]
    push_cast
    nlinarith
  refine ⟨fun t => V (t / N t) ^ N t, fun s hs t ht => ?_, fun t ht => ?_⟩
  · set n := N (s + t)
    have hn : 0 < n := Nat.succ_pos _
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hst := hN (s + t) (add_nonneg hs ht)
    have hs' : s / n ∈ Icc 0 ε :=
      ⟨by positivity, le_trans (div_le_div_of_nonneg_right (by linarith) hn'.le) hst⟩
    have ht' : t / n ∈ Icc 0 ε :=
      ⟨by positivity, le_trans (div_le_div_of_nonneg_right (by linarith) hn'.le) hst⟩
    have hc : Commute (V (s / n)) (V (t / n)) := by
      rw [Commute, SemiconjBy, ← hV _ hs' _ ht', ← hV _ ht' _ hs', add_comm]
    simp only
    rw [hwd s hs _ n (Nat.succ_pos _) hn (hN s hs) hs'.2,
      hwd t ht _ n (Nat.succ_pos _) hn (hN t ht) ht'.2, ← hc.mul_pow, ← hV _ hs' _ ht', add_div]
  · simp only
    rw [hwd t ht.1 _ 1 (Nat.succ_pos _) one_pos (hN t ht.1) (by simpa using ht.2)]
    simp

/-!
## D. The normalized local section
-/

/-- The phase `conj z / |z|`, which makes `unitPhase z * z = |z|`; it is `1` if `z = 0`. -/
def unitPhase (z : ℂ) : ℂ := if z = 0 then 1 else conj z / (‖z‖ : ℂ)

lemma norm_unitPhase (z : ℂ) : ‖unitPhase z‖ = 1 := by
  unfold unitPhase
  split_ifs with h
  · exact norm_one
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm,
      div_self (norm_ne_zero_iff.mpr h)]

lemma unitPhase_mul_self (z : ℂ) : unitPhase z * z = (‖z‖ : ℂ) := by
  unfold unitPhase
  split_ifs with h
  · simp [h]
  · have hz : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    rw [div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff hz]
    ring

/-- A phase times a unitary is unitary. -/
lemma smul_mem_unitary {c : ℂ} (hc : ‖c‖ = 1) {A : E →L[ℂ] E} (hA : A ∈ unitary (E →L[ℂ] E)) :
    c • A ∈ unitary (E →L[ℂ] E) := by
  have h1 : conj c * c = 1 := by rw [Complex.conj_mul', hc]; simp
  have h2 : c * conj c = 1 := by rw [mul_comm, h1]
  rw [Unitary.mem_iff, star_smul, Complex.star_def, smul_mul_smul_comm, smul_mul_smul_comm, h1,
    h2, Unitary.star_mul_self_of_mem hA, Unitary.mul_star_self_of_mem hA, one_smul]
  exact ⟨rfl, rfl⟩

/-- Conjugation does not see a phase. -/
lemma smul_mul_mul_star {c : ℂ} (hc : ‖c‖ = 1) (A X : E →L[ℂ] E) :
    c • A * X * star (c • A) = A * X * star A := by
  have h : c * conj c = 1 := by rw [Complex.mul_conj', hc]; simp
  rw [star_smul, Complex.star_def, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, h,
    one_smul]

/-- The section normalized by `⟪e, U t e⟫ ≥ 0`. -/
def normalizedSection (u : ℝ → E →L[ℂ] E) (e : E) (t : ℝ) : E →L[ℂ] E :=
  unitPhase ⟪e, u t e⟫_ℂ • u t

section Normalized

variable {u : ℝ → E →L[ℂ] E} {e : E}

lemma normalizedSection_mem_unitary (hu : ∀ t, u t ∈ unitary (E →L[ℂ] E)) (t : ℝ) :
    normalizedSection u e t ∈ unitary (E →L[ℂ] E) :=
  smul_mem_unitary (norm_unitPhase _) (hu t)

omit [CompleteSpace E] in
lemma inner_normalizedSection (t : ℝ) :
    ⟪e, normalizedSection u e t e⟫_ℂ = (‖⟪e, u t e⟫_ℂ‖ : ℂ) := by
  rw [normalizedSection, smul_apply, inner_smul_right, unitPhase_mul_self]

omit [CompleteSpace E] in
lemma rankOne_normalizedSection (t : ℝ) (x y : E) :
    rankOne ℂ (normalizedSection u e t x) (normalizedSection u e t y) =
      rankOne ℂ (u t x) (u t y) := by
  simp only [normalizedSection, smul_apply]
  exact rankOne_smul_smul (norm_unitPhase _) _ _

omit [CompleteSpace E] in
lemma proj_normalizedSection (t : ℝ) (x : E) :
    proj (normalizedSection u e t x) = proj (u t x) :=
  rankOne_normalizedSection t x x

omit [CompleteSpace E] in
/-- Where `⟪e, u t e⟫ ≠ 0`, the normalized section is recovered from the phase-free
`|u t x⟩⟨u t e|`. -/
lemma normalizedSection_apply_eq {t : ℝ} (hg : ⟪e, u t e⟫_ℂ ≠ 0) (x : E) :
    normalizedSection u e t x = ((‖⟪e, u t e⟫_ℂ‖ : ℂ))⁻¹ • rankOne ℂ (u t x) (u t e) e := by
  have hn : (‖⟪e, u t e⟫_ℂ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hg
  have h : ⟪normalizedSection u e t e, e⟫_ℂ = (‖⟪e, u t e⟫_ℂ‖ : ℂ) := by
    rw [← inner_conj_symm, inner_normalizedSection, Complex.conj_ofReal]
  rw [← rankOne_normalizedSection (e := e) t x e, rankOne_apply, h, smul_smul,
    inv_mul_cancel₀ hn, one_smul]

omit [CompleteSpace E] in
lemma norm_inner_sq (t : ℝ) :
    ‖⟪e, u t e⟫_ℂ‖ = √(⟪e, proj (u t e) e⟫_ℂ).re := by
  rw [inner_proj_apply, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _), norm_inner_symm]

end Normalized

/-- The multiplier `ω a b` of the normalized section, `U a U b = ω a b U (a + b)`. -/
def multiplier (u : ℝ → E →L[ℂ] E) (e : E) (a b : ℝ) : ℂ :=
  ⟪e, normalizedSection u e a (normalizedSection u e b e)⟫_ℂ /
    ⟪e, normalizedSection u e (a + b) e⟫_ℂ

/-!
## E. The multiplier is a continuous local 2-cocycle
-/

section Multiplier

variable {u : ℝ → E →L[ℂ] E} (hu : ∀ t, u t ∈ unitary (E →L[ℂ] E))
  (h0 : ∀ ψ : E, ‖ψ‖ = 1 → proj (u 0 ψ) = proj ψ)
  (hadd : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ψ : E, ‖ψ‖ = 1 → proj (u (s + t) ψ) = proj (u s (u t ψ)))
  (hcont : ∀ ψ : E, ‖ψ‖ = 1 → ContinuousWithinAt (fun t => proj (u t ψ)) (Ici 0) 0)
  {e : E} (he : ‖e‖ = 1)

include hu h0 hadd hcont he

theorem continuousWithinAt_norm_inner {t₀ : ℝ} (ht₀ : 0 ≤ t₀) :
    ContinuousWithinAt (fun t => ‖⟪e, u t e⟫_ℂ‖) (Ici 0) t₀ := by
  simp_rw [norm_inner_sq]
  have hF : Continuous fun X : E →L[ℂ] E => √(⟪e, X e⟫_ℂ).re := by fun_prop
  exact hF.continuousAt.comp_continuousWithinAt (continuousWithinAt_proj hu h0 hadd hcont ht₀ he)

omit [CompleteSpace E] hu hadd hcont in
lemma norm_inner_zero : ‖⟪e, u 0 e⟫_ℂ‖ = 1 := by
  rw [norm_inner_sq, h0 e he, inner_proj_apply, Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _),
    inner_self_eq_norm_sq_to_K, he]
  simp

omit h0 hcont he in
theorem multiplier_spec {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : ⟪e, u (a + b) e⟫_ℂ ≠ 0) :
    ‖multiplier u e a b‖ = 1 ∧ normalizedSection u e a * normalizedSection u e b =
      multiplier u e a b • normalizedSection u e (a + b) := by
  obtain ⟨c, hc, hceq⟩ := exists_eq_smul_of_proj_eq (normalizedSection_mem_unitary hu (a + b))
    (mul_mem (normalizedSection_mem_unitary hu a) (normalizedSection_mem_unitary hu b))
    fun ψ hψ => by
      rw [proj_normalizedSection (e := e), mul_apply_eq_comp, proj_normalizedSection (e := e),
        normalizedSection,
        smul_apply, map_smul, hadd a ha b hb ψ hψ]
      exact (rankOne_smul_smul (norm_unitPhase _) _ _).symm
  have hn : ⟪e, normalizedSection u e (a + b) e⟫_ℂ ≠ 0 := by
    rw [inner_normalizedSection]; exact_mod_cast norm_ne_zero_iff.mpr hab
  have hω : multiplier u e a b = c := by
    rw [multiplier, ← mul_apply_eq_comp, hceq, smul_apply, inner_smul_right, mul_div_assoc,
      div_self hn, mul_one]
  rw [hω]
  exact ⟨hc, hceq⟩

omit h0 hcont he in
theorem multiplier_cocycle {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hab : ⟪e, u (a + b) e⟫_ℂ ≠ 0) (hbc : ⟪e, u (b + c) e⟫_ℂ ≠ 0)
    (habc : ⟪e, u (a + b + c) e⟫_ℂ ≠ 0) :
    multiplier u e a b * multiplier u e (a + b) c =
      multiplier u e a (b + c) * multiplier u e b c := by
  have h1 := (multiplier_spec hu hadd ha hb hab).2
  have h2 := (multiplier_spec hu hadd (add_nonneg ha hb) hc habc).2
  have h3 := (multiplier_spec hu hadd hb hc hbc).2
  have h4 := (multiplier_spec hu hadd ha (add_nonneg hb hc)
    (by rwa [← add_assoc])).2
  have e1 : normalizedSection u e a * normalizedSection u e b * normalizedSection u e c =
      (multiplier u e a b * multiplier u e (a + b) c) • normalizedSection u e (a + b + c) := by
    rw [h1, smul_mul_assoc, h2, smul_smul]
  have e2 : normalizedSection u e a * (normalizedSection u e b * normalizedSection u e c) =
      (multiplier u e a (b + c) * multiplier u e b c) • normalizedSection u e (a + b + c) := by
    rw [h3, mul_smul_comm, h4, smul_smul, ← add_assoc, mul_comm (multiplier u e b c)]
  have key := e1.symm.trans ((mul_assoc _ _ _).trans e2)
  have hn : ⟪e, normalizedSection u e (a + b + c) e⟫_ℂ ≠ 0 := by
    rw [inner_normalizedSection]; exact_mod_cast norm_ne_zero_iff.mpr habc
  have := congrArg (fun A : E →L[ℂ] E => ⟪e, A e⟫_ℂ) key
  simp only [smul_apply, inner_smul_right] at this
  exact mul_right_cancel₀ hn this

end Multiplier

/-!
## F. The lift
-/

/-- **Bargmann's theorem for `ℝ`, phase-free form.** Let `u t` be unitaries whose action on pure
states is a semigroup on `t ≥ 0`, starts at the identity and is continuous at `0⁺`. Then a
strongly continuous unitary group `V` has the same action on pure states for all `t ≥ 0`. -/
theorem exists_stronglyContinuousUnitaryGroup_of_proj {u : ℝ → E →L[ℂ] E}
    (hu : ∀ t, u t ∈ unitary (E →L[ℂ] E))
    (h0 : ∀ ψ : E, ‖ψ‖ = 1 → proj (u 0 ψ) = proj ψ)
    (hadd : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ψ : E, ‖ψ‖ = 1 → proj (u (s + t) ψ) = proj (u s (u t ψ)))
    (hcont : ∀ ψ : E, ‖ψ‖ = 1 → ContinuousWithinAt (fun t => proj (u t ψ)) (Ici 0) 0) :
    ∃ V : StronglyContinuousUnitaryGroup E, ∀ t ≥ 0, ∀ ψ : E, ‖ψ‖ = 1 →
      proj (V t ψ) = proj (u t ψ) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨default, fun _ _ _ _ => ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _⟩
  obtain ⟨e, he⟩ := exists_norm_eq E zero_le_one
  -- A neighbourhood `[0, δ]` of `0` on which `⟪e, u t e⟫ ≠ 0`.
  obtain ⟨δ, hδ, hgδ⟩ : ∃ δ > 0, ∀ t ∈ Icc 0 δ, ⟪e, u t e⟫_ℂ ≠ 0 := by
    obtain ⟨δ', hδ', H⟩ := Metric.continuousWithinAt_iff.mp
      (continuousWithinAt_norm_inner hu h0 hadd hcont he le_rfl) 1 one_pos
    refine ⟨δ' / 2, by positivity, fun t ht hzero => ?_⟩
    have := H (x := t) ht.1 (by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]; linarith [ht.2])
    rw [hzero, norm_zero, norm_inner_zero h0 he, Real.dist_eq] at this
    norm_num at this
  set N := normalizedSection u e with hN_def
  have hN : ∀ t, N t ∈ unitary (E →L[ℂ] E) := normalizedSection_mem_unitary hu
  have hNc : ∀ x, ContinuousOn (fun t => N t x) (Icc 0 δ) := fun x t₀ ht₀ => by
    have hn : (‖⟪e, u t₀ e⟫_ℂ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hgδ t₀ ht₀)
    have hform : ContinuousWithinAt
        (fun t => ((‖⟪e, u t e⟫_ℂ‖ : ℂ))⁻¹ • rankOne ℂ (u t x) (u t e) e) (Ici 0) t₀ :=
      ((Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        (continuousWithinAt_norm_inner hu h0 hadd hcont he ht₀.1)).inv₀ hn).smul
        ((continuousWithinAt_rankOne hu h0 hadd hcont ht₀.1 x e).clm_apply
          continuousWithinAt_const)
    exact (hform.mono Icc_subset_Ici_self).congr
      (fun t ht => normalizedSection_apply_eq (hgδ t ht) x)
      (normalizedSection_apply_eq (hgδ t₀ ht₀) x)
  have hN0 : N 0 = 1 := by
    obtain ⟨c, -, hc⟩ := exists_eq_smul_of_proj_eq (one_mem _) (hN 0) fun ψ hψ => by
      rw [hN_def, proj_normalizedSection, h0 ψ hψ]; rfl
    have h1 := inner_normalizedSection (u := u) (e := e) 0
    rw [← hN_def, hc, norm_inner_zero h0 he, smul_apply, one_apply_eq_self,
      inner_smul_right, inner_self_eq_norm_sq_to_K, he] at h1
    rw [hc, show c = 1 by simpa using h1, one_smul]
  set ω := multiplier u e with hω_def
  have hspec : ∀ a b, 0 ≤ a → 0 ≤ b → a + b ≤ δ → ‖ω a b‖ = 1 ∧ N a * N b = ω a b • N (a + b) :=
    fun a b ha hb hab => multiplier_spec hu hadd ha hb (hgδ _ ⟨add_nonneg ha hb, hab⟩)
  -- `ω` is continuous on `[0, δ/2]²`.
  have hbox : MapsTo (fun q : ℝ × ℝ => q.1 + q.2) (Icc 0 (δ / 2) ×ˢ Icc 0 (δ / 2)) (Icc 0 δ) :=
    fun q hq => ⟨add_nonneg hq.1.1 hq.2.1, by linarith [hq.1.2, hq.2.2]⟩
  have hfst : MapsTo Prod.fst (Icc 0 (δ / 2) ×ˢ Icc 0 (δ / 2)) (Icc 0 δ) :=
    fun q hq => ⟨hq.1.1, by linarith [hq.1.2]⟩
  have hsnd : MapsTo Prod.snd (Icc 0 (δ / 2) ×ˢ Icc 0 (δ / 2)) (Icc 0 δ) :=
    fun q hq => ⟨hq.2.1, by linarith [hq.2.2]⟩
  have hωc : ContinuousOn (Function.uncurry ω) (Icc 0 (δ / 2) ×ˢ Icc 0 (δ / 2)) := by
    have hstar : ContinuousOn (fun a => star (N a) e) (Icc 0 δ) := fun a ha =>
      continuousWithinAt_star_apply hN (fun x => hNc x a ha) e
    have hnum : ContinuousOn (fun q : ℝ × ℝ => ⟪star (N q.1) e, N q.2 e⟫_ℂ)
        (Icc 0 (δ / 2) ×ˢ Icc 0 (δ / 2)) :=
      (hstar.comp continuousOn_fst hfst).inner ((hNc e).comp continuousOn_snd hsnd)
    have hden : ContinuousOn (fun q : ℝ × ℝ => ((‖⟪e, u (q.1 + q.2) e⟫_ℂ‖ : ℝ) : ℂ))
        (Icc 0 (δ / 2) ×ˢ Icc 0 (δ / 2)) := fun q hq =>
      Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt
        ((continuousWithinAt_norm_inner hu h0 hadd hcont he (hbox hq).1).comp
          (f := fun q : ℝ × ℝ => q.1 + q.2) (continuous_fst.add continuous_snd).continuousWithinAt
          fun q' hq' => (hbox hq').1)
    refine (hnum.div hden fun q hq => by
      exact_mod_cast norm_ne_zero_iff.mpr (hgδ _ (hbox hq))).congr
      fun q _ => ?_
    simp only [Function.uncurry, hω_def, multiplier, hN_def, inner_normalizedSection,
      Pi.div_apply, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  -- `Re ω > 0` near `0`.
  have hω00 : ω 0 0 = 1 := by
    rw [hω_def, multiplier, ← hN_def, add_zero, hN0, one_apply_eq_self, one_apply_eq_self,
      div_self (by rw [inner_self_eq_norm_sq_to_K, he]; norm_num)]
  obtain ⟨r, hr, hre⟩ : ∃ r > 0, ∀ a ∈ Icc 0 r, ∀ b ∈ Icc 0 r, 0 < (ω a b).re := by
    obtain ⟨ρ, hρ, H⟩ := Metric.continuousWithinAt_iff.mp
      (hωc (0, 0) ⟨⟨le_rfl, by positivity⟩, ⟨le_rfl, by positivity⟩⟩) 1 one_pos
    refine ⟨min (δ / 2) (ρ / 2), by positivity, fun a ha b hb => ?_⟩
    have hq : (a, b) ∈ Icc 0 (δ / 2) ×ˢ Icc 0 (δ / 2) :=
      ⟨⟨ha.1, ha.2.trans (min_le_left _ _)⟩, ⟨hb.1, hb.2.trans (min_le_left _ _)⟩⟩
    have hd : dist (a, b) ((0 : ℝ), (0 : ℝ)) < ρ := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, abs_of_nonneg ha.1,
        abs_of_nonneg hb.1, max_lt_iff]
      constructor <;> linarith [ha.2.trans (min_le_right _ _), hb.2.trans (min_le_right _ _)]
    have h1 := H hq hd
    simp only [Function.uncurry, hω00, dist_eq_norm] at h1
    have h2 := Complex.abs_re_le_norm (ω a b - 1)
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith [abs_lt.mp (lt_of_le_of_lt h2 h1)]
  -- The coboundary.
  set ε := min (δ / 4) (r / 2) with hε_def
  have hε : 0 < ε := by positivity
  have hεδ : ε ≤ δ / 4 := min_le_left _ _
  have hεr : ε ≤ r / 2 := min_le_right _ _
  obtain ⟨f, hf, hfω⟩ := Real.exists_eq_exp_of_localCocycle (α := 0) le_rfl hε (ω := ω)
    (hωc.mono fun q hq => by
      rw [mul_zero] at hq
      exact ⟨⟨hq.1.1, by linarith [hq.1.2]⟩, ⟨hq.2.1, by linarith [hq.2.2]⟩⟩)
    (fun a ha b hb => by
      rw [mul_zero] at ha hb
      exact hre a ⟨ha.1, by linarith [ha.2]⟩ b ⟨hb.1, by linarith [hb.2]⟩)
    (fun a ha b hb c hc => multiplier_cocycle hu hadd ha.1 hb.1 hc.1
      (hgδ _ ⟨by linarith [ha.1, hb.1], by linarith [ha.2, hb.2]⟩)
      (hgδ _ ⟨by linarith [hc.1, hb.1], by linarith [hc.2, hb.2]⟩)
      (hgδ _ ⟨by linarith [ha.1, hb.1, hc.1], by linarith [ha.2, hb.2, hc.2]⟩))
    (fun a ha b hb => (hspec a b ha.1 hb.1 (by linarith [ha.2, hb.2])).1)
  -- The local homomorphism `V t = exp (-i f t) U t`.
  obtain ⟨V, hV_def⟩ : ∃ V : ℝ → E →L[ℂ] E,
      V = fun t => Complex.exp (((-f t : ℝ) : ℂ) * Complex.I) • N t := ⟨_, rfl⟩
  have hVu : ∀ t, V t ∈ unitary (E →L[ℂ] E) := fun t =>
    hV_def ▸ smul_mem_unitary (Complex.norm_exp_ofReal_mul_I _) (hN t)
  have hVmul : ∀ a ∈ Icc 0 ε, ∀ b ∈ Icc 0 ε, V (a + b) = V a * V b := fun a ha b hb => by
    rw [hV_def]
    simp only
    rw [smul_mul_smul_comm, (hspec a b ha.1 hb.1 (by linarith [ha.2, hb.2])).2, smul_smul,
      hfω a ha b hb, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  let V' : ℝ → unitary (E →L[ℂ] E) := fun t => ⟨V t, hVu t⟩
  have hV'mul : ∀ a ∈ Icc 0 ε, ∀ b ∈ Icc 0 ε, V' (a + b) = V' a * V' b :=
    fun a ha b hb => Subtype.ext (hVmul a ha b hb)
  have hε0 : (0 : ℝ) ∈ Icc 0 ε := ⟨le_rfl, hε.le⟩
  have hV'0 : V' 0 = 1 := by
    have h := congrArg Subtype.val (hV'mul 0 hε0 0 hε0)
    rw [add_zero] at h
    refine Subtype.ext ?_
    change V 0 = 1
    calc V 0 = star (V 0) * V 0 * V 0 := by rw [Unitary.star_mul_self_of_mem (hVu 0), one_mul]
      _ = star (V 0) * V 0 := by rw [mul_assoc]; exact congrArg _ h.symm
      _ = 1 := Unitary.star_mul_self_of_mem (hVu 0)
  obtain ⟨W, hWadd, hWV⟩ := exists_map_add_of_local hε hV'0 hV'mul
  obtain ⟨G, hGadd, hGW⟩ := Wigner.exists_map_add_of_nonneg hWadd
  have hG0 : G 0 = 1 := by rw [hGW 0 le_rfl, hWV 0 hε0, hV'0]
  have hGV : ∀ t ∈ Icc 0 ε, (G t : E →L[ℂ] E) = V t := fun t ht => by
    rw [hGW t ht.1, hWV t ht]
  -- Strong continuity of `G`.
  have hright : ∀ x, ContinuousWithinAt (fun t => (G t : E →L[ℂ] E) x) (Ici 0) 0 := fun x => by
    have hVc : ContinuousWithinAt (fun t => V t x) (Icc 0 ε) 0 := by
      rw [hV_def]
      simp only [smul_apply]
      exact ((Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (hf.neg)).mul continuous_const)).continuousWithinAt).smul
        ((hNc x).mono (Icc_subset_Icc le_rfl (by linarith)) 0 hε0)
    exact (hVc.congr (fun t ht => by rw [hGV t ht]) (by rw [hGV 0 hε0])).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE hε)
  have hinv : ∀ t, (G t : E →L[ℂ] E) = star (G (-t) : E →L[ℂ] E) := fun t => by
    have h : G t * G (-t) = 1 := by rw [← hGadd, add_neg_cancel, hG0]
    rw [eq_inv_of_mul_eq_one_left h, ← Unitary.star_eq_inv, Unitary.coe_star]
  have hleft : ∀ x, ContinuousWithinAt (fun t => (G t : E →L[ℂ] E) x) (Iic 0) 0 := fun x => by
    have hs := continuousWithinAt_star_apply (A := fun t => (G t : E →L[ℂ] E)) (fun t => (G t).2)
      hright x
    rw [show (fun t => (G t : E →L[ℂ] E) x) = fun t => star (G (-t) : E →L[ℂ] E) x from
      funext fun t => by rw [hinv t]]
    exact hs.comp_of_eq (f := fun t : ℝ => -t) continuous_neg.continuousWithinAt
      (fun t ht => neg_nonneg.mpr ht) neg_zero
  have hat0 : ∀ x, ContinuousAt (fun t => (G t : E →L[ℂ] E) x) 0 := fun x => by
    rw [← continuousWithinAt_univ, ← Iic_union_Ici]
    exact (hleft x).union (hright x)
  have hcontG : ∀ x, Continuous fun t => (G t : E →L[ℂ] E) x := fun x =>
    continuous_iff_continuousAt.2 fun t₀ => by
      have h : (fun t => (G t : E →L[ℂ] E) x) =
          fun t => (G t₀ : E →L[ℂ] E) ((G (t - t₀) : E →L[ℂ] E) x) := by
        funext t
        rw [← mul_apply_eq_comp, ← Submonoid.coe_mul, ← hGadd, add_sub_cancel]
      rw [h]
      exact (G t₀ : E →L[ℂ] E).continuous.continuousAt.comp
        ((hat0 x).comp_of_eq (continuousAt_id.sub continuousAt_const) (sub_self t₀))
  -- `G` has the action of `u` on pure states.
  have hloc : ∀ s ∈ Icc 0 ε, ∀ φ : E, proj ((G s : E →L[ℂ] E) φ) = proj (u s φ) := fun s hs φ => by
    rw [hGV s hs, hV_def]
    simp only [hN_def, normalizedSection, smul_apply]
    rw [proj_smul_eq (Complex.norm_exp_ofReal_mul_I _), proj_smul_eq (norm_unitPhase _)]
  have hpow : ∀ s ∈ Icc 0 ε, ∀ k : ℕ, ∀ ψ : E, ‖ψ‖ = 1 →
      proj ((G (k * s) : E →L[ℂ] E) ψ) = proj (u (k * s) ψ) := by
    intro s hs k
    induction k with
    | zero => intro ψ hψ; simp [hG0, h0 ψ hψ]
    | succ k ih =>
      intro ψ hψ
      have hks : (0 : ℝ) ≤ k * s := mul_nonneg (Nat.cast_nonneg _) hs.1
      obtain ⟨c, hc, hcG⟩ := exists_eq_smul_of_proj_eq (hu (k * s)) (G (k * s)).2
        fun φ hφ => (ih φ hφ).symm
      have hψ' : ‖u (k * s) ψ‖ = 1 := by
        rw [ContinuousLinearMap.norm_map_of_mem_unitary (hu _), hψ]
      have e1 : ((k + 1 : ℕ) : ℝ) * s = s + k * s := by push_cast; ring
      rw [e1, hGadd, Submonoid.coe_mul, mul_apply_eq_comp, hcG, smul_apply, map_smul,
        proj_smul_eq hc, hloc s hs, hadd s hs.1 _ hks ψ hψ]
  have hrel : ∀ t ≥ 0, ∀ ψ : E, ‖ψ‖ = 1 → proj ((G t : E →L[ℂ] E) ψ) = proj (u t ψ) := by
    intro t ht ψ hψ
    set n : ℕ := ⌈t / ε⌉₊ + 1
    have hn : (0 : ℝ) < n := by positivity
    have hs : t / n ∈ Icc 0 ε := by
      refine ⟨by positivity, ?_⟩
      have h1 : t / ε ≤ ⌈t / ε⌉₊ := Nat.le_ceil _
      rw [div_le_iff₀ hn]
      have : t ≤ ε * ⌈t / ε⌉₊ := by rwa [div_le_iff₀' hε] at h1
      simp only [n]
      push_cast
      nlinarith
    have := hpow _ hs n ψ hψ
    rwa [mul_div_cancel₀ _ hn.ne'] at this
  exact ⟨⟨fun t => G t, fun t => (G t).2, by rw [hG0]; rfl,
    fun s t => by rw [hGadd]; rfl, hcontG⟩, hrel⟩

/-- **Bargmann's theorem for `ℝ`.** A time evolution of density operators that is, for each
`t ≥ 0`, conjugation by a unitary or an anti-unitary, starts at the identity, is a semigroup and
is continuous at `0⁺` on pure states is conjugation by a strongly continuous unitary group. -/
theorem exists_stronglyContinuousUnitaryGroup {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E}
    (hΦ : ∀ t ≥ 0, ImplementedOnDensityOperators (Φ t))
    (h0 : ∀ ψ : E, ‖ψ‖ = 1 → Φ 0 (proj ψ) = proj ψ)
    (hadd : ∀ s ≥ 0, ∀ t ≥ 0, ∀ ρ, IsDensityOperator ρ → Φ (s + t) ρ = Φ s (Φ t ρ))
    (hcont : ∀ ψ : E, ‖ψ‖ = 1 → ContinuousWithinAt (fun t => Φ t (proj ψ)) (Ici 0) 0) :
    ∃ V : StronglyContinuousUnitaryGroup E, ∀ t ≥ 0, ∀ ρ, IsDensityOperator ρ →
      Φ t ρ = V t * ρ * star (V t) := by
  -- Anti-unitaries are excluded by `Φ t = Φ (t / 2) ∘ Φ (t / 2)`.
  have hunit : ∀ t ≥ 0, ∃ v : E →L[ℂ] E, v ∈ unitary (E →L[ℂ] E) ∧
      ∀ ρ, IsDensityOperator ρ → Φ t ρ = v * ρ * star v := by
    intro t ht
    have hcomp : ∀ ρ, IsDensityOperator ρ → Φ t ρ = Φ (t / 2) (Φ (t / 2) ρ) := fun ρ hρ => by
      rw [← hadd _ (by positivity) _ (by positivity) ρ hρ, add_halves]
    obtain ⟨W, hW⟩ : ∃ W : E ≃ₗᵢ[ℂ] E, ∀ ρ, IsDensityOperator ρ → Φ t ρ = conjOp W ρ := by
      rcases hΦ (t / 2) (by positivity) with ⟨W, hW⟩ | ⟨W, hW⟩ <;>
        exact ⟨W.trans W, fun ρ hρ => by
          rw [hcomp ρ hρ, hW ρ hρ, hW _ (hρ.conjOp W), conjOp_trans_self]⟩
    exact ⟨(W : E →L[ℂ] E), (Unitary.linearIsometryEquiv.symm W).2, fun ρ hρ => by
      rw [hW ρ hρ, ← adL_apply, adL_eq_mul_mul_star]⟩
  set u : ℝ → E →L[ℂ] E := fun t => if ht : 0 ≤ t then (hunit t ht).choose else 1 with hu_def
  have hu : ∀ t, u t ∈ unitary (E →L[ℂ] E) := fun t => by
    by_cases ht : 0 ≤ t
    · simpa [hu_def, ht] using (hunit t ht).choose_spec.1
    · simp [hu_def, ht]
  have huΦ : ∀ t ≥ 0, ∀ ρ, IsDensityOperator ρ → Φ t ρ = u t * ρ * star (u t) :=
    fun t ht ρ hρ => by simpa [hu_def, ht] using (hunit t ht).choose_spec.2 ρ hρ
  have hproj : ∀ t ≥ 0, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (u t ψ) := fun t ht ψ hψ => by
    rw [huΦ t ht _ (isDensityOperator_proj hψ), mul_proj_mul_star]
  obtain ⟨V, hV⟩ := exists_stronglyContinuousUnitaryGroup_of_proj hu
    (fun ψ hψ => by rw [← hproj 0 le_rfl ψ hψ, h0 ψ hψ])
    (fun s hs t ht ψ hψ => by
      have hψ' : ‖u t ψ‖ = 1 := by rw [ContinuousLinearMap.norm_map_of_mem_unitary (hu t), hψ]
      rw [← hproj _ (add_nonneg hs ht) ψ hψ, hadd s hs t ht _ (isDensityOperator_proj hψ),
        hproj t ht ψ hψ, hproj s hs _ hψ'])
    (fun ψ hψ => (hcont ψ hψ).congr (fun t ht => (hproj t ht ψ hψ).symm)
      (hproj 0 le_rfl ψ hψ).symm)
  refine ⟨V, fun t ht ρ hρ => ?_⟩
  obtain ⟨c, hc, hVc⟩ := exists_eq_smul_of_proj_eq (hu t) (V.mem_unitary t)
    fun ψ hψ => (hV t ht ψ hψ).symm
  rw [huΦ t ht ρ hρ]
  rw [hVc, smul_mul_mul_star hc]

end QuantumMechanics
