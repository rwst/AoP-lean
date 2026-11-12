/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Inconsistent convergence in Hilbert space.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

In `ℓ²(ℕ)`, read as the harmonic oscillator with energy eigenbasis `|n⟩ = δₙ`, the states
`|eʲ⟩ = √((j-1)/j) |0⟩ + √(1/j) |j⟩` converge to the ground state `|0⟩`, while the expected
number `⟨eʲ|N|eʲ⟩` equals `1` for every `j ≥ 1`.

Formalized here:
* `norm_sub_ground_sq`  eq. (2): `‖eʲ - |0⟩‖² = (√((j-1)/j) - 1)² + 1/j`;
* `tendsto_e`           `eʲ → |0⟩` in `ℓ²`;
* `secondMoment_e`, `tendsto_secondMoment_e`  eq. (3): `∑ n² |eʲₙ|² = j → ∞`, so `eʲ` has no
  limit in the Schwartz sequence space `S(ℕ)`;
* `not_cauchySeq_level` the eigenstates `|j⟩` alone have no limit in `ℓ²`;
* `numberExp_e`         eq. (4): `⟨eʲ|N|eʲ⟩ = 1` for `j ≥ 1`;
* `not_continuousAt_numberExp`  eq. (5): `⟨N⟩` is not continuous at `|0⟩` in the `ℓ²` topology.

The brief's Prop. 1 indexes sequences from `1`, with `a` at `i = 1`; here indices start at `0`,
matching the oscillator of Section 3. The divergence in eq. (3) is the same up to this shift.
The expectations are written as weighted sums, since `N` is diagonal in the basis `|n⟩`; they
are only evaluated on finitely supported states.

For the reading as the oscillator, see the module `InconsistentConvergence.Oscillator`: the unitary
`ℓ²(ℕ) ≃ L²(ℝ)` of the Hermite basis sends `|n⟩` to the `n`-th oscillator eigenfunction, and `S(ℕ)`
onto the Schwartz space `𝓢(ℝ)`, with its topology. There `eʲ` has no limit in `𝓢(ℝ)`.

For the operators, see the module `InconsistentConvergence.NumberOperator`: the number operator
`N = a† a` is self-adjoint on its maximal domain, and `⟨x|N|x⟩ = numberExp x` there.
-/
public import Mathlib.Analysis.Normed.Lp.lpSpace

open Filter Topology

@[expose] public noncomputable section

namespace InconsistentConvergence

/-- The oscillator state space `ℓ²(ℕ)`. -/
abbrev H := lp (fun _ : ℕ => ℂ) 2

/-- The energy eigenstate `|j⟩`. -/
def level (j : ℕ) : H := lp.single 2 j 1

/-- The ground state `|0⟩`. -/
abbrev ground : H := level 0

/-- The amplitude `√((j-1)/j)` of `|0⟩` in `|eʲ⟩`. -/
def amp₀ (j : ℕ) : ℝ := √(((j : ℝ) - 1) / j)

/-- The amplitude `√(1/j)` of `|j⟩` in `|eʲ⟩`. -/
def ampⱼ (j : ℕ) : ℝ := √(1 / (j : ℝ))

/-- The states `|eʲ⟩ = √((j-1)/j) |0⟩ + √(1/j) |j⟩`. -/
def e (j : ℕ) : H := (amp₀ j : ℂ) • ground + (ampⱼ j : ℂ) • level j

/-- `⟨x|N|x⟩ = ∑ n |xₙ|²`. -/
def numberExp (x : H) : ℝ := ∑' n : ℕ, (n : ℝ) * ‖x n‖ ^ 2

/-- `‖N x‖² = ∑ n² |xₙ|²`, the square of a Schwartz seminorm on sequences. -/
def secondMoment (x : H) : ℝ := ∑' n : ℕ, (n : ℝ) ^ 2 * ‖x n‖ ^ 2

lemma norm_sq_eq_tsum (x : H) : ‖x‖ ^ 2 = ∑' n, ‖x n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  simpa [Real.rpow_two] using this

lemma tsum_pair {a b : ℕ} (hab : a ≠ b) (g : ℕ → ℝ) (hg : ∀ n, n ≠ a → n ≠ b → g n = 0) :
    ∑' n, g n = g a + g b := by
  rw [tsum_eq_sum (s := {a, b}) (fun n hn => by simp at hn; exact hg n hn.1 hn.2),
    Finset.sum_pair hab]

lemma level_apply (j n : ℕ) : level j n = if n = j then 1 else 0 := by
  simp [level, lp.single_apply, Pi.single_apply]

lemma e_apply (j n : ℕ) :
    e j n = (amp₀ j : ℂ) * (if n = 0 then 1 else 0) + (ampⱼ j : ℂ) * (if n = j then 1 else 0) := by
  simp only [e, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    level_apply]

lemma e_apply_zero {j : ℕ} (hj : j ≠ 0) : e j 0 = amp₀ j := by simp [e_apply, Ne.symm hj]

lemma e_apply_self {j : ℕ} (hj : j ≠ 0) : e j j = ampⱼ j := by simp [e_apply, hj]

lemma e_apply_of_ne {j n : ℕ} (h0 : n ≠ 0) (hj : n ≠ j) : e j n = 0 := by
  simp [e_apply, h0, hj]

lemma ampⱼ_sq (j : ℕ) : ampⱼ j ^ 2 = 1 / j := Real.sq_sqrt (by positivity)

/-- Eq. (2). -/
theorem norm_sub_ground_sq {j : ℕ} (hj : 1 ≤ j) :
    ‖e j - ground‖ ^ 2 = (amp₀ j - 1) ^ 2 + 1 / j := by
  have hj0 : j ≠ 0 := by omega
  rw [norm_sq_eq_tsum, tsum_pair (Ne.symm hj0)]
  · have h1 : (e j - ground) 0 = ((amp₀ j - 1 : ℝ) : ℂ) := by
      simp [e_apply_zero hj0, level_apply]
    have h2 : (e j - ground) j = (ampⱼ j : ℂ) := by
      simp [e_apply_self hj0, level_apply, hj0]
    rw [h1, h2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      sq_abs, sq_abs, ampⱼ_sq]
  · intro n h0 hn
    simp [e_apply_of_ne h0 hn, level_apply, h0]

lemma tendsto_sub_div : Tendsto (fun j : ℕ => ((j : ℝ) - 1) / j) atTop (𝓝 1) := by
  have h : Tendsto (fun j : ℕ => (1 : ℝ) - 1 / (j : ℝ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  have : (j : ℝ) ≠ 0 := by positivity
  field_simp

/-- `eʲ → |0⟩` in `ℓ²`. -/
theorem tendsto_e : Tendsto e atTop (𝓝 ground) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Tendsto amp₀ atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp tendsto_sub_div
    rwa [Real.sqrt_one] at this
  have hsq : Tendsto (fun j => (amp₀ j - 1) ^ 2 + 1 / (j : ℝ)) atTop (𝓝 ((1 - 1) ^ 2 + 0)) :=
    ((hc.sub_const 1).pow 2).add tendsto_one_div_atTop_nhds_zero_nat
  have hlim := (Real.continuous_sqrt.tendsto _).comp hsq
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  rw [Function.comp_apply, ← norm_sub_ground_sq hj, Real.sqrt_sq (norm_nonneg _)]

/-- Eq. (3): `∑ n² |eʲₙ|² = j`. -/
theorem secondMoment_e {j : ℕ} (hj : 1 ≤ j) : secondMoment (e j) = j := by
  have hj0 : j ≠ 0 := by omega
  rw [secondMoment, tsum_pair (Ne.symm hj0)]
  · rw [e_apply_self hj0, Complex.norm_real, Real.norm_eq_abs, sq_abs, ampⱼ_sq]
    have : (j : ℝ) ≠ 0 := by positivity
    field_simp
    simp
  · intro n h0 hn
    simp [e_apply_of_ne h0 hn]

/-- The Schwartz seminorm `∑ n² |eʲₙ|²` diverges, so `eʲ` does not converge in `S(ℕ)`. -/
theorem tendsto_secondMoment_e : Tendsto (fun j => secondMoment (e j)) atTop atTop := by
  refine tendsto_natCast_atTop_atTop.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  exact (secondMoment_e hj).symm

/-- The eigenstates `|j⟩` alone have no limit in `ℓ²`: `‖|j⟩ - |k⟩‖² = 2` for `j ≠ k`. -/
theorem not_cauchySeq_level : ¬ CauchySeq level := by
  have hdist : ∀ j k, j ≠ k → dist (level j) (level k) ^ 2 = 2 := by
    intro j k hjk
    rw [dist_eq_norm, norm_sq_eq_tsum, tsum_pair hjk]
    · simp [level_apply, hjk, Ne.symm hjk]
      norm_num
    · intro n hj hk
      simp [level_apply, hj, hk]
  intro h
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp h 1 one_pos
  have h1 := hN (N + 1) (by omega)
  have h2 := hdist (N + 1) N (by omega)
  nlinarith [dist_nonneg (x := level (N + 1)) (y := level N)]

/-- Eq. (4): `⟨eʲ|N|eʲ⟩ = 1` for `j ≥ 1`. -/
theorem numberExp_e {j : ℕ} (hj : 1 ≤ j) : numberExp (e j) = 1 := by
  have hj0 : j ≠ 0 := by omega
  rw [numberExp, tsum_pair (Ne.symm hj0)]
  · rw [e_apply_self hj0, Complex.norm_real, Real.norm_eq_abs, sq_abs, ampⱼ_sq]
    have : (j : ℝ) ≠ 0 := by positivity
    field_simp
    simp
  · intro n h0 hn
    simp [e_apply_of_ne h0 hn]

lemma numberExp_ground : numberExp ground = 0 := by
  rw [numberExp, tsum_pair (a := 0) (b := 1) (by omega)]
  · simp [level_apply]
  · intro n h0 _
    simp [level_apply, h0]

/-- Eq. (5): the state converges to the ground state, but the expected number stays at `1`.
So `⟨N⟩` is not continuous at `|0⟩` for the `ℓ²` topology, even along finitely supported
states. -/
theorem not_continuousAt_numberExp : ¬ ContinuousAt numberExp ground := by
  intro h
  have h0 : Tendsto (numberExp ∘ e) atTop (𝓝 0) := by
    simpa only [numberExp_ground] using h.tendsto.comp tendsto_e
  have h1 : Tendsto (numberExp ∘ e) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    exact (numberExp_e hj).symm
  exact zero_ne_one (tendsto_nhds_unique h0 h1)

end InconsistentConvergence
