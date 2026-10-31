/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuous local 2-cocycles on `ℝ` are coboundaries

Let `θ : ℝ → ℝ → ℝ` be continuous and satisfy the cocycle identity
`θ a b + θ (a + b) c = θ a (b + c) + θ b c` for `a, b, c ∈ [α, ε]`, where `α ≤ 0 < ε`. Then there
is a continuous `f : ℝ → ℝ` with `θ a b = f a + f b - f (a + b)` for `a, b ∈ [α, ε]`. The
interval may be one-sided (`α = 0`), as for a projective representation known only for `t ≥ 0`.

The proof integrates the cocycle identity over `c ∈ [0, ε]` and, once more, over the cocycle
identity at `(a, u, ε)` for `u` between `0` and `b`. With `Φ x = ∫_0^ε θ x c dc` and
`K x = ∫_0^x θ u ε du` this gives
`ε θ a b = Φ a + Φ b - Φ (a + b) + K (a + b) - K a - K b`,
so `f = (Φ - K) / ε` works. This is Bargmann's argument for the group `ℝ`, with the mollifier
replaced by the indicator of `[0, ε]`; no derivative is taken.

The result is the real-analysis step in lifting a continuous projective representation of `ℝ`
to a unitary one. A continuous local section `U` has `U a * U b = ω a b • U (a + b)` with `ω` near
`1`, so `arg ω` is a continuous local 2-cocycle, and `exp (i f a) • U a` is a local homomorphism.

## Main results

* `Real.mul_eq_of_isLocalCocycle`: the integrated identity.
* `Real.exists_eq_of_continuous_localCocycle`: the coboundary, for `θ` continuous on `ℝ²`.
* `Real.exists_eq_of_continuousOn_localCocycle`: the same for `θ` continuous on `[2α, 2ε]²`.
* `Real.exists_eq_exp_of_localCocycle`: a multiplicative 2-cocycle `ω` with values of modulus `1`
  and positive real part is `ω a b = exp (i (f a + f b - f (a + b)))`.

## References

* V. Bargmann, *On unitary ray representations of continuous groups*, Ann. of Math. 59 (1954),
  1–46, §4.
* B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton (1976), §7–8.
-/

@[expose] public section

open Set intervalIntegral

namespace Real

variable {θ : ℝ → ℝ → ℝ} {α ε : ℝ}

/-- **The integrated cocycle identity.** If `θ` is continuous and a 2-cocycle on `[α, ε]`, then
`ε θ a b = Φ a + Φ b - Φ (a + b) + K (a + b) - K a - K b` for `a, b ∈ [α, ε]`, where
`Φ x = ∫_0^ε θ x c dc` and `K x = ∫_0^x θ u ε du`. -/
theorem mul_eq_of_isLocalCocycle (hα : α ≤ 0) (hε : 0 < ε)
    (hθ : Continuous (Function.uncurry θ))
    (hco : ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε, ∀ c ∈ Icc α ε,
      θ a b + θ (a + b) c = θ a (b + c) + θ b c)
    {a b : ℝ} (ha : a ∈ Icc α ε) (hb : b ∈ Icc α ε) :
    ε * θ a b = (∫ c in 0..ε, θ a c) + (∫ c in 0..ε, θ b c) - (∫ c in 0..ε, θ (a + b) c) +
      (∫ u in 0..a + b, θ u ε) - (∫ u in 0..a, θ u ε) - (∫ u in 0..b, θ u ε) := by
  have hr : ∀ x, Continuous (θ x) := fun x => hθ.uncurry_left x
  have hl : Continuous fun x => θ x ε := hθ.uncurry_right ε
  have hεm : ε ∈ Icc α ε := ⟨by linarith, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Icc α ε := ⟨by linarith, hε.le⟩
  -- Integrate the cocycle identity at `(a, b, c)` over `c ∈ [0, ε]`.
  have h1 : ∫ c in 0..ε, (θ a b + θ (a + b) c) = ∫ c in 0..ε, (θ a (b + c) + θ b c) := by
    refine integral_congr fun c hc => hco a ha b hb c ?_
    rw [uIcc_of_le hε.le] at hc
    exact ⟨by linarith [hc.1], hc.2⟩
  have hbc : Continuous fun c => θ a (b + c) := (hr a).comp (continuous_const.add continuous_id)
  rw [integral_add intervalIntegrable_const ((hr _).intervalIntegrable _ _),
    integral_add (hbc.intervalIntegrable _ _) ((hr _).intervalIntegrable _ _),
    integral_const, smul_eq_mul, sub_zero] at h1
  -- Shift the window `[b, b + ε]` back to `[0, ε]`.
  have h2 : ∫ c in 0..ε, θ a (b + c) = ∫ u in b..b + ε, θ a u := by
    rw [integral_comp_add_left (θ a) b, add_zero]
  have h3 : (∫ u in 0..b, θ a u) + ∫ u in b..b + ε, θ a u =
      (∫ u in 0..ε, θ a u) + ∫ u in ε..b + ε, θ a u := by
    rw [integral_add_adjacent_intervals ((hr a).intervalIntegrable _ _)
        ((hr a).intervalIntegrable _ _),
      integral_add_adjacent_intervals ((hr a).intervalIntegrable _ _)
        ((hr a).intervalIntegrable _ _)]
  have h4 : ∫ u in ε..b + ε, θ a u = ∫ u in 0..b, θ a (u + ε) := by
    rw [integral_comp_add_right (θ a) ε, zero_add]
  -- The cocycle identity at `(a, u, ε)` turns the difference of windows into increments of `K`.
  have hue : Continuous fun u => θ a (u + ε) := (hr a).comp (continuous_id.add continuous_const)
  have hau : Continuous fun u => θ (a + u) ε := hl.comp (continuous_const.add continuous_id)
  have h5 : (∫ u in 0..b, θ a (u + ε)) - ∫ u in 0..b, θ a u =
      (∫ u in 0..b, θ (a + u) ε) - ∫ u in 0..b, θ u ε := by
    rw [← integral_sub (hue.intervalIntegrable _ _) ((hr a).intervalIntegrable _ _),
      ← integral_sub (hau.intervalIntegrable _ _) (hl.intervalIntegrable _ _)]
    refine integral_congr fun u hu => ?_
    have := hco a ha u (uIcc_subset_Icc h0 hb hu) ε hεm
    linarith
  have h6 : ∫ u in 0..b, θ (a + u) ε = (∫ u in 0..a + b, θ u ε) - ∫ u in 0..a, θ u ε := by
    rw [integral_comp_add_left (fun x => θ x ε) a, add_zero,
      integral_interval_sub_left (hl.intervalIntegrable _ _) (hl.intervalIntegrable _ _)]
  linarith

/-- **Continuous local 2-cocycles on `ℝ` are coboundaries.** If `θ` is continuous and satisfies
the cocycle identity on `[α, ε]`, then `θ a b = f a + f b - f (a + b)` on `[α, ε]` for a
continuous `f`. -/
theorem exists_eq_of_continuous_localCocycle (hα : α ≤ 0) (hε : 0 < ε)
    (hθ : Continuous (Function.uncurry θ))
    (hco : ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε, ∀ c ∈ Icc α ε,
      θ a b + θ (a + b) c = θ a (b + c) + θ b c) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε, θ a b = f a + f b - f (a + b) := by
  refine ⟨fun x => ((∫ c in 0..ε, θ x c) - ∫ u in 0..x, θ u ε) / ε, ?_, fun a ha b hb => ?_⟩
  · have hΦ := continuous_parametric_intervalIntegral_of_continuous' (μ := MeasureTheory.volume)
      hθ 0 ε
    have hK := continuous_primitive (μ := MeasureTheory.volume)
      (fun s t => (hθ.uncurry_right ε).intervalIntegrable s t) 0
    exact (hΦ.sub hK).div_const ε
  · have := mul_eq_of_isLocalCocycle hα hε hθ hco ha hb
    rw [← add_div, ← sub_div, eq_div_iff hε.ne']
    linarith

/-- **Continuous local 2-cocycles on `ℝ` are coboundaries**, for `θ` continuous only on the
square `[2α, 2ε]²` that the cocycle identity on `[α, ε]` involves. -/
theorem exists_eq_of_continuousOn_localCocycle (hα : α ≤ 0) (hε : 0 < ε)
    (hθ : ContinuousOn (Function.uncurry θ) (Icc (2 * α) (2 * ε) ×ˢ Icc (2 * α) (2 * ε)))
    (hco : ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε, ∀ c ∈ Icc α ε,
      θ a b + θ (a + b) c = θ a (b + c) + θ b c) :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε, θ a b = f a + f b - f (a + b) := by
  -- Precompose `θ` with the retraction onto `[-2ε, 2ε]` to make it continuous everywhere.
  have h2ε : 2 * α ≤ 2 * ε := by linarith
  set p : ℝ → ℝ := fun x => (projIcc (2 * α) (2 * ε) h2ε x : ℝ) with hp_def
  have hp : Continuous p := continuous_subtype_val.comp continuous_projIcc
  have hpI : ∀ x, p x ∈ Icc (2 * α) (2 * ε) := fun x => (projIcc _ _ h2ε x).2
  have hpx : ∀ x ∈ Icc (2 * α) (2 * ε), p x = x := fun x hx => by
    simp [hp_def, projIcc_of_mem h2ε hx]
  have hin : ∀ x ∈ Icc α ε, x ∈ Icc (2 * α) (2 * ε) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hin2 : ∀ x ∈ Icc α ε, ∀ y ∈ Icc α ε, x + y ∈ Icc (2 * α) (2 * ε) :=
    fun x hx y hy => ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hθ' : Continuous (Function.uncurry fun x y => θ (p x) (p y)) :=
    hθ.comp_continuous (hp.prodMap hp) fun q => ⟨hpI q.1, hpI q.2⟩
  obtain ⟨f, hf, hfθ⟩ := exists_eq_of_continuous_localCocycle hα hε hθ' fun a ha b hb c hc => by
    simp only [hpx a (hin a ha), hpx b (hin b hb), hpx c (hin c hc), hpx _ (hin2 a ha b hb),
      hpx _ (hin2 b hb c hc)]
    exact hco a ha b hb c hc
  refine ⟨f, hf, fun a ha b hb => ?_⟩
  rw [← hfθ a ha b hb, hpx a (hin a ha), hpx b (hin b hb)]

/-- **Continuous local multipliers on `ℝ` are coboundaries.** If `ω` is continuous with positive
real part on `[2α, 2ε]²`, satisfies the multiplicative cocycle identity on `[α, ε]` and has
modulus `1` there, then `ω a b = exp (i (f a + f b - f (a + b)))` on `[α, ε]` for a continuous
`f`. -/
theorem exists_eq_exp_of_localCocycle (hα : α ≤ 0) (hε : 0 < ε) {ω : ℝ → ℝ → ℂ}
    (hω : ContinuousOn (Function.uncurry ω) (Icc (2 * α) (2 * ε) ×ˢ Icc (2 * α) (2 * ε)))
    (hre : ∀ a ∈ Icc (2 * α) (2 * ε), ∀ b ∈ Icc (2 * α) (2 * ε), 0 < (ω a b).re)
    (hco : ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε, ∀ c ∈ Icc α ε,
      ω a b * ω (a + b) c = ω a (b + c) * ω b c)
    (hnorm : ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε, ‖ω a b‖ = 1) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ∀ a ∈ Icc α ε, ∀ b ∈ Icc α ε,
      ω a b = Complex.exp ((f a + f b - f (a + b) : ℝ) * Complex.I) := by
  have hin : ∀ x ∈ Icc α ε, x ∈ Icc (2 * α) (2 * ε) := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hin2 : ∀ x ∈ Icc α ε, ∀ y ∈ Icc α ε, x + y ∈ Icc (2 * α) (2 * ε) :=
    fun x hx y hy => ⟨by linarith [hx.1, hy.1], by linarith [hx.2, hy.2]⟩
  have hne : ∀ a ∈ Icc (2 * α) (2 * ε), ∀ b ∈ Icc (2 * α) (2 * ε), ω a b ≠ 0 :=
    fun a ha b hb h => by simpa [h] using hre a ha b hb
  have harg : ∀ a ∈ Icc (2 * α) (2 * ε), ∀ b ∈ Icc (2 * α) (2 * ε),
      |Complex.arg (ω a b)| < π / 2 :=
    fun a ha b hb => Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hre a ha b hb))
  -- The argument of a product of two numbers in the right half-plane is the sum of arguments.
  have hmul : ∀ a ∈ Icc (2 * α) (2 * ε), ∀ b ∈ Icc (2 * α) (2 * ε),
      ∀ c ∈ Icc (2 * α) (2 * ε), ∀ d ∈ Icc (2 * α) (2 * ε),
      Complex.arg (ω a b * ω c d) = Complex.arg (ω a b) + Complex.arg (ω c d) :=
    fun a ha b hb c hc d hd => by
      have h1 := abs_lt.mp (harg a ha b hb)
      have h2 := abs_lt.mp (harg c hc d hd)
      exact Complex.arg_mul (hne a ha b hb) (hne c hc d hd)
        ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  obtain ⟨f, hf, hfθ⟩ := exists_eq_of_continuousOn_localCocycle (θ := fun a b => (ω a b).arg) hα hε
    (fun q hq => (Complex.continuousAt_arg (Or.inl (hre _ hq.1 _ hq.2))).comp_continuousWithinAt
      (f := Function.uncurry ω) (hω q hq))
    fun a ha b hb c hc => by
      have h := congrArg Complex.arg (hco a ha b hb c hc)
      rwa [hmul _ (hin a ha) _ (hin b hb) _ (hin2 a ha b hb) _ (hin c hc),
        hmul _ (hin a ha) _ (hin2 b hb c hc) _ (hin b hb) _ (hin c hc)] at h
  refine ⟨f, hf, fun a ha b hb => ?_⟩
  rw [← hfθ a ha b hb]
  simpa [hnorm a ha b hb] using (Complex.norm_mul_exp_arg_mul_I (ω a b)).symm

end Real
