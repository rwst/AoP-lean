/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.GlueBumps
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth multipliers of Schwartz space have temperate growth

Let `E` be finite-dimensional and `F ≠ 0`. If `g : E → ℝ` is smooth and `g • f` is a Schwartz
function for every `f ∈ 𝓢(E, F)`, then `g` has temperate growth. Together with
`SchwartzMap.smulLeftCLM`, this says that the smooth multipliers of `𝓢` are exactly the functions
of temperate growth, the space `𝒪_M` of L. Schwartz.

The proof: if the `n`-th derivative of `g` is not polynomially bounded, there are points `x j`
with `‖Dⁿg(x j)‖ > j (1 + ‖x j‖)^j`. They run to infinity, since `Dⁿg` is bounded on compact
sets. Glue bumps of height `(1 + ‖x j‖)^{-j}` at a separated subsequence
(`SchwartzMap.exists_eqOn_ball_smul`); then `Dⁿ(g • f)` is unbounded along it, which a Schwartz
function cannot be.

## Main results

* `SchwartzMap.hasTemperateGrowth_of_forall_smul_mem`: a smooth multiplier of `𝓢` has temperate
  growth.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology ContDiff

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

variable [FiniteDimensional ℝ E]

/-- A bump in `𝓢(E, F)` that equals `a` on the ball of radius `1/8` and vanishes outside the
closed ball of radius `1/4`. -/
private lemma exists_bump (a : F) :
    ∃ ρ : 𝓢(E, F), tsupport ρ ⊆ closedBall 0 (1 / 4) ∧ ∀ z ∈ ball (0 : E) (1 / 8), ρ z = a := by
  let χ : ContDiffBump (0 : E) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  have hsupp : tsupport (fun z => χ z • a) ⊆ closedBall 0 (1 / 4) :=
    (tsupport_smul_subset_left _ _).trans χ.tsupport_eq.subset
  refine ⟨(χ.hasCompactSupport.smul_right (f' := fun _ => a)).toSchwartzMap
    (χ.contDiff.smul contDiff_const), hsupp, fun z hz => ?_⟩
  simp [χ.one_of_mem_closedBall (ball_subset_closedBall hz)]

variable [Nontrivial F]

/-- **Smooth multipliers of `𝓢` have temperate growth.** If `g : E → ℝ` is smooth and `g • f` is
a Schwartz function for every `f ∈ 𝓢(E, F)`, then `g` has temperate growth. -/
theorem hasTemperateGrowth_of_forall_smul_mem {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (h : ∀ f : 𝓢(E, F), ∃ G : 𝓢(E, F), ∀ x, G x = g x • f x) : g.HasTemperateGrowth := by
  refine ⟨hg, fun n => ?_⟩
  by_contra hcon
  push Not at hcon
  choose x hx using fun j : ℕ => hcon j j
  -- The points `x j` run to infinity.
  have htend : Tendsto (fun j => ‖x j‖) atTop atTop := by
    refine tendsto_atTop.2 fun R => ?_
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn
      (hg.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
    obtain ⟨j₀, hj₀⟩ := exists_nat_gt M
    filter_upwards [eventually_ge_atTop j₀] with j hj
    by_contra hlt
    push Not at hlt
    have h1 := hM (x j) (mem_closedBall_zero_iff.2 hlt.le)
    have h2 : (j : ℝ) ≤ j * (1 + ‖x j‖) ^ j :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by simp))
    have h3 : (j₀ : ℝ) ≤ j := mod_cast hj
    linarith [hx j]
  obtain ⟨σ, hσ, hsep⟩ := exists_strictMono_pairwise_one_le htend
  set y := fun j => x (σ j)
  set c : ℕ → ℝ := fun j => ((1 + ‖y j‖) ^ j)⁻¹
  -- The glued test function and its product with `g`.
  obtain ⟨a, ha⟩ := exists_norm_eq F zero_le_one
  obtain ⟨ρ, hρ, hρa⟩ := exists_bump (E := E) a
  obtain ⟨f, hf⟩ := exists_eqOn_ball_smul (c := c) (by norm_num : (1 / 4 : ℝ) < 1 / 2) hρ hsep
    (exists_abs_inv_pow_mul_le y)
  obtain ⟨G, hG⟩ := h f
  obtain ⟨C, -, hC⟩ := G.decay 0 n
  simp only [pow_zero, one_mul] at hC
  obtain ⟨j, hj⟩ := exists_nat_gt C
  let L := LinearIsometry.toSpanSingleton ℝ F ha
  -- Near `y j`, `G = c j • (L ∘ g)`.
  have hloc : (G : E → F) =ᶠ[𝓝 (y j)] c j • (L ∘ g) := by
    refine mem_of_superset (ball_mem_nhds (y j) (by norm_num : (0 : ℝ) < 1 / 8)) fun z hz => ?_
    have hz' : z - y j ∈ ball (0 : E) (1 / 8) := by
      rwa [mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]
    have hz'' : z ∈ ball (y j) (1 / 2) := ball_subset_ball (by norm_num) hz
    change G z = c j • L (g z)
    rw [hG, hf j hz'']
    change g z • (c j • ρ (z - y j)) = _
    rw [hρa _ hz', LinearIsometry.toSpanSingleton_apply, smul_smul, smul_smul, mul_comm]
  have hnorm : ‖iteratedFDeriv ℝ n G (y j)‖ = c j * ‖iteratedFDeriv ℝ n g (y j)‖ := by
    have hLg : ContDiffAt ℝ n (L ∘ g) (y j) :=
      (L.contDiff.comp (hg.of_le (mod_cast le_top))).contDiffAt
    rw [(hloc.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_const_smul_apply hLg, norm_smul,
      L.norm_iteratedFDeriv_comp_left (hg.of_le (mod_cast le_top)).contDiffAt le_rfl,
      Real.norm_of_nonneg (by positivity)]
  -- But `c j • ‖Dⁿg(y j)‖ > j`.
  have hbig : (j : ℝ) < c j * ‖iteratedFDeriv ℝ n g (y j)‖ := by
    have h1 : 1 ≤ 1 + ‖y j‖ := le_add_of_nonneg_right (norm_nonneg _)
    have hpos : 0 < (1 + ‖y j‖) ^ j := by positivity
    have hσj : (j : ℝ) ≤ σ j := mod_cast hσ.id_le j
    have : (j : ℝ) * (1 + ‖y j‖) ^ j ≤ σ j * (1 + ‖y j‖) ^ σ j :=
      mul_le_mul hσj (pow_le_pow_right₀ h1 (hσ.id_le j)) hpos.le (by positivity)
    change (j : ℝ) < ((1 + ‖y j‖) ^ j)⁻¹ * _
    rw [lt_inv_mul_iff₀ hpos, mul_comm]
    exact this.trans_lt (hx (σ j))
  linarith [hC (y j)]

end SchwartzMap
