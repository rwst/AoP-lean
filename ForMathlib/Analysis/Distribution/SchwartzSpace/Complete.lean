/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Completeness of the Schwartz space

For a complete space `F`, the Schwartz space `𝓢(E, F)` is complete. Together with its countable
family of seminorms, this makes it a Fréchet space.

The proof is the classical one; see J. Becnel and A. Sengupta, *The Schwartz space: tools for
quantum mechanics and infinite dimensional analysis*, Mathematics 3 (2015), §3.5. The uniformity
of `𝓢(E, F)` is countably generated, so it is enough that Cauchy sequences converge. For a Cauchy
sequence `u`, each `iteratedFDeriv ℝ n (u m)` converges uniformly, even with the weight `‖x‖ ^ k`,
to some `G n`. By the theorem on uniform limits of derivatives, the `G n` are the iterated
derivatives of `G 0`, so `G 0` is smooth. The weighted bounds pass to the limit, so `G 0` is a
Schwartz function, and `u` converges to it in every seminorm.

## Main results

* `SchwartzMap.exists_seminorm_sub_lt_of_cauchySeq`: along a Cauchy sequence, every Schwartz
  seminorm of the differences becomes small;
* `SchwartzMap.instCompleteSpace`: `𝓢(E, F)` is complete.
-/

open Filter Topology
open scoped ContDiff

public section

namespace SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Along a Cauchy sequence of Schwartz functions, every seminorm of the differences becomes
small. -/
theorem exists_seminorm_sub_lt_of_cauchySeq {u : ℕ → 𝓢(E, F)} (hu : CauchySeq u) (k n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ m ≥ N, ∀ m' ≥ N, SchwartzMap.seminorm ℝ k n (u m - u m') < ε := by
  have h := cauchySeq_iff_tendsto.mp hu
  rw [uniformity_eq_comap_nhds_zero, tendsto_comap_iff] at h
  have hc : Continuous (SchwartzMap.seminorm ℝ k n : 𝓢(E, F) → ℝ) :=
    (schwartz_withSeminorms ℝ E F).continuous_seminorm (k, n)
  have h2 := (hc.tendsto' 0 0 (map_zero _)).comp h
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.mp (h2.eventually (eventually_lt_nhds hε))
  exact ⟨N, fun m hm m' hm' => by simpa [Function.comp_def] using hN m' hm' m hm⟩

variable [CompleteSpace F]

/-- The Schwartz space is complete. -/
instance instCompleteSpace : CompleteSpace 𝓢(E, F) := by
  have := IsUniformAddGroup.uniformity_countably_generated (α := 𝓢(E, F))
  refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
  -- The weighted derivatives of `u` are uniformly Cauchy.
  have hC : ∀ k n ε, 0 < ε → ∃ N, ∀ m ≥ N, ∀ m' ≥ N, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u m) x - iteratedFDeriv ℝ n (u m') x‖ ≤ ε := by
    intro k n ε hε
    obtain ⟨N, hN⟩ := exists_seminorm_sub_lt_of_cauchySeq hu k n hε
    refine ⟨N, fun m hm m' hm' x => ?_⟩
    have h := le_seminorm ℝ k n (u m - u m') x
    rw [show ⇑(u m - u m') = ⇑(u m) - ⇑(u m') from rfl,
      iteratedFDeriv_sub_apply ((u m).smooth n).contDiffAt ((u m').smooth n).contDiffAt] at h
    exact h.trans (hN m hm m' hm').le
  -- So they converge pointwise, to `G n`.
  have hpt : ∀ n x, CauchySeq fun m => iteratedFDeriv ℝ n (u m) x := by
    intro n x
    refine Metric.cauchySeq_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hC 0 n (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm m' hm' => ?_⟩
    have h := hN m hm m' hm' x
    rw [pow_zero, one_mul] at h
    rw [dist_eq_norm]
    linarith
  choose G hG using fun n x => cauchySeq_tendsto_of_complete (hpt n x)
  -- The convergence is uniform, with every weight `‖x‖ ^ k`.
  have hL : ∀ k n ε, 0 < ε → ∃ N, ∀ m ≥ N, ∀ x,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u m) x - G n x‖ ≤ ε := by
    intro k n ε hε
    obtain ⟨N, hN⟩ := hC k n ε hε
    refine ⟨N, fun m hm x => ?_⟩
    have ht : Tendsto (fun m' => ‖x‖ ^ k *
        ‖iteratedFDeriv ℝ n (u m) x - iteratedFDeriv ℝ n (u m') x‖) atTop
        (𝓝 (‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u m) x - G n x‖)) :=
      ((tendsto_const_nhds.sub (hG n x)).norm).const_mul _
    exact le_of_tendsto ht (eventually_atTop.2 ⟨N, fun m' hm' => hN m hm m' hm' x⟩)
  have hU : ∀ n, TendstoUniformly (fun m => iteratedFDeriv ℝ n (u m)) (G n) atTop := by
    intro n
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    obtain ⟨N, hN⟩ := hL 0 n (ε / 2) (half_pos hε)
    refine eventually_atTop.2 ⟨N, fun m hm x => ?_⟩
    have h := hN m hm x
    rw [pow_zero, one_mul] at h
    rw [dist_comm, dist_eq_norm]
    linarith
  -- Each `G (n + 1)` is the derivative of `G n`.
  have hD : ∀ n x, HasFDerivAt (G n) (G (n + 1) x).curryLeft x := by
    intro n
    have hU' := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E)
      F).isometry.uniformContinuous.comp_tendstoUniformly (hU (n + 1))
    refine hasFDerivAt_of_tendstoUniformly hU' (fun m x => ?_) (fun x => hG n x)
    exact (contDiff_iff_ftaylorSeries.mp ((u m).smooth ⊤)).fderiv n
      (by exact_mod_cast ENat.natCast_lt_top n) x
  -- So `G` is the Taylor series of a smooth function `g`.
  have hT : HasFTaylorSeriesUpTo ∞ (fun x => (G 0 x).curry0) fun x n => G n x :=
    { zero_eq := fun _ => rfl
      fderiv := fun n _ x => hD n x
      cont := fun n _ => continuous_iff_continuousAt.2 fun x => (hD n x).continuousAt }
  have hiter : ∀ n x, iteratedFDeriv ℝ n (fun x => (G 0 x).curry0) x = G n x := fun n x =>
    (hT.eq_iteratedFDeriv (by exact_mod_cast le_top) x).symm
  let g : 𝓢(E, F) :=
    { toFun := fun x => (G 0 x).curry0
      smooth' := hT.contDiff
      decay' := fun k n => by
        obtain ⟨N, hN⟩ := hL k n 1 one_pos
        refine ⟨SchwartzMap.seminorm ℝ k n (u N) + 1, fun x => ?_⟩
        rw [hiter]
        have h : ‖G n x‖ ≤ ‖iteratedFDeriv ℝ n (u N) x‖ +
            ‖iteratedFDeriv ℝ n (u N) x - G n x‖ := by
          simpa using norm_sub_le (iteratedFDeriv ℝ n (u N) x)
            (iteratedFDeriv ℝ n (u N) x - G n x)
        calc ‖x‖ ^ k * ‖G n x‖
            ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u N) x‖ +
                ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (u N) x - G n x‖ := by
              rw [← mul_add]
              gcongr
          _ ≤ SchwartzMap.seminorm ℝ k n (u N) + 1 :=
            add_le_add (le_seminorm ℝ k n (u N) x) (hN N le_rfl x) }
  -- And `u` converges to `g` in every seminorm.
  refine ⟨g, ((schwartz_withSeminorms ℝ E F).tendsto_nhds u g).2 fun i ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hL i.1 i.2 (ε / 2) (half_pos hε)
  refine eventually_atTop.2 ⟨N, fun m hm => ?_⟩
  refine lt_of_le_of_lt (seminorm_le_bound ℝ i.1 i.2 _ (half_pos hε).le fun x => ?_)
    (half_lt_self hε)
  rw [show ⇑(u m - g) = ⇑(u m) - ⇑g from rfl,
    iteratedFDeriv_sub_apply ((u m).smooth i.2).contDiffAt (g.smooth i.2).contDiffAt]
  exact (hiter i.2 x).symm ▸ hN m hm x

end SchwartzMap
