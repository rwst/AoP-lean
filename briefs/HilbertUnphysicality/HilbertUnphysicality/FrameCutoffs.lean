/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import HilbertUnphysicality
import ForMathlib.Analysis.Fourier.Chirp
import ForMathlib.Analysis.Fourier.LpSpace
import ForMathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.Fourier.Continuous

/-!
# Unphysicality of Hilbert spaces: no state has finite position variance in every frame

[B]WDQ asks that a quantity well-defined in one frame be well-defined in every other. For the
position of one degree of freedom, and every smooth change of frame `y = e(x)`, this module
shows what the condition demands of a state `ψ ∈ L²(ℝ)`, and that quantum mechanics does not
allow it.

1. `ψ` lies in the domain of the position operator in every smooth frame if and only if it
   vanishes outside a bounded set (`forall_smoothFrameChange_mem_positionDomain_iff`). In the frame
   `y = e(x)`, the position variance of `ψ` is `∫ e(x)² |ψ(x)|² dx`. If `ψ` is not cut off, a
   smooth `e` growing fast enough on the shells `k + 1 ≤ |x| < k + 2` where `ψ` has mass makes
   this infinite (`Real.exists_contDiff_homeomorph_le_abs`, in `ForMathlib`). If it is cut off,
   `e` is bounded where `ψ` lives.
2. The free evolution destroys the cutoff at once: if `ψ ≠ 0` is cut off, `e^{-itH₀} ψ` is not,
   for every `t ≠ 0` (`freeEvolution_not_cutoff`). In momentum space the evolution multiplies by
   the chirp `e^{-2iπ²ξ²t}`, and by the Paley–Wiener and Phragmén–Lindelöf theorems that chirp
   cannot map one transform of a cut-off function to another
   (`Real.ae_eq_zero_of_fourier_eq_cexp_mul`, in `ForMathlib`).
3. Together: no nonzero state keeps finite position variance in every smooth frame under the
   free evolution (`not_forall_frames_freeEvolution`). With `quantum_no_cutoff`, in the module
   `HilbertUnphysicality.ClassicalCutoffs`, the same demand on position and momentum leaves only
   `ψ = 0`.

So [B]WDQ, read for all smooth frames, has no solution in any space of quantum states. A model
can satisfy it only for a restricted group of changes of frame.

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.

## Main results

* `smoothFrameChange`: the unitary of the change of frame `y = e(x)`, for a smooth
  diffeomorphism `e`;
* `memLp_mul_forall_iff`: `e ψ ∈ L²` for every smooth diffeomorphism `e` iff `ψ` is cut off;
* `forall_smoothFrameChange_mem_positionDomain_iff`: the same, as `U_e ψ ∈ D(Y)` in every frame;
* `freeEvolution_not_cutoff`: the free evolution takes no nonzero cut-off state to a cut-off one;
* `not_forall_frames_freeEvolution`: no nonzero state keeps finite position variance in every
  smooth frame at two different times.

## References

* J.-P. Antoine, Dirac formalism and symmetry problems in quantum mechanics. II. Symmetry
  problems, J. Math. Phys. 10 (1969) 2276–2290, Sec. II: a symmetry group is compatible with the
  space of states when that space is invariant under the group's representation. This module
  shows that the group cannot be all changes of frame.
* G. Carcassi, F. Calderón, C. A. Aidala, The unphysicality of Hilbert spaces,
  arXiv:2308.06669v3, Appendix, Sec. VIII: finite expectations for all functions of position
  force compact support, and by the Paley–Wiener theorem position and momentum cannot both be
  cut off.
* G. B. Folland, A. Sitaram, The uncertainty principle: a mathematical survey, J. Fourier Anal.
  Appl. 3 (1997) 207–238, Theorem 7.2 (Benedicks): a function and its Fourier transform cannot
  both be supported on sets of finite measure.
-/

open MeasureTheory Set Filter
open scoped ContDiff FourierTransform ENNReal

@[expose] public noncomputable section

namespace HilbertUnphysicality

/-! ### Part 1: all smooth frames -/

section Frames

/-- The shell `k + 1 ≤ |x| < k + 2`. -/
def shell (k : ℕ) : Set ℝ := {x | (k : ℝ) + 1 ≤ |x| ∧ |x| < k + 2}

lemma measurableSet_shell (k : ℕ) : MeasurableSet (shell k) :=
  (measurableSet_le measurable_const continuous_abs.measurable).inter
    (measurableSet_lt continuous_abs.measurable measurable_const)

lemma pairwise_disjoint_shell : Pairwise (Function.onFun Disjoint shell) := by
  intro j k hjk
  refine Set.disjoint_left.2 fun x hj hk => ?_
  rcases lt_or_gt_of_ne hjk with h | h
  · have : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast h
    push_cast at this
    linarith [hj.2, hk.1]
  · have : ((k + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast h
    push_cast at this
    linarith [hj.1, hk.2]

lemma mem_shell_floor {x : ℝ} (hx : 1 ≤ |x|) : x ∈ shell (⌊|x|⌋₊ - 1) := by
  have h1 : 1 ≤ ⌊|x|⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hc : ((⌊|x|⌋₊ - 1 : ℕ) : ℝ) = ⌊|x|⌋₊ - 1 := by rw [Nat.cast_sub h1, Nat.cast_one]
  refine ⟨?_, ?_⟩ <;> rw [hc]
  · linarith [Nat.floor_le (abs_nonneg x)]
  · linarith [Nat.lt_floor_add_one |x|]

/-- If `ψ` has no mass on the shells `k ≥ N`, it vanishes outside `[-(N + 1), N + 1]`. -/
lemma cutoff_of_shells {ψ : ℝ → ℂ} {N : ℕ} (h : ∀ k, N ≤ k → ∀ᵐ x, x ∈ shell k → ψ x = 0) :
    ∃ R : ℝ, ∀ᵐ x, R < |x| → ψ x = 0 := by
  refine ⟨N + 1, ?_⟩
  have h' : ∀ᵐ x, ∀ k, N ≤ k → x ∈ shell k → ψ x = 0 := by
    rw [ae_all_iff]
    intro k
    by_cases hk : N ≤ k
    · filter_upwards [h k hk] with x hx _ using hx
    · exact Eventually.of_forall fun x h => absurd h hk
  filter_upwards [h'] with x hx hR
  refine hx _ ?_ (mem_shell_floor (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
  have : (N : ℝ) + 1 ≤ ⌊|x|⌋₊ := by
    have := Nat.floor_le_floor hR.le
    rw [show (N : ℝ) + 1 = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast] at this
    exact_mod_cast this
  have : N + 1 ≤ ⌊|x|⌋₊ := by exact_mod_cast this
  omega

/-- **Part 1, functions.** `e ψ ∈ L²(ℝ)` for every smooth diffeomorphism `e` of `ℝ` if and only if
`ψ` vanishes almost everywhere outside a bounded set. -/
theorem memLp_mul_forall_iff {ψ : ℝ → ℂ} (hψ : MemLp ψ 2) :
    (∀ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e → ContDiff ℝ ∞ e.symm →
      MemLp (fun x => (e x : ℂ) * ψ x) 2) ↔ ∃ R : ℝ, ∀ᵐ x, R < |x| → ψ x = 0 := by
  constructor
  · intro hall
    by_contra hcut
    -- the mass of `ψ` on the shells
    set m : ℕ → ℝ≥0∞ := fun k => ∫⁻ x in shell k, ‖ψ x‖ₑ ^ (2 : ℝ)
    have hfin : ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) < ⊤ := by
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num)
        (by norm_num) hψ.aestronglyMeasurable).1 hψ.eLpNorm_lt_top
      simpa using this
    have hmfin (k : ℕ) : m k ≠ ⊤ :=
      (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hfin).ne
    -- infinitely many shells carry mass
    have hinf : {k | m k ≠ 0}.Infinite := by
      intro hfinite
      obtain ⟨N, hN⟩ := hfinite.bddAbove
      refine hcut (cutoff_of_shells (N := N + 1) fun k hk => ?_)
      have hk0 : m k = 0 := by
        by_contra h
        have := hN h
        omega
      have hmeas : AEMeasurable (fun x => ‖ψ x‖ₑ ^ (2 : ℝ)) (volume.restrict (shell k)) :=
        (hψ.aestronglyMeasurable.enorm.pow_const _).restrict
      rw [lintegral_eq_zero_iff' hmeas] at hk0
      rw [← ae_restrict_iff' (measurableSet_shell k)]
      filter_upwards [hk0] with x hx
      simpa using hx
    -- the frame
    set c : ℕ → ℝ := fun k => √((m k).toReal⁻¹)
    obtain ⟨e, he, he', hec⟩ := Real.exists_contDiff_homeomorph_le_abs c
    have hm := hall e he he'
    have hfin' : ∫⁻ x, ‖(e x : ℂ) * ψ x‖ₑ ^ (2 : ℝ) < ⊤ := by
      have := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (p := 2) (by norm_num)
        (by norm_num) hm.aestronglyMeasurable).1 hm.eLpNorm_lt_top
      simpa using this
    refine hfin'.ne (eq_top_iff.2 ?_)
    have hshell (k : ℕ) : (if m k ≠ 0 then 1 else 0) ≤
        ∫⁻ x in shell k, ‖(e x : ℂ) * ψ x‖ₑ ^ (2 : ℝ) := by
      split_ifs with hk
      · have hle : ∫⁻ x in shell k, ENNReal.ofReal (c k ^ 2) * ‖ψ x‖ₑ ^ (2 : ℝ) ≤
            ∫⁻ x in shell k, ‖(e x : ℂ) * ψ x‖ₑ ^ (2 : ℝ) := by
          refine setLIntegral_mono' (measurableSet_shell k) fun x hx => ?_
          rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          gcongr
          rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
            ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hec k x hx.1) 2
        refine le_trans (le_of_eq ?_) hle
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Real.sq_sqrt (by positivity),
          ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hk (hmfin k)), ENNReal.ofReal_toReal
            (hmfin k)]
        exact (ENNReal.inv_mul_cancel hk (hmfin k)).symm
      · exact bot_le
    calc (⊤ : ℝ≥0∞) = ∑' k, (if m k ≠ 0 then 1 else 0 : ℝ≥0∞) := by
          have : Infinite {k | m k ≠ 0} := hinf.to_subtype
          rw [← tsum_subtype_eq_of_support_subset (s := {k | m k ≠ 0})
            (fun k hk => by simpa using hk)]
          rw [show (fun k : {k | m k ≠ 0} => if m k ≠ 0 then (1 : ℝ≥0∞) else 0) = fun _ => 1 from
            funext fun k => ite_eq_left k.2]
          exact (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
      _ ≤ ∑' k, ∫⁻ x in shell k, ‖(e x : ℂ) * ψ x‖ₑ ^ (2 : ℝ) := tsum_le_tsum hshell
      _ = ∫⁻ x in ⋃ k, shell k, ‖(e x : ℂ) * ψ x‖ₑ ^ (2 : ℝ) :=
          (lintegral_iUnion measurableSet_shell pairwise_disjoint_shell _).symm
      _ ≤ ∫⁻ x, ‖(e x : ℂ) * ψ x‖ₑ ^ (2 : ℝ) := setLIntegral_le_lintegral _ _
  · rintro ⟨R, hR⟩ e _ _
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
      e.continuous.continuousOn
    refine (hψ.const_mul ((max C 0 : ℝ) : ℂ)).of_le
      ((Complex.continuous_ofReal.comp e.continuous).aestronglyMeasurable.mul
        hψ.aestronglyMeasurable) ?_
    filter_upwards [hR] with x hx
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs (max C 0),
      abs_of_nonneg (le_max_right C 0)]
    by_cases hxR : R < |x|
    · rw [hx hxR, norm_zero, mul_zero, mul_zero]
    · refine mul_le_mul_of_nonneg_right ((hC x ?_).trans (le_max_left _ _)) (norm_nonneg _)
      rw [not_lt, abs_le] at hxR
      exact ⟨hxR.1, hxR.2⟩

/-- The unitary `(U_e ψ)(y) = ψ(e⁻¹ y) √((e⁻¹)'(y))` of the change of frame `y = e(x)`, for a
smooth diffeomorphism `e` of `ℝ`. For `e = tan(π/2 · erf)` it is `frameUnitary`. -/
def smoothFrameChange (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm) :
    L2R ≃ₗᵢ[ℂ] L2R :=
  Lp.compDiffeo (g := e.symm.toEquiv) (he'.differentiable (by simp))
    (by simpa using he.differentiable (by simp))

/-- In the frame `y = e(x)`, `ψ` has finite position variance iff `e ψ ∈ L²`. -/
lemma smoothFrameChange_mem_positionDomain_iff (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e)
    (he' : ContDiff ℝ ∞ e.symm) (ψ : L2R) :
    smoothFrameChange e he he' ψ ∈ positionDomain ↔ MemLp (fun x => (e x : ℂ) * ψ x) 2 := by
  have h := Lp.compDiffeo_mem_mulDomain_iff (g := e.symm.toEquiv) (he'.differentiable (by simp))
    (by simpa using he.differentiable (by simp)) (a := e) e.continuous.measurable (ψ := ψ)
  have hid : ((e : ℝ → ℝ) ∘ e.symm.toEquiv) = fun y => y := funext fun y => by simp
  rw [hid] at h
  exact h

/-- **Part 1.** A state has finite position variance in every smooth frame if and only if it
vanishes almost everywhere outside a bounded set. -/
theorem forall_smoothFrameChange_mem_positionDomain_iff (ψ : L2R) :
    (∀ (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm),
      smoothFrameChange e he he' ψ ∈ positionDomain) ↔ ∃ R : ℝ, ∀ᵐ x, R < |x| → ψ x = 0 := by
  simp_rw [smoothFrameChange_mem_positionDomain_iff]
  exact memLp_mul_forall_iff (Lp.memLp ψ)

end Frames

/-! ### Part 2: the free evolution -/

section Evolution

lemma integrable_of_cutoff (ψ : L2R) {R : ℝ} (hR : ∀ᵐ x, R < |x| → ψ x = 0) :
    Integrable (ψ : ℝ → ℂ) := by
  have : IsFiniteMeasure (volume.restrict (Icc (-R) R)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  have hon : IntegrableOn (ψ : ℝ → ℂ) (Icc (-R) R) :=
    ((Lp.memLp ψ).restrict _).integrable one_le_two
  refine hon.integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [hR] with x hx hxI
  refine hx ?_
  rw [mem_Icc, not_and_or, not_le, not_le] at hxI
  rcases hxI with h | h
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
  · exact lt_of_lt_of_le h (le_abs_self x)

/-- In momentum space the free evolution is the chirp `e^{-2iπ²ξ²t}`, pointwise for the Fourier
integrals of cut-off states. -/
lemma fourier_freeEvolution_of_cutoff {ψ : L2R} {R : ℝ} (hR : ∀ᵐ x, R < |x| → ψ x = 0)
    (t : ℝ) (hφ : Integrable (freeEvolution t ψ : ℝ → ℂ)) (ξ : ℝ) :
    𝓕 (freeEvolution t ψ : ℝ → ℂ) ξ =
      Complex.exp ((-((2 * Real.pi ^ 2 * t) * ξ ^ 2) : ℝ) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ := by
  have hψ := integrable_of_cutoff ψ hR
  have h1 := Lp.fourier_coeFn_eq_of_integrable _ hφ
  have h2 := Lp.fourier_coeFn_eq_of_integrable _ hψ
  have h3 : fourierL2 (freeEvolution t ψ) = L2.mulEvolution measurable_kinetic t (fourierL2 ψ) := by
    rw [freeEvolution_apply, LinearIsometryEquiv.apply_symm_apply]
  have h4 := L2.coeFn_mulEvolution measurable_kinetic t (fourierL2 ψ)
  have hae : 𝓕 (freeEvolution t ψ : ℝ → ℂ) =ᵐ[volume] fun ξ =>
      Complex.exp ((-((2 * Real.pi ^ 2 * t) * ξ ^ 2) : ℝ) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ := by
    have h1' : (fourierL2 (freeEvolution t ψ) : ℝ → ℂ) =ᵐ[volume]
        𝓕 (freeEvolution t ψ : ℝ → ℂ) := h1
    have h2' : (fourierL2 ψ : ℝ → ℂ) =ᵐ[volume] 𝓕 (ψ : ℝ → ℂ) := h2
    filter_upwards [h1', h2', h4] with ξ e1 e2 e4
    rw [← e1, h3, e4, e2, lp.phase]
    congr 2
    push_cast
    ring
  have hc1 : Continuous (𝓕 (freeEvolution t ψ : ℝ → ℂ)) := hφ.continuous_fourier
  have hc2 : Continuous fun ξ : ℝ =>
      Complex.exp ((-((2 * Real.pi ^ 2 * t) * ξ ^ 2) : ℝ) * Complex.I) * 𝓕 (ψ : ℝ → ℂ) ξ :=
    (by fun_prop : Continuous fun ξ : ℝ =>
      Complex.exp ((-((2 * Real.pi ^ 2 * t) * ξ ^ 2) : ℝ) * Complex.I)).mul hψ.continuous_fourier
  exact congrFun ((Continuous.ae_eq_iff_eq volume hc1 hc2).1 hae) ξ

/-- **Part 2.** The free evolution takes no nonzero cut-off state to a cut-off state: if `ψ ≠ 0`
vanishes outside a bounded set, then for every `t ≠ 0` the state `e^{-itH₀} ψ` does not. -/
theorem freeEvolution_not_cutoff {ψ : L2R} (hψ : ψ ≠ 0) {R : ℝ}
    (hR : ∀ᵐ x, R < |x| → ψ x = 0) {t : ℝ} (ht : t ≠ 0) :
    ¬ ∃ S : ℝ, ∀ᵐ x, S < |x| → freeEvolution t ψ x = 0 := by
  rintro ⟨S, hS⟩
  set T := max R S
  have hR' : ∀ᵐ x, T < |x| → ψ x = 0 := by
    filter_upwards [hR] with x hx h using hx ((le_max_left R S).trans_lt h)
  have hS' : ∀ᵐ x, T < |x| → freeEvolution t ψ x = 0 := by
    filter_upwards [hS] with x hx h using hx ((le_max_right R S).trans_lt h)
  have ha : 2 * Real.pi ^ 2 * t ≠ 0 := by positivity
  have h0 := Real.ae_eq_zero_of_fourier_eq_cexp_mul (Lp.memLp ψ)
    (Lp.memLp (freeEvolution t ψ)) hR' hS' ha
    (fourier_freeEvolution_of_cutoff hR t (integrable_of_cutoff _ hS))
  refine hψ (Lp.ext ?_)
  filter_upwards [h0, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hz
  rw [hx, hz]

/-- **Parts 1 and 2 together.** No nonzero state has finite position variance in every smooth
frame both now and after a free evolution for a time `t ≠ 0`. -/
theorem not_forall_frames_freeEvolution {ψ : L2R} (hψ : ψ ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    ¬ ((∀ (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm),
        smoothFrameChange e he he' ψ ∈ positionDomain) ∧
      ∀ (e : ℝ ≃ₜ ℝ) (he : ContDiff ℝ ∞ e) (he' : ContDiff ℝ ∞ e.symm),
        smoothFrameChange e he he' (freeEvolution t ψ) ∈ positionDomain) := by
  rintro ⟨h1, h2⟩
  obtain ⟨R, hR⟩ := (forall_smoothFrameChange_mem_positionDomain_iff ψ).1 h1
  exact freeEvolution_not_cutoff hψ hR ht
    ((forall_smoothFrameChange_mem_positionDomain_iff _).1 h2)

end Evolution

end HilbertUnphysicality
