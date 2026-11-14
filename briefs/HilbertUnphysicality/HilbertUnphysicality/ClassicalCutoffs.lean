/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import ForMathlib.Analysis.Fourier.PaleyWiener
import ForMathlib.MeasureTheory.Measure.ProbabilityMeasure.CompactSupport

/-!
# Unphysicality of Hilbert spaces: classical cutoffs

The remarks in the proof of Theorem 5 that contrast QSTO:H with classical mechanics. For [B]COBS:
"one can, in principle, put a cutoff on all variables and work only with joint probability
distributions in that compact region. Quantum mechanics does not allow that". For [B]WDQ: "one
can again work with joint probability distributions with compact support, which bound all
moments".

The classical half, read on the phase space `ℝⁿ × ℝⁿ` of `n` degrees of freedom: fix a compact
region `K`, and take as states the probability measures concentrated on `K`, with the topology of
weak convergence.
* [B]COBS holds there: every continuous observable, in particular every moment of the positions
  and momenta, has a finite expectation, and the expectation is continuous in the state
  (`classical_cutoff_cobs`).
* [B]WDQ holds there: a change of frame is continuous, so it maps a state concentrated on `K` to
  one concentrated on a compact set, for which every continuous observable is again integrable,
  so all variances stay finite (`classical_cutoff_wdq`).

The quantum half, read for one degree of freedom: a cutoff on all variables cuts off position and
momentum, and no state allows both. If `ψ ∈ L²(ℝ)` vanishes outside a bounded set and so does
its momentum wave function, the Fourier transform `𝓕 ψ` (an integral, since `ψ` is integrable),
then `ψ = 0` (`quantum_no_cutoff`). A cutoff on position alone is allowed: smooth compactly
supported states have finite moments of all orders in position and in momentum.

This module is separate from the main file of the brief, so that the comparator lane, which
certifies the main file, is unchanged. No certified statement depends on it.

## Main results

* `classical_cutoff_cobs`: finite and continuous expectations under a classical cutoff;
* `classical_cutoff_wdq`: changes of frame keep the cutoff, and with it all moments finite;
* `quantum_no_cutoff`: the only state with a cutoff on position and momentum is zero.

## References

* G. B. Folland, A. Sitaram, The uncertainty principle: a mathematical survey, J. Fourier Anal.
  Appl. 3 (1997) 207–238, Theorem 7.2: a function and its Fourier transform cannot both be
  supported on sets of finite measure (M. Benedicks, J. Math. Anal. Appl. 106 (1985) 180–183;
  W. O. Amrein, A. M. Berthier, J. Funct. Anal. 24 (1977) 258–267). `quantum_no_cutoff` is the
  compact-support case, by the Paley–Wiener theorem.
-/

open MeasureTheory Set
open scoped FourierTransform

public section

namespace HilbertUnphysicality

/-- The classical phase space `ℝⁿ × ℝⁿ` of `n` degrees of freedom: positions and momenta. -/
abbrev PhaseSpace (n : ℕ) : Type := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)

/-- **Classical cutoffs, [B]COBS.** On the probability distributions concentrated on a compact
region `K` of phase space, every continuous observable `g` has a finite expectation, and the
expectation is continuous for the topology of weak convergence. -/
theorem classical_cutoff_cobs (n : ℕ) {K : Set (PhaseSpace n)} (hK : IsCompact K)
    {g : PhaseSpace n → ℝ} (hg : Continuous g) :
    (∀ μ : ProbabilityMeasure (PhaseSpace n), (μ : Measure (PhaseSpace n)) Kᶜ = 0 →
      Integrable g μ) ∧
    ContinuousOn (fun μ : ProbabilityMeasure (PhaseSpace n) => ∫ p, g p ∂μ)
      {μ | (μ : Measure (PhaseSpace n)) Kᶜ = 0} :=
  ⟨fun _ hμ => integrable_of_isCompact hK hμ hg,
    ProbabilityMeasure.continuousOn_integral_of_isCompact hK hg⟩

/-- **Classical cutoffs, [B]WDQ.** A continuous change of frame `φ` maps a probability
distribution concentrated on a compact region `K` to one concentrated on the compact region
`φ '' K`, for which every continuous observable is integrable: all moments stay finite. -/
theorem classical_cutoff_wdq (n : ℕ) {K : Set (PhaseSpace n)} (hK : IsCompact K)
    {φ : PhaseSpace n → PhaseSpace n} (hφ : Continuous φ) (μ : ProbabilityMeasure (PhaseSpace n))
    (hμ : (μ : Measure (PhaseSpace n)) Kᶜ = 0) :
    ∃ K' : Set (PhaseSpace n), IsCompact K' ∧ (μ : Measure (PhaseSpace n)).map φ K'ᶜ = 0 ∧
      ∀ g : PhaseSpace n → ℝ, Continuous g → Integrable g ((μ : Measure (PhaseSpace n)).map φ) :=
  ⟨φ '' K, hK.image hφ, Measure.map_compl_image_eq_zero hφ hK hμ, fun _ hg =>
    integrable_of_isCompact (hK.image hφ) (Measure.map_compl_image_eq_zero hφ hK hμ) hg⟩

/-- **Quantum mechanics does not allow a cutoff on all variables.** If a wave function
`ψ ∈ L²(ℝ)` vanishes outside `[-R, R]` and its momentum wave function `𝓕 ψ` vanishes outside
`[-S, S]`, then `ψ = 0`. -/
theorem quantum_no_cutoff {ψ : ℝ → ℂ} (hψ : MemLp ψ 2) {R S : ℝ}
    (hR : ∀ᵐ x, R < |x| → ψ x = 0) (hS : ∀ ξ, S < |ξ| → 𝓕 ψ ξ = 0) : ψ =ᵐ[volume] 0 :=
  Real.ae_eq_zero_of_fourier_eq_zero_of_lt_abs hψ hR hS

end HilbertUnphysicality
