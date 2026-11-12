/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import HilbertUnphysicality
public import ForMathlib.Analysis.InnerProductSpace.KatoRellich
public import ForMathlib.Analysis.Fourier.LpSpace

/-!
# Unphysicality of Hilbert spaces: potentials in `L² + L^∞`

The remark of Sec. 5 of the brief, that the Schrödinger equation holds only on `D(H)`, for
`H = H₀ + V` on `L²(ℝ)` with a potential `V ∈ L² + L^∞`: `|V| ≤ |W| + C` almost everywhere with
`W ∈ L²`. Such potentials include square wells and barriers, and singular ones like
`|x|^{-α}` near `0` for `α < 1/2`.

By the Kato–Rellich theorem, `H₀ + V` is self-adjoint on `D(H₀)`. The relative bound comes from
the one-dimensional Sobolev bound `‖ψ‖_∞ ≤ ε ‖H₀ ψ‖ + C_ε ‖ψ‖` on `D(H₀)`: the Fourier transform
of `ψ` is integrable, with `∫ |ψ̂| ≤ ε ‖ξ² ψ̂‖₂ + C ‖ψ̂‖₂`, and bounds `ψ` (in `ForMathlib`).

This module is separate from the main file of the brief because the Kato–Rellich theorem is
reached through `ForMathlib.Analysis.InnerProductSpace.KatoRellich`, whose TauCeti import clashes
with Physlib's unbounded operators in files that load private imports, such as the comparator's
exporter. No certified statement depends on it.

## Main results

* `exists_ae_norm_le_freeHamiltonian`: the Sobolev bound on `D(H₀)`;
* `exists_norm_mulOp_le_freeHamiltonian`: `D(H₀) ⊆ D(V)` and `‖V ψ‖ ≤ a ‖ψ‖ + ½ ‖H₀ ψ‖`;
* `isSelfAdjoint_schrodingerHamiltonian_of_memLp`, `domain_schrodingerHamiltonian_of_memLp`:
  `H₀ + V` is self-adjoint on `D(H₀)`;
* `memLp_schrodinger_only_on_domain`: the remark of Sec. 5 for `H₀ + V`.
-/

open Real MeasureTheory FourierTransform QuantumMechanics LinearPMap
open scoped ENNReal

@[expose] public noncomputable section

namespace HilbertUnphysicality

/-- **The Sobolev bound on `D(H₀)`.** For every `ε > 0` there is `C` such that every `ψ ∈ D(H₀)`
satisfies `|ψ(x)| ≤ ε ‖H₀ ψ‖ + C ‖ψ‖` for almost every `x`. -/
theorem exists_ae_norm_le_freeHamiltonian {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ ψ : freeHamiltonian.domain,
      ∀ᵐ x, ‖(ψ : L2R) x‖ ≤ ε * ‖freeHamiltonian ψ‖ + C * ‖(ψ : L2R)‖ := by
  have hk : (0 : ℝ) < 2 * π ^ 2 := by positivity
  obtain ⟨C, hC⟩ := Lp.exists_integral_norm_le_of_ae_eq_sq_mul (mul_pos hε hk)
  refine ⟨C, fun ψ => ?_⟩
  set f : L2R := fourierL2 ψ
  set Hf : L2R := L2.mulOp (fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2)
    ⟨f, mem_domain_freeHamiltonian.1 ψ.2⟩
  set g : L2R := (((2 * π ^ 2)⁻¹ : ℝ) : ℂ) • Hf
  have hg : (g : ℝ → ℂ) =ᵐ[volume] fun ξ => (ξ : ℂ) ^ 2 * f ξ := by
    filter_upwards [Lp.coeFn_smul (((2 * π ^ 2)⁻¹ : ℝ) : ℂ) Hf,
      L2.coeFn_mulOp (fun ξ : ℝ => 2 * π ^ 2 * ξ ^ 2) ⟨f, mem_domain_freeHamiltonian.1 ψ.2⟩]
      with ξ h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, ← mul_assoc]
    congr 1
    push_cast
    field_simp
  obtain ⟨hfi, hb⟩ := hC f g hg
  have hg' : ‖g‖ = (2 * π ^ 2)⁻¹ * ‖freeHamiltonian ψ‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), freeHamiltonian_apply,
      LinearIsometryEquiv.norm_map]
  have hf' : ‖f‖ = ‖(ψ : L2R)‖ := LinearIsometryEquiv.norm_map _ _
  have hψ : (ψ : L2R) = 𝓕⁻ f := (fourierL2.symm_apply_apply ψ).symm
  have hψ' : ((ψ : L2R) : ℝ → ℂ) = ((𝓕⁻ f : L2R) : ℝ → ℂ) :=
    congrArg (fun u : L2R => (u : ℝ → ℂ)) hψ
  filter_upwards [Lp.ae_norm_fourierInv_le_of_integrable f hfi] with x hx
  rw [hψ']
  refine hx.trans (hb.trans (le_of_eq ?_))
  rw [hg', hf']
  field_simp

variable {V W : ℝ → ℝ} {C : ℝ}

/-- **The relative bound.** If `|V| ≤ |W| + C` almost everywhere with `W ∈ L²`, then
`D(H₀) ⊆ D(V)` and `‖V ψ‖ ≤ a ‖ψ‖ + ½ ‖H₀ ψ‖` on `D(H₀)`, for some `a`. -/
theorem exists_norm_mulOp_le_freeHamiltonian (hV : Measurable V) (hW : MemLp W 2 volume)
    (hb : ∀ᵐ x, |V x| ≤ |W x| + C) :
    ∃ a, ∃ hdom : freeHamiltonian.domain ≤ (L2.mulOp V : L2R →ₗ.[ℂ] L2R).domain,
      ∀ ψ : freeHamiltonian.domain,
        ‖L2.mulOp V ⟨ψ, hdom ψ.2⟩‖ ≤ a * ‖(ψ : L2R)‖ + 1 / 2 * ‖freeHamiltonian ψ‖ := by
  set N : ℝ := (eLpNorm W 2 volume).toReal
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  set ε : ℝ := (2 * (N + 1))⁻¹
  have hε : 0 < ε := by positivity
  have hεN : N * ε ≤ 1 / 2 := by
    rw [show N * ε = N / (2 * (N + 1)) by ring, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨C₀, hC₀⟩ := exists_ae_norm_le_freeHamiltonian hε
  set C' := max C 0
  -- For `ψ ∈ D(H₀)` with `|ψ| ≤ M` a.e., `|V ψ| ≤ G := M |W| + C' |ψ|` a.e.
  have hG (ψ : freeHamiltonian.domain) :
      let M := max (ε * ‖freeHamiltonian ψ‖ + C₀ * ‖(ψ : L2R)‖) 0
      MemLp (fun x => M * ‖W x‖ + C' * ‖(ψ : L2R) x‖) 2 volume ∧
        ∀ᵐ x, ‖(V x : ℂ) * (ψ : L2R) x‖ ≤ M * ‖W x‖ + C' * ‖(ψ : L2R) x‖ := by
    intro M
    refine ⟨(hW.norm.const_mul M).add ((Lp.memLp (ψ : L2R)).norm.const_mul C'), ?_⟩
    filter_upwards [hb, hC₀ ψ] with x h1 h2
    have hM : ‖(ψ : L2R) x‖ ≤ M := h2.trans (le_max_left _ _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1' : |V x| ≤ |W x| + C' := h1.trans (by linarith [le_max_left C 0])
    nlinarith [norm_nonneg ((ψ : L2R) x), abs_nonneg (W x), le_max_right C 0,
      le_max_right (ε * ‖freeHamiltonian ψ‖ + C₀ * ‖(ψ : L2R)‖) 0]
  have hdom : freeHamiltonian.domain ≤ (L2.mulOp V : L2R →ₗ.[ℂ] L2R).domain := fun ψ hψ => by
    obtain ⟨hGm, hle⟩ := hG ⟨ψ, hψ⟩
    refine (L2.mem_mulDomain V).2 (hGm.of_le ?_ ?_)
    · exact hV.complex_ofReal.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)
    · filter_upwards [hle] with x hx
      exact hx.trans (le_abs_self _)
  refine ⟨N * max C₀ 0 + C', hdom, fun ψ => ?_⟩
  obtain ⟨hGm, hle⟩ := hG ψ
  set M := max (ε * ‖freeHamiltonian ψ‖ + C₀ * ‖(ψ : L2R)‖) 0
  -- `‖V ψ‖ ≤ ‖G‖₂ ≤ M N + C' ‖ψ‖`.
  have h1 : ‖L2.mulOp V ⟨ψ, hdom ψ.2⟩‖ ≤
      (eLpNorm (fun x => M * ‖W x‖ + C' * ‖(ψ : L2R) x‖) 2 volume).toReal := by
    rw [Lp.norm_def]
    refine ENNReal.toReal_mono hGm.eLpNorm_ne_top ?_
    rw [eLpNorm_congr_ae (L2.coeFn_mulOp V ⟨ψ, hdom ψ.2⟩)]
    refine eLpNorm_mono_ae
      (hV.complex_ofReal.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _)) ?_
    filter_upwards [hle] with x hx
    exact hx.trans (le_abs_self _)
  have hW' : (eLpNorm (fun x => M * ‖W x‖) 2 volume).toReal = M * N := by
    rw [show (fun x => M * ‖W x‖) = M • fun x => ‖W x‖ from rfl, eLpNorm_const_smul,
      eLpNorm_norm _ hW.aestronglyMeasurable, ENNReal.toReal_mul, toReal_enorm,
      Real.norm_of_nonneg (le_max_right _ _)]
  have hψ' : (eLpNorm (fun x => C' * ‖(ψ : L2R) x‖) 2 volume).toReal = C' * ‖(ψ : L2R)‖ := by
    rw [show (fun x => C' * ‖(ψ : L2R) x‖) = C' • fun x => ‖(ψ : L2R) x‖ from rfl,
      eLpNorm_const_smul, eLpNorm_norm _ (Lp.aestronglyMeasurable _), ENNReal.toReal_mul,
      toReal_enorm, Real.norm_of_nonneg (le_max_right _ _), Lp.norm_def]
  have h2 : (eLpNorm (fun x => M * ‖W x‖ + C' * ‖(ψ : L2R) x‖) 2 volume).toReal ≤
      M * N + C' * ‖(ψ : L2R)‖ := by
    rw [← hW', ← hψ']
    have hm1 := hW.norm.const_mul M
    have hm2 := (Lp.memLp (ψ : L2R)).norm.const_mul C'
    rw [← ENNReal.toReal_add hm1.eLpNorm_ne_top hm2.eLpNorm_ne_top]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hm1.eLpNorm_ne_top, hm2.eLpNorm_ne_top⟩)
      (eLpNorm_add_le one_le_two)
  -- `M N ≤ ½ ‖H₀ ψ‖ + N max C₀ 0 ‖ψ‖`, by the choice of `ε`.
  have h3 : M * N ≤ 1 / 2 * ‖freeHamiltonian ψ‖ + N * max C₀ 0 * ‖(ψ : L2R)‖ := by
    have hM : M ≤ ε * ‖freeHamiltonian ψ‖ + max C₀ 0 * ‖(ψ : L2R)‖ := by
      refine max_le ?_ (by positivity)
      nlinarith [le_max_left C₀ 0, norm_nonneg (ψ : L2R)]
    calc M * N ≤ (ε * ‖freeHamiltonian ψ‖ + max C₀ 0 * ‖(ψ : L2R)‖) * N :=
          mul_le_mul_of_nonneg_right hM hN
      _ = N * ε * ‖freeHamiltonian ψ‖ + N * max C₀ 0 * ‖(ψ : L2R)‖ := by ring
      _ ≤ _ := by nlinarith [norm_nonneg (freeHamiltonian ψ)]
  nlinarith [h1, h2, h3]

variable (hV : Measurable V) (hW : MemLp W 2 volume) (hb : ∀ᵐ x, |V x| ≤ |W x| + C)
include hV hW hb

/-- **Potentials in `L² + L^∞`.** If `|V| ≤ |W| + C` almost everywhere with `W ∈ L²`, then
`H₀ + V` is self-adjoint, by the Kato–Rellich theorem. -/
theorem isSelfAdjoint_schrodingerHamiltonian_of_memLp :
    IsSelfAdjoint (schrodingerHamiltonian V) := by
  obtain ⟨a, hdom, hbound⟩ := exists_norm_mulOp_le_freeHamiltonian hV hW hb
  exact isSelfAdjoint_freeHamiltonian.add_of_relativeBound
    (L2.isSelfAdjoint_mulOp hV).isFormalAdjoint hdom hbound (by norm_num)

/-- `D(H₀ + V) = D(H₀)`. -/
theorem domain_schrodingerHamiltonian_of_memLp :
    (schrodingerHamiltonian V).domain = freeHamiltonian.domain := by
  obtain ⟨_, hdom, _⟩ := exists_norm_mulOp_le_freeHamiltonian hV hW hb
  exact inf_eq_left.2 hdom

/-- `H₀ + V` is unbounded on its domain: `‖(H₀ + V) ψ‖ ≥ ½ ‖H₀ ψ‖ - a ‖ψ‖`. -/
theorem exists_lt_norm_schrodingerHamiltonian_of_memLp (c : ℝ) :
    ∃ ψ : (schrodingerHamiltonian V).domain,
      c * ‖(ψ : L2R)‖ < ‖schrodingerHamiltonian V ψ‖ := by
  obtain ⟨a, hdom, hbound⟩ := exists_norm_mulOp_le_freeHamiltonian hV hW hb
  obtain ⟨ψ, hψ⟩ := exists_lt_norm_freeHamiltonian (2 * (c + a))
  have hmem : (ψ : L2R) ∈ (schrodingerHamiltonian V).domain :=
    (domain_schrodingerHamiltonian_of_memLp hV hW hb).ge ψ.2
  refine ⟨⟨ψ, hmem⟩, ?_⟩
  have h1 := hbound ψ
  have h2 := norm_sub_norm_le (freeHamiltonian ψ) (-L2.mulOp V ⟨ψ, hdom ψ.2⟩)
  rw [sub_neg_eq_add, norm_neg] at h2
  change c * ‖(ψ : L2R)‖ < ‖freeHamiltonian ψ + L2.mulOp V ⟨ψ, hmem.2⟩‖
  linarith

/-- The remark of Sec. 5 for every potential in `L² + L^∞`: `H = H₀ + V` is self-adjoint on
`D(H) = D(H₀) ≠ L²(ℝ)`, the evolution `e^{-itH}` of Stone's theorem solves the Schrödinger
equation on `D(H)`, and off `D(H)` its orbit is differentiable nowhere. -/
theorem memLp_schrodinger_only_on_domain :
    (schrodingerHamiltonian V).domain = freeHamiltonian.domain ∧
      freeHamiltonian.domain ≠ ⊤ ∧
      SolvesSchrodinger 1 (schrodingerHamiltonian V)
        (schrodingerPropagator one_ne_zero
          (isSelfAdjoint_schrodingerHamiltonian_of_memLp hV hW hb)) ∧
      ∀ ψ ∉ freeHamiltonian.domain, ∀ t, ¬ DifferentiableAt ℝ (fun s =>
        schrodingerPropagator one_ne_zero
          (isSelfAdjoint_schrodingerHamiltonian_of_memLp hV hW hb) s ψ) t := by
  obtain ⟨h1, h2, h3⟩ := schrodinger_only_on_domain one_ne_zero
    (isSelfAdjoint_schrodingerHamiltonian_of_memLp hV hW hb)
    (exists_lt_norm_schrodingerHamiltonian_of_memLp hV hW hb)
  rw [domain_schrodingerHamiltonian_of_memLp hV hW hb] at h1 h3
  exact ⟨domain_schrodingerHamiltonian_of_memLp hV hW hb, h1, h2, h3⟩

end HilbertUnphysicality
