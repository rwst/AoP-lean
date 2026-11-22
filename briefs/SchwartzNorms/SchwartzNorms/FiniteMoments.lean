/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import SchwartzNorms
public import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
public import TauCeti.Analysis.Distribution.TemperedDistribution.SmulLeft
public import TauCeti.Analysis.Sobolev.WeakDeriv.Interval
public import TauCeti.Analysis.Sobolev.WeakDeriv.TemperedDistribution

/-!
# Finite moments imply Schwartz

The brief states that finiteness of all the expectation values is equivalent to membership in
`𝓢(ℝ)`: `𝓢(ℝ)` "is exactly the space of states for which all polynomial moments of position
and momentum are well-defined". Only the bound (10) is proved there. For the converse, the
operators `X^α ∂^β` have to act on states outside `𝓢(ℝ)`, so we take the state to be an arbitrary
tempered distribution `u` and differentiate it in the sense of distributions.

* `exists_schwartzMap_of_l2Norm_lt_top`: for smooth `f`, finite `L²` seminorms (3) make `f` a
  Schwartz function. This is Theorem 5 of the brief.
* `exists_schwartzMap_iff_forall_memL2`: a tempered distribution `u` is a Schwartz function iff
  every `x^α ∂^β u` is an `L²` function, i.e. `𝓢(ℝ) = ⋂_{α,β} {u | X^α ∂^β u ∈ L²}`.
* `exists_schwartzMap_ae_eq`: the same for an `L²` function `f`, up to equality almost
  everywhere.

The proof of the converse: the derivatives `∂^β u` are `L²` functions `g_β`, so `g_{β+1}` is the
weak derivative of `g_β` (`TauCeti.hasWeakLineDerivOn_of_lineDerivOp_toTemperedDistribution_eq`)
and `g_β` agrees almost everywhere with `c_β + ∫_0^x g_{β+1}`
(`TauCeti.HasWeakLineDerivOn.exists_ae_eq_add_intervalIntegral_top`). These continuous
representatives `G_β` satisfy `G_β' = G_{β+1}` everywhere, so `G_0` is smooth with
`G_0⁽ᵝ⁾ = G_β`, and its `L²` seminorms are those of the given functions `x^α ∂^β u`.
-/

open Real MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap LineDeriv

@[expose] public noncomputable section

namespace SchwartzNorms

/-- For smooth `f`, finite `L²` seminorms (3) make `f` a Schwartz function (Theorem 5). -/
theorem exists_schwartzMap_of_l2Norm_lt_top {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (h : ∀ α β, l2Norm α β f < ⊤) : ∃ F : 𝓢(ℝ, ℂ), ⇑F = f :=
  (exists_schwartzMap_iff hf).2 (((tfae_finite hf).out 1 3).2 h)

/-- The one-dimensional distributional derivative is the directional derivative along `1`. -/
lemma derivCLM_eq_lineDerivOp (v : 𝓢'(ℝ, ℂ)) : derivCLM ℂ v = ∂_{(1 : ℝ)} v := rfl

lemma hasTemperateGrowth_pow (α : ℕ) :
    (fun x : ℝ => (x : ℂ) ^ α).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.pow α

/-- If every `x^α ∂^β u` is an `L²` function, the tempered distribution `u` is a Schwartz
function. -/
theorem exists_schwartzMap_of_forall_memL2 (u : 𝓢'(ℝ, ℂ))
    (h : ∀ α β : ℕ, ∃ g : Lp ℂ 2 (volume : Measure ℝ),
      smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ α) ((derivCLM ℂ)^[β] u) = g) :
    ∃ F : 𝓢(ℝ, ℂ), u = F := by
  choose g hg using h
  -- The derivatives `∂^β u` are the `L²` functions `g 0 β`.
  have hd : ∀ β, (derivCLM ℂ)^[β] u = g 0 β := fun β => by simpa using hg 0 β
  have hw : ∀ β, TauCeti.HasWeakLineDerivOn volume ⊤ (g 0 β) (g 0 (β + 1)) 1 := fun β =>
    TauCeti.hasWeakLineDerivOn_of_lineDerivOp_toTemperedDistribution_eq <| by
      rw [← hd β, ← hd (β + 1), Function.iterate_succ_apply', derivCLM_eq_lineDerivOp]
  have hii : ∀ β a b, IntervalIntegrable (g 0 β) volume a b := fun β a b =>
    (((Lp.memLp (g 0 β)).locallyIntegrable (by norm_num)).integrableOn_isCompact
      isCompact_uIcc).intervalIntegrable
  -- Continuous representatives `G β = c β + ∫_0^x g 0 (β + 1)`.
  choose c hc using fun β => (hw β).exists_ae_eq_add_intervalIntegral_top 0
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ → ℂ, ∀ β t, G β t = c β + ∫ s in (0 : ℝ)..t, g 0 (β + 1) s :=
    ⟨_, fun _ _ => rfl⟩
  have hGae : ∀ β, (g 0 β : ℝ → ℂ) =ᵐ[volume] G β := fun β => by
    filter_upwards [hc β] with t ht
    rw [ht, hG]
  have hGc : ∀ β, Continuous (G β) := fun β => by
    have : G β = fun t => c β + ∫ s in (0 : ℝ)..t, g 0 (β + 1) s := funext (hG β)
    rw [this]
    exact continuous_const.add (intervalIntegral.continuous_primitive (hii (β + 1)) 0)
  have hderiv : ∀ β t, HasDerivAt (G β) (G (β + 1) t) t := fun β t => by
    have h1 := ((hGc (β + 1)).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (c β)
    convert h1 using 1
    funext s
    rw [hG]
    congr 1
    exact intervalIntegral.integral_congr_ae ((hGae (β + 1)).mono fun x hx _ => hx)
  have hderiv' : ∀ β, deriv (G β) = G (β + 1) := fun β => funext fun t => (hderiv β t).deriv
  have hsmooth : ∀ n : ℕ, ∀ β, ContDiff ℝ n (G β) := by
    intro n
    induction n with
    | zero => exact fun β => contDiff_zero.2 (hGc β)
    | succ n ih =>
      intro β
      rw [Nat.cast_succ, contDiff_succ_iff_deriv, hderiv']
      exact ⟨fun t => (hderiv β t).differentiableAt, by simp, ih (β + 1)⟩
  have hG0 : ContDiff ℝ (⊤ : ℕ∞) (G 0) := contDiff_infty.2 fun n => hsmooth n 0
  have hiter : ∀ β, iteratedDeriv β (G 0) = G β := by
    intro β
    induction β with
    | zero => exact iteratedDeriv_zero
    | succ n ih => rw [iteratedDeriv_succ, ih, hderiv']
  -- The `L²` functions `g α β` are `x^α G_0⁽ᵝ⁾`.
  have hweighted : ∀ α β, (g α β : ℝ → ℂ) =ᵐ[volume] weighted α β (G 0) := fun α β => by
    refine Lp.ae_eq_of_toTemperedDistribution_apply_eq (g α β)
      (continuous_weighted hG0 α β).locallyIntegrable fun φ => ?_
    rw [← hg α β, hd β, Lp.smulLeftCLM_toTemperedDistribution_apply (hasTemperateGrowth_pow α)]
    refine integral_congr_ae ?_
    filter_upwards [hGae β] with x hx
    rw [hx, weighted, hiter β]
    simp only [smul_eq_mul]
  have hl2 : ∀ α β, l2Norm α β (G 0) < ⊤ := fun α β => by
    rw [l2Norm, ← eLpNorm_congr_ae (hweighted α β)]
    exact Lp.eLpNorm_lt_top _
  obtain ⟨F, hF⟩ := exists_schwartzMap_of_l2Norm_lt_top hG0 hl2
  refine ⟨F, ?_⟩
  rw [← Function.iterate_zero_apply (derivCLM ℂ) u, hd 0]
  ext φ
  rw [Lp.toTemperedDistribution_apply]
  refine Eq.trans ?_ (SchwartzMap.coe_apply F φ).symm
  refine integral_congr_ae ?_
  filter_upwards [hGae 0] with x hx
  rw [hx, hF]

/-- Every `x^α ∂^β F` of a Schwartz function `F` is an `L²` function. -/
theorem forall_memL2_of_schwartzMap (F : 𝓢(ℝ, ℂ)) (α β : ℕ) :
    ∃ g : Lp ℂ 2 (volume : Measure ℝ),
      smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ α) ((derivCLM ℂ)^[β] (F : 𝓢'(ℝ, ℂ))) = g := by
  have hit : ∀ β, (derivCLM ℂ)^[β] (F : 𝓢'(ℝ, ℂ)) =
      ((SchwartzMap.derivCLM ℂ ℂ)^[β] F : 𝓢'(ℝ, ℂ)) := by
    intro β
    induction β with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, derivCLM_toTemperedDistributionCLM_eq ℂ,
        Function.iterate_succ_apply']
  refine ⟨(SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ α)
    ((SchwartzMap.derivCLM ℂ ℂ)^[β] F)).toLp 2, ?_⟩
  rw [hit, Lp.toTemperedDistribution_toLp_eq]
  exact smulLeftCLM_toTemperedDistributionCLM_eq _

/-- **Finite moments imply Schwartz.** A tempered distribution `u` is a Schwartz function iff
every `x^α ∂^β u`, taken in the sense of distributions, is an `L²` function. -/
theorem exists_schwartzMap_iff_forall_memL2 (u : 𝓢'(ℝ, ℂ)) :
    (∃ F : 𝓢(ℝ, ℂ), u = F) ↔ ∀ α β : ℕ, ∃ g : Lp ℂ 2 (volume : Measure ℝ),
      smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ α) ((derivCLM ℂ)^[β] u) = g :=
  ⟨fun ⟨F, hF⟩ => hF ▸ forall_memL2_of_schwartzMap F, exists_schwartzMap_of_forall_memL2 u⟩

/-- The same for a state `f ∈ L²`: if every `x^α ∂^β f` is an `L²` function, then `f` agrees
almost everywhere with a Schwartz function. -/
theorem exists_schwartzMap_ae_eq (f : Lp ℂ 2 (volume : Measure ℝ))
    (h : ∀ α β : ℕ, ∃ g : Lp ℂ 2 (volume : Measure ℝ),
      smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ α) ((derivCLM ℂ)^[β] (f : 𝓢'(ℝ, ℂ))) = g) :
    ∃ F : 𝓢(ℝ, ℂ), (f : ℝ → ℂ) =ᵐ[volume] F := by
  obtain ⟨F, hF⟩ := exists_schwartzMap_of_forall_memL2 _ h
  refine ⟨F, Lp.ae_eq_of_toTemperedDistribution_apply_eq f
    (F.continuous.locallyIntegrable) fun φ => ?_⟩
  rw [hF]
  exact SchwartzMap.coe_apply F φ

end SchwartzNorms
