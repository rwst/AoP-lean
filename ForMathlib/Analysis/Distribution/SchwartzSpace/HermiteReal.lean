/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteSeries
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Parseval

/-!
# Hermite expansions of Schwartz functions on the real line

The Schwartz functions on `ℝ` are exactly the vectors of `L²(ℝ)` whose coefficients
`cₙ = ⟪ψₙ, f⟫` in the Hermite basis are rapidly decreasing, `sup_n (n + 1)^K |cₙ| < ∞` for every
`K`, and a family of Schwartz functions converges in `𝓢(ℝ)` exactly when the coefficients of the
differences tend to zero in every one of these weighted suprema. So the Hermite basis identifies
`𝓢(ℝ)` with the space of rapidly decreasing sequences, together with its topology.

The results are transferred from `ℝ¹ = EuclideanSpace ℝ (Fin 1)`, where the multi-index Hermite
expansions of `HermiteCoeff.lean`, `HermiteSeminorm.lean` and `HermiteSeries.lean` live, along the
measure-preserving isomorphism `ℝ¹ ≃ ℝ`.

## Main definitions

* `SchwartzMap.euclideanFinOneEquiv`: the isomorphism `ℝ¹ ≃L[ℝ] ℝ`, `x ↦ x 0`;
* `SchwartzMap.euclideanFinOneCLE`: the induced isomorphism `𝓢(ℝ) ≃L[ℂ] 𝓢(ℝ¹)`.

## Main results

* `SchwartzMap.tendsto_iff_hermiteNorm`: on `ℝ^ι`, convergence in `𝓢` is convergence in every
  weighted supremum of the Hermite coefficients;
* `SchwartzMap.exists_toLp_eq_iff`: a vector of `L²(ℝ)` is a Schwartz function iff its Hermite
  coefficients are rapidly decreasing;
* `SchwartzMap.tendsto_iff_inner_hermiteFunctionLp`: convergence in `𝓢(ℝ)` in terms of the
  Hermite coefficients.
-/

open MeasureTheory Filter Topology TauCeti
open scoped SchwartzMap InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace SchwartzMap

/-! ### Convergence on `ℝ^ι` -/

variable {α : Type*} {l : Filter α}

/-- On `ℝ^ι`, a family of Schwartz functions converges exactly when the weighted suprema
`sup_α (1 + |α|)^K |c_α|` of the Hermite coefficients of the differences tend to zero, for every
`K`. -/
theorem tendsto_iff_hermiteNorm {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : α → 𝓢(EuclideanSpace ℝ ι, ℂ)} {G : 𝓢(EuclideanSpace ℝ ι, ℂ)} :
    Tendsto F l (𝓝 G) ↔ ∀ K : ℕ, Tendsto (fun j => hermiteNorm K (F j - G)) l (𝓝 0) := by
  constructor
  · intro h K
    obtain ⟨s, C, hC⟩ := exists_hermiteNorm_le_seminorm (ι := ι) K
    have hs : Tendsto (fun j => s.sup (schwartzSeminormFamily ℂ _ ℂ) (F j - G)) l (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      filter_upwards [((schwartz_withSeminorms ℂ _ ℂ).tendsto_nhds' F G).1 h s ε hε] with j hj
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)]
    have hup : Tendsto (fun j => (C : ℝ≥0∞) *
        ENNReal.ofReal (s.sup (schwartzSeminormFamily ℂ _ ℂ) (F j - G))) l (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) (ENNReal.tendsto_ofReal hs)
        (Or.inr ENNReal.coe_ne_top)
      rwa [ENNReal.ofReal_zero, mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => bot_le)
      fun j => hC _
  · intro h
    rw [(schwartz_withSeminorms ℂ _ ℂ).tendsto_nhds F G]
    rintro ⟨k, m⟩ ε hε
    obtain ⟨C, hC, hle⟩ := exists_seminorm_le_hermiteNorm (ι := ι) k m
    have hup : Tendsto (fun j => C * hermiteNorm (2 * Fintype.card ι + k + m) (F j - G)) l
        (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (h (2 * Fintype.card ι + k + m)) (Or.inr hC)
      rwa [mul_zero] at this
    filter_upwards [(tendsto_order.1 hup).2 _ (ENNReal.ofReal_pos.2 hε)] with j hj
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 ((hle _).trans_lt hj)

/-! ### The real line as `ℝ¹` -/

/-- The isomorphism `ℝ¹ ≃ ℝ`, `x ↦ x 0`. -/
def euclideanFinOneEquiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

@[simp]
lemma euclideanFinOneEquiv_apply (x : EuclideanSpace ℝ (Fin 1)) :
    euclideanFinOneEquiv x = x 0 :=
  rfl

lemma measurePreserving_euclideanFinOneEquiv : MeasurePreserving euclideanFinOneEquiv :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp (PiLp.volume_preserving_ofLp (Fin 1))

/-- The isomorphism `𝓢(ℝ) ≃ 𝓢(ℝ¹)`, `f ↦ (x ↦ f (x 0))`. -/
def euclideanFinOneCLE : 𝓢(ℝ, ℂ) ≃L[ℂ] 𝓢(EuclideanSpace ℝ (Fin 1), ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLMOfContinuousLinearEquiv ℂ euclideanFinOneEquiv)
    (compCLMOfContinuousLinearEquiv ℂ euclideanFinOneEquiv.symm)
    (fun f => by ext x; simp)
    (fun f => by ext x; exact congrArg f (euclideanFinOneEquiv.symm_apply_apply x))

@[simp]
lemma euclideanFinOneCLE_apply (f : 𝓢(ℝ, ℂ)) (x : EuclideanSpace ℝ (Fin 1)) :
    euclideanFinOneCLE f x = f (x 0) :=
  rfl

/-- The Hermite coefficient `⟪ψₙ, f⟫` of a Schwartz function on `ℝ` is its coefficient for the
multi-index `(n)` on `ℝ¹`. -/
lemma inner_hermiteFunctionLp_toLp (n : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ⟪hermiteFunctionLp ℂ n, f.toLp 2⟫_ℂ = hermiteCoeff (fun _ => n) (euclideanFinOneCLE f) := by
  rw [hermiteCoeff_eq_integral, L2.inner_def]
  have h := measurePreserving_euclideanFinOneEquiv.integral_comp
    euclideanFinOneEquiv.toHomeomorph.measurableEmbedding
    (fun t : ℝ => (hermiteFunction n t : ℂ) * f t)
  simp only [euclideanFinOneEquiv_apply] at h
  have hf : (fun x : EuclideanSpace ℝ (Fin 1) => hermitePiFun (fun _ => n) x *
      euclideanFinOneCLE f x) = fun x => (hermiteFunction n (x 0) : ℂ) * f (x 0) := by
    funext x
    simp [hermitePiFun]
  rw [hf, h]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_hermiteFunctionLp (𝕜 := ℂ) n, coeFn_toLp (p := 2) (μ := volume) f]
    with t h1 h2
  rw [h1, h2]
  simp [Complex.conj_ofReal, mul_comm]

lemma hermiteWeight_const (n : ℕ) : hermiteWeight (fun _ : Fin 1 => n) = n + 1 := by
  simp [hermiteWeight]

lemma const_apply_zero (α : Fin 1 → ℕ) : (fun _ : Fin 1 => α 0) = α :=
  funext fun i => by rw [Subsingleton.elim i 0]

/-- On `ℝ¹`, `sup_α (1 + |α|)^K |c_α(F)| ≤ ε` iff `(n + 1)^K |c_{(n)}(F)| ≤ ε` for every `n`. -/
lemma hermiteNorm_le_ofReal_iff (K : ℕ) (F : 𝓢(EuclideanSpace ℝ (Fin 1), ℂ)) {ε : ℝ}
    (hε : 0 ≤ ε) :
    hermiteNorm K F ≤ ENNReal.ofReal ε ↔
      ∀ n : ℕ, ((n : ℝ) + 1) ^ K * ‖hermiteCoeff (fun _ => n) F‖ ≤ ε := by
  have key : ∀ n : ℕ, (hermiteWeight (fun _ : Fin 1 => n) : ℝ≥0∞) ^ K *
      ‖hermiteCoeff (fun _ => n) F‖ₑ =
        ENNReal.ofReal (((n : ℝ) + 1) ^ K * ‖hermiteCoeff (fun _ => n) F‖) := by
    intro n
    rw [hermiteWeight_const, ENNReal.ofReal_mul (by positivity), ofReal_norm,
      ENNReal.ofReal_pow (by positivity)]
    congr 2
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
    push_cast
    rfl
  rw [hermiteNorm, iSup_le_iff]
  constructor
  · intro h n
    rw [← ENNReal.ofReal_le_ofReal_iff hε, ← key]
    exact h _
  · intro h α
    rw [← const_apply_zero α, key]
    exact ENNReal.ofReal_le_ofReal (h _)

/-! ### Schwartz functions on `ℝ` and their Hermite coefficients -/

/-- **Schwartz functions are the rapidly decreasing Hermite series.** A vector `g ∈ L²(ℝ)` is
(the class of) a Schwartz function iff its Hermite coefficients `⟪ψₙ, g⟫` are rapidly
decreasing. -/
theorem exists_toLp_eq_iff (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (∃ f : 𝓢(ℝ, ℂ), f.toLp 2 = g) ↔
      ∀ K : ℕ, ∃ C : ℝ, ∀ n : ℕ, ((n : ℝ) + 1) ^ K * ‖⟪hermiteFunctionLp ℂ n, g⟫_ℂ‖ ≤ C := by
  constructor
  · rintro ⟨f, rfl⟩ K
    refine ⟨(hermiteNorm K (euclideanFinOneCLE f)).toReal, fun n => ?_⟩
    have h := (hermiteNorm_le_ofReal_iff K (euclideanFinOneCLE f) ENNReal.toReal_nonneg).1
      (ENNReal.ofReal_toReal (hermiteNorm_ne_top K _)).ge n
    rwa [inner_hermiteFunctionLp_toLp]
  · intro h
    set c : (Fin 1 → ℕ) → ℂ := fun α => ⟪hermiteFunctionLp ℂ (α 0), g⟫_ℂ
    have hc : ∀ K, coeffNorm K c ≠ ⊤ := by
      intro K
      obtain ⟨C, hC⟩ := h K
      refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top (iSup_le fun α => ?_)
      rw [← const_apply_zero α, hermiteWeight_const, ← ofReal_norm,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      simpa [c] using hC (α 0)
    refine ⟨euclideanFinOneCLE.symm (hermiteSeries c hc), ?_⟩
    refine (hermiteHilbertBasis ℂ).repr.injective (lp.ext (funext fun n => ?_))
    simp only [hermiteHilbertBasis_repr_apply]
    rw [inner_hermiteFunctionLp_toLp, ContinuousLinearEquiv.apply_symm_apply,
      hermiteCoeff_hermiteSeries]

/-- **Convergence in `𝓢(ℝ)` in terms of Hermite coefficients.** A family of Schwartz functions
`f j` converges to `g` in `𝓢(ℝ)` iff, for every `K`, the weighted supremum
`sup_n (n + 1)^K |⟪ψₙ, f j - g⟫|` tends to zero. -/
theorem tendsto_iff_inner_hermiteFunctionLp {f : α → 𝓢(ℝ, ℂ)} {g : 𝓢(ℝ, ℂ)} :
    Tendsto f l (𝓝 g) ↔ ∀ K : ℕ, ∀ ε > 0, ∀ᶠ j in l, ∀ n : ℕ,
      ((n : ℝ) + 1) ^ K * ‖⟪hermiteFunctionLp ℂ n, (f j - g).toLp 2⟫_ℂ‖ ≤ ε := by
  rw [euclideanFinOneCLE.toHomeomorph.isEmbedding.tendsto_nhds_iff, tendsto_iff_hermiteNorm]
  simp only [ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply, ← map_sub,
    inner_hermiteFunctionLp_toLp]
  refine forall_congr' fun K => ?_
  rw [ENNReal.tendsto_nhds_zero]
  constructor
  · intro h ε hε
    filter_upwards [h _ (ENNReal.ofReal_pos.2 hε)] with j hj
    rwa [← hermiteNorm_le_ofReal_iff K _ hε.le]
  · intro h ε hε
    obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
      rcases eq_or_ne ε ⊤ with rfl | hε'
      · exact ⟨1, one_pos, le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hε', (ENNReal.ofReal_toReal hε').le⟩
    filter_upwards [h δ hδ] with j hj
    refine le_trans ?_ hδε
    rwa [hermiteNorm_le_ofReal_iff K _ hδ.le]

end SchwartzMap
