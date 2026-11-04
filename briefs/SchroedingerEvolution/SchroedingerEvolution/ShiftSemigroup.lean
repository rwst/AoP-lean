/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Multiple equivalent characterizations of the Schrödinger equation: the shift semigroup.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

In infinite dimension the reconstructed past in DR-PROB and DR-INFO cannot be dropped. The right
shifts `(V t f)(x) = f(x - t)` for `x > t`, and `0` otherwise, on `L²(0, ∞)` give an evolution
`Φ t ρ = V t ρ V t†` (`shiftEvolution`) that satisfies `IsEvolution`, maps pure states to pure
states, preserves the Born rule and the von Neumann entropy, but satisfies neither DR-EV nor
DR-UNIT: no pure state evolves into `|e⟩⟨e|` for a unit `e` supported in `(0, t)`.

Setting: `L²(0, ∞)` is the closed subspace `halfLine` of `L²(ℝ)` orthogonal to the indicators of
the sets of finite measure in `(-∞, 0)`, and `V t` is translation by `t` (`translate`), which
maps it into itself for `t ≥ 0`.

Conjugation by an isometry:
* `mapsPure_conj`, `preservesBorn_conj`  conjugation by `V` with `V† V = 1` maps pure states to
  pure states and preserves the Born rule;
* `not_bijOnPure_conj`  it is not a bijection of the pure states if a unit vector is orthogonal
  to the range of `V`.

Continuity in operator norm:
* `tendsto_mul_of_isCompactOperator`  bounded operators `A i` that tend to `0` pointwise tend to
  `0` uniformly on the image of the unit ball of a compact `T`: `A i T → 0` in operator norm;
* `continuousWithinAt_conj`  so for a strongly continuous family of isometries with `V 0 = 1`
  and a compact self-adjoint `ρ`, `t ↦ V t ρ V t†` is continuous at `0⁺` in operator norm.
  Density operators are trace class, hence compact (`IsTraceClass.isCompactOperator`).

The counterexample:
* `isEvolution_shiftEvolution`  `shiftEvolution` satisfies `IsEvolution`;
* `not_drEv_shiftEvolution`, `not_drUnit_shiftEvolution`  but neither DR-EV nor DR-UNIT;
* `shift_semigroup_counterexample`  all of it, with pure states, the Born rule and the entropy
  preserved: DR-PROB and DR-INFO without their reconstructed past.
-/

public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import SchroedingerEvolution.InfiniteDimensional

@[expose] public noncomputable section

namespace SchroedingerEvolution.InfiniteDimensional

open Filter MeasureTheory InnerProductSpace QuantumMechanics QuantumMechanics.Wigner
open UnitaryEntropy ProbabilisticTheory
open scoped ENNReal Topology

/-! ## Conjugation by an isometry -/

section Conj

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {V : E →L[ℂ] E}

lemma norm_map_of_star_mul_self (hV : star V * V = 1) (x : E) : ‖V x‖ = ‖x‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self V).mpr hV x

lemma inner_map_map_of_star_mul_self (hV : star V * V = 1) (x y : E) :
    ⟪V x, V y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self V).mpr hV x y

lemma norm_le_one_of_star_mul_self (hV : star V * V = 1) : ‖V‖ ≤ 1 :=
  V.opNorm_le_bound zero_le_one fun x => by rw [norm_map_of_star_mul_self hV, one_mul]

/-- Conjugation by an isometry maps `|ψ⟩⟨ψ|` to `|V ψ⟩⟨V ψ|`. -/
theorem mapsPure_conj (hV : star V * V = 1) : MapsPure fun ρ => V * ρ * star V :=
  fun ψ hψ => ⟨V ψ, by rw [norm_map_of_star_mul_self hV, hψ], mul_proj_mul_star V ψ⟩

/-- Conjugation by an isometry preserves the Born rule. -/
theorem preservesBorn_conj (hV : star V * V = 1) : PreservesBorn fun ρ => V * ρ * star V := by
  intro ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂
  rw [born_of_norm hψ' hϕ', born_of_norm hψ hϕ, ← norm_inner_sq_eq_of_proj_eq
    ((mul_proj_mul_star V ψ).symm.trans h₁) ((mul_proj_mul_star V ϕ).symm.trans h₂),
    inner_map_map_of_star_mul_self hV]

/-- Conjugation by an isometry is not a bijection of the pure states if a unit vector is
orthogonal to its range: no pure state is sent to `|e⟩⟨e|`. -/
theorem not_bijOnPure_conj (hV : star V * V = 1) {e : E} (he : ‖e‖ = 1)
    (horth : ∀ x, ⟪e, V x⟫_ℂ = 0) : ¬ BijOnPure fun ρ => V * ρ * star V := by
  intro h
  obtain ⟨ρ, ⟨ψ, hψ, rfl⟩, hρ⟩ := h.surjOn ⟨e, he, rfl⟩
  obtain ⟨c, hc, hce⟩ := phaseEq_of_rankOne_self_eq ((norm_map_of_star_mul_self hV ψ).trans hψ)
    he ((mul_proj_mul_star V ψ).symm.trans hρ)
  have h0 := horth ψ
  rw [hce, inner_smul_right, inner_self_eq_norm_sq_to_K, he] at h0
  norm_num at h0
  rw [h0, norm_zero] at hc
  exact zero_ne_one hc

end Conj

/-! ## Continuity in operator norm -/

section Continuity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Bounded operators that tend to `0` pointwise tend to `0` uniformly on the image of the unit
ball of a compact operator `T`, so `A i T` tends to `0` in operator norm. -/
theorem tendsto_mul_of_isCompactOperator {ι : Type*} {l : Filter ι} {A : ι → E →L[ℂ] E}
    {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ᶠ i in l, ‖A i‖ ≤ C) (hA : ∀ x, Tendsto (fun i => A i x) l (𝓝 0))
    {T : E →L[ℂ] E} (hT : IsCompactOperator T) : Tendsto (fun i => A i * T) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK, hTK⟩ := hT.image_closedBall_subset_compact 1
  set δ := ε / (4 * (C + 1)) with hδ_def
  have hδ : 0 < δ := by positivity
  have hCδ : C * δ ≤ ε / 4 := by
    rw [hδ_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨t, ht, hKt⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded δ hδ
  have hev : ∀ᶠ i in l, ∀ y ∈ t, ‖A i y‖ < ε / 2 := (eventually_all_finite ht).2 fun y _ =>
    (tendsto_zero_iff_norm_tendsto_zero.mp (hA y)).eventually (gt_mem_nhds (by positivity))
  filter_upwards [hC, hev] with i hCi hi
  rw [dist_zero_right]
  refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm
    (by positivity : 0 ≤ ε / 4 + ε / 2) fun x hx => ?_) (by linarith)
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp
    (hKt (hTK ⟨x, mem_closedBall_zero_iff.mpr hx.le, rfl⟩))
  have h1 : ‖A i (T x - y)‖ ≤ C * δ :=
    ((A i).le_opNorm _).trans (mul_le_mul hCi (by rw [← dist_eq_norm]; exact
      (Metric.mem_ball.mp hxy).le) (norm_nonneg _) hC₀)
  calc ‖(A i * T) x‖ = ‖A i (T x - y) + A i y‖ := by
        rw [map_sub, sub_add_cancel, mul_apply_eq_comp]
    _ ≤ ‖A i (T x - y)‖ + ‖A i y‖ := norm_add_le _ _
    _ ≤ ε / 4 + ε / 2 := add_le_add (h1.trans hCδ) (hi y hy).le

/-- For a strongly continuous family of isometries with `V 0 = 1` and a compact self-adjoint `ρ`,
`t ↦ V t ρ V t†` is continuous at `0⁺` in operator norm. -/
theorem continuousWithinAt_conj {V : ℝ → E →L[ℂ] E} (hV : ∀ t ≥ 0, star (V t) * V t = 1)
    (hV0 : V 0 = 1) (hc : ∀ x, ContinuousWithinAt (fun t => V t x) (Set.Ici 0) 0)
    {ρ : E →L[ℂ] E} (hρ : IsCompactOperator ρ) (hsa : IsSelfAdjoint ρ) :
    ContinuousWithinAt (fun t => V t * ρ * star (V t)) (Set.Ici 0) 0 := by
  have hA := tendsto_mul_of_isCompactOperator (l := 𝓝[Set.Ici 0] 0) (A := fun t => V t - 1)
    zero_le_two (eventually_nhdsWithin_of_forall fun t ht => (norm_sub_le _ _).trans <| by
      have h1 : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      linarith [norm_le_one_of_star_mul_self (hV t ht)])
    (fun x => by
      simpa [hV0] using (hc x).tendsto.sub (tendsto_const_nhds (x := x))) hρ
  rw [ContinuousWithinAt, hV0, one_mul, star_one, mul_one, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun t ht => ?_)
    (by simpa using (tendsto_zero_iff_norm_tendsto_zero.mp hA).const_mul 2)
  have hn : ‖star (V t)‖ ≤ 1 := by rw [norm_star]; exact norm_le_one_of_star_mul_self (hV t ht)
  have he : V t * ρ * star (V t) - ρ = (V t - 1) * ρ * star (V t) + star ((V t - 1) * ρ) := by
    rw [star_mul, hsa.star_eq, star_sub, star_one]
    noncomm_ring
  rw [he]
  calc ‖(V t - 1) * ρ * star (V t) + star ((V t - 1) * ρ)‖
      ≤ ‖(V t - 1) * ρ‖ * ‖star (V t)‖ + ‖(V t - 1) * ρ‖ :=
        (norm_add_le _ _).trans (by rw [norm_star]; gcongr; exact norm_mul_le _ _)
    _ ≤ ‖(V t - 1) * ρ‖ * 1 + ‖(V t - 1) * ρ‖ := by gcongr
    _ = 2 * ‖(V t - 1) * ρ‖ := by ring

end Continuity

/-! ## The shift semigroup on `L²(0, ∞)` -/

section Shift

/-- `2 ≠ ∞`, for the continuity of translation on `L²`. -/
theorem fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩

attribute [local instance] fact_two_ne_top

/-- Translation by `c` on `L²(ℝ)`, `(translate c f)(x) = f(x - c)`. -/
def translate (c : ℝ) : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := DomAddAct.mk (-c) +ᵥ f
  invFun f := DomAddAct.mk c +ᵥ f
  map_add' := DomAddAct.vadd_Lp_add _
  map_smul' a f := by rcases f with ⟨⟨_⟩, _⟩; rfl
  left_inv f := by
    change DomAddAct.mk c +ᵥ DomAddAct.mk (-c) +ᵥ f = f
    rw [← vadd_assoc, vadd_eq_add, ← DomAddAct.mk_add, neg_add_cancel, DomAddAct.mk_zero,
      zero_vadd]
  right_inv f := by
    change DomAddAct.mk (-c) +ᵥ DomAddAct.mk c +ᵥ f = f
    rw [← vadd_assoc, vadd_eq_add, ← DomAddAct.mk_add, add_neg_cancel, DomAddAct.mk_zero,
      zero_vadd]
  norm_map' := DomAddAct.norm_vadd_Lp _

lemma translate_apply (c : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    translate c f = DomAddAct.mk (-c) +ᵥ f :=
  rfl

lemma translate_zero (f : Lp ℂ 2 (volume : Measure ℝ)) : translate 0 f = f := by
  rw [translate_apply, neg_zero, DomAddAct.mk_zero, zero_vadd]

lemma translate_add (s t : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    translate (s + t) f = translate s (translate t f) := by
  rw [translate_apply, translate_apply, translate_apply, ← vadd_assoc, vadd_eq_add,
    ← DomAddAct.mk_add, neg_add_rev]

lemma translate_translate_neg (c : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    translate c (translate (-c) f) = f := by
  rw [← translate_add, add_neg_cancel, translate_zero]

lemma continuous_translate (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Continuous fun c => translate c f :=
  (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

lemma inner_translate_right (c : ℝ) (f g : Lp ℂ 2 (volume : Measure ℝ)) :
    ⟪g, translate c f⟫_ℂ = ⟪translate (-c) g, f⟫_ℂ := by
  conv_lhs => rw [← translate_translate_neg c g]
  exact (translate c).inner_map_map _ _

/-- The indicators of the sets of finite measure in `(-∞, 0)`. -/
def negIndicators : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {g | ∃ (s : Set ℝ) (hs : MeasurableSet s) (hμ : volume s ≠ ∞), s ⊆ Set.Iio 0 ∧
    g = indicatorConstLp 2 hs hμ (1 : ℂ)}

/-- `L²(0, ∞)`: the functions of `L²(ℝ)` orthogonal to every indicator of a set of finite measure
in `(-∞, 0)`, that is, vanishing almost everywhere on `(-∞, 0)`. -/
def halfLine : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  (Submodule.span ℂ negIndicators)ᗮ

instance : CompleteSpace halfLine :=
  Submodule.instOrthogonalCompleteSpace _

lemma mem_halfLine {f : Lp ℂ 2 (volume : Measure ℝ)} :
    f ∈ halfLine ↔ ∀ g ∈ negIndicators, ⟪g, f⟫_ℂ = 0 := by
  refine ⟨fun hf g hg => Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hg) hf,
    fun h => (Submodule.mem_orthogonal _ f).mpr fun u hu => ?_⟩
  induction hu using Submodule.span_induction with
  | mem g hg => exact h g hg
  | zero => exact inner_zero_left _
  | add u v _ _ hu hv => rw [inner_add_left, hu, hv, add_zero]
  | smul a u _ hu => rw [inner_smul_left, hu, mul_zero]

/-- Translation by `c` sends a function of `L²(0, ∞)` to one orthogonal to the indicators of
the sets in `(-∞, c)`. -/
lemma inner_indicatorConstLp_translate {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ∈ halfLine)
    {c : ℝ} {s : Set ℝ} (hs : MeasurableSet s) (hμ : volume s ≠ ∞) (hsub : s ⊆ Set.Iio c) :
    ⟪indicatorConstLp 2 hs hμ (1 : ℂ), translate c f⟫_ℂ = 0 := by
  rw [inner_translate_right, translate_apply, neg_neg, DomAddAct.mk_vadd_indicatorConstLp]
  refine mem_halfLine.mp hf _ ⟨_, _, _, fun x hx => ?_, rfl⟩
  have := hsub hx
  simp only [Set.mem_Iio, vadd_eq_add] at this ⊢
  linarith

lemma translate_mem_halfLine {f : Lp ℂ 2 (volume : Measure ℝ)} (hf : f ∈ halfLine) {c : ℝ}
    (hc : 0 ≤ c) : translate c f ∈ halfLine := by
  rw [mem_halfLine]
  rintro _ ⟨s, hs, hμ, hsub, rfl⟩
  exact inner_indicatorConstLp_translate hf hs hμ fun x hx => (hsub hx).trans_le hc

/-- `L²(0, ∞)` as a type, with only the normed structure of `halfLine`: on the subtype, the
subtype topology and the normed one do not unify when instances are synthesized. -/
def HalfLine : Type := halfLine

instance : NormedAddCommGroup HalfLine := inferInstanceAs (NormedAddCommGroup halfLine)

instance : InnerProductSpace ℂ HalfLine := inferInstanceAs (InnerProductSpace ℂ halfLine)

instance : CompleteSpace HalfLine := inferInstanceAs (CompleteSpace halfLine)

namespace HalfLine

/-- The underlying function in `L²(ℝ)`. -/
def val (x : HalfLine) : Lp ℂ 2 (volume : Measure ℝ) := Subtype.val (x : ↥halfLine)

/-- A function of `L²(ℝ)` vanishing on `(-∞, 0)`, as an element of `L²(0, ∞)`. -/
def mk (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ∈ halfLine) : HalfLine :=
  (⟨f, hf⟩ : ↥halfLine)

lemma val_mem (x : HalfLine) : x.val ∈ halfLine := (x : ↥halfLine).2

lemma val_mk (f : Lp ℂ 2 (volume : Measure ℝ)) (hf : f ∈ halfLine) : (mk f hf).val = f := rfl

lemma ext {x y : HalfLine} (h : x.val = y.val) : x = y := Subtype.ext h

lemma norm_val (x : HalfLine) : ‖x.val‖ = ‖x‖ := rfl

lemma inner_val (x y : HalfLine) : ⟪x.val, y.val⟫_ℂ = ⟪x, y⟫_ℂ := rfl

end HalfLine

/-- The right shift by `t ≥ 0` on `L²(0, ∞)`, as a linear isometry; negative `t` are treated as
`0`. -/
def rightShiftₗᵢ (t : ℝ) : HalfLine →ₗᵢ[ℂ] HalfLine where
  toFun x := .mk (translate (max t 0) x.val) (translate_mem_halfLine x.val_mem (le_max_right t 0))
  map_add' x y := HalfLine.ext (map_add (translate (max t 0)) x.val y.val)
  map_smul' a x := HalfLine.ext (map_smul (translate (max t 0)) a x.val)
  norm_map' x := (translate (max t 0)).norm_map x.val

/-- The right shift by `t ≥ 0` on `L²(0, ∞)`. -/
def rightShift (t : ℝ) : HalfLine →L[ℂ] HalfLine :=
  (rightShiftₗᵢ t).toContinuousLinearMap

lemma val_rightShift (t : ℝ) (x : HalfLine) :
    (rightShift t x).val = translate (max t 0) x.val :=
  rfl

lemma star_rightShift_mul_self (t : ℝ) : star (rightShift t) * rightShift t = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (rightShiftₗᵢ t).norm_map

lemma rightShift_zero : rightShift 0 = 1 := by
  ext1 x
  exact HalfLine.ext (by rw [val_rightShift, max_self, translate_zero]; rfl)

lemma rightShift_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    rightShift (s + t) = rightShift s * rightShift t := by
  ext1 x
  refine HalfLine.ext ?_
  rw [mul_apply_eq_comp, val_rightShift, val_rightShift, val_rightShift,
    max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht, translate_add]

lemma continuousWithinAt_rightShift (x : HalfLine) :
    ContinuousWithinAt (fun t => rightShift t x) (Set.Ici 0) 0 := by
  have h : Continuous fun t : ℝ => translate (max t 0) x.val :=
    (continuous_translate _).comp (continuous_id.max continuous_const)
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  exact (tendsto_iff_norm_sub_tendsto_zero.mp (h.tendsto 0)).mono_left nhdsWithin_le_nhds

/-- For `t > 0`, a unit vector of `L²(0, ∞)` orthogonal to the range of the shift by `t`: the
normalized indicator of `(0, t)`. -/
lemma exists_unit_orthogonal_rightShift {t : ℝ} (ht : 0 < t) :
    ∃ e : HalfLine, ‖e‖ = 1 ∧ ∀ x, ⟪e, rightShift t x⟫_ℂ = 0 := by
  have hμ : volume (Set.Ioo 0 t) ≠ ∞ := measure_Ioo_lt_top.ne
  set u := indicatorConstLp 2 measurableSet_Ioo hμ (1 : ℂ)
  have hu : u ∈ halfLine := by
    rw [mem_halfLine]
    rintro _ ⟨s, hs, hμs, hsub, rfl⟩
    have hd : s ∩ Set.Ioo 0 t = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => (hsub hx.1).not_ge hx.2.1.le
    rw [L2.inner_indicatorConstLp_indicatorConstLp, hd, measureReal_empty, zero_smul]
  have hu0 : u ≠ 0 := by
    intro h
    have := L2.inner_indicatorConstLp_indicatorConstLp (𝕜 := ℂ) measurableSet_Ioo
      measurableSet_Ioo hμ hμ (1 : ℂ) 1
    rw [← show u = indicatorConstLp 2 measurableSet_Ioo hμ (1 : ℂ) from rfl, h, inner_zero_left,
      Set.inter_self, Real.volume_real_Ioo_of_le ht.le, inner_self_eq_norm_sq_to_K] at this
    norm_num at this
    exact ht.ne' (by exact_mod_cast this.symm)
  set c : ℂ := ((‖u‖⁻¹ : ℝ) : ℂ)
  refine ⟨.mk (c • u) (halfLine.smul_mem c hu), ?_, fun x => ?_⟩
  · rw [← HalfLine.norm_val, HalfLine.val_mk, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu0)
  · rw [← HalfLine.inner_val, HalfLine.val_mk, val_rightShift, max_eq_left ht.le,
      inner_smul_left, inner_indicatorConstLp_translate x.val_mem measurableSet_Ioo hμ
        fun y hy => hy.2, mul_zero]

/-- The evolution of the shift semigroup, `Φ t ρ = V t ρ V t†`. -/
def shiftEvolution (t : ℝ) (ρ : HalfLine →L[ℂ] HalfLine) : HalfLine →L[ℂ] HalfLine :=
  rightShift t * ρ * star (rightShift t)

/-- The shift semigroup is an evolution: `Φ t` maps density operators affinely to density
operators, `Φ 0 = id`, `Φ (s + t) = Φ s ∘ Φ t`, and `t ↦ Φ t ρ` is continuous at `0⁺` in
operator norm, since density operators are compact. -/
theorem isEvolution_shiftEvolution : IsEvolution shiftEvolution where
  isDensityOperator t _ ρ hρ := hρ.conj (star_rightShift_mul_self t)
  affine t _ ρ σ _ _ s _ _ := by
    simp only [shiftEvolution, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  map_zero ρ _ := by rw [shiftEvolution, rightShift_zero, one_mul, star_one, mul_one]
  map_add s hs t ht ρ _ := by
    simp only [shiftEvolution, rightShift_add hs ht, star_mul, mul_assoc]
  continuousWithinAt ρ hρ := continuousWithinAt_conj (fun t _ => star_rightShift_mul_self t)
    rightShift_zero continuousWithinAt_rightShift hρ.isTraceClass.isCompactOperator
    hρ.isSelfAdjoint

/-- The shift semigroup does not satisfy DR-EV: for `t > 0`, no pure state evolves into the
normalized indicator of `(0, t)`. -/
theorem not_drEv_shiftEvolution : ¬ DrEv shiftEvolution := fun h => by
  obtain ⟨e, he, horth⟩ := exists_unit_orthogonal_rightShift one_pos
  exact not_bijOnPure_conj (star_rightShift_mul_self 1) he horth (h 1 zero_le_one)

/-- The shift semigroup does not satisfy DR-UNIT, which would imply DR-EV. -/
theorem not_drUnit_shiftEvolution : ¬ DrUnit shiftEvolution := fun h =>
  not_drEv_shiftEvolution (h.drEv isEvolution_shiftEvolution)

/-- **The reconstructed past is needed in infinite dimension.** The shift semigroup on
`L²(0, ∞)` is an evolution whose maps send pure states to pure states and preserve the Born rule
and the von Neumann entropy, so it satisfies DR-PROB and DR-INFO without their reconstructed
past, but it satisfies neither DR-EV nor DR-UNIT. -/
theorem shift_semigroup_counterexample :
    IsEvolution shiftEvolution ∧
      (∀ t ≥ 0, MapsPure (shiftEvolution t) ∧ PreservesBorn (shiftEvolution t) ∧
        ∀ ρ, IsDensityOperator ρ →
          vonNeumannEntropy (shiftEvolution t ρ) = vonNeumannEntropy ρ) ∧
      ¬ DrEv shiftEvolution ∧ ¬ DrUnit shiftEvolution :=
  ⟨isEvolution_shiftEvolution, fun t _ => ⟨mapsPure_conj (star_rightShift_mul_self t),
    preservesBorn_conj (star_rightShift_mul_self t),
    fun _ hρ => hρ.vonNeumannEntropy_conj (star_rightShift_mul_self t)⟩,
    not_drEv_shiftEvolution, not_drUnit_shiftEvolution⟩

end Shift

end SchroedingerEvolution.InfiniteDimensional
