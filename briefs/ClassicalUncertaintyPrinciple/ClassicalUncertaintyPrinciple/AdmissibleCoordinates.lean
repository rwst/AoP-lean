/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ClassicalUncertaintyPrinciple.InfiniteEntropy
public import ForMathlib.Analysis.Calculus.InverseFunctionTheorem.Global

/-!
# Classical uncertainty relation: admissible coordinates

Definition 2 of the brief *Classical uncertainty relation* calls a coordinate transformation
`T = (f, g)` admissible for `ρ` if it is a `C¹` diffeomorphism of the plane onto an open region
`U`, with `C¹` inverse, and `E[|ln J_T|] < ∞` for the absolute Jacobian determinant
`J_T = |det DT|`. `ClassicalUncertaintyPrinciple.IsAdmissible` asks only for `C¹` coordinates,
injectivity and a nowhere vanishing Jacobian `{f, g} = det DT`; by the global inverse function
theorem (`ContDiff.exists_contDiffOn_leftInverse_of_det_ne_zero`) these give the rest, and the
two definitions agree (`ClassicalUncertaintyPrinciple.isAdmissible_iff`). The range `U` is open
and connected, and the inverse is `Cⁿ` when `f` and `g` are.

The remark *Bounded coordinate ranges* says that bounded coordinate ranges keep every point of
phase space, through an invertible map; that their boundedness holds for every distribution
once the coordinates are fixed; and that the integrability of the logarithmic Jacobian is checked
for the ensemble under consideration. The coordinates `(Φ(q), Φ(p))`, with `Φ(u) = ∫₀ᵘ φ` for
the standard Gaussian density `φ`, show all three: their range is bounded, and they are a `C¹`
diffeomorphism of the plane onto it; every probability density has finite variances in them,
as in any bounded coordinates; and their Jacobian is `φ(q) φ(p)`, so they are admissible for `ρ`
exactly when `E[q² + p²] < ∞`: for the standard Gaussian, but not for the product of two Cauchy
densities.

## Main results

* `ClassicalUncertaintyPrinciple.isAdmissible_iff`: Definition 2 in the brief's form;
  `ClassicalUncertaintyPrinciple.exists_contDiffOn_leftInverse_of_poissonBracket_ne_zero`: its
  coordinate part, for `Cⁿ` coordinates.
* `ClassicalUncertaintyPrinciple.integrable_sq_mul_of_isBounded_range`: bounded coordinates have
  finite variances for every probability density.
* `ClassicalUncertaintyPrinciple.isAdmissible_gaussPrim_iff`: the coordinates `(Φ(q), Φ(p))` are
  admissible for `ρ` iff `E[q² + p²] < ∞`.
* `ClassicalUncertaintyPrinciple.exists_coordinates_isBounded_range`: the remark *Bounded
  coordinate ranges*.
-/

@[expose] public section

open Real MeasureTheory Set Function Topology ProbabilityTheory

open scoped NNReal

namespace ClassicalUncertaintyPrinciple

variable {ρ f g : ℝ × ℝ → ℝ}

/-! ### Definition 2 -/

section Definition2

lemma det_fderiv_prodMk (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    (fderiv ℝ (fun x => (f x, g x)) x).det = poissonBracket f g x :=
  (poissonBracket_eq_det (hf.prodMk hg) x).symm

/-- **Definition 2, the coordinates.** `Cⁿ` coordinates `(f, g)`, `n ≠ 0`, with
`(q, p) ↦ (f, g)` injective and `{f, g} ≠ 0` everywhere are a `Cⁿ` diffeomorphism of the plane
onto an open region: the range is open and connected, and has a `Cⁿ` inverse on it. -/
theorem exists_contDiffOn_leftInverse_of_poissonBracket_ne_zero {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (hn : n ≠ 0)
    (hinj : Injective fun x => (f x, g x)) (hpb : ∀ x, poissonBracket f g x ≠ 0) :
    IsOpen (range fun x => (f x, g x)) ∧ IsConnected (range fun x => (f x, g x)) ∧
      ∃ S : ℝ × ℝ → ℝ × ℝ, ContDiffOn ℝ n S (range fun x => (f x, g x)) ∧
        LeftInverse S fun x => (f x, g x) := by
  have hT := hf.prodMk hg
  obtain ⟨hU, hS⟩ := hT.exists_contDiffOn_leftInverse_of_det_ne_zero hn (fun x => by
    rw [det_fderiv_prodMk (hf.differentiable hn) (hg.differentiable hn)]
    exact hpb x) hinj
  exact ⟨hU, isConnected_range hT.continuous, hS⟩

/-- Admissible coordinates have an open range. -/
theorem IsAdmissible.isOpen_range (H : IsAdmissible ρ f g) :
    IsOpen (range fun x => (f x, g x)) :=
  (exists_contDiffOn_leftInverse_of_poissonBracket_ne_zero H.contDiff_fst H.contDiff_snd
    one_ne_zero H.injective H.poissonBracket_ne_zero).1

/-- Admissible coordinates have a `C¹` inverse on their range. -/
theorem IsAdmissible.exists_contDiffOn_leftInverse (H : IsAdmissible ρ f g) :
    ∃ S : ℝ × ℝ → ℝ × ℝ, ContDiffOn ℝ 1 S (range fun x => (f x, g x)) ∧
      LeftInverse S fun x => (f x, g x) :=
  (exists_contDiffOn_leftInverse_of_poissonBracket_ne_zero H.contDiff_fst H.contDiff_snd
    one_ne_zero H.injective H.poissonBracket_ne_zero).2.2

/-- **Definition 2** in the brief's form: `(f, g)` is admissible for `ρ` iff `T = (f, g)` is a
`C¹` diffeomorphism of the plane onto an open region, with `C¹` inverse, and
`E[|ln |det DT||] < ∞`. -/
theorem isAdmissible_iff : IsAdmissible ρ f g ↔
    ContDiff ℝ 1 (fun x => (f x, g x)) ∧ IsOpen (range fun x => (f x, g x)) ∧
      IsConnected (range fun x => (f x, g x)) ∧
      (∃ S : ℝ × ℝ → ℝ × ℝ, ContDiffOn ℝ 1 S (range fun x => (f x, g x)) ∧
        LeftInverse S fun x => (f x, g x)) ∧
      Integrable fun x => ρ x * log |(fderiv ℝ (fun x => (f x, g x)) x).det| := by
  constructor
  · intro H
    obtain ⟨hU, hc, hS⟩ := exists_contDiffOn_leftInverse_of_poissonBracket_ne_zero
      H.contDiff_fst H.contDiff_snd one_ne_zero H.injective H.poissonBracket_ne_zero
    refine ⟨H.contDiff_fst.prodMk H.contDiff_snd, hU, hc, hS, ?_⟩
    simp_rw [det_fderiv_prodMk (H.contDiff_fst.differentiable one_ne_zero)
      (H.contDiff_snd.differentiable one_ne_zero)]
    exact H.integrable_log
  · rintro ⟨hT, hU, -, ⟨S, hS, hST⟩, hi⟩
    have hf : ContDiff ℝ 1 f := contDiff_fst.comp hT
    have hg : ContDiff ℝ 1 g := contDiff_snd.comp hT
    have hdet : ∀ x, (fderiv ℝ (fun x => (f x, g x)) x).det = poissonBracket f g x :=
      det_fderiv_prodMk (hf.differentiable one_ne_zero) (hg.differentiable one_ne_zero)
    refine ⟨hf, hg, hST.injective, fun x => ?_, ?_⟩
    · rw [← hdet]
      exact det_fderiv_ne_zero_of_leftInverse (hT.differentiable one_ne_zero x)
        ((hS.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds (mem_range_self x))) hST
    · simpa only [hdet] using hi

end Definition2

/-! ### Bounded coordinate ranges -/

section Bounded

lemma integrable_sq_mul_of_abs_le (hρ : IsDensity ρ) (hf : Measurable f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) : Integrable fun x => f x ^ 2 * ρ x :=
  (hρ.integrable.const_mul (M ^ 2)).mono' ((hf.pow_const 2).aestronglyMeasurable.mul
    hρ.integrable.1) (ae_of_all _ fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρ.nonneg x)), ← sq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM x) 2) (hρ.nonneg x))

/-- **Bounded coordinate ranges**, the variances. In coordinates with a bounded range, every
probability density has finite variances. -/
theorem integrable_sq_mul_of_isBounded_range (hρ : IsDensity ρ) (hf : Measurable f)
    (hg : Measurable g) (hb : Bornology.IsBounded (range fun x => (f x, g x))) :
    (Integrable fun x => f x ^ 2 * ρ x) ∧ Integrable fun x => g x ^ 2 * ρ x := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  have h := fun x => hC _ (mem_range_self x)
  exact ⟨integrable_sq_mul_of_abs_le hρ hf fun x => (norm_fst_le _).trans (h x),
    integrable_sq_mul_of_abs_le hρ hg fun x => (norm_snd_le _).trans (h x)⟩

lemma contDiff_gaussPrim_comp_fst : ContDiff ℝ 1 fun x : ℝ × ℝ => gaussPrim x.1 :=
  contDiff_gaussPrim.comp contDiff_fst

lemma contDiff_gaussPrim_comp_snd : ContDiff ℝ 1 fun x : ℝ × ℝ => gaussPrim x.2 :=
  contDiff_gaussPrim.comp contDiff_snd

lemma injective_gaussPrim_prodMap :
    Injective fun x : ℝ × ℝ => (gaussPrim x.1, gaussPrim x.2) := fun x y hxy => by
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext (strictMono_gaussPrim.injective hxy.1) (strictMono_gaussPrim.injective hxy.2)

lemma isBounded_range_gaussPrim_prodMap :
    Bornology.IsBounded (range fun x : ℝ × ℝ => (gaussPrim x.1, gaussPrim x.2)) :=
  isBounded_iff_forall_norm_le.2 ⟨1, by
    rintro _ ⟨x, rfl⟩
    exact norm_prod_le_iff.2 ⟨abs_gaussPrim_le _, abs_gaussPrim_le _⟩⟩

/-- The Jacobian of `(Φ(q), Φ(p))` is `φ(q) φ(p)`. -/
lemma poissonBracket_gaussPrim (x : ℝ × ℝ) :
    poissonBracket (fun x => gaussPrim x.1) (fun x => gaussPrim x.2) x = gaussProd 0 1 0 1 x := by
  have h1 : HasFDerivAt (fun x : ℝ × ℝ => gaussPrim x.1)
      (gaussianPDFReal 0 1 x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (hasDerivAt_gaussPrim _).comp_hasFDerivAt x hasFDerivAt_fst
  have h2 : HasFDerivAt (fun x : ℝ × ℝ => gaussPrim x.2)
      (gaussianPDFReal 0 1 x.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) x :=
    (hasDerivAt_gaussPrim _).comp_hasFDerivAt x hasFDerivAt_snd
  rw [poissonBracket, h1.fderiv, h2.fderiv]
  simp [gaussProd]

/-- **Bounded coordinate ranges**, admissibility. The coordinates `(Φ(q), Φ(p))` are admissible
for a probability density `ρ` iff `E[q² + p²] < ∞`. -/
theorem isAdmissible_gaussPrim_iff (hρ : IsDensity ρ) :
    IsAdmissible ρ (fun x => gaussPrim x.1) (fun x => gaussPrim x.2) ↔
      Integrable fun x => (x.1 ^ 2 + x.2 ^ 2) * ρ x := by
  have key : ∀ x, ρ x * log |poissonBracket (fun x => gaussPrim x.1)
      (fun x => gaussPrim x.2) x| = -log (2 * π) * ρ x - (x.1 ^ 2 + x.2 ^ 2) * ρ x / 2 :=
    fun x => by
      rw [poissonBracket_gaussPrim, abs_of_pos (gaussProd_pos one_ne_zero one_ne_zero x),
        log_gaussProd_zero_one]
      ring
  constructor
  · intro H
    refine (((hρ.integrable.const_mul (-log (2 * π))).sub H.integrable_log).const_mul 2).congr
      (ae_of_all _ fun x => ?_)
    simp only [Pi.sub_apply, key]
    ring
  · intro hi
    refine ⟨contDiff_gaussPrim_comp_fst, contDiff_gaussPrim_comp_snd,
      injective_gaussPrim_prodMap, fun x => ?_, ?_⟩
    · rw [poissonBracket_gaussPrim]
      exact (gaussProd_pos one_ne_zero one_ne_zero x).ne'
    · exact ((hρ.integrable.const_mul (-log (2 * π))).sub (hi.div_const 2)).congr
        (ae_of_all _ fun x => (key x).symm)

/-- **Bounded coordinate ranges.** The coordinates `(Φ(q), Φ(p))` have a bounded range, and are
a `C¹` diffeomorphism of the plane onto it, with no reference to a distribution: they keep every
point of phase space. Every probability density has finite variances in them. Admissibility,
the integrability of the logarithmic Jacobian, depends on the ensemble: they are admissible for
the standard Gaussian, but not for the product of two standard Cauchy densities. -/
theorem exists_coordinates_isBounded_range :
    ∃ f g : ℝ × ℝ → ℝ, Bornology.IsBounded (range fun x => (f x, g x)) ∧
      ContDiff ℝ 1 f ∧ ContDiff ℝ 1 g ∧ IsOpen (range fun x => (f x, g x)) ∧
      (∃ S : ℝ × ℝ → ℝ × ℝ, ContDiffOn ℝ 1 S (range fun x => (f x, g x)) ∧
        LeftInverse S fun x => (f x, g x)) ∧
      (∀ ρ : ℝ × ℝ → ℝ, IsDensity ρ →
        (Integrable fun x => f x ^ 2 * ρ x) ∧ Integrable fun x => g x ^ 2 * ρ x) ∧
      ∃ ρ₁ ρ₂ : ℝ × ℝ → ℝ, IsEnsemble ρ₁ ∧ IsEnsemble ρ₂ ∧ IsAdmissible ρ₁ f g ∧
        ¬IsAdmissible ρ₂ f g := by
  have hc := contDiff_gaussPrim_comp_fst
  have hd := contDiff_gaussPrim_comp_snd
  have hpb : ∀ x, poissonBracket (fun x => gaussPrim x.1) (fun x => gaussPrim x.2) x ≠ 0 :=
    fun x => by
      rw [poissonBracket_gaussPrim]
      exact (gaussProd_pos one_ne_zero one_ne_zero x).ne'
  obtain ⟨hU, -, hS⟩ := exists_contDiffOn_leftInverse_of_poissonBracket_ne_zero hc hd
    one_ne_zero injective_gaussPrim_prodMap hpb
  obtain ⟨ρ₂, hρ₂, hq, -⟩ := exists_isEnsemble_extendedVar_eq_top
  have hG := isEnsemble_gaussProd (a := 0) (b := 0) (v := 1) (w := 1) one_ne_zero one_ne_zero
  refine ⟨_, _, isBounded_range_gaussPrim_prodMap, hc, hd, hU, hS, fun ρ hρ =>
    integrable_sq_mul_of_isBounded_range hρ hc.continuous.measurable hd.continuous.measurable
      isBounded_range_gaussPrim_prodMap, _, ρ₂, hG, hρ₂,
    (isAdmissible_gaussPrim_iff hG.isDensity).2 ?_, fun H => ?_⟩
  · refine ((integrable_fst_sub_sq_mul_gaussProd (a := 0) (b := 0) (w := 1) one_ne_zero 0).add
      (integrable_snd_sub_sq_mul_gaussProd (a := 0) (b := 0) (v := 1) one_ne_zero 0)).congr
      (ae_of_all _ fun x => ?_)
    simp only [Pi.add_apply, sub_zero]
    ring
  · have hi := (isAdmissible_gaussPrim_iff hρ₂.isDensity).1 H
    refine (extendedVar_eq_top_iff hρ₂.isDensity measurable_fst).1 hq (hi.mono'
      ((measurable_fst.pow_const 2).aestronglyMeasurable.mul hρ₂.isDensity.integrable.1)
      (ae_of_all _ fun x => ?_))
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hρ₂.nonneg x))]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (hρ₂.nonneg x)

end Bounded

end ClassicalUncertaintyPrinciple
