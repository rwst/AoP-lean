/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Other state spaces

Non-uniqueness of the moment problem for Schwartz functions, Sec. 3: "Consequently any space that
contains functions with compact support will suffer the same consequences."

The argument of the brief uses nothing about `𝓢(ℝ)` beyond two nonzero functions with disjoint
supports and operators that do not enlarge supports. So it is stated here for any space `V` of
functions on any domain `D`, given as a linear map `ev : V →ₗ[ℂ] D → ℂ` (not necessarily
injective), any measure on `D`, and any operator `A` on `V` that is local in Peetre's sense:
* `localOps ev`  the local operators form a subalgebra;
* `integrand_psi`  for local `A` and disjointly supported `f, g`, the integrand of
  `⟨ψ_θ|A|ψ_θ⟩` is that of `⟨f|A|f⟩ + ⟨g|A|g⟩`, pointwise, so it does not depend on `θ`;
* `matrixElement_psi_eq`  hence `⟨ψ_θ|A|ψ_θ⟩ = ⟨ψ_θ'|A|ψ_θ'⟩`, with no integrability hypothesis;
* `linearIndependent_psi`  while `ψ_θ, ψ_θ'` are linearly independent for `e^{iθ} ≠ e^{iθ'}`.

What the brief's sentence needs is two nonzero functions with disjoint supports; compact support
is neither needed nor, for a single function, enough (in the span of one bump every state is the
same ray). A space on a nontrivial normed space that contains one nonzero function with compact
support and is closed under translations has two (`exists_disjoint_translate`), and suffers
the same consequences (`exists_same_matrixElements_of_translate`).

The instance: `𝓢(E, ℂ)` on any nontrivial finite-dimensional real inner product space `E`, e.g.
`ℝⁿ` with `n ≥ 1`, with positions `X ℓ` (multiplication by a linear functional `ℓ`) and momenta
`P ħ v = -iħ ∂_v`. Every polynomial in them is local (`adjoin_le_localOps`), and there are two
linearly independent states on which all of them have the same expectation values
(`exists_same_moments`), Theorem 1 of the brief in `n` dimensions.
-/

open Complex ComplexConjugate MeasureTheory SchwartzMap LineDeriv

@[expose] public noncomputable section

namespace SchwartzMomentProblem.OtherSpaces

section General

variable {D : Type*} [TopologicalSpace D] {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ev : V →ₗ[ℂ] D → ℂ)

/-- `A` is local (Peetre): `supp (Aφ) ⊆ supp φ` for every `φ`. -/
def IsLocal (A : Module.End ℂ V) : Prop := ∀ φ, tsupport (ev (A φ)) ⊆ tsupport (ev φ)

/-- The local operators form a subalgebra. -/
def localOps : Subalgebra ℂ (Module.End ℂ V) where
  carrier := {A | IsLocal ev A}
  mul_mem' {A B} hA hB φ := (hA (B φ)).trans (hB φ)
  add_mem' {A B} hA hB φ := by
    change tsupport (ev (A φ + B φ)) ⊆ _
    rw [map_add]
    exact (tsupport_add _ _).trans (Set.union_subset (hA φ) (hB φ))
  algebraMap_mem' c φ := by
    change tsupport (ev (c • φ)) ⊆ _
    rw [map_smul]
    exact tsupport_smul_subset_right (fun _ => c) (ev φ)

lemma mem_localOps {A : Module.End ℂ V} : A ∈ localOps ev ↔ IsLocal ev A := Iff.rfl

/-- `ψ_θ = f + e^{iθ} g`. -/
def psi (f g : V) (θ : ℝ) : V := f + exp (θ * I) • g

variable {ev} {f g : V}

/-- A local operator has no matrix elements between disjointly supported functions,
pointwise: `conj (f x) · (Ag)(x) = 0`. -/
lemma conj_mul_eq_zero {A : Module.End ℂ V} (hA : IsLocal ev A)
    (hfg : Disjoint (tsupport (ev f)) (tsupport (ev g))) (x : D) :
    conj (ev f x) * ev (A g) x = 0 := by
  by_cases hx : ev f x = 0
  · simp [hx]
  · rw [image_eq_zero_of_notMem_tsupport fun h =>
      hfg.notMem_of_mem_left (subset_tsupport _ hx) (hA g h), mul_zero]

/-- For a local `A`, the integrand of `⟨ψ_θ|A|ψ_θ⟩` is that of `⟨f|A|f⟩ + ⟨g|A|g⟩`. -/
theorem integrand_psi {A : Module.End ℂ V} (hA : IsLocal ev A)
    (hfg : Disjoint (tsupport (ev f)) (tsupport (ev g))) (θ : ℝ) (x : D) :
    conj (ev (psi f g θ) x) * ev (A (psi f g θ)) x =
      conj (ev f x) * ev (A f) x + conj (ev g x) * ev (A g) x := by
  have h1 := conj_mul_eq_zero hA hfg x
  have h2 := conj_mul_eq_zero hA hfg.symm x
  have hc : conj (exp (θ * I)) * exp (θ * I) = 1 := by
    rw [conj_mul', norm_exp_ofReal_mul_I]
    simp
  simp only [psi, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination exp (θ * I) * h1 + conj (exp (θ * I)) * h2 +
    conj (ev g x) * ev (A g) x * hc

/-- No local operator detects the phase: `⟨ψ_θ|A|ψ_θ⟩ = ⟨ψ_θ'|A|ψ_θ'⟩` for every measure on the
domain. The integrands agree, so no integrability is needed. -/
theorem matrixElement_psi_eq [MeasurableSpace D] (μ : Measure D) {A : Module.End ℂ V}
    (hA : IsLocal ev A) (hfg : Disjoint (tsupport (ev f)) (tsupport (ev g))) (θ θ' : ℝ) :
    ∫ x, conj (ev (psi f g θ) x) * ev (A (psi f g θ)) x ∂μ =
      ∫ x, conj (ev (psi f g θ') x) * ev (A (psi f g θ')) x ∂μ := by
  simp only [integrand_psi hA hfg]

/-- Different phases give linearly independent states, hence different rays. -/
theorem linearIndependent_psi (hf0 : ev f ≠ 0) (hg0 : ev g ≠ 0)
    (hfg : Disjoint (tsupport (ev f)) (tsupport (ev g))) {θ θ' : ℝ}
    (hθ : exp (θ * I) ≠ exp (θ' * I)) : LinearIndependent ℂ ![psi f g θ, psi f g θ'] := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, ev f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf0 (funext h)
  obtain ⟨y₀, hy₀⟩ : ∃ y, ev g y ≠ 0 := by
    by_contra h
    push Not at h
    exact hg0 (funext h)
  have hgx : ev g x₀ = 0 := image_eq_zero_of_notMem_tsupport
    (hfg.notMem_of_mem_left (subset_tsupport _ hx₀))
  have hfy : ev f y₀ = 0 := image_eq_zero_of_notMem_tsupport
    (hfg.symm.notMem_of_mem_left (subset_tsupport _ hy₀))
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have e := congrArg ev hst
  have ex := congrFun e x₀
  have ey := congrFun e y₀
  simp only [psi, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_zero,
    Pi.zero_apply, hgx, hfy] at ex ey
  have hst' : s + t = 0 := by
    have : (s + t) * ev f x₀ = 0 := by linear_combination ex
    exact (mul_eq_zero.mp this).resolve_right hx₀
  have hs' : s * exp (θ * I) + t * exp (θ' * I) = 0 := by
    have : (s * exp (θ * I) + t * exp (θ' * I)) * ev g y₀ = 0 := by linear_combination ey
    exact (mul_eq_zero.mp this).resolve_right hy₀
  have hs : s = 0 := by
    have : s * (exp (θ * I) - exp (θ' * I)) = 0 := by
      linear_combination hs' - exp (θ' * I) * hst'
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hθ)
  exact ⟨hs, by linear_combination hst' - hs⟩

/-- Two states with the same matrix elements for every local operator and every measure. -/
theorem exists_same_matrixElements (hf0 : ev f ≠ 0) (hg0 : ev g ≠ 0)
    (hfg : Disjoint (tsupport (ev f)) (tsupport (ev g))) :
    ∃ ψ₁ ψ₂ : V, LinearIndependent ℂ ![ψ₁, ψ₂] ∧
      ∀ A : Module.End ℂ V, IsLocal ev A → ∀ [MeasurableSpace D] (μ : Measure D),
        ∫ x, conj (ev ψ₁ x) * ev (A ψ₁) x ∂μ = ∫ x, conj (ev ψ₂ x) * ev (A ψ₂) x ∂μ := by
  have hθ : exp ((0 : ℝ) * I) ≠ exp ((Real.pi : ℝ) * I) := by
    rw [ofReal_zero, zero_mul, exp_zero, exp_pi_mul_I]
    norm_num
  exact ⟨psi f g 0, psi f g Real.pi, linearIndependent_psi hf0 hg0 hfg hθ,
    fun A hA _ μ => matrixElement_psi_eq μ hA hfg 0 Real.pi⟩

end General

section Translation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- A compactly supported function and a far enough translate have disjoint supports. -/
theorem exists_disjoint_translate {h : E → ℂ} (hh : HasCompactSupport h) :
    ∃ a : E, Disjoint (tsupport h) (tsupport fun x => h (x - a)) := by
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall 0
  obtain ⟨a, ha⟩ := NormedSpace.exists_lt_norm ℝ E (2 * R)
  refine ⟨a, Set.disjoint_left.mpr fun x hx hxa => ?_⟩
  have hxa' : x - a ∈ tsupport h :=
    tsupport_comp_subset_preimage h (continuous_sub_right a) hxa
  have h1 := mem_closedBall_zero_iff.mp (hR hx)
  have h2 := mem_closedBall_zero_iff.mp (hR hxa')
  have : ‖a‖ ≤ ‖x‖ + ‖x - a‖ := by
    simpa using norm_sub_le x (x - a)
  linarith

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {ev : V →ₗ[ℂ] E → ℂ}

/-- The sentence of the brief, for translation-invariant spaces: if `V` is closed under
translations and contains a nonzero function with compact support, then two linearly independent
states of `V` have the same matrix elements for every local operator. -/
theorem exists_same_matrixElements_of_translate
    (htr : ∀ φ : V, ∀ a : E, ∃ φ' : V, ev φ' = fun x => ev φ (x - a))
    {f : V} (hf : HasCompactSupport (ev f)) (hf0 : ev f ≠ 0) :
    ∃ ψ₁ ψ₂ : V, LinearIndependent ℂ ![ψ₁, ψ₂] ∧
      ∀ A : Module.End ℂ V, IsLocal ev A → ∀ [MeasurableSpace E] (μ : Measure E),
        ∫ x, conj (ev ψ₁ x) * ev (A ψ₁) x ∂μ = ∫ x, conj (ev ψ₂ x) * ev (A ψ₂) x ∂μ := by
  obtain ⟨a, ha⟩ := exists_disjoint_translate hf
  obtain ⟨g, hg⟩ := htr f a
  have hg0 : ev g ≠ 0 := by
    intro h0
    apply hf0
    funext x
    simpa [hg] using congrFun h0 (x + a)
  exact exists_same_matrixElements hf0 hg0 (hg ▸ ha)

end Translation

section Schwartz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Schwartz functions as functions. -/
def coeLM : 𝓢(E, ℂ) →ₗ[ℂ] E → ℂ where
  toFun φ := φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma coeLM_apply (φ : 𝓢(E, ℂ)) : coeLM φ = ⇑φ := rfl

/-- The position operator along a linear functional `ℓ`: `(X ℓ φ)(x) = ℓ(x) φ(x)`. -/
def X (ℓ : E →L[ℝ] ℝ) : Module.End ℂ 𝓢(E, ℂ) :=
  (smulLeftCLM ℂ (fun x => (ℓ x : ℂ))).toLinearMap

/-- The momentum operator along `v`: `P ħ v = -iħ ∂_v`. -/
def P (ħ : ℝ) (v : E) : Module.End ℂ 𝓢(E, ℂ) :=
  ((-I * ħ) • lineDerivOpCLM ℂ 𝓢(E, ℂ) v).toLinearMap

lemma X_apply (ℓ : E →L[ℝ] ℝ) (φ : 𝓢(E, ℂ)) (x : E) : X ℓ φ x = ℓ x * φ x := by
  have : (fun x => (ℓ x : ℂ)).HasTemperateGrowth := (ofRealCLM.comp ℓ).hasTemperateGrowth
  simp [X, smulLeftCLM_apply_apply this]

lemma isLocal_X (ℓ : E →L[ℝ] ℝ) : IsLocal coeLM (X ℓ) := fun φ => by
  have : coeLM (X ℓ φ) = fun x : E => (ℓ x : ℂ) • φ x := funext fun x => X_apply ℓ φ x
  rw [this]
  exact tsupport_smul_subset_right _ _

lemma isLocal_P (ħ : ℝ) (v : E) : IsLocal coeLM (P ħ v) := fun φ => by
  have : coeLM (P ħ v φ) = fun x : E => (-I * ħ) • (∂_{v} φ : 𝓢(E, ℂ)) x := by
    funext x
    simp [P, coeLM_apply]
  rw [this]
  exact (tsupport_smul_subset_right _ _).trans (tsupport_lineDerivOp_subset v φ)

/-- Every polynomial in the positions and momenta is a local operator. -/
theorem adjoin_le_localOps (ħ : ℝ) :
    Algebra.adjoin ℂ (Set.range X ∪ Set.range (P (E := E) ħ)) ≤ localOps coeLM :=
  Algebra.adjoin_le (Set.union_subset (Set.range_subset_iff.mpr isLocal_X)
    (Set.range_subset_iff.mpr (isLocal_P ħ)))

/-- The real bump at `0`, equal to `1` on the ball of radius `1/2` and supported in the
closed unit ball. -/
def realBump : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

variable [FiniteDimensional ℝ E]

/-- A nonzero Schwartz function with compact support: the bump at `0`, as a complex function. -/
def bump : 𝓢(E, ℂ) :=
  HasCompactSupport.toSchwartzMap (f := fun x => (((realBump : ContDiffBump (0 : E)) x : ℝ) : ℂ))
    (realBump.hasCompactSupport.comp_left ofReal_zero)
    (ofRealCLM.contDiff.comp realBump.contDiff)

lemma hasCompactSupport_bump : HasCompactSupport (coeLM (bump (E := E))) :=
  (realBump : ContDiffBump (0 : E)).hasCompactSupport.comp_left ofReal_zero

lemma bump_ne_zero : coeLM (bump (E := E)) ≠ 0 := by
  intro h
  have h1 : (realBump : ContDiffBump (0 : E)) 0 = 1 :=
    realBump.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num [realBump]))
  have hc : coeLM (bump (E := E)) 0 = (((realBump : ContDiffBump (0 : E)) 0 : ℝ) : ℂ) :=
    rfl
  have := congrFun h 0
  rw [hc, h1] at this
  norm_num at this

/-- Theorem 1 of the brief on any nontrivial finite-dimensional `E`, e.g. `ℝⁿ` with `n ≥ 1`: two
linearly independent Schwartz functions on which every polynomial in the positions and momenta
has the same expectation value. -/
theorem exists_same_moments [Nontrivial E] (ħ : ℝ) :
    ∃ ψ₁ ψ₂ : 𝓢(E, ℂ), LinearIndependent ℂ ![ψ₁, ψ₂] ∧
      ∀ A ∈ Algebra.adjoin ℂ (Set.range X ∪ Set.range (P (E := E) ħ)),
        ∀ [MeasurableSpace E] (μ : Measure E),
          ∫ x, conj (ψ₁ x) * A ψ₁ x ∂μ = ∫ x, conj (ψ₂ x) * A ψ₂ x ∂μ := by
  obtain ⟨ψ₁, ψ₂, hli, h⟩ := exists_same_matrixElements_of_translate (ev := coeLM)
    (fun φ a => ⟨compSubConstCLM ℂ a φ, rfl⟩) (hasCompactSupport_bump (E := E))
    (bump_ne_zero (E := E))
  exact ⟨ψ₁, ψ₂, hli, fun A hA _ μ => h A (adjoin_le_localOps ħ hA) μ⟩

end Schwartz

end SchwartzMomentProblem.OtherSpaces
