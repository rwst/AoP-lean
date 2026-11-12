/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Distribution.SchwartzSpace.HermiteSeries

/-!
# Schwartz spaces of different dimensions are isomorphic

For positive integers `n` and `m` there is a unitary `U : L²(ℝⁿ) → L²(ℝᵐ)` that maps `𝓢(ℝⁿ)`
onto `𝓢(ℝᵐ)` and restricts to an isomorphism of topological vector spaces
`𝓢(ℝⁿ) ≃L[ℂ] 𝓢(ℝᵐ)`; in other words, the rigged Hilbert spaces `𝓢(ℝⁿ) ⊆ L²(ℝⁿ)` and
`𝓢(ℝᵐ) ⊆ L²(ℝᵐ)` are isomorphic.

The isomorphism relabels Hermite functions: a bijection `σ : ℕⁿ ≃ ℕᵐ` of multi-indices with
`1 + |σ α| ≤ (1 + |α|)^P` and `1 + |σ⁻¹ β| ≤ (1 + |β|)^Q` maps rapidly decreasing families to
rapidly decreasing families. Such a bijection is the composite of the iterated Cantor pairings
`ℕⁿ ≃ ℕ` and `ℕ ≃ ℕᵐ`.

## Main definitions

* `SchwartzMap.multiIndexEquiv n : (Fin (n + 1) → ℕ) ≃ ℕ`, by iterated pairing;
* `SchwartzMap.reindexCLM σ hσ`: the continuous linear map `∑ c_α h_α ↦ ∑ c_α h_{σ α}`.

## Main results

* `SchwartzMap.exists_unitary_schwartzEquiv`: the isomorphism above.
-/

open MeasureTheory Finset Module
open scoped SchwartzMap InnerProductSpace ENNReal NNReal

@[expose] public noncomputable section

namespace SchwartzMap

/-! ### Multi-indices -/

lemma add_le_pair (a b : ℕ) : a + b ≤ Nat.pair a b := by
  unfold Nat.pair
  split_ifs <;> nlinarith

/-- An enumeration of the multi-indices `Fin (n + 1) → ℕ`, by iterated pairing. -/
def multiIndexEquiv : (n : ℕ) → (Fin (n + 1) → ℕ) ≃ ℕ
  | 0 => Equiv.funUnique (Fin 1) ℕ
  | n + 1 => (Fin.consEquiv fun _ : Fin (n + 2) => ℕ).symm.trans
      ((Equiv.prodCongr (Equiv.refl ℕ) (multiIndexEquiv n)).trans Nat.pairEquiv)

lemma multiIndexEquiv_succ (n : ℕ) (α : Fin (n + 2) → ℕ) :
    multiIndexEquiv (n + 1) α = Nat.pair (α 0) (multiIndexEquiv n (Fin.tail α)) :=
  rfl

lemma sum_le_multiIndexEquiv : ∀ (n : ℕ) (α : Fin (n + 1) → ℕ), ∑ i, α i ≤ multiIndexEquiv n α
  | 0, α => by simp [multiIndexEquiv]
  | n + 1, α => by
    rw [multiIndexEquiv_succ, Fin.sum_univ_succ]
    have := sum_le_multiIndexEquiv n (Fin.tail α)
    have := add_le_pair (α 0) (multiIndexEquiv n (Fin.tail α))
    simp only [Fin.tail] at *
    omega

lemma exists_multiIndexEquiv_le :
    ∀ n : ℕ, ∃ P : ℕ, 1 ≤ P ∧ ∀ α : Fin (n + 1) → ℕ,
      multiIndexEquiv n α + 1 ≤ (∑ i, α i + 1) ^ P
  | 0 => ⟨1, le_rfl, fun α => by simp [multiIndexEquiv]⟩
  | n + 1 => by
    obtain ⟨P, hP, h⟩ := exists_multiIndexEquiv_le n
    refine ⟨2 * P, by omega, fun α => ?_⟩
    rw [multiIndexEquiv_succ]
    have hsum : ∑ i, α i = α 0 + ∑ i, Fin.tail α i := by
      rw [Fin.sum_univ_succ]
      rfl
    have h1 : α 0 + 1 ≤ (∑ i, α i + 1) ^ P :=
      (by omega : α 0 + 1 ≤ ∑ i, α i + 1).trans (Nat.le_self_pow (by omega) _)
    have h2 : multiIndexEquiv n (Fin.tail α) + 1 ≤ (∑ i, α i + 1) ^ P :=
      (h _).trans (Nat.pow_le_pow_left (by omega) _)
    have h3 := Nat.pair_lt_max_add_one_sq (α 0) (multiIndexEquiv n (Fin.tail α))
    calc Nat.pair (α 0) (multiIndexEquiv n (Fin.tail α)) + 1
        ≤ (max (α 0) (multiIndexEquiv n (Fin.tail α)) + 1) ^ 2 := h3
      _ ≤ ((∑ i, α i + 1) ^ P) ^ 2 := by
          gcongr
          exact max_add_add_right (α 0) _ 1 ▸ max_le h1 h2
      _ = (∑ i, α i + 1) ^ (2 * P) := by ring

/-- A relabelling of multi-indices with polynomial bounds in both directions. -/
lemma exists_multiIndex_equiv (n m : ℕ) :
    ∃ (σ : (Fin (n + 1) → ℕ) ≃ (Fin (m + 1) → ℕ)) (P Q : ℕ),
      (∀ α, hermiteWeight (σ α) ≤ hermiteWeight α ^ P) ∧
      (∀ β, hermiteWeight (σ.symm β) ≤ hermiteWeight β ^ Q) := by
  obtain ⟨P, -, hP⟩ := exists_multiIndexEquiv_le n
  obtain ⟨Q, -, hQ⟩ := exists_multiIndexEquiv_le m
  refine ⟨(multiIndexEquiv n).trans (multiIndexEquiv m).symm, P, Q, fun α => ?_, fun β => ?_⟩
  · have h1 := sum_le_multiIndexEquiv m ((multiIndexEquiv m).symm (multiIndexEquiv n α))
    rw [Equiv.apply_symm_apply] at h1
    have h2 := hP α
    simp only [hermiteWeight, Equiv.trans_apply]
    omega
  · have h1 := sum_le_multiIndexEquiv n ((multiIndexEquiv n).symm (multiIndexEquiv m β))
    rw [Equiv.apply_symm_apply] at h1
    have h2 := hQ β
    simp only [hermiteWeight, Equiv.symm_trans_apply, Equiv.symm_symm]
    omega

/-! ### Reindexing Hermite expansions -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

lemma coeffNorm_comp_le (τ : (κ → ℕ) ≃ (ι → ℕ)) {Q : ℕ}
    (hτ : ∀ β, hermiteWeight β ≤ hermiteWeight (τ β) ^ Q) (K : ℕ) (c : (ι → ℕ) → ℂ) :
    coeffNorm K (fun β => c (τ β)) ≤ coeffNorm (Q * K) c := by
  refine iSup_le fun β => ?_
  calc (hermiteWeight β : ℝ≥0∞) ^ K * ‖c (τ β)‖ₑ
      ≤ ((hermiteWeight (τ β) : ℝ≥0∞) ^ Q) ^ K * ‖c (τ β)‖ₑ := by
        gcongr
        exact_mod_cast hτ β
    _ = (hermiteWeight (τ β) : ℝ≥0∞) ^ (Q * K) * ‖c (τ β)‖ₑ := by ring
    _ ≤ coeffNorm (Q * K) c := weight_mul_le_coeffNorm _ _ _

lemma weight_le_symm (σ : (ι → ℕ) ≃ (κ → ℕ)) {P : ℕ}
    (hσ : ∀ α, hermiteWeight (σ α) ≤ hermiteWeight α ^ P) (β : κ → ℕ) :
    hermiteWeight β ≤ hermiteWeight (σ.symm β) ^ P := by
  have h := hσ (σ.symm β)
  rwa [Equiv.apply_symm_apply] at h

/-- Two Schwartz functions with the same Hermite coefficients are equal. -/
lemma eq_of_hermiteCoeff_eq {f g : 𝓢(EuclideanSpace ℝ ι, ℂ)}
    (h : ∀ α, hermiteCoeff α f = hermiteCoeff α g) : f = g := by
  refine injective_toLp (E := EuclideanSpace ℝ ι) (F := ℂ) 2 volume ?_
  refine (hermitePiBasis (ι := ι)).repr.injective (lp.ext (funext fun α => ?_))
  simpa only [HilbertBasis.repr_apply_apply, hermiteCoeff_apply] using h α

/-! ### The unitary -/

/-- The Hilbert basis `α ↦ h_{σ α}` of `L²(ℝ^κ)`. -/
def reindexBasis (σ : (ι → ℕ) ≃ (κ → ℕ)) :
    HilbertBasis (ι → ℕ) ℂ (Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ κ))) :=
  HilbertBasis.mk (v := fun α => hermitePiBasis (σ α))
    ((hermitePiBasis (ι := κ)).orthonormal.comp σ σ.injective)
    (by
      rw [show Set.range (fun α => hermitePiBasis (σ α)) = Set.range (hermitePiBasis (ι := κ))
        from σ.surjective.range_comp _]
      exact (hermitePiBasis (ι := κ)).dense_span.ge)

/-- The unitary `h_α ↦ h_{σ α}`. -/
def reindexUnitary (σ : (ι → ℕ) ≃ (κ → ℕ)) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ κ)) :=
  (hermitePiBasis (ι := ι)).repr.trans (reindexBasis σ).repr.symm

lemma inner_reindexUnitary (σ : (ι → ℕ) ≃ (κ → ℕ))
    (v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ ι))) (α : ι → ℕ) :
    ⟪hermitePiBasis (σ α), reindexUnitary σ v⟫_ℂ = ⟪hermitePiBasis α, v⟫_ℂ := by
  have h := HilbertBasis.repr_apply_apply (reindexBasis σ) (reindexUnitary σ v) α
  rw [reindexUnitary, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply,
    HilbertBasis.repr_apply_apply, reindexBasis, HilbertBasis.coe_mk] at h
  exact h.symm

variable [Nonempty κ] [DecidableEq κ]

omit [Nonempty κ] [DecidableEq κ] in
/-- The coefficient family `β ↦ c_{σ⁻¹ β}(f)` of a Schwartz function is rapidly decreasing. -/
lemma coeffNorm_hermiteCoeff_symm_ne_top (σ : (ι → ℕ) ≃ (κ → ℕ)) {P : ℕ}
    (hσ : ∀ α, hermiteWeight (σ α) ≤ hermiteWeight α ^ P) (f : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (K : ℕ) : coeffNorm K (fun β => hermiteCoeff (σ.symm β) f) ≠ ⊤ :=
  ne_top_of_le_ne_top (hermiteNorm_ne_top (P * K) f)
    ((coeffNorm_comp_le σ.symm (weight_le_symm σ hσ) K fun α => hermiteCoeff α f).trans_eq
      (hermiteNorm_eq_coeffNorm _ f).symm)

lemma summable_mul_hermitePiFun (c : (κ → ℕ) → ℂ) (hc : ∀ K, coeffNorm K c ≠ ⊤)
    (x : EuclideanSpace ℝ κ) : Summable fun α => c α * hermitePiFun α x :=
  (summable_norm_mul_seminorm c hc 0 0).of_norm_bounded fun α => by
    rw [norm_mul]
    gcongr
    simpa [hermitePi_apply] using norm_le_seminorm ℂ (hermitePi α) x

/-- The continuous linear map `∑ c_α h_α ↦ ∑ c_α h_{σ α}`, for a relabelling `σ` of
multi-indices with a polynomial bound. -/
def reindexCLM (σ : (ι → ℕ) ≃ (κ → ℕ)) {P : ℕ}
    (hσ : ∀ α, hermiteWeight (σ α) ≤ hermiteWeight α ^ P) :
    𝓢(EuclideanSpace ℝ ι, ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ κ, ℂ) :=
  mkCLM (σ := RingHom.id ℂ)
    (fun f => hermiteSeries (fun β => hermiteCoeff (σ.symm β) f)
      (coeffNorm_hermiteCoeff_symm_ne_top σ hσ f))
    (fun f g x => by
      simp only [hermiteSeries_apply, map_add, add_mul]
      exact (summable_mul_hermitePiFun _ (coeffNorm_hermiteCoeff_symm_ne_top σ hσ f) x).tsum_add
        (summable_mul_hermitePiFun _ (coeffNorm_hermiteCoeff_symm_ne_top σ hσ g) x))
    (fun a f x => by
      simp only [hermiteSeries_apply, map_smul, smul_eq_mul, RingHom.id_apply, mul_assoc]
      exact tsum_mul_left)
    (fun f => (hermiteSeries _ _).smooth ⊤)
    (fun n => by
      obtain ⟨C₁, hC₁, L, h₁⟩ := exists_seminorm_hermiteSeries_le (ι := κ) n.1 n.2
      obtain ⟨s, C₂, h₂⟩ := exists_hermiteNorm_le_seminorm (ι := ι) (P * L)
      refine ⟨s, (C₁ * C₂).toReal, ENNReal.toReal_nonneg, fun f x => ?_⟩
      set F := hermiteSeries (fun β => hermiteCoeff (σ.symm β) f)
        (coeffNorm_hermiteCoeff_symm_ne_top σ hσ f)
      have hfin : C₁ * C₂ * ENNReal.ofReal (s.sup (schwartzSeminormFamily ℂ _ ℂ) f) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.mul_ne_top hC₁ ENNReal.coe_ne_top) ENNReal.ofReal_ne_top
      have key : ENNReal.ofReal (‖x‖ ^ n.1 * ‖iteratedFDeriv ℝ n.2 F x‖) ≤
          C₁ * C₂ * ENNReal.ofReal (s.sup (schwartzSeminormFamily ℂ _ ℂ) f) := by
        calc ENNReal.ofReal (‖x‖ ^ n.1 * ‖iteratedFDeriv ℝ n.2 F x‖)
            ≤ ENNReal.ofReal (SchwartzMap.seminorm ℂ n.1 n.2 F) :=
              ENNReal.ofReal_le_ofReal (le_seminorm ℂ _ _ F x)
          _ ≤ C₁ * coeffNorm L (fun β => hermiteCoeff (σ.symm β) f) := h₁ _ _
          _ ≤ C₁ * hermiteNorm (P * L) f := by
              gcongr
              exact (coeffNorm_comp_le σ.symm (weight_le_symm σ hσ) L
                fun α => hermiteCoeff α f).trans_eq (hermiteNorm_eq_coeffNorm _ f).symm
          _ ≤ C₁ * (C₂ * ENNReal.ofReal (s.sup (schwartzSeminormFamily ℂ _ ℂ) f)) := by
              gcongr
              exact h₂ f
          _ = C₁ * C₂ * ENNReal.ofReal (s.sup (schwartzSeminormFamily ℂ _ ℂ) f) := by ring
      have := (ENNReal.ofReal_le_iff_le_toReal hfin).1 key
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (apply_nonneg _ _)] at this)

lemma reindexCLM_apply (σ : (ι → ℕ) ≃ (κ → ℕ)) {P : ℕ}
    (hσ : ∀ α, hermiteWeight (σ α) ≤ hermiteWeight α ^ P) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    reindexCLM σ hσ f = hermiteSeries (fun β => hermiteCoeff (σ.symm β) f)
      (coeffNorm_hermiteCoeff_symm_ne_top σ hσ f) :=
  rfl

lemma hermiteCoeff_reindexCLM (σ : (ι → ℕ) ≃ (κ → ℕ)) {P : ℕ}
    (hσ : ∀ α, hermiteWeight (σ α) ≤ hermiteWeight α ^ P) (f : 𝓢(EuclideanSpace ℝ ι, ℂ))
    (β : κ → ℕ) : hermiteCoeff β (reindexCLM σ hσ f) = hermiteCoeff (σ.symm β) f := by
  rw [reindexCLM_apply, hermiteCoeff_hermiteSeries]

/-- On Schwartz functions, the unitary `h_α ↦ h_{σ α}` is the map `reindexCLM σ`. -/
theorem toLp_reindexCLM (σ : (ι → ℕ) ≃ (κ → ℕ)) {P : ℕ}
    (hσ : ∀ α, hermiteWeight (σ α) ≤ hermiteWeight α ^ P) (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) :
    (reindexCLM σ hσ f).toLp 2 = reindexUnitary σ (f.toLp 2) := by
  refine (reindexBasis σ).repr.injective (lp.ext (funext fun α => ?_))
  simp only [HilbertBasis.repr_apply_apply, reindexBasis, HilbertBasis.coe_mk]
  rw [inner_reindexUnitary, ← hermiteCoeff_apply, ← hermiteCoeff_apply,
    hermiteCoeff_reindexCLM, Equiv.symm_apply_apply]

/-! ### Schwartz spaces of different dimensions -/

/-- **Schwartz spaces of different dimensions are isomorphic.** For positive integers `n + 1`
and `m + 1` there is a unitary `U : L²(ℝⁿ⁺¹) → L²(ℝᵐ⁺¹)` that restricts to an isomorphism of
topological vector spaces `𝓢(ℝⁿ⁺¹) ≃L[ℂ] 𝓢(ℝᵐ⁺¹)`. -/
theorem exists_unitary_schwartzEquiv (n m : ℕ) :
    ∃ (U : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin (m + 1)))))
      (T : 𝓢(EuclideanSpace ℝ (Fin (n + 1)), ℂ) ≃L[ℂ] 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)),
      ∀ f, (T f).toLp 2 = U (f.toLp 2) := by
  obtain ⟨σ, P, Q, hP, hQ⟩ := exists_multiIndex_equiv n m
  refine ⟨reindexUnitary σ, ContinuousLinearEquiv.equivOfInverse (reindexCLM σ hP)
    (reindexCLM σ.symm hQ) (fun f => ?_) (fun g => ?_), toLp_reindexCLM σ hP⟩
  · refine eq_of_hermiteCoeff_eq fun α => ?_
    rw [hermiteCoeff_reindexCLM, hermiteCoeff_reindexCLM, Equiv.symm_symm,
      Equiv.symm_apply_apply]
  · refine eq_of_hermiteCoeff_eq fun β => ?_
    rw [hermiteCoeff_reindexCLM, hermiteCoeff_reindexCLM, Equiv.symm_symm,
      Equiv.apply_symm_apply]

/-- `𝓢(ℝⁿ⁺¹)` and `𝓢(ℝᵐ⁺¹)` are isomorphic as topological vector spaces. -/
theorem nonempty_schwartzEquiv (n m : ℕ) :
    Nonempty (𝓢(EuclideanSpace ℝ (Fin (n + 1)), ℂ) ≃L[ℂ] 𝓢(EuclideanSpace ℝ (Fin (m + 1)), ℂ)) :=
  let ⟨_, T, _⟩ := exists_unitary_schwartzEquiv n m
  ⟨T⟩

end SchwartzMap
