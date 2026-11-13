/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Expectations of unbounded operators are discontinuous

For a densely defined operator `A` on a complex inner product space, the expectation
`x ↦ ⟪x, A x⟫` on the domain of `A` is continuous at one point only if `A` is bounded. So for an
unbounded operator, the expectation is discontinuous at every point of its domain, and so is the
normalized expectation `⟪x, A x⟫ / ‖x‖²` at every nonzero point.

No symmetry is needed: over `ℂ`, the quadratic form `⟪x, A x⟫` determines the sesquilinear form
`⟪x, A y⟫` by polarization.

## Main results

* `LinearPMap.exists_bound_of_continuousAt_inner`: if the expectation is continuous at one point
  of the domain, then `‖A x‖ ≤ C ‖x‖` on the domain;
* `LinearPMap.not_continuousAt_inner`: for an unbounded `A`, the expectation is discontinuous at
  every point of the domain;
* `LinearPMap.not_continuousAt_inner_div`: the same for the normalized expectation at every
  nonzero point;
* `LinearPMap.domain_ne_top_of_isFormalAdjoint`: Hellinger–Toeplitz, a symmetric operator that
  is unbounded on its domain is not defined on the whole space.
-/

open Filter Topology
open scoped InnerProductSpace

@[expose] public section

namespace LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : E →ₗ.[ℂ] E}

/-- The parallelogram law of the quadratic form `⟪x, A x⟫`. -/
lemma inner_apply_add_add_inner_apply_sub (x h : A.domain) :
    ⟪((x + h : A.domain) : E), A (x + h)⟫_ℂ + ⟪((x - h : A.domain) : E), A (x - h)⟫_ℂ =
      2 * ⟪(x : E), A x⟫_ℂ + 2 * ⟪(h : E), A h⟫_ℂ := by
  simp only [Submodule.coe_add, Submodule.coe_sub, LinearPMap.map_add, LinearPMap.map_sub,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  ring

/-- Polarization: `4 ⟪x, A y⟫` in terms of the quadratic form `⟪z, A z⟫`. -/
lemma four_mul_inner_apply (x y : A.domain) :
    4 * ⟪(x : E), A y⟫_ℂ =
      ⟪((x + y : A.domain) : E), A (x + y)⟫_ℂ - ⟪((x - y : A.domain) : E), A (x - y)⟫_ℂ -
        Complex.I * ⟪((x + Complex.I • y : A.domain) : E), A (x + Complex.I • y)⟫_ℂ +
        Complex.I * ⟪((x - Complex.I • y : A.domain) : E), A (x - Complex.I • y)⟫_ℂ := by
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, LinearPMap.map_add,
    LinearPMap.map_sub, LinearPMap.map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma norm_four_le (a b c d : ℂ) :
    ‖a - b - Complex.I * c + Complex.I * d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  calc ‖a - b - Complex.I * c + Complex.I * d‖
      ≤ ‖a - b - Complex.I * c‖ + ‖Complex.I * d‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ + ‖Complex.I * c‖ + ‖Complex.I * d‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ‖a‖ + ‖b‖ + ‖Complex.I * c‖ + ‖Complex.I * d‖ := by gcongr; exact norm_sub_le _ _
    _ = ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by simp

/-- Continuity of the expectation at one point gives continuity at `0`. -/
lemma continuousAt_zero_of_continuousAt_inner {x₀ : A.domain}
    (h : ContinuousAt (fun x : A.domain => ⟪(x : E), A x⟫_ℂ) x₀) :
    ContinuousAt (fun x : A.domain => ⟪(x : E), A x⟫_ℂ) 0 := by
  set q := fun x : A.domain => ⟪(x : E), A x⟫_ℂ
  have h1 : Tendsto (fun h => q (x₀ + h)) (𝓝 0) (𝓝 (q x₀)) := by
    exact h.tendsto.comp ((continuous_const_add x₀).tendsto' 0 x₀ (add_zero x₀))
  have h2 : Tendsto (fun h => q (x₀ - h)) (𝓝 0) (𝓝 (q x₀)) := by
    exact h.tendsto.comp ((continuous_const.sub continuous_id).tendsto' 0 x₀ (sub_zero x₀))
  have hq (h : A.domain) : q h = (q (x₀ + h) + q (x₀ - h) - 2 * q x₀) / 2 := by
    have := inner_apply_add_add_inner_apply_sub x₀ h
    simp only [q] at this ⊢
    rw [this]
    ring
  have h0 : q 0 = 0 := by simp [q]
  have := ((h1.add h2).sub (tendsto_const_nhds (x := 2 * q x₀))).div_const 2
  rw [show (q x₀ + q x₀ - 2 * q x₀) / 2 = q 0 by rw [h0]; ring] at this
  exact this.congr fun h => (hq h).symm

/-- Continuity of the expectation at `0` bounds the quadratic form: `|⟪x, A x⟫| ≤ C ‖x‖²`. -/
lemma exists_bound_inner_of_continuousAt_zero
    (h : ContinuousAt (fun x : A.domain => ⟪(x : E), A x⟫_ℂ) 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : A.domain, ‖⟪(x : E), A x⟫_ℂ‖ ≤ C * ‖(x : E)‖ ^ 2 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 h 1 one_pos
  refine ⟨4 / δ ^ 2, by positivity, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hx' : 0 < ‖(x : E)‖ := norm_pos_iff.2 (by simpa using hx)
  set c : ℝ := δ / (2 * ‖(x : E)‖)
  have hc : 0 < c := by positivity
  have hcx : dist ((c : ℂ) • x) 0 < δ := by
    rw [dist_zero_right, ← Submodule.norm_coe, Submodule.coe_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hc.le]
    simp only [c]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hq := hball hcx
  simp only [Submodule.coe_zero, inner_zero_left, dist_zero_right, Submodule.coe_smul,
    LinearPMap.map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc.le] at hq
  have hc2 : c * c = δ ^ 2 / (4 * ‖(x : E)‖ ^ 2) := by
    simp only [c]
    field_simp
    ring
  rw [← mul_assoc, hc2] at hq
  rw [div_mul_eq_mul_div, div_lt_one (by positivity)] at hq
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- **Expectations determine boundedness.** If `A` is densely defined and the expectation
`x ↦ ⟪x, A x⟫` is continuous at one point of the domain, then `A` is bounded on its domain. -/
theorem exists_bound_of_continuousAt_inner (hA : Dense (A.domain : Set E)) {x₀ : A.domain}
    (h : ContinuousAt (fun x : A.domain => ⟪(x : E), A x⟫_ℂ) x₀) :
    ∃ C : ℝ, ∀ x : A.domain, ‖A x‖ ≤ C * ‖(x : E)‖ := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_inner_of_continuousAt_zero (continuousAt_zero_of_continuousAt_inner h)
  -- Polarization: `|⟪φ, A ψ⟫| ≤ C (‖φ‖ + ‖ψ‖)²` on the domain.
  have hpol (φ ψ : A.domain) : ‖⟪(φ : E), A ψ⟫_ℂ‖ ≤ C * (‖(φ : E)‖ + ‖(ψ : E)‖) ^ 2 := by
    have hz (z : A.domain) (hz : ‖(z : E)‖ ≤ ‖(φ : E)‖ + ‖(ψ : E)‖) :
        ‖⟪(z : E), A z⟫_ℂ‖ ≤ C * (‖(φ : E)‖ + ‖(ψ : E)‖) ^ 2 :=
      (hC z).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (z : E)) hz 2) hC0)
    have hIψ : ‖((Complex.I • ψ : A.domain) : E)‖ = ‖(ψ : E)‖ := by
      rw [Submodule.coe_smul, norm_smul, Complex.norm_I, one_mul]
    have e1 := hz (φ + ψ) (norm_add_le _ _)
    have e2 := hz (φ - ψ) (norm_sub_le _ _)
    have e3 := hz (φ + Complex.I • ψ)
      ((norm_add_le (φ : E) ((Complex.I • ψ : A.domain) : E)).trans_eq (by rw [hIψ]))
    have e4 := hz (φ - Complex.I • ψ)
      ((norm_sub_le (φ : E) ((Complex.I • ψ : A.domain) : E)).trans_eq (by rw [hIψ]))
    have h4 : ‖4 * ⟪(φ : E), A ψ⟫_ℂ‖ ≤ 4 * (C * (‖(φ : E)‖ + ‖(ψ : E)‖) ^ 2) := by
      rw [four_mul_inner_apply]
      refine (norm_four_le _ _ _ _).trans ?_
      linarith
    rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num] at h4
    linarith
  -- By density, `|⟪v, A ψ⟫| ≤ C (‖v‖ + ‖ψ‖)²` for every `v`.
  have hall (ψ : A.domain) (v : E) : ‖⟪v, A ψ⟫_ℂ‖ ≤ C * (‖v‖ + ‖(ψ : E)‖) ^ 2 := by
    have hcl : _root_.IsClosed {v : E | ‖⟪v, A ψ⟫_ℂ‖ ≤ C * (‖v‖ + ‖(ψ : E)‖) ^ 2} :=
      isClosed_le (continuous_id.inner continuous_const).norm
        (continuous_const.mul ((continuous_norm.add continuous_const).pow 2))
    have hsub : (A.domain : Set E) ⊆ {v : E | ‖⟪v, A ψ⟫_ℂ‖ ≤ C * (‖v‖ + ‖(ψ : E)‖) ^ 2} :=
      fun v hv => hpol ⟨v, hv⟩ ψ
    have := hcl.closure_subset_iff.2 hsub
    rw [hA.closure_eq] at this
    exact this (Set.mem_univ v)
  refine ⟨4 * C, fun ψ => ?_⟩
  rcases eq_or_ne ‖A ψ‖ 0 with h0 | h0
  · rw [h0]
    positivity
  have hAψ : 0 < ‖A ψ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  -- Test against `v = (‖ψ‖ / ‖A ψ‖) A ψ`.
  set s : ℝ := ‖(ψ : E)‖ / ‖A ψ‖
  have hs : 0 ≤ s := by positivity
  have hv := hall ψ ((s : ℂ) • A ψ)
  rw [inner_smul_left, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hs, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg hs, norm_pow] at hv
  simp only [RCLike.norm_ofReal, abs_norm] at hv
  have hsA : s * ‖A ψ‖ = ‖(ψ : E)‖ := div_mul_cancel₀ _ h0
  have hlhs : s * ‖A ψ‖ ^ 2 = ‖(ψ : E)‖ * ‖A ψ‖ := by rw [sq, ← mul_assoc, hsA]
  rw [hlhs, hsA] at hv
  rcases eq_or_lt_of_le (norm_nonneg (ψ : E)) with hψ | hψ
  · have : (ψ : E) = 0 := norm_eq_zero.1 hψ.symm
    have hψ0 : ψ = 0 := Subtype.ext this
    rw [hψ0, LinearPMap.map_zero, norm_zero] at h0
    exact absurd rfl h0
  · nlinarith

/-- **Unbounded operators have discontinuous expectations.** For a densely defined unbounded
operator `A`, the expectation `x ↦ ⟪x, A x⟫` is discontinuous at every point of the domain. -/
theorem not_continuousAt_inner (hA : Dense (A.domain : Set E))
    (hu : ∀ C : ℝ, ∃ x : A.domain, C * ‖(x : E)‖ < ‖A x‖) (x₀ : A.domain) :
    ¬ ContinuousAt (fun x : A.domain => ⟪(x : E), A x⟫_ℂ) x₀ := fun h => by
  obtain ⟨C, hC⟩ := exists_bound_of_continuousAt_inner hA h
  obtain ⟨x, hx⟩ := hu C
  exact (hC x).not_gt hx

/-- The normalized expectation `⟪x, A x⟫ / ‖x‖²` of a densely defined unbounded operator `A` is
discontinuous at every nonzero point of the domain. -/
theorem not_continuousAt_inner_div (hA : Dense (A.domain : Set E))
    (hu : ∀ C : ℝ, ∃ x : A.domain, C * ‖(x : E)‖ < ‖A x‖) {x₀ : A.domain} (hx₀ : x₀ ≠ 0) :
    ¬ ContinuousAt (fun x : A.domain => ⟪(x : E), A x⟫_ℂ / (‖(x : E)‖ ^ 2 : ℂ)) x₀ := by
  intro h
  refine not_continuousAt_inner hA hu x₀ ?_
  have hn : ContinuousAt (fun x : A.domain => ((‖(x : E)‖ ^ 2 : ℝ) : ℂ)) x₀ :=
    (Complex.continuous_ofReal.comp
      ((continuous_norm.comp continuous_subtype_val).pow 2)).continuousAt
  refine (hn.mul h).congr ?_
  filter_upwards [isOpen_ne.mem_nhds hx₀] with x hx
  have hx' : ((‖(x : E)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (x : E) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.2 this)
  simp only [Pi.mul_apply]
  push_cast at hx' ⊢
  rw [mul_comm]
  exact div_mul_cancel₀ _ hx'

/-- **Hellinger–Toeplitz** for partially defined operators: a symmetric operator that is
unbounded on its domain is not defined on the whole space. -/
theorem domain_ne_top_of_isFormalAdjoint [CompleteSpace E] (hT : A.IsFormalAdjoint A)
    (hu : ∀ C : ℝ, ∃ x : A.domain, C * ‖(x : E)‖ < ‖A x‖) : A.domain ≠ ⊤ := by
  intro htop
  let e : E ≃ₗ[ℂ] A.domain := (LinearEquiv.ofTop A.domain htop).symm
  have he (x : A.domain) : e x = x := Subtype.ext (by simp [e])
  have he' (x : E) : (e x : E) = x := by simp [e]
  let T : E →ₗ[ℂ] E := A.toFun ∘ₗ e.toLinearMap
  have hsym : T.IsSymmetric := fun x y => by simpa [T, he'] using hT (e x) (e y)
  let L : E →L[ℂ] E := ⟨T, hsym.continuous⟩
  obtain ⟨x, hx⟩ := hu ‖L‖
  have hLx : L x = A x := by simp [L, T, he]
  have := L.le_opNorm x
  rw [hLx] at this
  linarith

end LinearPMap
