/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.TraceNorm

/-!
# Kadison's theorem in any dimension

## i. Overview

A map `T` of density operators that is affine, in the sense that it preserves the mixtures
`t ρ + (1 - t) σ`, is determined by its values on the pure states. For such a map, being bijective
on the pure states, being bijective on the density operators and being conjugation by a unitary or
an anti-unitary are equivalent, on a Hilbert space of any dimension and without any continuity
hypothesis. This is Kadison's theorem.

The finite-dimensional proof (`QuantumMechanics.Wigner.kadison`) shows that overlaps do not shrink
and then averages over an orthonormal basis to get equality. The averaging needs the trace of the
identity, so here the equality comes from a two-dimensional argument instead. Let `r ⊥ s` with
`T |r⟩⟨r| = |a⟩⟨a|` and `T |s⟩⟨s| = |b⟩⟨b|`. Every orthonormal pair `x, y` in the plane of `r, s`
has `|x⟩⟨x| + |y⟩⟨y| = |r⟩⟨r| + |s⟩⟨s|`, so its images have the same equal mixture as `a, b`.
If `⟪a, b⟫ = δ ∈ (0, 1)`, let `f₊, f₋` be the eigenvectors of `|a⟩⟨a| + |b⟩⟨b|`. The number
`z(x) = ⟪f₋, T |x⟩⟨x| f₊⟫` then lies on the circle `|z|² = (1 - δ²) / 4`, and affinity makes `z`
send vectors with `|⟪x, y⟫|² = ½` to perpendicular points. The vectors `r`, `(r + s) / √2` and
`(r + i s) / √2` are pairwise at overlap `½`, and three pairwise perpendicular nonzero vectors
do not fit in the plane. Injectivity excludes `δ = 1`, so orthogonal pure states stay orthogonal.
Writing `mix(|ψ⟩⟨ψ|, |ϕ⟩⟨ϕ|)` as a mixture of two orthogonal pure states then shows that overlaps
are preserved, and Wigner's theorem gives a unitary or anti-unitary `W` on the pure states.

The mixed states follow without continuity. Cut the canonical expansion `ρ = ∑ᵢ μᵢ |bᵢ⟩⟨bᵢ|`
after a finite set of weight `m`, so that `ρ = m ρ_F + (1 - m) σ_F` with a finite mixture `ρ_F` and
the normalized tail `σ_F`. The map `T` and conjugation by `W` agree on `ρ_F`, so their values on `ρ`
differ by at most `2 (1 - m)` in operator norm.

The pure states are the extreme points of the density operators, and conjugation by a unitary or
an anti-unitary preserves density operators. Together these close the cycle of equivalences.

## ii. Key results

- `QuantumMechanics.sq_add_sq_add_eq_of_smul_proj_add_smul_proj_eq`: the Hilbert–Schmidt square
  of a combination of two pure states does not depend on the representation.
- `QuantumMechanics.proj_add_proj_eq_of_apply_eq`: two orthonormal pairs spanning the same plane
  give the same projection.
- `QuantumMechanics.AffineOnDensityOperators.inner_eq_zero`: orthogonal pure states stay
  orthogonal.
- `QuantumMechanics.AffineOnDensityOperators.norm_inner_eq`: overlaps are preserved.
- `QuantumMechanics.AffineOnDensityOperators.exists_unitary_or_antiunitary`: Wigner's theorem for
  affine maps that are bijective on pure states.
- `QuantumMechanics.AffineOnDensityOperators.eq_conjOp`: the mixed-state extension.
- `QuantumMechanics.IsDensityOperator.conjOp`: conjugation by a unitary or an anti-unitary
  preserves density operators.
- `QuantumMechanics.isPure_iff_isExtremeDensityOperator`: the pure states are the extreme points.
- `QuantumMechanics.AffineOnDensityOperators.tfae`: Kadison's theorem, three forms.

## iii. Table of contents

- A. Pure-state algebra
- B. Orthogonal pure states stay orthogonal
- C. Overlaps are preserved
- D. Mixed states follow from pure states
- E. Conjugation preserves density operators
- F. Pure states are the extreme points
- G. Three characterizations of state automorphisms

## iv. References

- R. V. Kadison, *Transformations of states in operator theory and dynamics*, Topology 3,
  suppl. 2 (Pergamon Press, 1965), 177–198.
- B. Simon, *Quantum dynamics: from automorphism to Hamiltonian*, in *Studies in Mathematical
  Physics*, Princeton University Press (1976), 327–349.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexOrder ComplexConjugate
open InnerProductSpace QuantumMechanics.Wigner
open ContinuousLinearMap (mul_def star_eq_adjoint)
open ContinuousLinearMap (posTrace posTrace_add posTrace_smul posTrace_eq_zero_iff)
open ProbabilisticTheory ProbabilisticTheory.TraceClass Filter Topology

namespace QuantumMechanics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## A. Pure-state algebra -/

/-- The quadratic form of a real combination of two pure states. -/
lemma re_inner_smul_proj_add_smul_proj (c₁ c₂ : ℝ) (x₁ x₂ u : E) :
    (⟪u, ((c₁ : ℂ) • proj x₁ + (c₂ : ℂ) • proj x₂) u⟫_ℂ).re =
      c₁ * ‖⟪x₁, u⟫_ℂ‖ ^ 2 + c₂ * ‖⟪x₂, u⟫_ℂ‖ ^ 2 := by
  simp only [add_apply, smul_apply, inner_add_right, inner_smul_right, inner_proj_apply,
    Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]

/-- **The Hilbert–Schmidt square of two pure states.** `tr (c₁ P₁ + c₂ P₂)² =
c₁² + c₂² + 2 c₁ c₂ |⟪x₁, x₂⟫|²` does not depend on how the operator is written. -/
theorem sq_add_sq_add_eq_of_smul_proj_add_smul_proj_eq {x₁ x₂ y₁ y₂ : E} (hx₁ : ‖x₁‖ = 1)
    (hx₂ : ‖x₂‖ = 1) (hy₁ : ‖y₁‖ = 1) (hy₂ : ‖y₂‖ = 1) {c₁ c₂ d₁ d₂ : ℝ}
    (h : (c₁ : ℂ) • proj x₁ + (c₂ : ℂ) • proj x₂ = (d₁ : ℂ) • proj y₁ + (d₂ : ℂ) • proj y₂) :
    c₁ ^ 2 + c₂ ^ 2 + 2 * c₁ * c₂ * ‖⟪x₁, x₂⟫_ℂ‖ ^ 2 =
      d₁ ^ 2 + d₂ ^ 2 + 2 * d₁ * d₂ * ‖⟪y₁, y₂⟫_ℂ‖ ^ 2 := by
  have e : ∀ u : E, c₁ * ‖⟪x₁, u⟫_ℂ‖ ^ 2 + c₂ * ‖⟪x₂, u⟫_ℂ‖ ^ 2 =
      d₁ * ‖⟪y₁, u⟫_ℂ‖ ^ 2 + d₂ * ‖⟪y₂, u⟫_ℂ‖ ^ 2 := fun u => by
    rw [← re_inner_smul_proj_add_smul_proj, ← re_inner_smul_proj_add_smul_proj, h]
  have e₁ := e x₁
  have e₂ := e x₂
  have e₃ := e y₁
  have e₄ := e y₂
  rw [norm_inner_self_eq_one hx₁, norm_inner_symm x₂ x₁, norm_inner_symm y₁ x₁,
    norm_inner_symm y₂ x₁] at e₁
  rw [norm_inner_self_eq_one hx₂, norm_inner_symm y₁ x₂, norm_inner_symm y₂ x₂] at e₂
  rw [norm_inner_self_eq_one hy₁, norm_inner_symm y₂ y₁] at e₃
  rw [norm_inner_self_eq_one hy₂] at e₄
  linear_combination c₁ * e₁ + c₂ * e₂ + d₁ * e₃ + d₂ * e₄

/-- Two pure states with the same equal mixture as `|a⟩⟨a|` and `|b⟩⟨b|` have the same overlap. -/
theorem norm_inner_eq_of_proj_add_proj_eq {x y a b : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (h : proj x + proj y = proj a + proj b) :
    ‖⟪x, y⟫_ℂ‖ = ‖⟪a, b⟫_ℂ‖ := by
  have h' := sq_add_sq_add_eq_of_smul_proj_add_smul_proj_eq hx hy ha hb (c₁ := 1) (c₂ := 1)
    (d₁ := 1) (d₂ := 1) (by simpa using h)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

/-- The product of two pure states. -/
lemma proj_mul_proj (x y : E) : proj x * proj y = ⟪x, y⟫_ℂ • rankOne ℂ x y :=
  rankOne_comp_rankOne x x y y

/-- A pure state is idempotent. -/
lemma proj_mul_proj_self {x : E} (hx : ‖x‖ = 1) : proj x * proj x = proj x :=
  isIdempotentElem_rankOne_self hx

/-- Orthogonal pure states multiply to zero. -/
lemma proj_mul_proj_of_inner_eq_zero {x y : E} (h : ⟪x, y⟫_ℂ = 0) : proj x * proj y = 0 := by
  rw [proj_mul_proj, h, zero_smul]

/-- Unit vectors with `|⟪x, y⟫| = 1` give the same pure state. -/
lemma proj_eq_proj_of_norm_inner_eq_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (h : ‖⟪x, y⟫_ℂ‖ = 1) : proj x = proj y := by
  obtain ⟨c, hc, rfl⟩ := exists_norm_eq_one_smul_of_norm_inner_eq_one hx hy h
  rw [proj_smul, hc]
  simp

/-- Orthogonal unit vectors give different pure states. -/
lemma proj_ne_proj_of_inner_eq_zero {r s : E} (hr : ‖r‖ = 1) (hrs : ⟪r, s⟫_ℂ = 0) :
    proj r ≠ proj s := by
  intro h
  have h' := congrArg (fun A : E →L[ℂ] E => ⟪r, A r⟫_ℂ) h
  simp only [inner_proj_apply, norm_inner_self_eq_one hr, inner_eq_zero_symm.mp hrs] at h'
  norm_num at h'

/-- **Two orthonormal pairs spanning the same plane.** If `r ⊥ s` and `x ⊥ y` are unit vectors
and `|r⟩⟨r| + |s⟩⟨s|` fixes `x` and `y`, then `|x⟩⟨x| + |y⟩⟨y| = |r⟩⟨r| + |s⟩⟨s|`. Both are
projections, the difference is a projection too, and its trace is `2 - 2 = 0`. -/
theorem proj_add_proj_eq_of_apply_eq [CompleteSpace E] {r s x y : E} (hr : ‖r‖ = 1)
    (hs : ‖s‖ = 1) (hrs : ⟪r, s⟫_ℂ = 0) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ⟪x, y⟫_ℂ = 0)
    (hQx : (proj r + proj s) x = x) (hQy : (proj r + proj s) y = y) :
    proj x + proj y = proj r + proj s := by
  set Q := proj r + proj s
  set R := proj x + proj y
  have hsr : ⟪s, r⟫_ℂ = 0 := inner_eq_zero_symm.mp hrs
  have hyx : ⟪y, x⟫_ℂ = 0 := inner_eq_zero_symm.mp hxy
  have hQQ : Q * Q = Q := by
    simp only [Q, add_mul, mul_add, proj_mul_proj_self hr, proj_mul_proj_self hs,
      proj_mul_proj_of_inner_eq_zero hrs, proj_mul_proj_of_inner_eq_zero hsr, add_zero, zero_add]
  have hRR : R * R = R := by
    simp only [R, add_mul, mul_add, proj_mul_proj_self hx, proj_mul_proj_self hy,
      proj_mul_proj_of_inner_eq_zero hxy, proj_mul_proj_of_inner_eq_zero hyx, add_zero, zero_add]
  have hstar : ∀ z : E, star (proj z) = proj z := fun z => by
    rw [star_eq_adjoint, adjoint_rankOne]
  have hQs : star Q = Q := by simp only [Q, star_add, hstar]
  have hRs : star R = R := by simp only [R, star_add, hstar]
  have hQR : Q * R = R := by
    simp only [R, mul_add, mul_def, comp_rankOne, hQx, hQy]
  have hRQ : R * Q = R := by
    have := congrArg star hQR
    rwa [star_mul, hQs, hRs] at this
  set D := Q - R
  have hDs : star D = D := by simp only [D, star_sub, hQs, hRs]
  have hDD : D * D = D := by
    simp only [D, sub_mul, mul_sub, hQQ, hQR, hRQ, hRR]
    abel
  have hD0 : 0 ≤ D := by
    have := star_mul_self_nonneg D
    rwa [hDs, hDD] at this
  have hR0 : 0 ≤ R := add_nonneg (proj_nonneg x) (proj_nonneg y)
  have htr : ∀ z : E, ‖z‖ = 1 → posTrace (proj z) = 1 := fun z hz =>
    (isDensityOperator_proj hz).posTrace_eq_one
  have h2 : posTrace R + posTrace D = posTrace R + 0 := by
    rw [← posTrace_add hR0 hD0, add_zero, show R + D = Q by simp [D]]
    simp only [Q, R, posTrace_add (proj_nonneg _) (proj_nonneg _), htr _ hr, htr _ hs,
      htr _ hx, htr _ hy]
  have hne : posTrace R ≠ ⊤ := by
    simp only [R, posTrace_add (proj_nonneg _) (proj_nonneg _), htr _ hx, htr _ hy]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.one_ne_top⟩
  have hD : D = 0 := (posTrace_eq_zero_iff hD0).mp ((ENNReal.add_right_inj hne).mp h2)
  exact (sub_eq_zero.mp hD).symm

/-- **Two-state decomposition, in the plane.** For unit `ψ, ϕ` with `|⟪ψ, ϕ⟫| < 1`,
`mix(|ψ⟩⟨ψ|, |ϕ⟩⟨ϕ|) = λ |r⟩⟨r| + (1 - λ) |s⟩⟨s|` with `λ = (1 + |⟪ψ, ϕ⟫|) / 2` and orthonormal
`r, s` that are fixed by every operator fixing `ψ` and `ϕ`. -/
lemma exists_mix_proj_eq_of_norm_inner_lt_one {ψ φ : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (h1 : ‖⟪ψ, φ⟫_ℂ‖ < 1) :
    ∃ r s : E, ‖r‖ = 1 ∧ ‖s‖ = 1 ∧ ⟪r, s⟫_ℂ = 0 ∧
      (∀ L : E →L[ℂ] E, L ψ = ψ → L φ = φ → L r = r ∧ L s = s) ∧
      mix (proj ψ) (proj φ) = (((1 + ‖⟪ψ, φ⟫_ℂ‖) / 2 : ℝ) : ℂ) • proj r +
        ((1 - (1 + ‖⟪ψ, φ⟫_ℂ‖) / 2 : ℝ) : ℂ) • proj s := by
  obtain ⟨w, hw, hwc⟩ := Complex.exists_norm_eq_mul_self ⟪ψ, φ⟫_ℂ
  set c := ‖⟪ψ, φ⟫_ℂ‖
  have hc0 : 0 ≤ c := norm_nonneg _
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hφφ : ⟪φ, φ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hcw : conj w * ⟪φ, ψ⟫_ℂ = c := by
    rw [← inner_conj_symm, ← map_mul, ← hwc, Complex.conj_ofReal]
  have hww : conj w * w = 1 := by rw [Complex.conj_mul', hw]; simp
  have hre : RCLike.re ⟪ψ, w • φ⟫_ℂ = c := by
    rw [inner_smul_right, ← hwc]; simp
  have hwφ : ‖w • φ‖ = 1 := by rw [norm_smul, hw, hφ, one_mul]
  set r₀ := ψ + w • φ
  set s₀ := ψ - w • φ
  have hr₀ : ‖r₀‖ ^ 2 = 2 + 2 * c := by rw [@norm_add_sq ℂ, hre, hψ, hwφ]; ring
  have hs₀ : ‖s₀‖ ^ 2 = 2 - 2 * c := by rw [@norm_sub_sq ℂ, hre, hψ, hwφ]; ring
  have hrs₀ : ⟪r₀, s₀⟫_ℂ = 0 := by
    simp only [r₀, s₀, inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right, hψψ,
      hφφ]
    linear_combination hcw + hwc - hww
  have h4 : (4 : ℂ) • mix (proj ψ) (proj φ) = proj r₀ + proj s₀ := by
    rw [proj_add_add_proj_sub, proj_smul, hw, smul_add, smul_smul, smul_smul, smul_smul]
    norm_num
  have hrpos : 0 < ‖r₀‖ := norm_pos_iff.mpr fun h0 => by rw [h0, norm_zero] at hr₀; linarith
  have hspos : 0 < ‖s₀‖ := norm_pos_iff.mpr fun h0 => by rw [h0, norm_zero] at hs₀; linarith
  refine ⟨(‖r₀‖ : ℂ)⁻¹ • r₀, (‖s₀‖ : ℂ)⁻¹ • s₀, ?_, ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hrpos.ne']
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hspos.ne']
  · rw [inner_smul_left, inner_smul_right, hrs₀, mul_zero, mul_zero]
  · intro L hLψ hLφ
    simp [r₀, s₀, hLψ, hLφ]
  · have hmix : mix (proj ψ) (proj φ) = (4⁻¹ : ℂ) • (proj r₀ + proj s₀) := by
      rw [← h4, smul_smul]; norm_num [mix]
    have hnr : ‖(‖r₀‖ : ℂ)⁻¹‖ ^ 2 = (2 + 2 * c)⁻¹ := by
      rw [norm_inv, Complex.norm_real, norm_norm, inv_pow, hr₀]
    have hns : ‖(‖s₀‖ : ℂ)⁻¹‖ ^ 2 = (2 - 2 * c)⁻¹ := by
      rw [norm_inv, Complex.norm_real, norm_norm, inv_pow, hs₀]
    have hc1 : (2 + 2 * (c : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (2 : ℝ) + 2 * c ≠ 0)
    have hc2 : (2 - 2 * (c : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (2 : ℝ) - 2 * c ≠ 0)
    have hc3 : (1 - (c : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) - c ≠ 0)
    rw [hmix, proj_smul, proj_smul, hnr, hns, smul_smul, smul_smul, smul_add]
    congr 2 <;> push_cast <;> field_simp <;> ring

/-! ## B. Orthogonal pure states stay orthogonal -/

/-- Three nonzero complex numbers of equal modulus cannot be pairwise orthogonal in `ℝ²`. -/
lemma not_pairwise_re_mul_conj_eq_zero {z₁ z₂ z₃ : ℂ} {k : ℝ} (hk : 0 < k)
    (h₁ : Complex.normSq z₁ = k) (h₂ : Complex.normSq z₂ = k) (h₃ : Complex.normSq z₃ = k)
    (h₁₂ : (z₁ * conj z₂).re = 0) (h₁₃ : (z₁ * conj z₃).re = 0)
    (h₂₃ : (z₂ * conj z₃).re = 0) : False := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im] at *
  -- `z₂` and `z₃` are both orthogonal to `z₁ ≠ 0`, so they are parallel.
  have hcross : z₂.re * z₃.im - z₂.im * z₃.re = 0 := by
    have : (z₁.re * z₁.re + z₁.im * z₁.im) * (z₂.re * z₃.im - z₂.im * z₃.re) = 0 := by
      linear_combination (z₁.re * z₃.im - z₁.im * z₃.re) * h₁₂ -
        (z₁.re * z₂.im - z₁.im * z₂.re) * h₁₃
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have : (z₂.re * z₂.re + z₂.im * z₂.im) * (z₃.re * z₃.re + z₃.im * z₃.im) = 0 := by
    linear_combination (z₂.re * z₃.re - -z₂.im * z₃.im) * h₂₃ +
      (z₂.re * z₃.im - z₂.im * z₃.re) * hcross
  rw [h₂, h₃] at this
  nlinarith

/-- **The latitude of an image.** Let `a, b` be unit vectors with `⟪a, b⟫ = δ ∈ (0, 1)`, and
`fp, fm` the orthonormal eigenvectors of `|a⟩⟨a| + |b⟩⟨b| = (1 + δ) |fp⟩⟨fp| + (1 - δ) |fm⟩⟨fm|`.
If also `|a⟩⟨a| + |b⟩⟨b| = |x⟩⟨x| + |y⟩⟨y|`, then `z = ⟪fm, |x⟩⟨x| fp⟫` has
`|z|² = (1 - δ²) / 4` and `y` gives `-z`. -/
theorem normSq_inner_proj_eq_of_proj_add_proj_eq {a b fp fm x y : E} {δ : ℝ} (hδ : 0 < δ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ‖⟪a, b⟫_ℂ‖ = δ) (hfp : ‖fp‖ = 1) (hfm : ‖fm‖ = 1)
    (hf : ⟪fp, fm⟫_ℂ = 0)
    (hK : proj a + proj b = ((1 + δ : ℝ) : ℂ) • proj fp + ((1 - δ : ℝ) : ℂ) • proj fm)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (h : proj x + proj y = proj a + proj b) :
    ⟪fm, proj y fp⟫_ℂ = -⟪fm, proj x fp⟫_ℂ ∧
      Complex.normSq ⟪fm, proj x fp⟫_ℂ = (1 - δ ^ 2) / 4 := by
  have hf' : ⟪fm, fp⟫_ℂ = 0 := inner_eq_zero_symm.mp hf
  constructor
  · have hz := congrArg (fun A : E →L[ℂ] E => ⟪fm, A fp⟫_ℂ) (h.trans hK)
    simp only [add_apply, smul_apply, inner_add_right, inner_smul_right, proj_apply,
      inner_self_eq_norm_sq_to_K, hfp, hf', mul_zero, zero_smul, inner_zero_right, add_zero] at hz
    simp only [proj_apply, inner_smul_right] at hz ⊢
    linear_combination hz
  · have hxy := norm_inner_eq_of_proj_add_proj_eq hx hy ha hb h
    -- `A = |⟪fp, x⟫|²`, `B = |⟪fm, x⟫|²` and the same for `y`.
    have e : ∀ u : E, ‖⟪x, u⟫_ℂ‖ ^ 2 + ‖⟪y, u⟫_ℂ‖ ^ 2 =
        (1 + δ) * ‖⟪fp, u⟫_ℂ‖ ^ 2 + (1 - δ) * ‖⟪fm, u⟫_ℂ‖ ^ 2 := fun u => by
      have h1 := re_inner_smul_proj_add_smul_proj 1 1 x y u
      have h2 := re_inner_smul_proj_add_smul_proj (1 + δ) (1 - δ) fp fm u
      simp only [Complex.ofReal_one, one_smul, one_mul] at h1
      rw [← h1, ← h2, h.trans hK]
    have ep := e fp
    have em := e fm
    have eₓ := e x
    simp only [norm_inner_self_eq_one hfp, norm_inner_self_eq_one hfm, norm_inner_self_eq_one hx,
      hf, hf', norm_zero] at ep em eₓ
    rw [norm_inner_symm y x, hxy, hab] at eₓ
    have bx := sq_norm_inner_add_sq_norm_inner_le_of_orthonormal hfp hfm hf x
    have by' := sq_norm_inner_add_sq_norm_inner_le_of_orthonormal hfp hfm hf y
    rw [hx] at bx
    rw [hy] at by'
    rw [norm_inner_symm x fp, norm_inner_symm y fp] at ep
    rw [norm_inner_symm x fm, norm_inner_symm y fm] at em
    set A := ‖⟪fp, x⟫_ℂ‖ ^ 2
    set B := ‖⟪fm, x⟫_ℂ‖ ^ 2
    have hsum : A + B = 1 := by nlinarith
    have hA : A = (1 + δ) / 2 := by
      have : δ * (2 * A - 1 - δ) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h0 | h0
      · linarith
      · linarith
    have hB : B = (1 - δ) / 2 := by linarith
    rw [proj_apply, inner_smul_right, Complex.normSq_mul, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, ← inner_conj_symm, Complex.norm_conj]
    change A * B = _
    rw [hA, hB]
    ring

variable [CompleteSpace E] {T : (E →L[ℂ] E) → E →L[ℂ] E}

/-- A map that is affine on density operators preserves their equal mixtures. -/
lemma AffineOnDensityOperators.map_mix (hT : AffineOnDensityOperators T) {ρ σ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) : T (mix ρ σ) = mix (T ρ) (T σ) := by
  have h := hT ρ σ hρ hσ 2⁻¹ (by norm_num) (by norm_num)
  norm_num at h
  simpa [mix, one_div] using h

omit [CompleteSpace E] in
/-- The vectors `(r + ω s) / √2` on the equator of the plane of an orthonormal pair `r, s`. -/
lemma inner_equator {r s : E} (hr : ‖r‖ = 1) (hs : ‖s‖ = 1) (hrs : ⟪r, s⟫_ℂ = 0) (ω ω' : ℂ) :
    ⟪(((√2)⁻¹ : ℝ) : ℂ) • (r + ω • s), (((√2)⁻¹ : ℝ) : ℂ) • (r + ω' • s)⟫_ℂ =
      (1 + conj ω * ω') / 2 := by
  have hκ : (((√2)⁻¹ : ℝ) : ℂ) * (((√2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
    push_cast
    ring
  have hrr : ⟪r, r⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hr]; simp
  have hss : ⟪s, s⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hs]; simp
  have hsr : ⟪s, r⟫_ℂ = 0 := inner_eq_zero_symm.mp hrs
  simp only [inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    Complex.conj_ofReal, hrr, hss, hrs, hsr]
  linear_combination (1 + conj ω * ω') * hκ

omit [CompleteSpace E] in
/-- The overlap of `r` with an equator vector. -/
lemma inner_left_equator {r s : E} (hr : ‖r‖ = 1) (hrs : ⟪r, s⟫_ℂ = 0) (ω : ℂ) :
    ⟪r, (((√2)⁻¹ : ℝ) : ℂ) • (r + ω • s)⟫_ℂ = (((√2)⁻¹ : ℝ) : ℂ) := by
  have hrr : ⟪r, r⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hr]; simp
  rw [inner_smul_right, inner_add_right, inner_smul_right, hrr, hrs, mul_zero, add_zero, mul_one]

omit [CompleteSpace E] in
/-- The equator vectors are unit vectors. -/
lemma norm_equator {r s : E} (hr : ‖r‖ = 1) (hs : ‖s‖ = 1) (hrs : ⟪r, s⟫_ℂ = 0) {ω : ℂ}
    (hω : ‖ω‖ = 1) : ‖(((√2)⁻¹ : ℝ) : ℂ) • (r + ω • s)‖ = 1 := by
  have h' : ‖(((√2)⁻¹ : ℝ) : ℂ) • (r + ω • s)‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, inner_equator hr hs hrs, Complex.conj_mul', hω]
    norm_num
  nlinarith [norm_nonneg ((((√2)⁻¹ : ℝ) : ℂ) • (r + ω • s))]

/-- **Orthogonal pure states stay orthogonal.** Let `T` be affine on density operators, map pure
states to pure states and be injective on them. If `r ⊥ s` and `T |r⟩⟨r| = |a⟩⟨a|`,
`T |s⟩⟨s| = |b⟩⟨b|` with `⟪a, b⟫ = δ ∈ (0, 1)`, then the functional `z(x) = ⟪f₋, T|x⟩⟨x| f₊⟫` on
the unit vectors of the plane of `r, s` takes values on the circle `|z|² = (1 - δ²) / 4`, and it
sends vectors with `|⟪x, y⟫|² = ½` to perpendicular points. The three vectors `r`, `(r + s)/√2`,
`(r + i s)/√2` are pairwise of this kind, which is impossible in the plane. -/
theorem AffineOnDensityOperators.false_of_inner_eq_ofReal (hT : AffineOnDensityOperators T)
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    {r s a b : E} (hr : ‖r‖ = 1) (hs : ‖s‖ = 1) (hrs : ⟪r, s⟫_ℂ = 0) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hTr : T (proj r) = proj a) (hTs : T (proj s) = proj b) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hab : ⟪a, b⟫_ℂ = δ) : False := by
  -- The eigenvectors `f₊ ∝ a + b` and `f₋ ∝ a - b` of `|a⟩⟨a| + |b⟩⟨b|`.
  have hba : ⟪b, a⟫_ℂ = δ := by rw [← inner_conj_symm, hab, Complex.conj_ofReal]
  have haa : ⟪a, a⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, ha]; simp
  have hbb : ⟪b, b⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hb]; simp
  have hre : RCLike.re ⟪a, b⟫_ℂ = δ := by rw [hab]; simp
  have hp : ‖a + b‖ ^ 2 = 2 * (1 + δ) := by rw [@norm_add_sq ℂ, hre, ha, hb]; ring
  have hm : ‖a - b‖ ^ 2 = 2 * (1 - δ) := by rw [@norm_sub_sq ℂ, hre, ha, hb]; ring
  have hp0 : 0 < ‖a + b‖ := norm_pos_iff.mpr fun h0 => by
    rw [h0, norm_zero] at hp; nlinarith
  have hm0 : 0 < ‖a - b‖ := norm_pos_iff.mpr fun h0 => by
    rw [h0, norm_zero] at hm; nlinarith
  set fp := (‖a + b‖ : ℂ)⁻¹ • (a + b)
  set fm := (‖a - b‖ : ℂ)⁻¹ • (a - b)
  have hfp : ‖fp‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hp0.ne']
  have hfm : ‖fm‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hm0.ne']
  have hf : ⟪fp, fm⟫_ℂ = 0 := by
    simp only [fp, fm, inner_smul_left, inner_smul_right, inner_add_left, inner_sub_right, haa,
      hbb, hab, hba]
    ring
  have hK : proj a + proj b = ((1 + δ : ℝ) : ℂ) • proj fp + ((1 - δ : ℝ) : ℂ) • proj fm := by
    have hnp : ‖(‖a + b‖ : ℂ)⁻¹‖ ^ 2 = (2 * (1 + δ))⁻¹ := by
      rw [norm_inv, Complex.norm_real, norm_norm, inv_pow, hp]
    have hnm : ‖(‖a - b‖ : ℂ)⁻¹‖ ^ 2 = (2 * (1 - δ))⁻¹ := by
      rw [norm_inv, Complex.norm_real, norm_norm, inv_pow, hm]
    have h1 : (1 + δ) * (2 * (1 + δ))⁻¹ = 2⁻¹ := by field_simp
    have h2 : (1 - δ) * (2 * (1 - δ))⁻¹ = 2⁻¹ := by
      have : 1 - δ ≠ 0 := by linarith
      field_simp
    rw [proj_smul, proj_smul, hnp, hnm, smul_smul, smul_smul, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul, h1, h2, ← smul_add, proj_add_add_proj_sub, smul_add, smul_smul,
      smul_smul]
    norm_num
  -- Pairs spanning the plane of `r, s` are sent to pairs with the same equal mixture as `a, b`.
  set Q := proj r + proj s
  have hpair : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ⟪x, y⟫_ℂ = 0 → Q x = x → Q y = y →
      ∀ x' y' : E, T (proj x) = proj x' → T (proj y) = proj y' →
        proj x' + proj y' = proj a + proj b := by
    intro x y hx hy hxy hQx hQy x' y' hTx hTy
    have hsum := proj_add_proj_eq_of_apply_eq hr hs hrs hx hy hxy hQx hQy
    have hmix : mix (proj x) (proj y) = mix (proj r) (proj s) := by
      simp only [mix, ← smul_add, hsum]
    have h := congrArg T hmix
    rw [hT.map_mix (isDensityOperator_proj hx) (isDensityOperator_proj hy),
      hT.map_mix (isDensityOperator_proj hr) (isDensityOperator_proj hs), hTx, hTy, hTr,
      hTs] at h
    have h2 := congrArg (fun A : E →L[ℂ] E => (2 : ℂ) • A) h
    simpa [mix, smul_add, smul_smul] using h2
  set g : E → ℂ := fun x => ⟪fm, T (proj x) fp⟫_ℂ
  set k : ℝ := (1 - δ ^ 2) / 4
  have hk : 0 < k := by
    have : δ ^ 2 < 1 := by nlinarith
    simp only [k]; linarith
  have hlat : ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ⟪x, y⟫_ℂ = 0 → Q x = x → Q y = y →
      g y = -g x ∧ Complex.normSq (g x) = k := by
    intro x y hx hy hxy hQx hQy
    obtain ⟨x', hx', hTx⟩ := hpure x hx
    obtain ⟨y', hy', hTy⟩ := hpure y hy
    have := normSq_inner_proj_eq_of_proj_add_proj_eq hδ0 ha hb (by rw [hab]; simp [abs_of_pos hδ0])
      hfp hfm hf hK hx' hy' (hpair x y hx hy hxy hQx hQy x' y' hTx hTy)
    simpa [g, hTx, hTy] using this
  -- Vectors at overlap `½` are sent to perpendicular points of the circle.
  have hperp : ∀ χ χ' η η' : E, ‖χ‖ = 1 → ‖χ'‖ = 1 → ⟪χ, χ'⟫_ℂ = 0 → Q χ = χ → Q χ' = χ' →
      ‖η‖ = 1 → ‖η'‖ = 1 → ⟪η, η'⟫_ℂ = 0 → Q η = η → Q η' = η' →
      ‖⟪χ, η⟫_ℂ‖ ^ 2 = 1 / 2 → (g χ * conj (g η)).re = 0 := by
    intro χ χ' η η' hχ hχ' hχχ' hQχ hQχ' hη hη' hηη' hQη hQη' hχη
    have hc0 := norm_nonneg ⟪χ, η⟫_ℂ
    have hlt : ‖⟪χ, η⟫_ℂ‖ < 1 := by nlinarith
    obtain ⟨r₀, s₀, hr₀, hs₀, hrs₀, hL, hdec⟩ := exists_mix_proj_eq_of_norm_inner_lt_one hχ hη hlt
    obtain ⟨hQr₀, hQs₀⟩ := hL Q hQχ hQη
    set c := ‖⟪χ, η⟫_ℂ‖
    have hT1 := congrArg T hdec
    rw [hT.map_mix (isDensityOperator_proj hχ) (isDensityOperator_proj hη),
      hT _ _ (isDensityOperator_proj hr₀) (isDensityOperator_proj hs₀) _ (by positivity)
        (by linarith)] at hT1
    have hz := congrArg (fun A : E →L[ℂ] E => ⟪fm, A fp⟫_ℂ) hT1
    simp only [mix, add_apply, smul_apply, inner_add_right, inner_smul_right] at hz
    obtain ⟨hg₀, -⟩ := hlat r₀ s₀ hr₀ hs₀ hrs₀ hQr₀ hQs₀
    have hsum : g χ + g η = (2 * c : ℝ) • g r₀ := by
      have : g s₀ = -g r₀ := hg₀
      simp only [g] at this ⊢
      rw [this] at hz
      rw [Complex.real_smul]
      push_cast at hz ⊢
      linear_combination 2 * hz
    have hn := congrArg Complex.normSq hsum
    rw [Complex.normSq_add, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal,
      (hlat χ χ' hχ hχ' hχχ' hQχ hQχ').2, (hlat η η' hη hη' hηη' hQη hQη').2,
      (hlat r₀ s₀ hr₀ hs₀ hrs₀ hQr₀ hQs₀).2] at hn
    have : 2 * c * (2 * c) = 2 := by nlinarith
    nlinarith
  -- The three test vectors.
  have hsr : ⟪s, r⟫_ℂ = 0 := inner_eq_zero_symm.mp hrs
  have hQr : Q r = r := by
    simp [Q, inner_self_eq_norm_sq_to_K, hr, hsr]
  have hQs : Q s = s := by
    simp [Q, inner_self_eq_norm_sq_to_K, hs, hrs]
  set e : ℂ → E := fun ω => (((√2)⁻¹ : ℝ) : ℂ) • (r + ω • s)
  have hQe : ∀ ω, Q (e ω) = e ω := fun ω => by
    simp only [e, map_smul, map_add, hQr, hQs]
  have he : ∀ ω : ℂ, ‖ω‖ = 1 → ‖e ω‖ = 1 := fun ω hω => norm_equator hr hs hrs hω
  have hee : ∀ ω : ℂ, ‖ω‖ = 1 → ⟪e ω, e (-ω)⟫_ℂ = 0 := fun ω hω => by
    simp only [e]
    rw [inner_equator hr hs hrs, mul_neg, Complex.conj_mul', hω]
    simp
  have hI : ‖(-Complex.I)‖ = 1 := by simp
  have hrel : ∀ ω : ℂ, ‖⟪r, e ω⟫_ℂ‖ ^ 2 = 1 / 2 := fun ω => by
    simp only [e]
    rw [inner_left_equator hr hrs, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num
  have h₁₂ := hperp r s (e 1) (e (-1)) hr hs hrs hQr hQs (he 1 (by simp)) (he _ (by simp))
    (hee 1 (by simp)) (hQe _) (hQe _) (hrel 1)
  have h₁₃ := hperp r s (e Complex.I) (e (-Complex.I)) hr hs hrs hQr hQs
    (he _ (by simp)) (he _ hI) (hee _ (by simp)) (hQe _) (hQe _) (hrel _)
  have h₂₃ := hperp (e 1) (e (-1)) (e Complex.I) (e (-Complex.I)) (he 1 (by simp))
    (he _ (by simp)) (hee 1 (by simp)) (hQe _) (hQe _) (he _ (by simp)) (he _ hI)
    (hee _ (by simp)) (hQe _) (hQe _) (by
      simp only [e]
      rw [inner_equator hr hs hrs, map_one, one_mul, ← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_apply]
      norm_num)
  exact not_pairwise_re_mul_conj_eq_zero hk (hlat r s hr hs hrs hQr hQs).2
    (hlat _ _ (he 1 (by simp)) (he _ (by simp)) (hee 1 (by simp)) (hQe _) (hQe _)).2
    (hlat _ _ (he _ (by simp)) (he _ hI) (hee _ (by simp)) (hQe _) (hQe _)).2 h₁₂ h₁₃ h₂₃

/-- **Orthogonal pure states stay orthogonal** under a map that is affine on density operators,
maps pure states to pure states and is injective on them. -/
theorem AffineOnDensityOperators.inner_eq_zero (hT : AffineOnDensityOperators T)
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (hinj : ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 → T (proj ψ) = T (proj φ) → proj ψ = proj φ)
    {r s a b : E} (hr : ‖r‖ = 1) (hs : ‖s‖ = 1) (hrs : ⟪r, s⟫_ℂ = 0) (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hTr : T (proj r) = proj a) (hTs : T (proj s) = proj b) :
    ⟪a, b⟫_ℂ = 0 := by
  by_contra h0
  have hδ0 : 0 < ‖⟪a, b⟫_ℂ‖ := norm_pos_iff.mpr h0
  have hδ1 : ‖⟪a, b⟫_ℂ‖ < 1 := by
    refine lt_of_le_of_ne (by simpa [ha, hb] using norm_inner_le_norm (𝕜 := ℂ) a b) fun h1 => ?_
    have := hinj r s hr hs (by rw [hTr, hTs, proj_eq_proj_of_norm_inner_eq_one ha hb h1])
    exact proj_ne_proj_of_inner_eq_zero hr hrs this
  obtain ⟨w, hw, hwc⟩ := Complex.exists_norm_eq_mul_self ⟪a, b⟫_ℂ
  have hwb : ‖w • b‖ = 1 := by rw [norm_smul, hw, hb, one_mul]
  have hTs' : T (proj s) = proj (w • b) := by rw [hTs, proj_smul, hw]; simp
  exact hT.false_of_inner_eq_ofReal hpure hr hs hrs ha hwb hTr hTs' hδ0 hδ1
    (by rw [inner_smul_right, hwc])

/-! ## C. Overlaps are preserved -/

omit [CompleteSpace E] in
/-- Equal pure states have overlap one. -/
lemma norm_inner_eq_one_of_proj_eq {x y : E} (hx : ‖x‖ = 1) (h : proj x = proj y) :
    ‖⟪x, y⟫_ℂ‖ = 1 := by
  have h' : ((1 : ℝ) : ℂ) = ((‖⟪y, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    have := congrArg (fun A : E →L[ℂ] E => ⟪x, A x⟫_ℂ) h
    simpa only [inner_proj_apply, norm_inner_self_eq_one hx, one_pow] using this
  have h'' : ‖⟪y, x⟫_ℂ‖ ^ 2 = 1 := by exact_mod_cast h'.symm
  rw [norm_inner_symm]
  nlinarith [norm_nonneg ⟪y, x⟫_ℂ]

/-- **Overlaps are preserved** by a map that is affine on density operators, maps pure states to
pure states and is injective on them. Write `mix(|ψ⟩⟨ψ|, |ϕ⟩⟨ϕ|) = λ |r⟩⟨r| + (1 - λ) |s⟩⟨s|`
with `r ⊥ s`; the images of `r, s` are orthogonal, and the Hilbert–Schmidt square of the two
sides gives `|⟪ψ', ϕ'⟫|² = |⟪ψ, ϕ⟫|²`. -/
theorem AffineOnDensityOperators.norm_inner_eq (hT : AffineOnDensityOperators T)
    (hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ')
    (hinj : ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 → T (proj ψ) = T (proj φ) → proj ψ = proj φ)
    {ψ φ ψ' φ' : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (hψ' : ‖ψ'‖ = 1) (hφ' : ‖φ'‖ = 1)
    (hTψ : T (proj ψ) = proj ψ') (hTφ : T (proj φ) = proj φ') :
    ‖⟪ψ', φ'⟫_ℂ‖ = ‖⟪ψ, φ⟫_ℂ‖ := by
  have hc : ‖⟪ψ, φ⟫_ℂ‖ ≤ 1 := by simpa [hψ, hφ] using norm_inner_le_norm (𝕜 := ℂ) ψ φ
  rcases hc.lt_or_eq with hlt | heq
  · obtain ⟨r₀, s₀, hr₀, hs₀, hrs₀, -, hdec⟩ := exists_mix_proj_eq_of_norm_inner_lt_one hψ hφ hlt
    obtain ⟨r', hr', hTr⟩ := hpure r₀ hr₀
    obtain ⟨s', hs', hTs⟩ := hpure s₀ hs₀
    have hrs' := hT.inner_eq_zero hpure hinj hr₀ hs₀ hrs₀ hr' hs' hTr hTs
    have hc0 := norm_nonneg ⟪ψ, φ⟫_ℂ
    have hT1 := congrArg T hdec
    rw [hT.map_mix (isDensityOperator_proj hψ) (isDensityOperator_proj hφ), hTψ, hTφ,
      hT _ _ (isDensityOperator_proj hr₀) (isDensityOperator_proj hs₀) _ (by positivity)
        (by linarith), hTr, hTs] at hT1
    have h1 := sq_add_sq_add_eq_of_smul_proj_add_smul_proj_eq hψ' hφ' hr' hs' (c₁ := 2⁻¹)
      (c₂ := 2⁻¹) (by rw [← hT1]; simp [mix])
    rw [hrs', norm_zero] at h1
    have : ‖⟪ψ', φ'⟫_ℂ‖ ^ 2 = ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by linear_combination 2 * h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
  · rw [heq]
    exact norm_inner_eq_one_of_proj_eq hψ'
      (by rw [← hTψ, ← hTφ, proj_eq_proj_of_norm_inner_eq_one hψ hφ heq])

/-- **Wigner's theorem for affine maps.** An affine map of the density operators that is a
bijection of the pure states agrees on them with conjugation by a unitary or an anti-unitary. -/
theorem AffineOnDensityOperators.exists_unitary_or_antiunitary (hT : AffineOnDensityOperators T)
    (hbij : BijOnPure T) :
    (∃ W : E ≃ₗᵢ[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → T (proj ψ) = proj (W ψ)) ∨
      ∃ W : E ≃ₗᵢ⋆[ℂ] E, ∀ ψ : E, ‖ψ‖ = 1 → T (proj ψ) = proj (W ψ) := by
  classical
  have hpure : ∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ T (proj ψ) = proj ψ' := fun ψ hψ => by
    obtain ⟨ψ', hψ', h⟩ := hbij.mapsTo (⟨ψ, hψ, rfl⟩ : IsPure (proj ψ))
    exact ⟨ψ', hψ', h⟩
  have hinj : ∀ ψ φ : E, ‖ψ‖ = 1 → ‖φ‖ = 1 → T (proj ψ) = T (proj φ) → proj ψ = proj φ :=
    fun ψ φ hψ hφ h => hbij.injOn (⟨ψ, hψ, rfl⟩ : IsPure (proj ψ)) ⟨φ, hφ, rfl⟩ h
  let f : E → E := fun ψ => if h : ‖ψ‖ = 1 then (hpure ψ h).choose else 0
  have hf : ∀ ψ (h : ‖ψ‖ = 1), ‖f ψ‖ = 1 ∧ T (proj ψ) = proj (f ψ) := fun ψ h => by
    simpa [f, h] using (hpure ψ h).choose_spec
  have hw : IsWignerMap f := fun v w hv hw =>
    hT.norm_inner_eq hpure hinj hv hw (hf v hv).1 (hf w hw).1 (hf v hv).2 (hf w hw).2
  have hs : ∀ w : E, ‖w‖ = 1 → ∃ v, ‖v‖ = 1 ∧ PhaseEq (f v) w := fun w hw => by
    obtain ⟨ρ, ⟨v, hv, rfl⟩, h⟩ := hbij.surjOn (⟨w, hw, rfl⟩ : IsPure (proj w))
    exact ⟨v, hv, phaseEq_of_rankOne_self_eq (hf v hv).1 hw ((hf v hv).2.symm.trans h)⟩
  rcases hw.exists_unitary_or_antiunitary_of_surjective hs with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun ψ hψ => (hf ψ hψ).2.trans (hU ψ hψ).rankOne_self⟩
  · exact Or.inr ⟨U, fun ψ hψ => (hf ψ hψ).2.trans (hU ψ hψ).rankOne_self⟩

/-! ## D. Mixed states follow from pure states -/

/-- The trace in `[0, ∞]` is additive on finite sums of positive operators. -/
lemma posTrace_sum {ι : Type*} (s : Finset ι) {A : ι → E →L[ℂ] E} (hA : ∀ i ∈ s, 0 ≤ A i) :
    posTrace (∑ i ∈ s, A i) = ∑ i ∈ s, posTrace (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      posTrace_add (hA a (by simp)) (Finset.sum_nonneg fun i hi => hA i (by simp [hi])),
      ih fun i hi => hA i (by simp [hi])]

/-- A nonnegative real multiple of a positive operator is positive. -/
lemma smul_nonneg_of_nonneg {r : ℝ} (hr : 0 ≤ r) {A : E →L[ℂ] E} (hA : 0 ≤ A) :
    0 ≤ (r : ℂ) • A := by
  rw [Complex.coe_smul]; exact smul_nonneg hr hA

/-- Density operators are closed under finite convex combinations. -/
theorem IsDensityOperator.sum {ι : Type*} {s : Finset ι} {μ : ι → ℝ} {ρ : ι → E →L[ℂ] E}
    (hμ : ∀ i ∈ s, 0 ≤ μ i) (hμ1 : ∑ i ∈ s, μ i = 1) (hρ : ∀ i ∈ s, IsDensityOperator (ρ i)) :
    IsDensityOperator (∑ i ∈ s, (μ i : ℂ) • ρ i) := by
  have h0 : ∀ i ∈ s, 0 ≤ (μ i : ℂ) • ρ i := fun i hi => smul_nonneg_of_nonneg (hμ i hi)
    (hρ i hi).nonneg
  refine isDensityOperator_iff.mpr ⟨Finset.sum_nonneg h0, ?_⟩
  rw [posTrace_sum s h0, Finset.sum_congr rfl fun i hi => by
    rw [posTrace_smul (hμ i hi), (hρ i hi).posTrace_eq_one, mul_one],
    ← ENNReal.ofReal_sum_of_nonneg hμ, hμ1, ENNReal.ofReal_one]

/-- A map that is affine on density operators preserves their finite convex combinations. -/
theorem AffineOnDensityOperators.map_sum (hT : AffineOnDensityOperators T) {ι : Type*}
    (s : Finset ι) {μ : ι → ℝ} {ρ : ι → E →L[ℂ] E} (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (hμ1 : ∑ i ∈ s, μ i = 1) (hρ : ∀ i ∈ s, IsDensityOperator (ρ i)) :
    T (∑ i ∈ s, (μ i : ℂ) • ρ i) = ∑ i ∈ s, (μ i : ℂ) • T (ρ i) := by
  classical
  induction s using Finset.induction_on generalizing μ with
  | empty => simp at hμ1
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hμ1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hm0 : 0 ≤ ∑ i ∈ s, μ i := Finset.sum_nonneg fun i hi => hμ i (by simp [hi])
    have hma : μ a = 1 - ∑ i ∈ s, μ i := by linarith
    rcases hm0.eq_or_lt with hm | hm
    · have h0 : ∀ i ∈ s, μ i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i hi => hμ i (by simp [hi])).mp hm.symm
      have hs0 : ∀ τ : ι → E →L[ℂ] E, ∑ i ∈ s, (μ i : ℂ) • τ i = 0 := fun τ =>
        Finset.sum_eq_zero fun i hi => by simp [h0 i hi]
      rw [hs0, hs0, show μ a = 1 by linarith]
      simp
    set m := ∑ i ∈ s, μ i
    have hν1 : ∑ i ∈ s, μ i / m = 1 := by rw [← Finset.sum_div, div_self hm.ne']
    have hν : ∀ i ∈ s, 0 ≤ μ i / m := fun i hi => div_nonneg (hμ i (by simp [hi])) hm0
    have hρs : ∀ i ∈ s, IsDensityOperator (ρ i) := fun i hi => hρ i (by simp [hi])
    have hsplit : ∀ τ : ι → E →L[ℂ] E,
        ∑ i ∈ s, (μ i : ℂ) • τ i = ((1 - μ a : ℝ) : ℂ) • ∑ i ∈ s, ((μ i / m : ℝ) : ℂ) • τ i := by
      intro τ
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ← Complex.ofReal_mul, hma, sub_sub_cancel, mul_div_cancel₀ _ hm.ne']
    rw [hsplit, hsplit, hT _ _ (hρ a (by simp)) (IsDensityOperator.sum hν hν1 hρs) _
      (hμ a (by simp)) (by linarith), ih hν hν1 hρs]

/-- **The tails of the canonical expansion.** A density operator is `ρ = ∑ᵢ μᵢ |bᵢ⟩⟨bᵢ|` over a
Hilbert basis, with `μᵢ ≥ 0` summing to one, and for every finite set `F` of indices the tail
`ρ - ∑_{i ∈ F} μᵢ |bᵢ⟩⟨bᵢ|` is positive of trace `1 - ∑_{i ∈ F} μᵢ`. -/
theorem IsDensityOperator.exists_tail {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    ∃ (w : Set E) (b : HilbertBasis w ℂ E) (μ : w → ℝ), (∀ i, 0 ≤ μ i) ∧ HasSum μ 1 ∧
      ∀ F : Finset w, 0 ≤ ρ - ∑ i ∈ F, (μ i : ℂ) • proj (b i) ∧
        posTrace (ρ - ∑ i ∈ F, (μ i : ℂ) • proj (b i)) + ENNReal.ofReal (∑ i ∈ F, μ i) = 1 := by
  classical
  obtain ⟨w, b, μ, -, -, hμ0, hμ1, -, hS⟩ := hρ.isTraceClass.exists_hasSum_rankOne hρ.nonneg
  rw [hρ.traceNorm_eq_one] at hμ1
  have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have hP0 : ∀ F : Finset w, 0 ≤ ∑ i ∈ F, (μ i : ℂ) • proj (b i) := fun F =>
    Finset.sum_nonneg fun i _ => smul_nonneg_of_nonneg (hμ0 i) (proj_nonneg _)
  have htail : ∀ F : Finset w, 0 ≤ ρ - ∑ i ∈ F, (μ i : ℂ) • proj (b i) := by
    intro F
    have h := (hasSum_ite_not_mem hS F).mapL toOperator
    rw [map_sub, _root_.map_sum] at h
    simp only [toOperator_apply, ofOperator_coe] at h
    refine h.nonneg fun i => ?_
    split_ifs
    · exact le_refl (0 : E →L[ℂ] E)
    · exact smul_nonneg_of_nonneg (hμ0 i) (proj_nonneg _)
  refine ⟨w, b, μ, hμ0, hμ1, fun F => ⟨htail F, ?_⟩⟩
  rw [← hρ.posTrace_eq_one, add_comm]
  conv_rhs => rw [← add_sub_cancel (∑ i ∈ F, (μ i : ℂ) • proj (b i)) ρ]
  rw [posTrace_add (hP0 F) (htail F), posTrace_sum F fun i _ =>
    smul_nonneg_of_nonneg (hμ0 i) (proj_nonneg _), ENNReal.ofReal_sum_of_nonneg
    fun i _ => hμ0 i]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [posTrace_smul (hμ0 i), (isDensityOperator_proj (hbn i)).posTrace_eq_one, mul_one]

/-- **Mixed-state extension.** A map that sends density operators to density operators, is
affine on them and agrees on pure states with conjugation by a unitary or an anti-unitary `W`
agrees with it on every density operator. Write `ρ = m ρ_F + (1 - m) σ_F` with `ρ_F` a finite
part of the canonical expansion, of weight `m`, and `σ_F` the normalized tail. Both maps agree on
`ρ_F`, so they differ on `ρ` by `(1 - m)` times a difference of two operators of norm at most
one, and `m` can be taken as close to `1` as we like. -/
theorem AffineOnDensityOperators.eq_conjOp (hT : AffineOnDensityOperators T)
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (T ρ)) {σ : ℂ →+* ℂ}
    [RingHomInvPair σ σ] [RingHomIsometric σ] {W : E ≃ₛₗᵢ[σ] E}
    (hW : ∀ ψ : E, ‖ψ‖ = 1 → T (proj ψ) = proj (W ψ)) {ρ : E →L[ℂ] E}
    (hρ : IsDensityOperator ρ) : T ρ = conjOp W ρ := by
  obtain ⟨w, b, μ, hμ0, hμ1, htail⟩ := hρ.exists_tail
  have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  -- Both maps agree on finite mixtures of the eigenvectors.
  have hfin : ∀ (F : Finset w) (ν : w → ℝ), (∀ i ∈ F, 0 ≤ ν i) → ∑ i ∈ F, ν i = 1 →
      T (∑ i ∈ F, (ν i : ℂ) • proj (b i)) = conjOp W (∑ i ∈ F, (ν i : ℂ) • proj (b i)) := by
    intro F ν hν hν1
    rw [hT.map_sum F hν hν1 fun i _ => isDensityOperator_proj (hbn i), conjOp_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [conjOp_ofReal_smul, conjOp_proj, hW _ (hbn i)]
  set τ := T ρ - conjOp W ρ
  suffices h : ∀ ε : ℝ, 0 < ε → ε < 1 → ‖τ‖ ≤ 2 * ε by
    have hτ : ‖τ‖ = 0 := by
      by_contra hne
      have hpos : 0 < ‖τ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      have h1 := h (min (‖τ‖ / 4) (1 / 2)) (by positivity)
        ((min_le_right _ _).trans_lt (by norm_num))
      have h2 : min (‖τ‖ / 4) (1 / 2) ≤ ‖τ‖ / 4 := min_le_left _ _
      linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp hτ)
  intro ε hε hε1
  have hμt : Tendsto (fun F : Finset w => ∑ i ∈ F, μ i) atTop (𝓝 1) := hμ1
  obtain ⟨F, hF⟩ : ∃ F : Finset w, 1 - ε < ∑ i ∈ F, μ i :=
    (hμt.eventually (lt_mem_nhds (by linarith))).exists
  set m := ∑ i ∈ F, μ i with hm
  set R := ρ - ∑ i ∈ F, (μ i : ℂ) • proj (b i) with hR
  have hm1 : m ≤ 1 := by
    have : ENNReal.ofReal m ≤ 1 := by rw [← (htail F).2]; exact le_add_self
    exact ENNReal.ofReal_le_one.mp this
  have hm0 : 0 < m := by linarith
  rcases hm1.lt_or_eq with hlt | heq
  · have hRtr : posTrace R = ENNReal.ofReal (1 - m) := by
      have h2 : ENNReal.ofReal (1 - m) + ENNReal.ofReal m = 1 := by
        rw [← ENNReal.ofReal_add (by linarith) hm0.le]; simp
      exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp ((htail F).2.trans h2.symm)
    have hσ := isDensityOperator_inv_smul (htail F).1 (sub_pos.mpr hlt) hRtr
    set σF := (((1 - m)⁻¹ : ℝ) : ℂ) • R
    set ν : w → ℝ := fun i => μ i / m
    have hν1 : ∑ i ∈ F, ν i = 1 := by simp only [ν]; rw [← Finset.sum_div, div_self hm0.ne']
    have hν0 : ∀ i ∈ F, 0 ≤ ν i := fun i _ => div_nonneg (hμ0 i) hm0.le
    have hρF := IsDensityOperator.sum hν0 hν1 fun i _ => isDensityOperator_proj (hbn i)
    have hdec : ρ = (m : ℂ) • ∑ i ∈ F, (ν i : ℂ) • proj (b i) + ((1 - m : ℝ) : ℂ) • σF := by
      have h1 : (m : ℂ) • ∑ i ∈ F, (ν i : ℂ) • proj (b i) = ∑ i ∈ F, (μ i : ℂ) • proj (b i) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← Complex.ofReal_mul, mul_div_cancel₀ _ hm0.ne']
      have h2 : ((1 - m : ℝ) : ℂ) • σF = R := by
        rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (sub_pos.mpr hlt).ne',
          Complex.ofReal_one, one_smul]
      rw [h1, h2, hR, add_sub_cancel]
    have hTρ : T ρ = (m : ℂ) • T (∑ i ∈ F, (ν i : ℂ) • proj (b i)) +
        ((1 - m : ℝ) : ℂ) • T σF := by
      conv_lhs => rw [hdec]
      exact hT _ _ hρF hσ m hm0.le hm1
    have hCρ : conjOp W ρ = (m : ℂ) • conjOp W (∑ i ∈ F, (ν i : ℂ) • proj (b i)) +
        ((1 - m : ℝ) : ℂ) • conjOp W σF := by
      conv_lhs => rw [hdec]
      rw [conjOp_add, conjOp_ofReal_smul, conjOp_ofReal_smul]
    have hτ : τ = ((1 - m : ℝ) : ℂ) • (T σF - conjOp W σF) := by
      simp only [τ]
      rw [hTρ, hCρ, hfin F ν hν0 hν1, smul_sub]
      abel
    rw [hτ, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have h1 : ‖T σF - conjOp W σF‖ ≤ 2 := by
      calc _ ≤ ‖T σF‖ + ‖conjOp W σF‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (hD _ hσ).norm_le_one
            ((norm_conjOp_le W σF).trans hσ.norm_le_one)
        _ = 2 := by norm_num
    nlinarith
  · have hR0 : R = 0 := by
      have h1 : posTrace R + ENNReal.ofReal m = 1 := (htail F).2
      rw [heq, ENNReal.ofReal_one] at h1
      have h2 : (1 : ℝ≥0∞) + posTrace R = 1 + 0 := by rw [add_comm, h1, add_zero]
      exact (posTrace_eq_zero_iff (htail F).1).mp
        ((ENNReal.add_right_inj ENNReal.one_ne_top).mp h2)
    have hρeq : ρ = ∑ i ∈ F, (μ i : ℂ) • proj (b i) := sub_eq_zero.mp hR0
    have : τ = 0 := by
      show T ρ - conjOp W ρ = 0
      rw [hρeq, hfin F μ (fun i _ => hμ0 i) (hm.symm.trans heq), sub_self]
    rw [this, norm_zero]
    linarith

/-! ## E. Conjugation preserves density operators -/

section Conj

variable {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ] (W : E ≃ₛₗᵢ[σ] E)

omit [CompleteSpace E] [RingHomIsometric σ] in
/-- Conjugation is multiplicative. -/
lemma conjOp_mul (A B : E →L[ℂ] E) : conjOp W (A * B) = conjOp W A * conjOp W B := by
  ext x
  simp [conjOp_apply]

/-- Conjugation commutes with the adjoint. -/
lemma conjOp_star (A : E →L[ℂ] E) : conjOp W (star A) = star (conjOp W A) := by
  rw [star_eq_adjoint, star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun x y => ?_
  have h1 := W.toLinearIsometry.inner_map_map_semilinear
    (ContinuousLinearMap.adjoint A (W.symm x)) (W.symm y)
  have h2 := W.toLinearIsometry.inner_map_map_semilinear (W.symm x) (A (W.symm y))
  simp only [LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
    at h1 h2
  rw [conjOp_apply, conjOp_apply, h1, h2, ContinuousLinearMap.adjoint_inner_left]

/-- Conjugation by a unitary or an anti-unitary preserves positivity. -/
lemma conjOp_nonneg {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) : 0 ≤ conjOp W ρ := by
  rw [← ContinuousLinearMap.sqrt_mul_star_sqrt hρ, conjOp_mul, conjOp_star]
  exact mul_star_self_nonneg _

omit [RingHomInvPair σ σ] [RingHomIsometric σ] in
/-- Conjugation by a unitary preserves the trace. -/
lemma posTrace_conjOp_of_linear (U : E ≃ₗᵢ[ℂ] E) {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) :
    posTrace (conjOp U ρ) = posTrace ρ := by
  have h : conjOp U ρ = (U : E →L[ℂ] E) * ρ * star (U : E →L[ℂ] E) := by
    ext x
    simp [conjOp_apply, LinearIsometryEquiv.star_eq_symm]
  rw [h, ContinuousLinearMap.posTrace_conj_of_star_mul_self hρ]
  ext x
  simp [LinearIsometryEquiv.star_eq_symm]

omit [RingHomInvPair σ σ] [RingHomIsometric σ] in
/-- Coordinatewise conjugation in a Hilbert basis preserves the trace. -/
lemma posTrace_conjOp_conjugation {ι : Type*} (b : HilbertBasis ι ℂ E) {ρ : E →L[ℂ] E}
    (hρ : 0 ≤ ρ) : posTrace (conjOp b.conjugation ρ) = posTrace ρ := by
  rw [ContinuousLinearMap.posTrace_eq_tsum (conjOp_nonneg _ hρ) b,
    ContinuousLinearMap.posTrace_eq_tsum hρ b]
  congr! 3 with i
  rw [conjOp_apply, HilbertBasis.conjugation_symm, HilbertBasis.conjugation_basis,
    HilbertBasis.inner_basis_conjugation, Complex.conj_re]

/-- Conjugation by a unitary or an anti-unitary preserves the trace. An anti-unitary is a unitary
after the coordinatewise conjugation of a Hilbert basis, which fixes the trace in that basis. -/
theorem posTrace_conjOp {ρ : E →L[ℂ] E} (hρ : 0 ≤ ρ) : posTrace (conjOp W ρ) = posTrace ρ := by
  obtain rfl | rfl := Complex.ringHom_eq_id_or_conj_of_isometric σ
  · exact posTrace_conjOp_of_linear W hρ
  · set J := (ContinuousLinearMap.posTraceBasis E).conjugation
    have h : conjOp W ρ = conjOp (J.trans W : E ≃ₗᵢ[ℂ] E) (conjOp J ρ) := by
      ext x
      simp [conjOp_apply, LinearIsometryEquiv.symm_trans, J]
    rw [h, posTrace_conjOp_of_linear _ (conjOp_nonneg J hρ), posTrace_conjOp_conjugation _ hρ]

/-- Conjugation by a unitary or an anti-unitary preserves density operators. -/
theorem IsDensityOperator.conjOp {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    IsDensityOperator (Wigner.conjOp W ρ) :=
  isDensityOperator_iff.mpr ⟨conjOp_nonneg W hρ.nonneg, by
    rw [posTrace_conjOp W hρ.nonneg, hρ.posTrace_eq_one]⟩

end Conj

/-! ## F. Pure states are the extreme points -/

/-- `ρ` is an extreme point of the density operators: in every proper mixture
`ρ = t σ + (1 - t) τ` of density operators, `σ = ρ`. -/
def IsExtremeDensityOperator (ρ : E →L[ℂ] E) : Prop :=
  IsDensityOperator ρ ∧ ∀ σ τ : E →L[ℂ] E, IsDensityOperator σ → IsDensityOperator τ →
    ∀ t : ℝ, 0 < t → t < 1 → ρ = (t : ℂ) • σ + ((1 - t : ℝ) : ℂ) • τ → σ = ρ

/-- A density operator that kills the orthogonal complement of a unit vector `ψ` is `|ψ⟩⟨ψ|`. -/
lemma IsDensityOperator.eq_proj_of_apply_eq_zero {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ)
    {ψ : E} (hψ : ‖ψ‖ = 1) (h : ∀ x, ⟪ψ, x⟫_ℂ = 0 → ρ x = 0) : ρ = proj ψ := by
  have hpos := ContinuousLinearMap.nonneg_iff_isPositive.mp hρ.nonneg
  have hperp : ∀ x, ⟪ψ, x - ⟪ψ, x⟫_ℂ • ψ⟫_ℂ = 0 := fun x => by
    simp [inner_sub_right, inner_smul_right, hψ]
  have hsymm : ∀ x y, ⟪ρ x, y⟫_ℂ = ⟪x, ρ y⟫_ℂ := hpos.isSymmetric
  set c := ⟪ψ, ρ ψ⟫_ℂ
  have hc : ρ ψ = c • ψ := by
    set r := ρ ψ - c • ψ
    have hr : ⟪r, r⟫_ℂ = 0 := by
      calc ⟪r, r⟫_ℂ = ⟪r, ρ ψ⟫_ℂ - c * ⟪r, ψ⟫_ℂ := by
            rw [← inner_smul_right, ← inner_sub_right]
        _ = 0 := by
          rw [← hsymm, h r (hperp _), inner_zero_left, ← inner_conj_symm, hperp, map_zero,
            mul_zero, sub_zero]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hr)
  have hρc : ρ = c • proj ψ := by
    ext x
    have hx := h _ (hperp x)
    rw [map_sub, map_smul, hc, sub_eq_zero] at hx
    rw [hx, smul_apply, proj_apply, smul_smul, smul_smul, mul_comm]
  -- `c ≥ 0` is real, and the trace fixes it to one.
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hpos.inner_nonneg_right ψ)
  have hcre : c = (c.re : ℂ) := Complex.ext rfl (by simpa using him.symm)
  have h1 := hρ.posTrace_eq_one
  rw [hρc, hcre, posTrace_smul hre, (isDensityOperator_proj hψ).posTrace_eq_one, mul_one,
    ENNReal.ofReal_eq_one] at h1
  rw [hρc, hcre, h1, Complex.ofReal_one, one_smul]

/-- **Pure ⇒ extreme.** If `|ψ⟩⟨ψ| = t σ + (1 - t) τ` with `0 < t < 1`, the quadratic form of `σ`
vanishes on `ψ^⊥`, so `σ` kills `ψ^⊥` by positivity, and `σ = |ψ⟩⟨ψ|` by the trace. -/
lemma IsPure.isExtremeDensityOperator {ρ : E →L[ℂ] E} (h : IsPure ρ) :
    IsExtremeDensityOperator ρ := by
  obtain ⟨ψ, hψ, rfl⟩ := h
  refine ⟨isDensityOperator_proj hψ, fun σ τ hσ hτ t ht0 ht1 hmix => ?_⟩
  refine hσ.eq_proj_of_apply_eq_zero hψ fun x hx => ?_
  have hσp := ContinuousLinearMap.nonneg_iff_isPositive.mp hσ.nonneg
  have hτp := ContinuousLinearMap.nonneg_iff_isPositive.mp hτ.nonneg
  have key := congrArg (fun A : E →L[ℂ] E => (⟪x, A x⟫_ℂ).re) hmix
  simp only [inner_proj_apply, hx, norm_zero, add_apply, smul_apply, inner_add_right,
    inner_smul_right, Complex.add_re, Complex.re_ofReal_mul] at key
  have h1 := hσp.re_inner_nonneg_right x
  have h2 := hτp.re_inner_nonneg_right x
  simp only [RCLike.re_to_complex] at h1 h2
  have h0 : (⟪x, σ x⟫_ℂ).re = 0 := by
    norm_num at key
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) h2]
  have := hσp.toLinearMap.apply_eq_zero_of_re_inner_eq_zero (x := x)
    (by rw [inner_re_symm]; simpa using h0)
  simpa using this

/-- **Extreme ⇒ pure.** Pick a weight `μᵢ > 0` in the canonical expansion. If `μᵢ < 1`, then `ρ` is
the proper mixture of `|bᵢ⟩⟨bᵢ|` and the normalized tail, so `ρ = |bᵢ⟩⟨bᵢ|`. If `μᵢ = 1`, the tail
has trace zero and vanishes. -/
lemma IsExtremeDensityOperator.isPure {ρ : E →L[ℂ] E} (h : IsExtremeDensityOperator ρ) :
    IsPure ρ := by
  classical
  obtain ⟨hρ, hext⟩ := h
  obtain ⟨w, b, μ, hμ0, hμ1, htail⟩ := hρ.exists_tail
  have hbn : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  obtain ⟨i, hi⟩ : ∃ i, 0 < μ i := by
    by_contra! h
    have : μ = 0 := funext fun i => le_antisymm (h i) (hμ0 i)
    rw [this] at hμ1
    exact one_ne_zero (hμ1.unique hasSum_zero)
  obtain ⟨hR0, hRtr⟩ := htail {i}
  simp only [Finset.sum_singleton] at hR0 hRtr
  have hm1 : μ i ≤ 1 := by
    have : ENNReal.ofReal (μ i) ≤ 1 := by rw [← hRtr]; exact le_add_self
    exact ENNReal.ofReal_le_one.mp this
  rcases hm1.lt_or_eq with hlt | heq
  · have hRtr' : posTrace (ρ - (μ i : ℂ) • proj (b i)) = ENNReal.ofReal (1 - μ i) := by
      have h2 : ENNReal.ofReal (1 - μ i) + ENNReal.ofReal (μ i) = 1 := by
        rw [← ENNReal.ofReal_add (by linarith) (hμ0 i)]; simp
      exact (ENNReal.add_left_inj ENNReal.ofReal_ne_top).mp (hRtr.trans h2.symm)
    have hσ := isDensityOperator_inv_smul hR0 (sub_pos.mpr hlt) hRtr'
    refine ⟨b i, hbn i, (hext _ _ (isDensityOperator_proj (hbn i)) hσ (μ i) hi hlt ?_).symm⟩
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (sub_pos.mpr hlt).ne',
      Complex.ofReal_one, one_smul, add_sub_cancel]
  · have hx1 : ENNReal.ofReal (μ i) = 1 := by rw [heq, ENNReal.ofReal_one]
    rw [hx1] at hRtr
    have h2 : (1 : ℝ≥0∞) + posTrace (ρ - (μ i : ℂ) • proj (b i)) = 1 + 0 := by
      rw [add_comm, hRtr, add_zero]
    have hR : ρ - (μ i : ℂ) • proj (b i) = 0 :=
      (posTrace_eq_zero_iff hR0).mp ((ENNReal.add_right_inj ENNReal.one_ne_top).mp h2)
    refine ⟨b i, hbn i, ?_⟩
    rw [sub_eq_zero.mp hR, heq, Complex.ofReal_one, one_smul]

/-- The pure states are the extreme points of the density operators. -/
theorem isPure_iff_isExtremeDensityOperator {ρ : E →L[ℂ] E} :
    IsPure ρ ↔ IsExtremeDensityOperator ρ :=
  ⟨IsPure.isExtremeDensityOperator, IsExtremeDensityOperator.isPure⟩

/-! ## G. Three characterizations of state automorphisms -/

/-- `T` is conjugation by a unitary or by an anti-unitary on every density operator. -/
def ImplementedOnDensityOperators (T : (E →L[ℂ] E) → E →L[ℂ] E) : Prop :=
  (∃ W : E ≃ₗᵢ[ℂ] E, ∀ ρ, IsDensityOperator ρ → T ρ = conjOp W ρ) ∨
    (∃ W : E ≃ₗᵢ⋆[ℂ] E, ∀ ρ, IsDensityOperator ρ → T ρ = conjOp W ρ)

/-- An affine bijection of the density operators maps the extreme points, which are the pure
states, bijectively onto themselves. -/
theorem AffineOnDensityOperators.bijOnPure (hT : AffineOnDensityOperators T)
    (hbij : Set.BijOn T {ρ | IsDensityOperator ρ} {ρ | IsDensityOperator ρ}) : BijOnPure T := by
  refine ⟨fun ρ hρ => ?_, hbij.injOn.mono fun ρ hρ =>
    (isPure_iff_isExtremeDensityOperator.mp hρ).1, fun ρ' hρ' => ?_⟩
  · obtain ⟨hρD, hext⟩ := isPure_iff_isExtremeDensityOperator.mp hρ
    refine isPure_iff_isExtremeDensityOperator.mpr
      ⟨hbij.mapsTo hρD, fun σ τ hσ hτ t ht0 ht1 hmix => ?_⟩
    obtain ⟨σ₀, hσ₀, rfl⟩ := hbij.surjOn hσ
    obtain ⟨τ₀, hτ₀, rfl⟩ := hbij.surjOn hτ
    have h : (t : ℂ) • σ₀ + ((1 - t : ℝ) : ℂ) • τ₀ = ρ :=
      hbij.injOn (IsDensityOperator.smul_add_smul hσ₀ hτ₀ ht0.le ht1.le) hρD
        (by rw [hT _ _ hσ₀ hτ₀ t ht0.le ht1.le, hmix])
    rw [hext σ₀ τ₀ hσ₀ hτ₀ t ht0 ht1 h.symm]
  · obtain ⟨hρ'D, hext⟩ := isPure_iff_isExtremeDensityOperator.mp hρ'
    obtain ⟨ρ, hρD, rfl⟩ := hbij.surjOn hρ'D
    refine ⟨ρ, isPure_iff_isExtremeDensityOperator.mpr
      ⟨hρD, fun σ τ hσ hτ t ht0 ht1 hmix => ?_⟩, rfl⟩
    exact hbij.injOn hσ hρD (hext (T σ) (T τ) (hbij.mapsTo hσ) (hbij.mapsTo hτ) t ht0 ht1
      (by rw [hmix, hT _ _ hσ hτ t ht0.le ht1.le]))

/-- Conjugation by a unitary or an anti-unitary `W` is a bijection of the density operators,
with inverse conjugation by `W⁻¹`. -/
theorem bijOn_of_eq_conjOp {σ : ℂ →+* ℂ} [RingHomInvPair σ σ] [RingHomIsometric σ]
    (W : E ≃ₛₗᵢ[σ] E) (hW : ∀ ρ, IsDensityOperator ρ → T ρ = conjOp W ρ) :
    Set.BijOn T {ρ | IsDensityOperator ρ} {ρ | IsDensityOperator ρ} := by
  refine ⟨fun ρ hρ => ?_, fun ρ hρ τ hτ h => ?_,
    fun τ hτ => ⟨conjOp W.symm τ, IsDensityOperator.conjOp W.symm hτ, ?_⟩⟩
  · show IsDensityOperator (T ρ)
    rw [hW ρ hρ]
    exact IsDensityOperator.conjOp W hρ
  · rw [hW ρ hρ, hW τ hτ] at h
    simpa [conjOp_symm_conjOp] using congrArg (conjOp W.symm) h
  · rw [hW _ (IsDensityOperator.conjOp W.symm hτ), conjOp_conjOp_symm]

/-- **Kadison's theorem, three forms**, in any dimension. For a map `T` that sends density
operators to density operators and is affine on them, the following are equivalent:
(i) `T` is bijective on the pure states; (ii) `T` is bijective on the density operators;
(iii) `T` is conjugation by a unitary or an anti-unitary. No continuity is assumed. -/
theorem AffineOnDensityOperators.tfae (hT : AffineOnDensityOperators T)
    (hD : ∀ ρ, IsDensityOperator ρ → IsDensityOperator (T ρ)) :
    [BijOnPure T, Set.BijOn T {ρ | IsDensityOperator ρ} {ρ | IsDensityOperator ρ},
      ImplementedOnDensityOperators T].TFAE := by
  tfae_have 1 → 3 := fun h => by
    rcases hT.exists_unitary_or_antiunitary h with ⟨W, hW⟩ | ⟨W, hW⟩
    · exact Or.inl ⟨W, fun ρ hρ => hT.eq_conjOp hD hW hρ⟩
    · exact Or.inr ⟨W, fun ρ hρ => hT.eq_conjOp hD hW hρ⟩
  tfae_have 3 → 2 := by
    rintro (⟨W, hW⟩ | ⟨W, hW⟩)
    exacts [bijOn_of_eq_conjOp W hW, bijOn_of_eq_conjOp W hW]
  tfae_have 2 → 1 := hT.bijOnPure
  tfae_finish

end QuantumMechanics
