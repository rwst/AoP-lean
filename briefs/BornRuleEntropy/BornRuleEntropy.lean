/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForPhyslib.QuantumMechanics.VonNeumannEntropyMixture

/-!
# The Born rule is equivalent to the von Neumann entropy

## i. Overview

Formalization of the technical brief *The Born rule is equivalent to the von Neumann entropy*
(G. Carcassi, Assumptions of Physics). The setting is a complex Hilbert space `E` of any
dimension. Pure states are rank-one projections `|ψ⟩⟨ψ|` of unit vectors, ensembles are density
operators, the entropy `S` takes values in `[0, ∞]`, and logarithms are natural, so the brief's
"entropy one" (one bit) is `log 2` here.

**Proposition 3.** The entropy of the equal mixture of two pure states is a strictly decreasing
function of their Born probability `λ = |⟨ψ, ϕ⟩|²`, namely `h((1 + √λ) / 2)` with `h` the binary
entropy (Fig. 2). Orthogonality is therefore the same as the mixture having entropy `log 2`
(Corollary 7).

**Theorem 9.** Over the base condition EQST on the conditional probability `p`, any two of
BR-BORN (`p` is the Born rule), BR-ENT (`S` is the von Neumann entropy) and [B]MUTEX (pairwise
mutual exclusivity under `p` is the same as the entropy of every mixture being the Shannon entropy
of its weights) imply the third.

The hard direction is BR-ENT + [B]MUTEX ⇒ BR-BORN. Orthogonal states are mutually exclusive, so
for a unit `ψ` and a unit `χ ⊥ ψ`, `f = p(ψ | ·)` is `1` on `ψ` and `0` on `χ`. On the qubit
spanned by `ψ, χ`, convex identities between pure states give
`f(r ψ + s ζ̄ χ) = r² + 2 r s (f(e_ζ) - ½)` for the equatorial states
`e_ζ = (ψ + ζ̄ χ) / √2`, and `f(e_ζ) + f(e_{-ζ}) = 1`. If `f(e_ζ) < ½`, the state with
`r / s = ½ - f(e_ζ)` has `f < 0`; so `f(e_ζ) = ½` and `f(r ψ + s ζ̄ χ) = r²`, the Born rule.

## ii. Key results

- `BornRuleEntropy.entropyOfBorn`, `BornRuleEntropy.strictAntiOn_entropyOfBorn`: Fig. 2.
- `BornRuleEntropy.vonNeumannEntropy_mix_proj_eq`, `BornRuleEntropy.norm_inner_sq_eq_iff`:
  Proposition 3.
- `BornRuleEntropy.inner_eq_zero_iff`: Corollary 7.
- `BornRuleEntropy.EnsemblesAndStates`, `BornRuleEntropy.BornRule`,
  `BornRuleEntropy.IsVonNeumannEntropy`, `BornRuleEntropy.MutualExclusivity`: the conditions
  EQST, BR-BORN, BR-ENT, [B]MUTEX.
- `BornRuleEntropy.MutualExclusivity.of_bornRule`: BR-BORN + BR-ENT ⇒ [B]MUTEX.
- `BornRuleEntropy.IsVonNeumannEntropy.of_bornRule`: BR-BORN + [B]MUTEX ⇒ BR-ENT.
- `BornRuleEntropy.BornRule.of_isVonNeumannEntropy`: BR-ENT + [B]MUTEX ⇒ BR-BORN.
- `BornRuleEntropy.two_conditions_imply_third`: Theorem 9.

## iii. Table of contents

- A. Born rule and entropy of equal mixtures
- B. The conditions
- C. BR-BORN and BR-ENT imply [B]MUTEX
- D. BR-BORN and [B]MUTEX imply BR-ENT
- E. Affine functions on a qubit
- F. BR-ENT and [B]MUTEX imply BR-BORN
- G. Theorem 9

## iv. References

- G. Carcassi, *The Born rule is equivalent to the von Neumann entropy*, Assumptions of Physics
  technical brief.
-/

@[expose] public noncomputable section

open scoped InnerProductSpace ENNReal ComplexConjugate
open InnerProductSpace Real QuantumMechanics QuantumMechanics.Wigner

namespace BornRuleEntropy

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## A. Born rule and entropy of equal mixtures -/

/-- The entropy `h((1 + √λ) / 2)` of an equal mixture of two pure states with Born probability
`λ` (Fig. 2). -/
def entropyOfBorn (q : ℝ) : ℝ := binEntropy ((1 + √q) / 2)

/-- **Fig. 2.** The entropy of the equal mixture is strictly decreasing in the Born probability. -/
theorem strictAntiOn_entropyOfBorn : StrictAntiOn entropyOfBorn (Set.Icc 0 1) := by
  have mem : ∀ {x : ℝ}, x ∈ Set.Icc (0 : ℝ) 1 → (1 + √x) / 2 ∈ Set.Icc (2⁻¹ : ℝ) 1 :=
    fun {x} hx => ⟨by linarith [Real.sqrt_nonneg x], by
      linarith [Real.sqrt_one ▸ Real.sqrt_le_sqrt hx.2]⟩
  intro a ha b hb hab
  exact binEntropy_strictAntiOn (mem ha) (mem hb) (by linarith [Real.sqrt_lt_sqrt ha.1 hab])

lemma entropyOfBorn_nonneg {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ entropyOfBorn q :=
  binEntropy_nonneg (by linarith [Real.sqrt_nonneg q])
    (by linarith [Real.sqrt_one ▸ Real.sqrt_le_sqrt hq.2])

lemma entropyOfBorn_zero : entropyOfBorn 0 = log 2 := by
  rw [entropyOfBorn, Real.sqrt_zero, add_zero, binEntropy_eq_log_two]
  norm_num

/-- **Proposition 3**, eq. (6): `S(½ ρ_ψ + ½ ρ_ϕ) = h((1 + √λ) / 2)` with `λ = |⟨ψ, ϕ⟩|²`. -/
theorem vonNeumannEntropy_mix_proj_eq {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    vonNeumannEntropy (mix (proj ψ) (proj ϕ)) =
      ENNReal.ofReal (entropyOfBorn (‖⟪ψ, ϕ⟫_ℂ‖ ^ 2)) := by
  rw [vonNeumannEntropy_mix_proj hψ hϕ, entropyOfBorn, Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace E] in
lemma norm_inner_sq_mem_Icc {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  have h : ‖⟪ψ, ϕ⟫_ℂ‖ ≤ 1 := by simpa [hψ, hϕ] using norm_inner_le_norm (𝕜 := ℂ) ψ ϕ
  exact ⟨by positivity, pow_le_one₀ (norm_nonneg _) h⟩

/-- **Proposition 3.** The Born probability is `λ` iff the equal mixture has entropy
`h((1 + √λ) / 2)`. -/
theorem norm_inner_sq_eq_iff {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2 = q ↔
      vonNeumannEntropy (mix (proj ψ) (proj ϕ)) = ENNReal.ofReal (entropyOfBorn q) := by
  have hm := norm_inner_sq_mem_Icc hψ hϕ
  rw [vonNeumannEntropy_mix_proj_eq hψ hϕ,
    ENNReal.ofReal_eq_ofReal_iff (entropyOfBorn_nonneg hm) (entropyOfBorn_nonneg hq)]
  exact ⟨fun h => h ▸ rfl, fun h => strictAntiOn_entropyOfBorn.injOn hm hq h⟩

/-- **Corollary 7.** Two pure states are orthogonal iff their equal mixture has entropy `log 2`
(one bit). -/
theorem inner_eq_zero_iff {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    ⟪ψ, ϕ⟫_ℂ = 0 ↔ vonNeumannEntropy (mix (proj ψ) (proj ϕ)) = ENNReal.ofReal (log 2) := by
  rw [← entropyOfBorn_zero, ← norm_inner_sq_eq_iff hψ hϕ ⟨le_rfl, zero_le_one⟩]
  simp

/-! ## B. The conditions -/

/-- **Condition EQST.** `p (proj ψ) ρ` is the probability of finding the pure state `ψ` having
prepared the ensemble `ρ`: it lies in `[0, 1]`, it is affine in the ensemble (for mixtures of two
pure states), and `p(ϕ | ψ) = 1` iff `ϕ = ψ`. -/
structure EnsemblesAndStates (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) : Prop where
  mem_Icc : ∀ {ψ : E} {ρ : E →L[ℂ] E}, ‖ψ‖ = 1 → IsDensityOperator ρ →
    p (proj ψ) ρ ∈ Set.Icc 0 1
  affine : ∀ {ψ φ₁ φ₂ : E} {t : ℝ}, ‖ψ‖ = 1 → ‖φ₁‖ = 1 → ‖φ₂‖ = 1 → 0 ≤ t → t ≤ 1 →
    p (proj ψ) ((t : ℂ) • proj φ₁ + ((1 - t : ℝ) : ℂ) • proj φ₂) =
      t * p (proj ψ) (proj φ₁) + (1 - t) * p (proj ψ) (proj φ₂)
  eq_one_iff : ∀ {ψ φ : E}, ‖ψ‖ = 1 → ‖φ‖ = 1 → (p (proj ψ) (proj φ) = 1 ↔ proj ψ = proj φ)

/-- **Condition BR-BORN.** `p(ψ | ϕ) = |⟨ψ, ϕ⟩|²` for unit vectors. -/
def BornRule (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) : Prop :=
  ∀ {ψ ϕ : E}, ‖ψ‖ = 1 → ‖ϕ‖ = 1 → p (proj ψ) (proj ϕ) = ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2

/-- **Condition BR-ENT.** `S(ρ) = -tr (ρ log ρ)` on density operators. -/
def IsVonNeumannEntropy (S : (E →L[ℂ] E) → ℝ≥0∞) : Prop :=
  ∀ ρ, IsDensityOperator ρ → S ρ = vonNeumannEntropy ρ

/-- **Condition [B]MUTEX.** A countable family of pure states is pairwise mutually exclusive iff
every mixture of it has the Shannon entropy of its weights. -/
def MutualExclusivity (S : (E →L[ℂ] E) → ℝ≥0∞) (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) : Prop :=
  ∀ (ι : Type u) [Countable ι] (ψ : ι → E), (∀ i, ‖ψ i‖ = 1) →
    ((∀ i j, i ≠ j → p (proj (ψ i)) (proj (ψ j)) = 0) ↔
      ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → HasSum w 1 →
        S (∑' i, (w i : ℂ) • proj (ψ i)) = ∑' i, ENNReal.ofReal (negMulLog (w i)))

variable {p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ} {S : (E →L[ℂ] E) → ℝ≥0∞}

/-! ## C. BR-BORN and BR-ENT imply [B]MUTEX -/

/-- BR-BORN and BR-ENT imply [B]MUTEX. -/
theorem MutualExclusivity.of_bornRule (hB : BornRule p) (hS : IsVonNeumannEntropy S) :
    MutualExclusivity S p := by
  intro ι _ ψ hψ
  constructor
  · intro h w hw0 hw
    have hon : Orthonormal ℂ ψ := by
      classical
      rw [orthonormal_iff_ite]
      intro i j
      split_ifs with hij
      · subst hij
        rw [inner_self_eq_norm_sq_to_K, hψ]
        simp
      · have h' := hB (hψ i) (hψ j)
        rw [h i j hij] at h'
        exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h'.symm)
    rw [hS _ (isDensityOperator_tsum_smul_proj hon hw0 hw),
      vonNeumannEntropy_tsum_smul_proj hon hw0 hw]
  · intro h i j hij
    classical
    set w : ι → ℝ := fun k => if k = i ∨ k = j then 2⁻¹ else 0 with hw_def
    have hsupp : ∀ k ∉ ({i, j} : Finset ι), w k = 0 := fun k hk => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      simp [w, hk.1, hk.2]
    have hwi : w i = 2⁻¹ := by simp [w]
    have hwj : w j = 2⁻¹ := by simp [w]
    have hw : HasSum w 1 := by
      have h : HasSum w (∑ k ∈ {i, j}, w k) := hasSum_sum_of_ne_finset_zero hsupp
      rwa [Finset.sum_pair hij, hwi, hwj, show (2⁻¹ : ℝ) + 2⁻¹ = 1 by norm_num] at h
    have hmix : ∑' k, (w k : ℂ) • proj (ψ k) = mix (proj (ψ i)) (proj (ψ j)) := by
      rw [tsum_eq_sum (s := {i, j}) fun k hk => by rw [hsupp k hk]; simp, Finset.sum_pair hij,
        hwi, hwj, mix]
      push_cast
      rfl
    have hη : negMulLog 2⁻¹ = 2⁻¹ * log 2 := by
      rw [negMulLog, Real.log_inv]
      ring
    have hent : ∑' k, ENNReal.ofReal (negMulLog (w k)) = ENNReal.ofReal (log 2) := by
      rw [tsum_eq_sum (s := {i, j}) fun k hk => by rw [hsupp k hk]; simp, Finset.sum_pair hij,
        hwi, hwj, hη, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      ring_nf
    have hS2 := h w (fun k => by simp only [w]; split_ifs <;> norm_num) hw
    rw [hmix, hS _ ((isDensityOperator_proj (hψ i)).mix (isDensityOperator_proj (hψ j))),
      hent] at hS2
    rw [hB (hψ i) (hψ j), (inner_eq_zero_iff (hψ i) (hψ j)).mpr hS2]
    simp

/-! ## D. BR-BORN and [B]MUTEX imply BR-ENT -/

/-- BR-BORN and [B]MUTEX imply BR-ENT. The eigenvectors with nonzero eigenvalue of a density
operator form a countable orthonormal family, mutually exclusive by BR-BORN. -/
theorem IsVonNeumannEntropy.of_bornRule (hB : BornRule p) (hM : MutualExclusivity S p) :
    IsVonNeumannEntropy S := by
  intro ρ hρ
  set e := hρ.eigenbasis
  set ev := hρ.eigenvalue
  have he : IsEigenbasis ρ e ev := hρ.isEigenbasis
  have hev0 : ∀ i, 0 ≤ ev i := fun i => (he.eigenvalue_mem_Icc hρ i).1
  have hsum : HasSum ev 1 := by
    have h1 := he.tsum_ofReal_eq_one hρ
    have hs : Summable ev := (summable_iff_tsum_ofReal_ne_top hev0).mpr (by rw [h1]; simp)
    rw [← ENNReal.ofReal_tsum_of_nonneg hev0 hs, ENNReal.ofReal_eq_one] at h1
    exact h1 ▸ hs.hasSum
  set s := Function.support ev
  have : Countable s := hsum.summable.countable_support.to_subtype
  set φ : s → E := fun i => e i
  set w : s → ℝ := fun i => ev i
  have hφ : Orthonormal ℂ φ := e.orthonormal.comp _ Subtype.val_injective
  have hw : HasSum w 1 := (hasSum_subtype_iff_of_support_subset subset_rfl).mpr hsum
  have hw0 : ∀ i, 0 ≤ w i := fun i => hev0 i
  have hρ' : ∑' i, (w i : ℂ) • proj (φ i) = ρ := by
    refine ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr e.dense_span) ?_
    rintro _ ⟨k, rfl⟩
    by_cases hk : k ∈ s
    · exact (tsum_smul_proj_apply_self hφ hw.summable ⟨k, hk⟩).trans (he.apply_eq k).symm
    · have hk0 : ev k = 0 := by simpa [s] using hk
      rw [tsum_smul_proj_apply_of_inner_eq_zero hφ hw.summable
        fun i => e.orthonormal.2 fun h => hk (by rw [← h]; exact i.2), he.apply_eq k, hk0]
      simp
  have hM' := (hM s φ hφ.1).mp (fun i j hij => by
    rw [hB (hφ.1 i) (hφ.1 j), hφ.2 hij]
    simp) w hw0 hw
  rw [hρ'] at hM'
  rw [hM', ← vonNeumannEntropy_tsum_smul_proj hφ hw0 hw, hρ']

/-! ## E. Affine functions on a qubit -/

section Qubit

variable {ψ χ : E}

/-- The vector `r ψ + s ζ̄ χ`. -/
def planeVec (ψ χ : E) (r s : ℝ) (ζ : ℂ) : E := (r : ℂ) • ψ + ((s : ℂ) * conj ζ) • χ

/-- The equatorial state `e_ζ = (ψ + ζ̄ χ) / √2`. -/
def halfVec (ψ χ : E) (ζ : ℂ) : E := planeVec ψ χ (√2)⁻¹ (√2)⁻¹ ζ

/-- The off-diagonal part `ζ |ψ⟩⟨χ| + ζ̄ |χ⟩⟨ψ|`. -/
def cross (ψ χ : E) (ζ : ℂ) : E →L[ℂ] E := ζ • rankOne ℂ ψ χ + conj ζ • rankOne ℂ χ ψ

omit [CompleteSpace E] in
lemma cross_neg (ζ : ℂ) : cross ψ χ (-ζ) = -cross ψ χ ζ := by
  simp [cross, neg_smul]
  abel

omit [CompleteSpace E] in
lemma proj_planeVec (r s : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    proj (planeVec ψ χ r s ζ) = ((r ^ 2 : ℝ) : ℂ) • proj ψ + ((s ^ 2 : ℝ) : ℂ) • proj χ +
      ((r * s : ℝ) : ℂ) • cross ψ χ ζ := by
  have h : ζ * conj ζ = 1 := by rw [Complex.mul_conj', hζ]; simp
  ext v
  simp only [planeVec, cross, add_apply, smul_apply, rankOne_apply, inner_add_left,
    inner_smul_left, map_mul, Complex.conj_ofReal, Complex.conj_conj, smul_add, smul_smul]
  match_scalars <;> first | ring1 | linear_combination (s ^ 2 * ⟪χ, v⟫_ℂ : ℂ) * h

omit [CompleteSpace E] in
lemma proj_halfVec {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    proj (halfVec ψ χ ζ) = (2⁻¹ : ℂ) • (proj ψ + proj χ + cross ψ χ ζ) := by
  have h2 : ((√2)⁻¹ : ℝ) ^ 2 = 2⁻¹ := by rw [inv_pow, Real.sq_sqrt zero_le_two]
  rw [halfVec, proj_planeVec _ _ hζ, ← sq, h2]
  push_cast
  simp only [smul_add]

variable (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) (hψχ : ⟪ψ, χ⟫_ℂ = 0)
include hψ hχ hψχ

omit [CompleteSpace E] in
lemma norm_planeVec {r s : ℝ} (hrs : r ^ 2 + s ^ 2 = 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖planeVec ψ χ r s ζ‖ = 1 := by
  have h0 : ⟪(r : ℂ) • ψ, ((s : ℂ) * conj ζ) • χ⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, hψχ]
    simp
  have h : ‖planeVec ψ χ r s ζ‖ ^ 2 = 1 := by
    rw [planeVec, norm_add_sq (𝕜 := ℂ), h0, norm_smul, norm_smul, norm_mul, Complex.norm_conj, hζ,
      hψ, hχ, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [map_zero, mul_zero, add_zero, mul_one, sq_abs]
    linarith
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

omit [CompleteSpace E] in
lemma norm_halfVec {ζ : ℂ} (hζ : ‖ζ‖ = 1) : ‖halfVec ψ χ ζ‖ = 1 := by
  have h2 : ((√2)⁻¹ : ℝ) ^ 2 = 2⁻¹ := by rw [inv_pow, Real.sq_sqrt zero_le_two]
  exact norm_planeVec hψ hχ hψχ (by rw [h2]; norm_num) hζ

omit hχ hψχ in
/-- Equal-weight convex identities between pure states give relations between the values of
`p(ψ | ·)`. -/
lemma EnsemblesAndStates.mul_add_mul_eq (hp : EnsemblesAndStates p) {a b c d : E}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1) {t₁ t₂ s₁ s₂ : ℝ}
    (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂) (hT : t₁ + t₂ = s₁ + s₂)
    (hpos : 0 < t₁ + t₂)
    (h : (t₁ : ℂ) • proj a + (t₂ : ℂ) • proj b = (s₁ : ℂ) • proj c + (s₂ : ℂ) • proj d) :
    t₁ * p (proj ψ) (proj a) + t₂ * p (proj ψ) (proj b) =
      s₁ * p (proj ψ) (proj c) + s₂ * p (proj ψ) (proj d) := by
  have hT0 : t₁ + t₂ ≠ 0 := hpos.ne'
  have hab := hp.affine hψ ha hb (div_nonneg ht₁ hpos.le) ((div_le_one hpos).mpr (by linarith))
  have hcd := hp.affine hψ hc hd (div_nonneg hs₁ hpos.le)
    ((div_le_one hpos).mpr (by linarith))
  have r1 : 1 - t₁ / (t₁ + t₂) = (t₁ + t₂)⁻¹ * t₂ := by field_simp; ring
  have r2 : 1 - s₁ / (t₁ + t₂) = (t₁ + t₂)⁻¹ * s₂ := by field_simp; linear_combination hT
  rw [r1, div_eq_inv_mul] at hab
  rw [r2, div_eq_inv_mul] at hcd
  have e : ∀ {x y : ℝ} {X Y : E →L[ℂ] E}, ((((t₁ + t₂)⁻¹ * x : ℝ) : ℂ) • X +
      (((t₁ + t₂)⁻¹ * y : ℝ) : ℂ) • Y) = (((t₁ + t₂)⁻¹ : ℝ) : ℂ) • ((x : ℂ) • X + (y : ℂ) • Y) :=
    fun {x y X Y} => by rw [smul_add, smul_smul, smul_smul]; push_cast; rfl
  rw [e, h, ← e, hcd] at hab
  have key : (t₁ + t₂)⁻¹ * (t₁ * p (proj ψ) (proj a) + t₂ * p (proj ψ) (proj b)) =
      (t₁ + t₂)⁻¹ * (s₁ * p (proj ψ) (proj c) + s₂ * p (proj ψ) (proj d)) := by
    linear_combination -hab
  exact mul_left_cancel₀ (inv_ne_zero hT0) key

variable (hp : EnsemblesAndStates p) (h1 : p (proj ψ) (proj ψ) = 1)
  (h0 : p (proj ψ) (proj χ) = 0)
include hp h1 h0

/-- `p(ψ | r ψ + s ζ̄ χ) = r² + 2 r s (p(ψ | e_ζ) - ½)`. -/
lemma apply_planeVec {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ^ 2 + s ^ 2 = 1) {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) :
    p (proj ψ) (proj (planeVec ψ χ r s ζ)) =
      r ^ 2 + 2 * r * s * (p (proj ψ) (proj (halfVec ψ χ ζ)) - 2⁻¹) := by
  have hu := norm_planeVec hψ hχ hψχ hrs hζ
  have he := norm_halfVec hψ hχ hψχ hζ
  rcases le_total s r with h | h
  · have key := hp.mul_add_mul_eq hψ hu hχ hψ he (t₁ := 1) (t₂ := s * (r - s))
      (s₁ := r * (r - s)) (s₂ := 2 * r * s) zero_le_one (by nlinarith) (by nlinarith)
      (by positivity) (by linear_combination -hrs) (by nlinarith) (by
        rw [proj_planeVec _ _ hζ, proj_halfVec hζ]
        push_cast
        module)
    rw [h0, h1] at key
    linear_combination key
  · have key := hp.mul_add_mul_eq hψ hu hψ hχ he (t₁ := 1) (t₂ := r * (s - r))
      (s₁ := s * (s - r)) (s₂ := 2 * r * s) zero_le_one (by nlinarith) (by nlinarith)
      (by positivity) (by linear_combination -hrs) (by nlinarith) (by
        rw [proj_planeVec _ _ hζ, proj_halfVec hζ]
        push_cast
        module)
    rw [h0, h1] at key
    linear_combination key

/-- Antipodal equatorial states: `p(ψ | e_ζ) + p(ψ | e_{-ζ}) = 1`. -/
lemma apply_halfVec_add_apply_halfVec_neg {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    p (proj ψ) (proj (halfVec ψ χ ζ)) + p (proj ψ) (proj (halfVec ψ χ (-ζ))) = 1 := by
  have hζ' : ‖-ζ‖ = 1 := by rw [norm_neg, hζ]
  have key := hp.mul_add_mul_eq hψ (norm_halfVec hψ hχ hψχ hζ) (norm_halfVec hψ hχ hψχ hζ') hψ hχ
    (t₁ := 2⁻¹) (t₂ := 2⁻¹) (s₁ := 2⁻¹) (s₂ := 2⁻¹) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) rfl (by norm_num) (by
      rw [proj_halfVec hζ, proj_halfVec hζ', cross_neg]
      push_cast
      module)
  rw [h0, h1] at key
  linear_combination 2 * key

/-- `p(ψ | e_ζ) ≥ ½`: otherwise the state with `r / s = ½ - p(ψ | e_ζ)` would have negative
probability. -/
lemma half_le_apply_halfVec {ζ : ℂ} (hζ : ‖ζ‖ = 1) : 2⁻¹ ≤ p (proj ψ) (proj (halfVec ψ χ ζ)) := by
  by_contra hlt
  push Not at hlt
  set d := p (proj ψ) (proj (halfVec ψ χ ζ)) - 2⁻¹
  have hd : d < 0 := by simp only [d]; linarith
  set q := √(1 + d ^ 2)
  have hq2 : q ^ 2 = 1 + d ^ 2 := Real.sq_sqrt (by positivity)
  have hq : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hrs : (-d / q) ^ 2 + (1 / q) ^ 2 = 1 := by
    field_simp
    linarith
  have hu := norm_planeVec hψ hχ hψχ hrs hζ
  have hnn := (hp.mem_Icc hψ (isDensityOperator_proj hu)).1
  rw [apply_planeVec hψ hχ hψχ hp h1 h0 (div_nonneg (by linarith) hq.le) (by positivity) hrs hζ]
    at hnn
  have : (-d / q) ^ 2 + 2 * (-d / q) * (1 / q) * d = -d ^ 2 / q ^ 2 := by
    field_simp
    ring
  rw [this] at hnn
  have : 0 < d ^ 2 / q ^ 2 := div_pos (by nlinarith) (by positivity)
  linarith [neg_div (q ^ 2) (d ^ 2)]

/-- The equatorial states have `p(ψ | e_ζ) = ½`. -/
lemma apply_halfVec {ζ : ℂ} (hζ : ‖ζ‖ = 1) : p (proj ψ) (proj (halfVec ψ χ ζ)) = 2⁻¹ := by
  have hζ' : ‖-ζ‖ = 1 := by rw [norm_neg, hζ]
  have := apply_halfVec_add_apply_halfVec_neg hψ hχ hψχ hp h1 h0 hζ
  have := half_le_apply_halfVec hψ hχ hψχ hp h1 h0 hζ
  have := half_le_apply_halfVec hψ hχ hψχ hp h1 h0 hζ'
  linarith

/-- **The Born rule on a qubit.** `p(ψ | r ψ + s ζ̄ χ) = r²`. -/
theorem apply_planeVec_eq {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ^ 2 + s ^ 2 = 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) : p (proj ψ) (proj (planeVec ψ χ r s ζ)) = r ^ 2 := by
  rw [apply_planeVec hψ hχ hψχ hp h1 h0 hr hs hrs hζ, apply_halfVec hψ hχ hψχ hp h1 h0 hζ]
  ring

end Qubit

/-! ## F. BR-ENT and [B]MUTEX imply BR-BORN -/

/-- Under BR-ENT and [B]MUTEX, orthogonal pure states are mutually exclusive. -/
lemma apply_eq_zero_of_inner_eq_zero (hS : IsVonNeumannEntropy S) (hM : MutualExclusivity S p)
    {ψ χ : E} (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) (hψχ : ⟪ψ, χ⟫_ℂ = 0) :
    p (proj ψ) (proj χ) = 0 := by
  set φ : ULift.{u} (Fin 2) → E := fun k => ![ψ, χ] k.down
  have hφ : Orthonormal ℂ φ := by
    rw [orthonormal_iff_ite]
    rintro ⟨i⟩ ⟨j⟩
    have hχψ : ⟪χ, ψ⟫_ℂ = 0 := by rw [← inner_conj_symm, hψχ, map_zero]
    fin_cases i <;> fin_cases j <;> simp [φ, hψχ, hχψ, inner_self_eq_norm_sq_to_K, hψ, hχ]
  have h := (hM _ φ hφ.1).mpr fun w hw0 hw => by
    rw [hS _ (isDensityOperator_tsum_smul_proj hφ hw0 hw),
      vonNeumannEntropy_tsum_smul_proj hφ hw0 hw]
  exact h ⟨0⟩ ⟨1⟩ (by simp)

/-- BR-ENT and [B]MUTEX imply BR-BORN, over EQST. -/
theorem BornRule.of_isVonNeumannEntropy (hp : EnsemblesAndStates p)
    (hS : IsVonNeumannEntropy S) (hM : MutualExclusivity S p) : BornRule p := by
  intro ψ ϕ hψ hϕ
  set c := ⟪ψ, ϕ⟫_ℂ with hc
  have h1 : p (proj ψ) (proj ψ) = 1 := (hp.eq_one_iff hψ hψ).mpr rfl
  have hc1 : ‖c‖ ≤ 1 := by simpa [hψ, hϕ] using norm_inner_le_norm (𝕜 := ℂ) ψ ϕ
  rcases hc1.lt_or_eq with hlt | heq
  swap
  · have hψ0 : ψ ≠ 0 := by rintro rfl; simp at hψ
    have hϕ0 : ϕ ≠ 0 := by rintro rfl; simp at hϕ
    obtain ⟨r, -, hr⟩ :=
      (norm_inner_eq_norm_iff hψ0 hϕ0).mp (by rw [← hc, heq, hψ, hϕ, one_mul])
    have hrn : ‖r‖ = 1 := by simpa [hr, norm_smul, hψ] using hϕ
    rw [heq, hr, proj_smul, hrn, one_pow, Complex.ofReal_one, one_smul, h1]
  set v := ϕ - c • ψ
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have hψv : ⟪ψ, v⟫_ℂ = 0 := by
    rw [inner_sub_right, inner_smul_right, hψψ, ← hc]
    ring
  have hv2 : ‖v‖ ^ 2 = 1 - ‖c‖ ^ 2 := by
    have hϕv : ϕ = c • ψ + v := by simp [v]
    have h := norm_add_sq (𝕜 := ℂ) (c • ψ) v
    rw [← hϕv, hϕ, inner_smul_left, hψv, norm_smul, hψ] at h
    simp at h
    linarith
  set b := ‖v‖
  have hb : 0 < b := by
    by_contra hb
    have : b = 0 := le_antisymm (not_lt.mp hb) (norm_nonneg _)
    rw [this] at hv2
    nlinarith [norm_nonneg c]
  set χ := ((b : ℂ)⁻¹) • v
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hχ : ‖χ‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb,
      inv_mul_cancel₀ hb.ne']
  have hψχ : ⟪ψ, χ⟫_ℂ = 0 := by rw [inner_smul_right, hψv, mul_zero]
  set ζ : ℂ := if c = 0 then 1 else c / (‖c‖ : ℂ)
  have hζ : ‖ζ‖ = 1 := by
    simp only [ζ]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
        div_self (norm_ne_zero_iff.mpr h)]
  have hcζ : (‖c‖ : ℂ) * ζ = c := by
    simp only [ζ]
    split_ifs with h
    · simp [h]
    · have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
      field_simp
  have hζζ : ζ * conj ζ = 1 := by rw [Complex.mul_conj', hζ]; simp
  have hϕ' : ϕ = ζ • planeVec ψ χ ‖c‖ b ζ := by
    rw [planeVec, smul_add, smul_smul, smul_smul, mul_comm ζ (‖c‖ : ℂ), hcζ,
      show ζ * ((b : ℂ) * conj ζ) = b * (ζ * conj ζ) by ring, hζζ, mul_one]
    simp only [χ, smul_smul, mul_inv_cancel₀ hbc, one_smul, v]
    abel
  have h0 := apply_eq_zero_of_inner_eq_zero hS hM hψ hχ hψχ
  have hrs : ‖c‖ ^ 2 + b ^ 2 = 1 := by rw [hv2]; ring
  rw [hϕ', proj_smul, hζ, one_pow, Complex.ofReal_one, one_smul,
    apply_planeVec_eq hψ hχ hψχ hp h1 h0 (norm_nonneg c) hb.le hrs hζ]

/-! ## G. Theorem 9 -/

/-- **Theorem 9.** Over EQST, any two of BR-BORN, BR-ENT and [B]MUTEX imply the third. -/
theorem two_conditions_imply_third (hp : EnsemblesAndStates p) :
    (BornRule p → IsVonNeumannEntropy S → MutualExclusivity S p) ∧
      (BornRule p → MutualExclusivity S p → IsVonNeumannEntropy S) ∧
      (IsVonNeumannEntropy S → MutualExclusivity S p → BornRule p) :=
  ⟨MutualExclusivity.of_bornRule, IsVonNeumannEntropy.of_bornRule,
    BornRule.of_isVonNeumannEntropy hp⟩

end BornRuleEntropy
