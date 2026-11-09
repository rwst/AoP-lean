/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Convex.AffineOnBall
public import ForPhyslib.QuantumMechanics.Kadison
public import ForPhyslib.QuantumMechanics.Qubit.BlochBall
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
(Corollary 7). A second proof follows the brief's geometric diagonalization (Fig. 1, eqs. (4)–(5)):
the two states lie in a plane whose states form a Bloch ball, and the equal mixture, the midpoint of
their Bloch vectors, is diagonal in the ends of the diameter through it.

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

A second proof follows the brief's Fig. 3. The states of the plane form a Bloch ball, on which
`f` is affine along every chord, at most `1`, `1` at `ψ` and `0` at the antipode `χ`. Such a
function is `(1 + a · r) / 2` with `a` the Bloch vector of `ψ`, which on the sphere is the Born
rule.

`EnsemblesAndStates` assumes affinity only for mixtures of two pure states, which makes Theorem 9
stronger. The brief's affinity for countable mixtures implies it, so Theorem 9 holds over the
brief's EQST as well. Every ensemble is a countable mixture of pure states, its eigenvectors, so
countable affinity determines `p` from its values on pure states (Corollary 8); with BR-BORN,
`p(ϕ | ρ) = ⟨ϕ, ρ ϕ⟩`.

The three conditions are independent over EQST, when `E` has two orthonormal vectors: each one
holds in a model where the other two fail. The models use the Born rule for ensembles
`b(ψ | ρ) = ⟨ψ, ρ ψ⟩` and its shift `(1 + b) / 2`, which is affine and `1` only on the same ray
but never `0`: `b` with entropy `0` (BR-BORN only), `(1 + b) / 2` with the von Neumann entropy
(BR-ENT only), and `(1 + b) / 2` with the entropy `0` on pure states and `∞` otherwise ([B]MUTEX
only, since no two states are mutually exclusive and no mixture of two has entropy `log 2`). In
dimension at most one, EQST alone implies BR-BORN.

## ii. Key results

- `BornRuleEntropy.entropyOfBorn`, `BornRuleEntropy.strictAntiOn_entropyOfBorn`: Fig. 2.
- `BornRuleEntropy.vonNeumannEntropy_mix_proj_eq`, `BornRuleEntropy.norm_inner_sq_eq_iff`:
  Proposition 3.
- `BornRuleEntropy.BlochBall.vonNeumannEntropy_mix_proj_eq`: eq. (6) by the geometric
  diagonalization.
- `BornRuleEntropy.inner_eq_zero_iff`: Corollary 7.
- `BornRuleEntropy.EnsemblesAndStates`, `BornRuleEntropy.BornRule`,
  `BornRuleEntropy.IsVonNeumannEntropy`, `BornRuleEntropy.MutualExclusivity`: the conditions
  EQST, BR-BORN, BR-ENT, [B]MUTEX.
- `BornRuleEntropy.MutualExclusivity.of_bornRule`: BR-BORN + BR-ENT ⇒ [B]MUTEX.
- `BornRuleEntropy.IsVonNeumannEntropy.of_bornRule`: BR-BORN + [B]MUTEX ⇒ BR-ENT.
- `BornRuleEntropy.BornRule.of_isVonNeumannEntropy`: BR-ENT + [B]MUTEX ⇒ BR-BORN.
- `BornRuleEntropy.BlochBall.BornRule.of_isVonNeumannEntropy`: the same, on the Bloch ball.
- `BornRuleEntropy.two_conditions_imply_third`: Theorem 9.
- `BornRuleEntropy.CountablyAffine`: the brief's countable affinity.
- `BornRuleEntropy.two_conditions_imply_third_of_countablyAffine`: Theorem 9 over the brief's
  EQST.
- `BornRuleEntropy.CountablyAffine.exists_hasSum_proj`,
  `BornRuleEntropy.CountablyAffine.eq_of_eq_on_pure`: Corollary 8.
- `BornRuleEntropy.CountablyAffine.apply_eq_re_inner`: the Born rule for ensembles.
- `BornRuleEntropy.conditions_independent`: the conditions are independent over EQST.
- `BornRuleEntropy.BornRule.of_rank_le_one`: in dimension at most one, EQST implies BR-BORN.

## iii. Table of contents

- A. Born rule and entropy of equal mixtures
- B. The conditions
- C. BR-BORN and BR-ENT imply [B]MUTEX
- D. BR-BORN and [B]MUTEX imply BR-ENT
- E. Affine functions on a qubit
- F. BR-ENT and [B]MUTEX imply BR-BORN
- G. BR-ENT and [B]MUTEX imply BR-BORN on the Bloch ball
- H. Theorem 9
- I. Countable affinity and Corollary 8
- J. Independence of the conditions

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

/-- **Proposition 3**, eq. (6), by the geometric diagonalization of Fig. 1 and eqs. (4)–(5).
`ψ` and `ϕ` lie in a plane, whose states form a Bloch ball. There the equal mixture is
`((1 + √λ) / 2) ρ₊ + ((1 - √λ) / 2) ρ₋` for two orthogonal pure states `ρ±`, the ends of the
diameter through the midpoint of `ψ` and `ϕ` (`Qubit.exists_mix_proj_planeVector_eq`), so its
entropy is `h((1 + √λ) / 2)`. -/
theorem BlochBall.vonNeumannEntropy_mix_proj_eq {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    vonNeumannEntropy (mix (proj ψ) (proj ϕ)) =
      ENNReal.ofReal (entropyOfBorn (‖⟪ψ, ϕ⟫_ℂ‖ ^ 2)) := by
  rw [entropyOfBorn, Real.sqrt_sq (norm_nonneg _)]
  rcases Qubit.eq_smul_or_exists_planeVector_eq hψ ϕ with ⟨c, rfl⟩ | ⟨χ, hχ, hψχ, u, rfl⟩
  · have hc : ‖c‖ = 1 := by simpa [norm_smul, hψ] using hϕ
    have hm : mix (proj ψ) (proj (c • ψ)) = proj ψ := by
      rw [proj_smul, hc, one_pow, Complex.ofReal_one, one_smul, mix, ← add_smul]
      norm_num
    rw [hm, vonNeumannEntropy_proj hψ, inner_smul_right, norm_mul, hc, inner_self_eq_norm_sq_to_K,
      hψ]
    simp
  set e : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hψe : Qubit.planeVector ψ χ e = ψ := by simp [e, Qubit.planeVector]
  have hu : ‖u‖ = 1 := by rwa [Qubit.norm_planeVector hψ hχ hψχ] at hϕ
  obtain ⟨u₁, u₂, h₁, h₂, h₁₂, hmix⟩ := Qubit.exists_mix_proj_planeVector_eq hψ hχ hψχ he hu
  rw [hψe] at hmix
  set c := ‖⟪ψ, Qubit.planeVector ψ χ u⟫_ℂ‖
  have hc1 : c ≤ 1 := by
    simpa [hψ, hϕ] using norm_inner_le_norm (𝕜 := ℂ) ψ (Qubit.planeVector ψ χ u)
  have hc0 : 0 ≤ c := norm_nonneg _
  set v : Fin 2 → E := ![Qubit.planeVector ψ χ u₁, Qubit.planeVector ψ χ u₂]
  set q : Fin 2 → ℝ := ![(1 + c) / 2, (1 - c) / 2]
  have hv : Orthonormal ℂ v := by
    have n₁ := (Qubit.norm_planeVector hψ hχ hψχ u₁).trans h₁
    have n₂ := (Qubit.norm_planeVector hψ hχ hψχ u₂).trans h₂
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [v, h₁₂, inner_eq_zero_symm.mp h₁₂, inner_self_eq_norm_sq_to_K, n₁, n₂]
  have hq0 : ∀ i, 0 ≤ q i := fun i => by fin_cases i <;> simp [q] <;> linarith
  have hq : HasSum q 1 := by
    convert hasSum_fintype q using 1
    simp [q, Fin.sum_univ_two]
    ring
  have hρ : mix (proj ψ) (proj (Qubit.planeVector ψ χ u)) = ∑' i, (q i : ℂ) • proj (v i) := by
    rw [tsum_fintype, Fin.sum_univ_two, hmix]
    rfl
  rw [hρ, vonNeumannEntropy_tsum_smul_proj hv hq0 hq, tsum_fintype, Fin.sum_univ_two,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub, show 1 - (1 + c) / 2 = (1 - c) / 2 by ring]
  exact (ENNReal.ofReal_add (negMulLog_nonneg (hq0 0) (by simp [q]; linarith))
    (negMulLog_nonneg (hq0 1) (by simp [q]; linarith))).symm

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

omit [CompleteSpace E] in
/-- The weights `½, ½` on two indices `i ≠ j` of a family of vectors: their mixture is the equal
mixture of `ψᵢ` and `ψⱼ`, and their Shannon entropy is `log 2`. -/
lemma exists_weights_mix {ι : Type*} (ψ : ι → E) {i j : ι} (hij : i ≠ j) :
    ∃ w : ι → ℝ, (∀ k, 0 ≤ w k) ∧ HasSum w 1 ∧
      ∑' k, (w k : ℂ) • proj (ψ k) = mix (proj (ψ i)) (proj (ψ j)) ∧
      ∑' k, ENNReal.ofReal (negMulLog (w k)) = ENNReal.ofReal (log 2) := by
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
  exact ⟨w, fun k => by simp only [w]; split_ifs <;> norm_num, hw, hmix, hent⟩

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
    obtain ⟨w, hw0, hw, hmix, hent⟩ := exists_weights_mix ψ hij
    have hS2 := h w hw0 hw
    rw [hmix, hS _ ((isDensityOperator_proj (hψ i)).mix (isDensityOperator_proj (hψ j))),
      hent] at hS2
    rw [hB (hψ i) (hψ j), (inner_eq_zero_iff (hψ i) (hψ j)).mpr hS2]
    simp

/-! ## D. BR-BORN and [B]MUTEX imply BR-ENT -/

/-- BR-BORN and [B]MUTEX imply BR-ENT. The eigenvectors with nonzero eigenvalue of a density
operator form a countable orthonormal family (`IsDensityOperator.exists_tsum_smul_proj`),
mutually exclusive by BR-BORN. -/
theorem IsVonNeumannEntropy.of_bornRule (hB : BornRule p) (hM : MutualExclusivity S p) :
    IsVonNeumannEntropy S := by
  intro ρ hρ
  obtain ⟨ι, _, φ, w, hφ, hw0, hw, hρ'⟩ := hρ.exists_tsum_smul_proj
  have hM' := (hM ι φ hφ.1).mp (fun i j hij => by
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

/-! ## G. BR-ENT and [B]MUTEX imply BR-BORN on the Bloch ball -/

/-- BR-ENT and [B]MUTEX imply BR-BORN, over EQST, by the brief's argument of Fig. 3. `ψ` and `ϕ`
lie in a plane, whose states form a Bloch ball. On it, `f(r) = p(ψ | ρ(r))` is affine along every
chord, since the ends of a chord are pure states and EQST makes `p` affine in mixtures of two pure
states. Also `f ≤ 1`, `f = 1` at `ψ`, and `f = 0` at the antipode `ψ⊥`, since orthogonal states
are mutually exclusive. So `f(r) = (1 + a · r) / 2` with `a` the Bloch vector of `ψ`
(`eq_of_chord_of_le_one`), and on the sphere this is `|⟨ψ|ϕ⟩|²`. -/
theorem BlochBall.BornRule.of_isVonNeumannEntropy (hp : EnsemblesAndStates p)
    (hS : IsVonNeumannEntropy S) (hM : MutualExclusivity S p) : BornRule p := by
  intro ψ ϕ hψ hϕ
  rcases Qubit.eq_smul_or_exists_planeVector_eq hψ ϕ with ⟨c, rfl⟩ | ⟨χ, hχ, hψχ, u, rfl⟩
  · have hc : ‖c‖ = 1 := by simpa [norm_smul, hψ] using hϕ
    rw [proj_smul, hc, one_pow, Complex.ofReal_one, one_smul, (hp.eq_one_iff hψ hψ).mpr rfl,
      inner_smul_right, norm_mul, hc, inner_self_eq_norm_sq_to_K, hψ]
    simp
  set e : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![1, 0]
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  have hψe : Qubit.planeVector ψ χ e = ψ := by simp [e, Qubit.planeVector]
  have hu : ‖u‖ = 1 := by rwa [Qubit.norm_planeVector hψ hχ hψχ] at hϕ
  -- The Bloch ball as the unit ball of Euclidean `ℝ³`.
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin 3), ⟪x, y⟫_ℝ = x.ofLp ⬝ᵥ y.ofLp := fun x y => by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  have hdot : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → x.ofLp ⬝ᵥ x.ofLp = 1 := fun x hx => by
    rw [← hinner, real_inner_self_eq_norm_sq, hx, one_pow]
  have hnorm : ∀ a : Fin 3 → ℝ, a ⬝ᵥ a = 1 → ‖WithLp.toLp 2 a‖ = 1 := fun a ha => by
    rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← real_inner_self_eq_norm_sq,
      hinner]
    exact ha
  -- A unit Bloch vector is a pure state of the plane.
  have hpure : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 →
      ∃ w : EuclideanSpace ℂ (Fin 2), ‖Qubit.planeVector ψ χ w‖ = 1 ∧
        Qubit.blochVector w = x.ofLp ∧
        Qubit.blochOperator ψ χ x.ofLp = proj (Qubit.planeVector ψ χ w) := fun x hx => by
    obtain ⟨w, hw, hbw, hpw⟩ := Qubit.exists_proj_planeVector_eq (ψ := ψ) (χ := χ) (hdot x hx)
    exact ⟨w, (Qubit.norm_planeVector hψ hχ hψχ w).trans hw, hbw, hpw.symm⟩
  set f : EuclideanSpace ℝ (Fin 3) → ℝ := fun r => p (proj ψ) (Qubit.blochOperator ψ χ r.ofLp)
  have hchord : ∀ x y : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → ‖y‖ = 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • x + (1 - t) • y) = t * f x + (1 - t) * f y := by
    intro x y hx hy t ht0 ht1
    obtain ⟨wx, hwx, -, hpx⟩ := hpure x hx
    obtain ⟨wy, hwy, -, hpy⟩ := hpure y hy
    simp only [f, WithLp.ofLp_add, WithLp.ofLp_smul, Qubit.blochOperator_convex, hpx, hpy]
    exact hp.affine hψ hwx hwy ht0 ht1
  have hle : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ = 1 → f x ≤ 1 := fun x hx => by
    obtain ⟨w, hw, -, hpw⟩ := hpure x hx
    simp only [f, hpw]
    exact (hp.mem_Icc hψ (isDensityOperator_proj hw)).2
  -- `ψ` and its antipode.
  have hae : Qubit.blochVector e ⬝ᵥ Qubit.blochVector e = 1 := by
    rw [Qubit.blochVector_dotProduct_self, he, one_pow]
  set a : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (Qubit.blochVector e)
  have ha : ‖a‖ = 1 := hnorm _ hae
  have hfa : f a = 1 := by
    simp only [f, a, ← Qubit.proj_planeVector he, hψe]
    exact (hp.eq_one_iff hψ hψ).mpr rfl
  have hfna : f (-a) = 0 := by
    obtain ⟨w, hw, hbw, hpw⟩ := hpure (-a) (by rwa [norm_neg])
    have hw' : ‖w‖ = 1 := by rwa [Qubit.norm_planeVector hψ hχ hψχ] at hw
    have horth : ⟪ψ, Qubit.planeVector ψ χ w⟫_ℂ = 0 := by
      have h := Qubit.inner_planeVector_eq_zero_iff hψ hχ hψχ he hw'
      rw [hψe] at h
      rw [h, hbw]
      simp [a]
    simp only [f, hpw]
    exact apply_eq_zero_of_inner_eq_zero hS hM hψ hw horth
  -- The affine function is `(1 + a · r) / 2`.
  have hb : ‖(WithLp.toLp 2 (Qubit.blochVector u) : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    refine hnorm _ ?_
    rw [Qubit.blochVector_dotProduct_self, hu, one_pow]
  have key := eq_of_chord_of_le_one hchord hle ha hfa hfna hb.le
  simp only [f, a, hinner] at key
  have hB := Qubit.norm_inner_planeVector_sq hψ hχ hψχ he hu
  rw [hψe] at hB
  rw [Qubit.proj_planeVector hu, key, hB]

/-! ## H. Theorem 9 -/

/-- **Theorem 9.** Over EQST, any two of BR-BORN, BR-ENT and [B]MUTEX imply the third. -/
theorem two_conditions_imply_third (hp : EnsemblesAndStates p) :
    (BornRule p → IsVonNeumannEntropy S → MutualExclusivity S p) ∧
      (BornRule p → MutualExclusivity S p → IsVonNeumannEntropy S) ∧
      (IsVonNeumannEntropy S → MutualExclusivity S p → BornRule p) :=
  ⟨MutualExclusivity.of_bornRule, IsVonNeumannEntropy.of_bornRule,
    BornRule.of_isVonNeumannEntropy hp⟩


/-! ## I. Countable affinity and Corollary 8 -/

/-- **Affinity in EQST**, as the brief states it: `p(ϕ | ∑ᵢ wᵢ ψᵢ) = ∑ᵢ wᵢ p(ϕ | ψᵢ)` for every
countable mixture of pure states, with the sum on the right converging. -/
def CountablyAffine (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) : Prop :=
  ∀ {ϕ : E} (ι : Type u) [Countable ι] (ψ : ι → E) (w : ι → ℝ), ‖ϕ‖ = 1 → (∀ i, ‖ψ i‖ = 1) →
    (∀ i, 0 ≤ w i) → HasSum w 1 →
      HasSum (fun i => w i * p (proj ϕ) (proj (ψ i))) (p (proj ϕ) (∑' i, (w i : ℂ) • proj (ψ i)))

private lemma tsum_ulift_fin_two {X : Type*} [AddCommMonoid X] [TopologicalSpace X]
    (F : ULift.{u} (Fin 2) → X) : ∑' i, F i = F ⟨0⟩ + F ⟨1⟩ := by
  rw [← Equiv.ulift.symm.tsum_eq, tsum_fintype, Fin.sum_univ_two]
  rfl

omit [CompleteSpace E] in
/-- Countable affinity implies the affinity for two pure states of `EnsemblesAndStates`. -/
theorem CountablyAffine.affine (hp : CountablyAffine p) {ψ φ₁ φ₂ : E} {t : ℝ} (hψ : ‖ψ‖ = 1)
    (h₁ : ‖φ₁‖ = 1) (h₂ : ‖φ₂‖ = 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    p (proj ψ) ((t : ℂ) • proj φ₁ + ((1 - t : ℝ) : ℂ) • proj φ₂) =
      t * p (proj ψ) (proj φ₁) + (1 - t) * p (proj ψ) (proj φ₂) := by
  set φ : ULift.{u} (Fin 2) → E := fun i => ![φ₁, φ₂] i.down
  set w : ULift.{u} (Fin 2) → ℝ := fun i => ![t, 1 - t] i.down
  have hw : HasSum w 1 := by
    rw [← Equiv.ulift.symm.hasSum_iff]
    convert hasSum_fintype (w ∘ Equiv.ulift.symm)
    simp [w, Fin.sum_univ_two]
  have h := (hp _ φ w hψ (by rintro ⟨i⟩; fin_cases i <;> simpa [φ])
    (by rintro ⟨i⟩; fin_cases i <;> simp [w, ht0, ht1]) hw).tsum_eq
  rw [tsum_ulift_fin_two, tsum_ulift_fin_two] at h
  exact h.symm

/-- The brief's EQST, with countable affinity, implies `EnsemblesAndStates`. -/
theorem EnsemblesAndStates.of_countablyAffine
    (mem_Icc : ∀ {ψ : E} {ρ : E →L[ℂ] E}, ‖ψ‖ = 1 → IsDensityOperator ρ →
      p (proj ψ) ρ ∈ Set.Icc 0 1)
    (hp : CountablyAffine p)
    (eq_one_iff : ∀ {ψ φ : E}, ‖ψ‖ = 1 → ‖φ‖ = 1 →
      (p (proj ψ) (proj φ) = 1 ↔ proj ψ = proj φ)) :
    EnsemblesAndStates p :=
  ⟨mem_Icc, hp.affine, eq_one_iff⟩

/-- **Theorem 9** over the brief's EQST, with affinity for countable mixtures. -/
theorem two_conditions_imply_third_of_countablyAffine
    (mem_Icc : ∀ {ψ : E} {ρ : E →L[ℂ] E}, ‖ψ‖ = 1 → IsDensityOperator ρ →
      p (proj ψ) ρ ∈ Set.Icc 0 1)
    (hp : CountablyAffine p)
    (eq_one_iff : ∀ {ψ φ : E}, ‖ψ‖ = 1 → ‖φ‖ = 1 →
      (p (proj ψ) (proj φ) = 1 ↔ proj ψ = proj φ)) :
    (BornRule p → IsVonNeumannEntropy S → MutualExclusivity S p) ∧
      (BornRule p → MutualExclusivity S p → IsVonNeumannEntropy S) ∧
      (IsVonNeumannEntropy S → MutualExclusivity S p → BornRule p) :=
  two_conditions_imply_third (EnsemblesAndStates.of_countablyAffine mem_Icc hp eq_one_iff)

/-- **Corollary 8.** Every ensemble is a countable mixture of pure states,
`ρ = ∑ᵢ wᵢ |ψᵢ⟩⟨ψᵢ|`, and then `p(ϕ | ρ) = ∑ᵢ wᵢ p(ϕ | ψᵢ)`. -/
theorem CountablyAffine.exists_hasSum_proj (hp : CountablyAffine p) {ϕ : E} (hϕ : ‖ϕ‖ = 1)
    {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    ∃ (ι : Type u) (_ : Countable ι) (ψ : ι → E) (w : ι → ℝ), Orthonormal ℂ ψ ∧
      (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧ ∑' i, (w i : ℂ) • proj (ψ i) = ρ ∧
      HasSum (fun i => w i * p (proj ϕ) (proj (ψ i))) (p (proj ϕ) ρ) := by
  obtain ⟨ι, _, ψ, w, hψ, hw0, hw, rfl⟩ := hρ.exists_tsum_smul_proj
  exact ⟨ι, inferInstance, ψ, w, hψ, hw0, hw, rfl, hp ι ψ w hϕ hψ.1 hw0 hw⟩

/-- **Corollary 8.** `p` is fully specified by its values on pure states: two countably affine
conditional probabilities that agree on pure states agree on all ensembles. -/
theorem CountablyAffine.eq_of_eq_on_pure {q : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ}
    (hp : CountablyAffine p) (hq : CountablyAffine q)
    (h : ∀ {ϕ ψ : E}, ‖ϕ‖ = 1 → ‖ψ‖ = 1 → p (proj ϕ) (proj ψ) = q (proj ϕ) (proj ψ))
    {ϕ : E} (hϕ : ‖ϕ‖ = 1) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    p (proj ϕ) ρ = q (proj ϕ) ρ := by
  obtain ⟨ι, _, ψ, w, hψ, hw0, hw, rfl⟩ := hρ.exists_tsum_smul_proj
  refine (hp ι ψ w hϕ hψ.1 hw0 hw).unique ?_
  convert hq ι ψ w hϕ hψ.1 hw0 hw using 3 with i
  exact h hϕ (hψ.1 i)

/-- With BR-BORN, Corollary 8 gives the Born rule for ensembles: `p(ϕ | ρ) = ⟨ϕ, ρ ϕ⟩`. -/
theorem CountablyAffine.apply_eq_re_inner (hp : CountablyAffine p) (hB : BornRule p) {ϕ : E}
    (hϕ : ‖ϕ‖ = 1) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    p (proj ϕ) ρ = (⟪ϕ, ρ ϕ⟫_ℂ).re := by
  obtain ⟨ι, _, ψ, w, hψ, hw0, hw, rfl⟩ := hρ.exists_tsum_smul_proj
  refine (hp ι ψ w hϕ hψ.1 hw0 hw).unique ?_
  convert Complex.hasSum_re
    ((innerSL ℂ ϕ).hasSum (hasSum_smul_proj_apply hψ hw.summable ϕ)) using 2 with i
  · rw [hB hϕ (hψ.1 i), norm_inner_symm, innerSL_apply_apply, inner_smul_right,
      ← inner_conj_symm ϕ (ψ i), mul_assoc, Complex.mul_conj']
    norm_cast
  · rfl

/-! ## J. Independence of the conditions -/

open Classical in
/-- The Born rule extended to ensembles, `p(ψ | ρ) = ⟨ψ, ρ ψ⟩`, read off the pure state
`|ψ⟩⟨ψ|` (and `0` if the first argument is not a pure state). -/
def bornProb (A ρ : E →L[ℂ] E) : ℝ :=
  if h : ∃ ψ : E, ‖ψ‖ = 1 ∧ A = proj ψ then (⟪h.choose, ρ h.choose⟫_ℂ).re else 0

omit [CompleteSpace E] in
lemma bornProb_proj {ψ : E} (hψ : ‖ψ‖ = 1) (ρ : E →L[ℂ] E) :
    bornProb (proj ψ) ρ = (⟪ψ, ρ ψ⟫_ℂ).re := by
  rw [bornProb]
  split_ifs with h
  swap
  · exact absurd ⟨ψ, hψ, rfl⟩ h
  obtain ⟨hφ, he⟩ := h.choose_spec
  obtain ⟨c, hc, hcφ⟩ := exists_norm_eq_one_smul_of_norm_inner_eq_one (𝕜 := ℂ) hφ hψ
    (by rw [norm_inner_symm]; exact norm_inner_eq_one_of_proj_eq hψ he)
  rw [hcφ, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', hc]
  simp

omit [CompleteSpace E] in
lemma bornProb_proj_proj {ψ : E} (hψ : ‖ψ‖ = 1) (φ : E) :
    bornProb (proj ψ) (proj φ) = ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  rw [bornProb_proj hψ, inner_proj_apply, Complex.ofReal_re, norm_inner_symm]

lemma bornProb_mem_Icc {ψ : E} (hψ : ‖ψ‖ = 1) {ρ : E →L[ℂ] E} (hρ : IsDensityOperator ρ) :
    bornProb (proj ψ) ρ ∈ Set.Icc 0 1 := by
  rw [bornProb_proj hψ]
  refine ⟨ContinuousLinearMap.re_inner_apply_nonneg hρ.nonneg ψ, ?_⟩
  calc (⟪ψ, ρ ψ⟫_ℂ).re ≤ ‖⟪ψ, ρ ψ⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖ψ‖ * ‖ρ ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (‖ρ‖ * ‖ψ‖) := by gcongr; exact ρ.le_opNorm ψ
    _ ≤ 1 := by rw [hψ, one_mul, mul_one]; exact hρ.norm_le_one

theorem bornProb_countablyAffine : CountablyAffine (bornProb (E := E)) := by
  intro ϕ ι _ ψ w hϕ hψ hw0 hw
  have hs : Summable fun i => (w i : ℂ) • proj (ψ i) :=
    Summable.of_norm_bounded hw.summable.abs fun i => by simp [norm_smul, hψ i]
  have h := Complex.hasSum_re
    ((innerSL ℂ ϕ).hasSum ((ContinuousLinearMap.apply ℂ E ϕ).hasSum hs.hasSum))
  rw [bornProb_proj hϕ]
  convert h using 1
  · funext i
    rw [bornProb_proj hϕ]
    simp [inner_smul_right]
  · rfl

/-- The Born rule extended to ensembles satisfies EQST. -/
theorem ensemblesAndStates_bornProb : EnsemblesAndStates (bornProb (E := E)) :=
  .of_countablyAffine (fun hψ hρ => bornProb_mem_Icc hψ hρ) bornProb_countablyAffine fun hψ hφ => by
    rw [bornProb_proj_proj hψ, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]
    exact ⟨proj_eq_proj_of_norm_inner_eq_one hψ hφ, norm_inner_eq_one_of_proj_eq hψ⟩

omit [CompleteSpace E] in
lemma bornRule_bornProb : BornRule (bornProb (E := E)) := fun hψ _ => bornProb_proj_proj hψ _

/-- The Born rule moved halfway to certainty, `p(ψ | ρ) = (1 + ⟨ψ, ρ ψ⟩) / 2`. -/
def halfBornProb (A ρ : E →L[ℂ] E) : ℝ := 2⁻¹ + 2⁻¹ * bornProb A ρ

theorem halfBornProb_countablyAffine : CountablyAffine (halfBornProb (E := E)) := by
  intro ϕ ι _ ψ w hϕ hψ hw0 hw
  convert (hw.mul_left 2⁻¹).add ((bornProb_countablyAffine ι ψ w hϕ hψ hw0 hw).mul_left 2⁻¹)
    using 1
  · funext i
    simp only [halfBornProb]
    ring
  · simp [halfBornProb]

/-- `(1 + ⟨ψ, ρ ψ⟩) / 2` satisfies EQST. -/
theorem ensemblesAndStates_halfBornProb : EnsemblesAndStates (halfBornProb (E := E)) :=
  .of_countablyAffine
    (fun hψ hρ => by
      have h := bornProb_mem_Icc hψ hρ
      simp only [halfBornProb, Set.mem_Icc] at h ⊢
      constructor <;> linarith [h.1, h.2])
    halfBornProb_countablyAffine fun hψ hφ => by
      rw [halfBornProb, ← ensemblesAndStates_bornProb.eq_one_iff hψ hφ]
      constructor <;> intro h <;> linarith

open Classical in
/-- The entropy `0` on pure states and `∞` on all other operators. -/
def pureEntropy (ρ : E →L[ℂ] E) : ℝ≥0∞ :=
  if ∃ ψ : E, ‖ψ‖ = 1 ∧ ρ = proj ψ then 0 else ⊤

omit [CompleteSpace E] in
lemma pureEntropy_proj {ψ : E} (hψ : ‖ψ‖ = 1) : pureEntropy (proj ψ) = 0 := by
  rw [pureEntropy]
  split_ifs with h
  · rfl
  · exact absurd ⟨ψ, hψ, rfl⟩ h

omit [CompleteSpace E] in
lemma pureEntropy_eq_zero_or_eq_top (ρ : E →L[ℂ] E) : pureEntropy ρ = 0 ∨ pureEntropy ρ = ⊤ := by
  unfold pureEntropy
  split_ifs <;> simp

/-- `(1 + ⟨ψ, ρ ψ⟩) / 2` and `pureEntropy` satisfy [B]MUTEX: no two states are mutually exclusive,
and every mixture of two or more states has entropy `0` or `∞`, never a Shannon entropy `log 2`. -/
theorem mutualExclusivity_pureEntropy : MutualExclusivity (pureEntropy (E := E)) halfBornProb := by
  intro ι _ φ hφ
  have hpos : ∀ i j, halfBornProb (proj (φ i)) (proj (φ j)) ≠ 0 := fun i j h => by
    have := (bornProb_mem_Icc (hφ i) (isDensityOperator_proj (hφ j))).1
    rw [halfBornProb] at h
    linarith
  constructor
  · intro h0 w hw0 hw
    have hsub : ∀ i j, i = j := fun i j => by_contra fun hij => hpos i j (h0 i j hij)
    have hne : Nonempty ι := by
      by_contra hne
      have : IsEmpty ι := not_nonempty_iff.mp hne
      exact one_ne_zero (hw.unique hasSum_empty)
    obtain ⟨i⟩ := hne
    have hwi : w i = 1 := (hasSum_single i fun j hj => absurd (hsub j i) hj).unique hw
    rw [tsum_eq_single i fun j hj => absurd (hsub j i) hj,
      tsum_eq_single i fun j hj => absurd (hsub j i) hj, hwi]
    simp [pureEntropy_proj (hφ i)]
  · intro hS i j hij
    obtain ⟨w, hw0, hw, hmix, hent⟩ := exists_weights_mix φ hij
    have h := hS w hw0 hw
    rw [hmix, hent] at h
    rcases pureEntropy_eq_zero_or_eq_top (mix (proj (φ i)) (proj (φ j))) with h' | h'
    · rw [h] at h'
      exact absurd h' (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two)).ne'
    · rw [h] at h'
      exact absurd h' ENNReal.ofReal_ne_top

section Models

variable {ψ χ : E} (hψ : ‖ψ‖ = 1) (hχ : ‖χ‖ = 1) (hψχ : ⟪ψ, χ⟫_ℂ = 0)
include hψ hχ hψχ

omit [CompleteSpace E] in
lemma not_bornRule_halfBornProb : ¬ BornRule (halfBornProb (E := E)) := fun hB => by
  have h := hB hψ hχ
  rw [halfBornProb, bornProb_proj_proj hψ, hψχ] at h
  norm_num at h

/-- **Independence, first model.** The Born rule with entropy `0` satisfies EQST and BR-BORN, but
neither BR-ENT nor [B]MUTEX. -/
theorem exists_bornRule_not_isVonNeumannEntropy :
    ∃ (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) (S : (E →L[ℂ] E) → ℝ≥0∞), EnsemblesAndStates p ∧
      CountablyAffine p ∧ BornRule p ∧ ¬ IsVonNeumannEntropy S ∧ ¬ MutualExclusivity S p := by
  have hS : ¬ IsVonNeumannEntropy (fun _ => 0 : (E →L[ℂ] E) → ℝ≥0∞) := fun h => by
    have h0 := h _ ((isDensityOperator_proj hψ).mix (isDensityOperator_proj hχ))
    rw [(inner_eq_zero_iff hψ hχ).mp hψχ] at h0
    exact (ENNReal.ofReal_pos.mpr (Real.log_pos one_lt_two)).ne h0
  exact ⟨bornProb, _, ensemblesAndStates_bornProb, bornProb_countablyAffine, bornRule_bornProb,
    hS, fun hM => hS (IsVonNeumannEntropy.of_bornRule bornRule_bornProb hM)⟩

/-- **Independence, second model.** `(1 + ⟨ψ, ρ ψ⟩) / 2` with the von Neumann entropy satisfies
EQST and BR-ENT, but neither BR-BORN nor [B]MUTEX. -/
theorem exists_isVonNeumannEntropy_not_bornRule :
    ∃ (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) (S : (E →L[ℂ] E) → ℝ≥0∞), EnsemblesAndStates p ∧
      CountablyAffine p ∧ IsVonNeumannEntropy S ∧ ¬ BornRule p ∧ ¬ MutualExclusivity S p :=
  ⟨halfBornProb, vonNeumannEntropy, ensemblesAndStates_halfBornProb,
    halfBornProb_countablyAffine, fun _ _ => rfl, not_bornRule_halfBornProb hψ hχ hψχ,
    fun hM => not_bornRule_halfBornProb hψ hχ hψχ
      (BornRule.of_isVonNeumannEntropy ensemblesAndStates_halfBornProb (fun _ _ => rfl) hM)⟩

/-- **Independence, third model.** `(1 + ⟨ψ, ρ ψ⟩) / 2` with `pureEntropy` satisfies EQST and
[B]MUTEX, but neither BR-BORN nor BR-ENT. -/
theorem exists_mutualExclusivity_not_bornRule :
    ∃ (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) (S : (E →L[ℂ] E) → ℝ≥0∞), EnsemblesAndStates p ∧
      CountablyAffine p ∧ MutualExclusivity S p ∧ ¬ BornRule p ∧ ¬ IsVonNeumannEntropy S :=
  ⟨halfBornProb, pureEntropy, ensemblesAndStates_halfBornProb, halfBornProb_countablyAffine,
    mutualExclusivity_pureEntropy, not_bornRule_halfBornProb hψ hχ hψχ,
    fun hS => not_bornRule_halfBornProb hψ hχ hψχ (BornRule.of_isVonNeumannEntropy
      ensemblesAndStates_halfBornProb hS mutualExclusivity_pureEntropy)⟩

/-- **Independence of the conditions.** If `E` has two orthonormal vectors, none of BR-BORN,
BR-ENT and [B]MUTEX implies another over EQST (with countable affinity): for each condition
there are `p` and `S` satisfying it and violating the other two. -/
theorem conditions_independent :
    (∃ (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) (S : (E →L[ℂ] E) → ℝ≥0∞), EnsemblesAndStates p ∧
      CountablyAffine p ∧ BornRule p ∧ ¬ IsVonNeumannEntropy S ∧ ¬ MutualExclusivity S p) ∧
    (∃ (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) (S : (E →L[ℂ] E) → ℝ≥0∞), EnsemblesAndStates p ∧
      CountablyAffine p ∧ IsVonNeumannEntropy S ∧ ¬ BornRule p ∧ ¬ MutualExclusivity S p) ∧
    (∃ (p : (E →L[ℂ] E) → (E →L[ℂ] E) → ℝ) (S : (E →L[ℂ] E) → ℝ≥0∞), EnsemblesAndStates p ∧
      CountablyAffine p ∧ MutualExclusivity S p ∧ ¬ BornRule p ∧ ¬ IsVonNeumannEntropy S) :=
  ⟨exists_bornRule_not_isVonNeumannEntropy hψ hχ hψχ,
    exists_isVonNeumannEntropy_not_bornRule hψ hχ hψχ,
    exists_mutualExclusivity_not_bornRule hψ hχ hψχ⟩

end Models

/-- In dimension at most one, EQST alone implies BR-BORN, since all unit vectors span the same
ray; so independence needs two orthonormal vectors. -/
theorem BornRule.of_rank_le_one (hp : EnsemblesAndStates p) (hE : Module.rank ℂ E ≤ 1) :
    BornRule p := by
  intro ψ ϕ hψ hϕ
  obtain ⟨v, hv⟩ := rank_le_one_iff.mp hE
  obtain ⟨a, rfl⟩ := hv ψ
  obtain ⟨b, rfl⟩ := hv ϕ
  have h1 : ‖⟪a • v, b • v⟫_ℂ‖ = 1 := by
    rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [norm_mul, Complex.norm_conj, norm_pow, RCLike.norm_ofReal, abs_norm]
    rw [norm_smul] at hψ hϕ
    linear_combination (‖b‖ * ‖v‖) * hψ + hϕ
  rw [(hp.eq_one_iff hψ hϕ).mpr (proj_eq_proj_of_norm_inner_eq_one hψ hϕ h1), h1, one_pow]

end BornRuleEntropy
