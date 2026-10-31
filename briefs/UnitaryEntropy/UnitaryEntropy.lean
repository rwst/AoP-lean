/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

/-
Schrödinger equation is equivalent to information conservation.
Technical brief by G. Carcassi for the Assumptions of Physics collaboration,
https://assumptionsofphysics.org/resources/briefs

Setting: a finite-dimensional complex Hilbert space `E`. Density operators are positive operators
of trace one (`IsDensity`), pure states are the projectors `proj ψ = |ψ⟩⟨ψ|` for unit `ψ` (both
from `ForPhyslib/QuantumMechanics/Wigner/Density`), and the
von Neumann entropy `vonNeumann ρ` is the sum of `-μ log μ` over the eigenvalues `μ` of `ρ`,
counted with multiplicity.

Corollary 1 (Born rule is entropy):
* `vonNeumann_mix_proj`  `S(½ρψ + ½ρϕ) = -(1+√p)/2 log((1+√p)/2) - (1-√p)/2 log((1-√p)/2)`
  with `p = born ψ ϕ`;
* `mixEntropy_strictAntiOn`  this function of `p` is strictly decreasing on `[0, 1]`;
* `born_eq_iff`  `p(ϕ|ψ) = p` iff the mixture has that entropy.

Theorem 2, DR-SCEQ ⇒ DR-INFO + EVDIFF:
* `star_mul_self_of_schrodinger`  a propagator solving `U' = (iħ)⁻¹ H(t) U` with self-adjoint
  `H(t)` and `U(t₀) = 1` is an isometry, hence unitary in finite dimension;
* `hasDerivAt_exp_schrodinger`  for constant `H`, `exp (t (iħ)⁻¹ H)` is such a propagator;
* `vonNeumann_unitary_conj`  unitary conjugation preserves the entropy;
* `schrodinger_conserves_entropy`  `ρF = U ρ U†` is a density operator, the reconstructed past
  is `ρ`, and `S(ρF) = S(ρ)`.

Theorem 2, DR-INFO + EVDIFF ⇒ DR-SCEQ:
* `vonNeumann_eq_zero_iff`  Step 1: a density operator is pure iff its entropy is zero;
* `pure_and_born_of_preserves`  Steps 1–2: an entropy-preserving map that preserves equal
  mixtures sends pure states to pure states and preserves transition probabilities;
* `exists_hamiltonian`  Step 3: the derivative of a differentiable unitary family at
  `U(t₀) = 1` is `(iħ)⁻¹ H` with `H` self-adjoint;
* `schrodinger_of_preserves`  the whole direction: Wigner's theorem
  (`ForPhyslib/QuantumMechanics/Wigner`) turns Steps 1–2 into unitaries `U(t)`, chosen with
  `U(t₀) = 1` and differentiable at `t₀`, and Step 3 gives the Schrödinger equation at `t₀`.
-/

public import ForMathlib.Analysis.Calculus.Deriv.Star
public import ForMathlib.Analysis.InnerProductSpace.Adjoint
public import ForPhyslib.QuantumMechanics.Wigner.Density
public import ForPhyslib.QuantumMechanics.Wigner.Differentiable
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public noncomputable section

namespace UnitaryEntropy

open Real InnerProductSpace ComplexConjugate ComplexOrder QuantumMechanics.Wigner
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

section Entropy

/-- The Born rule `p(ψ | ϕ) = ⟨ϕ|ψ⟩⟨ψ|ϕ⟩ / (⟨ψ|ψ⟩⟨ϕ|ϕ⟩)`. -/
def born (ψ ϕ : E) : ℝ := ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2 / (‖ψ‖ ^ 2 * ‖ϕ‖ ^ 2)

/-- The entropy of an equal mixture of two pure states with transition probability `p`. -/
def mixEntropy (p : ℝ) : ℝ := binEntropy ((1 + √p) / 2)

theorem mixEntropy_eq (p : ℝ) :
    mixEntropy p = negMulLog ((1 + √p) / 2) + negMulLog ((1 - √p) / 2) := by
  rw [mixEntropy, binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  ring_nf

theorem mixEntropy_strictAntiOn : StrictAntiOn mixEntropy (Set.Icc 0 1) := by
  have h := qaryEntropy_strictAntiOn (q := 2) le_rfl
  rw [qaryEntropy_two] at h
  have mem : ∀ r ∈ Set.Icc (0 : ℝ) 1, (1 + √r) / 2 ∈ Set.Icc (1 - 1 / ((2 : ℕ) : ℝ)) 1 := by
    intro r hr
    have h0 := Real.sqrt_nonneg r
    have h1 : √r ≤ 1 := Real.sqrt_le_one.mpr hr.2
    constructor <;> push_cast <;> linarith
  intro p hp q hq hpq
  exact h (mem p hp) (mem q hq) (by linarith [Real.sqrt_lt_sqrt hp.1 hpq])

lemma born_of_norm {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    born ψ ϕ = ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2 := by
  simp [born, hψ, hϕ]

lemma born_mem_Icc {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) : born ψ ϕ ∈ Set.Icc 0 1 := by
  rw [born_of_norm hψ hϕ]
  have := norm_inner_le_norm (𝕜 := ℂ) ψ ϕ
  rw [hψ, hϕ, one_mul] at this
  exact ⟨by positivity, pow_le_one₀ (norm_nonneg _) this⟩

/-- Two points can be interpolated: `-μ log μ = α μ + β μ²` at `μ = a` and `μ = b`. -/
lemma exists_negMulLog_eq (a b : ℝ) :
    ∃ α β : ℝ, negMulLog a = α * a + β * a ^ 2 ∧ negMulLog b = α * b + β * b ^ 2 := by
  by_cases hab : a = b
  · subst hab
    exact ⟨-log a, 0, by simp only [negMulLog]; ring, by simp only [negMulLog]; ring⟩
  · have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    refine ⟨-log a - (log a - log b) / (b - a) * a, (log a - log b) / (b - a), ?_, ?_⟩ <;>
      simp only [negMulLog] <;> field_simp <;> ring

/-- `ρ = ½ |ψ⟩⟨ψ| + ½ |ϕ⟩⟨ϕ|` satisfies `ρ³ = ρ² - ((1 - |⟨ψ|ϕ⟩|²) / 4) ρ`. -/
lemma mix_proj_cubic {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) (x : E) :
    mix (proj ψ) (proj ϕ) (mix (proj ψ) (proj ϕ) (mix (proj ψ) (proj ϕ) x)) =
      mix (proj ψ) (proj ϕ) (mix (proj ψ) (proj ϕ) x) -
        ((1 - ⟪ψ, ϕ⟫_ℂ * ⟪ϕ, ψ⟫_ℂ) / 4) • mix (proj ψ) (proj ϕ) x := by
  have h1 : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have h2 : ⟪ϕ, ϕ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hϕ]; simp
  simp only [mix, add_apply, smul_apply, proj_apply,
    inner_add_right, inner_smul_right, h1, h2]
  module

/-- `(½ |ψ⟩⟨ψ| + ½ |ϕ⟩⟨ϕ|)²` as a combination of rank-one operators. -/
lemma mix_proj_sq (ψ ϕ : E) (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    mix (proj ψ) (proj ϕ) * mix (proj ψ) (proj ϕ) =
      (4⁻¹ : ℂ) • (proj ψ + proj ϕ + ⟪ψ, ϕ⟫_ℂ • rankOne ℂ ψ ϕ + ⟪ϕ, ψ⟫_ℂ • rankOne ℂ ϕ ψ) := by
  have h1 : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
  have h2 : ⟪ϕ, ϕ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hϕ]; simp
  ext x
  simp only [mix, mul_apply_eq_comp, add_apply,
    smul_apply, rankOne_apply, inner_add_right,
    inner_smul_right, h1, h2]
  module

variable [FiniteDimensional ℂ E]

/-- The von Neumann entropy `-tr (ρ log ρ)`: the sum of `-μ log μ` over the eigenvalues `μ` of `ρ`,
counted with multiplicity as roots of the characteristic polynomial. -/
def vonNeumann (ρ : E →L[ℂ] E) : ℝ :=
  ((ρ : E →ₗ[ℂ] E).charpoly.roots.map fun z => negMulLog z.re).sum

theorem vonNeumann_eq_sum {ρ : E →L[ℂ] E} (hρ : (ρ : E →ₗ[ℂ] E).IsSymmetric) :
    vonNeumann ρ = ∑ i, negMulLog (hρ.eigenvalues rfl i) := by
  rw [vonNeumann, hρ.roots_charpoly_eq_eigenvalues rfl, Multiset.map_map]
  simp [Function.comp_def, Finset.sum]

/-- The entropy only depends on the characteristic polynomial, so it is invariant under
conjugation. -/
theorem vonNeumann_conj (e : E ≃ₗ[ℂ] E) {ρ σ : E →L[ℂ] E}
    (h : (σ : E →ₗ[ℂ] E) = e.conj ρ) : vonNeumann σ = vonNeumann ρ := by
  rw [vonNeumann, vonNeumann, h, LinearEquiv.charpoly_conj]

/-- **Corollary 1** (Born rule is entropy), entropy formula: the equal mixture of two pure states
with transition probability `p` has entropy
`-(1 + √p)/2 log ((1 + √p)/2) - (1 - √p)/2 log ((1 - √p)/2)`. -/
theorem vonNeumann_mix_proj {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) :
    vonNeumann (mix (proj ψ) (proj ϕ)) = mixEntropy (born ψ ϕ) := by
  have hD := (isDensity_proj hψ).mix (isDensity_proj hϕ)
  set ρ := mix (proj ψ) (proj ϕ) with hρ
  have hsym := hD.isPositive.isSymmetric
  set μ := hsym.eigenvalues rfl
  set e := hsym.eigenvectorBasis rfl
  have he : ∀ i, ρ (e i) = (μ i : ℂ) • e i := hsym.apply_eigenvectorBasis rfl
  have hee : ∀ i, ⟪e i, e i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, e.norm_eq_one]; simp
  set q := ‖⟪ψ, ϕ⟫_ℂ‖ ^ 2 with hq
  have hqC : (q : ℂ) = ⟪ψ, ϕ⟫_ℂ * ⟪ϕ, ψ⟫_ℂ := by
    rw [hq, ← inner_conj_symm ϕ ψ, RCLike.mul_conj]; push_cast; rfl
  have hq0 : 0 ≤ q := by positivity
  -- the trace of `ρ` and of `ρ²`
  have h1 : ∑ i, μ i = 1 := hD.sum_eigenvalues
  have h2 : ∑ i, μ i ^ 2 = (1 + q) / 2 := by
    have ht1 := LinearMap.trace_eq_sum_inner ((ρ * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E) e
    have ht2 : LinearMap.trace ℂ E ((ρ * ρ : E →L[ℂ] E) : E →ₗ[ℂ] E) = (1 + q) / 2 := by
      have hsq : ρ * ρ = _ := mix_proj_sq ψ ϕ hψ hϕ
      rw [hsq]
      simp only [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
        map_add, map_smul, trace_rankOne, smul_eq_mul]
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hψ, hϕ, hqC]
      push_cast
      ring
    rw [ht2] at ht1
    simp only [ContinuousLinearMap.coe_coe, mul_apply_eq_comp, he, map_smul, inner_smul_right,
      hee, mul_one] at ht1
    have : ((∑ i, μ i ^ 2 : ℝ) : ℂ) = (1 + q) / 2 := by
      push_cast
      rw [ht1]
      exact Finset.sum_congr rfl fun i _ => by ring
    exact_mod_cast this
  -- every eigenvalue is a root of `μ (μ - a) (μ - b)`
  set a := (1 + √q) / 2
  set b := (1 - √q) / 2
  have hs : √q ^ 2 = q := Real.sq_sqrt hq0
  have hroot : ∀ i, μ i = 0 ∨ μ i = a ∨ μ i = b := by
    intro i
    have h := congrArg (fun v => ⟪e i, v⟫_ℂ) (mix_proj_cubic hψ hϕ (e i))
    simp only [← hρ, he, map_smul, inner_sub_right, inner_smul_right, hee, ← hqC] at h
    have h' : μ i ^ 3 = μ i ^ 2 - (1 - q) / 4 * μ i := by
      have : ((μ i ^ 3 : ℝ) : ℂ) = ((μ i ^ 2 - (1 - q) / 4 * μ i : ℝ) : ℂ) := by
        push_cast; linear_combination h
      exact_mod_cast this
    have : μ i * ((μ i - a) * (μ i - b)) = 0 := by
      simp only [a, b]; linear_combination h' - (μ i / 4) * hs
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  -- interpolate `-μ log μ` on the spectrum
  obtain ⟨α, β, ha, hb⟩ := exists_negMulLog_eq a b
  have hμ : ∀ i, negMulLog (μ i) = α * μ i + β * μ i ^ 2 := by
    intro i
    rcases hroot i with h | h | h <;> rw [h]
    · simp
    · exact ha
    · exact hb
  rw [vonNeumann_eq_sum hsym, born_of_norm hψ hϕ, mixEntropy_eq, ← hq]
  change ∑ i, negMulLog (μ i) = _
  simp only [hμ, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
  change _ = negMulLog a + negMulLog b
  rw [ha, hb]
  simp only [a, b]
  linear_combination (-β / 2) * hs

/-- **Corollary 1** (Born rule is entropy): the transition probability of two pure states is
determined by the entropy of their equal mixture, and vice versa. -/
theorem born_eq_iff {ψ ϕ : E} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    born ψ ϕ = p ↔ vonNeumann (mix (proj ψ) (proj ϕ)) = mixEntropy p := by
  rw [vonNeumann_mix_proj hψ hϕ]
  exact (mixEntropy_strictAntiOn.injOn.eq_iff (born_mem_Icc hψ hϕ) hp).symm

theorem vonNeumann_proj {ψ : E} (hψ : ‖ψ‖ = 1) : vonNeumann (proj ψ) = 0 := by
  have h : proj ψ = mix (proj ψ) (proj ψ) := by
    rw [mix, ← add_smul]
    norm_num
  rw [h, vonNeumann_mix_proj hψ hψ, born_of_norm hψ hψ, inner_self_eq_norm_sq_to_K, hψ]
  simp [mixEntropy]

/-- A density operator with zero entropy is pure. -/
theorem exists_eq_proj_of_vonNeumann_eq_zero {ρ : E →L[ℂ] E} (hρ : IsDensity ρ)
    (h : vonNeumann ρ = 0) : ∃ ψ : E, ‖ψ‖ = 1 ∧ ρ = proj ψ := by
  have hsym := hρ.isPositive.isSymmetric
  set μ := hsym.eigenvalues rfl
  set e := hsym.eigenvectorBasis rfl
  have h0 : ∀ i, 0 ≤ μ i := hρ.isPositive.nonneg_eigenvalues rfl
  have h1 : ∑ i, μ i = 1 := hρ.sum_eigenvalues
  have hle : ∀ i, μ i ≤ 1 := fun i =>
    h1 ▸ Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  rw [vonNeumann_eq_sum hsym] at h
  have hz : ∀ i, negMulLog (μ i) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => negMulLog_nonneg (h0 j) (hle j)).mp h i
      (Finset.mem_univ i)
  have h01 : ∀ i, μ i = 0 ∨ μ i = 1 := by
    intro i
    have := hz i
    simp only [negMulLog, neg_eq_zero, mul_eq_zero] at this
    rcases this with h | h
    · exact Or.inl h
    rcases Real.log_eq_zero.mp h with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · linarith [h0 i]
  obtain ⟨i, hi⟩ : ∃ i, μ i = 1 := by
    by_contra hne
    push Not at hne
    have : ∑ j, μ j = 0 := Finset.sum_eq_zero fun j _ => (h01 j).resolve_right (hne j)
    linarith
  have hj : ∀ j, j ≠ i → μ j = 0 := by
    intro j hji
    refine (h01 j).resolve_right fun hj1 => ?_
    have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j})
      (fun k _ _ => h0 k)
    rw [Finset.sum_pair (Ne.symm hji), hi, hj1, h1] at this
    linarith
  refine ⟨e i, e.norm_eq_one i, ?_⟩
  ext x
  conv_lhs => rw [← e.sum_repr (ρ x)]
  have hx : ∀ j, e.repr (ρ x) j = μ j * e.repr x j :=
    hsym.eigenvectorBasis_apply_self_apply rfl x
  simp only [hx]
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [hj j hji]) (by simp), hi]
  simp [e.repr_apply_apply]

/-- **Theorem 2** (⇐), Step 1: a density operator is pure iff its entropy is zero. -/
theorem vonNeumann_eq_zero_iff {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) :
    vonNeumann ρ = 0 ↔ ∃ ψ : E, ‖ψ‖ = 1 ∧ ρ = proj ψ :=
  ⟨exists_eq_proj_of_vonNeumann_eq_zero hρ, fun ⟨_, hψ, h⟩ => h ▸ vonNeumann_proj hψ⟩

/-- **Theorem 2** (⇐), Steps 1 and 2 up to Wigner's theorem: a map on density operators that
preserves entropy and equal mixtures sends pure states to pure states and preserves their
transition probabilities. -/
theorem pure_and_born_of_preserves (Φ : (E →L[ℂ] E) → E →L[ℂ] E)
    (hD : ∀ ρ, IsDensity ρ → IsDensity (Φ ρ))
    (hS : ∀ ρ, IsDensity ρ → vonNeumann (Φ ρ) = vonNeumann ρ)
    (hmix : ∀ ρ σ, IsDensity ρ → IsDensity σ → Φ (mix ρ σ) = mix (Φ ρ) (Φ σ)) :
    (∀ ψ : E, ‖ψ‖ = 1 → ∃ ψ' : E, ‖ψ'‖ = 1 ∧ Φ (proj ψ) = proj ψ') ∧
    ∀ ψ ϕ ψ' ϕ' : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 → ‖ψ'‖ = 1 → ‖ϕ'‖ = 1 →
      Φ (proj ψ) = proj ψ' → Φ (proj ϕ) = proj ϕ' → born ψ' ϕ' = born ψ ϕ := by
  refine ⟨fun ψ hψ => (vonNeumann_eq_zero_iff (hD _ (isDensity_proj hψ))).mp ?_, ?_⟩
  · rw [hS _ (isDensity_proj hψ), vonNeumann_proj hψ]
  · intro ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂
    refine (born_eq_iff hψ' hϕ' (born_mem_Icc hψ hϕ)).mpr ?_
    rw [← h₁, ← h₂, ← hmix _ _ (isDensity_proj hψ) (isDensity_proj hϕ),
      hS _ ((isDensity_proj hψ).mix (isDensity_proj hϕ)), vonNeumann_mix_proj hψ hϕ]

end Entropy

section Evolution

variable [CompleteSpace E]

/-- The adjoint of the Schrödinger generator `(iħ)⁻¹ H` is its negative. -/
lemma star_inv_I_mul (ħ : ℝ) : star ((Complex.I * ħ)⁻¹) = -(Complex.I * ħ)⁻¹ := by
  rw [star_inv₀, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_mul,
    inv_neg]

/-- A skew-adjoint `A` is `(iħ)⁻¹ H` for a self-adjoint `H`. -/
theorem exists_hamiltonian_of_star_eq_neg {A : E →L[ℂ] E} (hA : star A = -A) {ħ : ℝ}
    (hħ : ħ ≠ 0) : ∃ H : E →L[ℂ] E, IsSelfAdjoint H ∧ A = (Complex.I * ħ)⁻¹ • H := by
  refine ⟨(Complex.I * ħ) • A, ?_, ?_⟩
  · have hs : star (Complex.I * ħ) = -(Complex.I * ħ) := by
      rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_mul]
    rw [IsSelfAdjoint, star_smul, hs, hA, neg_smul_neg]
  · rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hħ)),
      one_smul]

/-- **Theorem 2** (⇐), Step 3: a differentiable family of unitaries with `U(t₀) = 1` has
derivative `(iħ)⁻¹ H` at `t₀` for a self-adjoint `H`, which is the Schrödinger equation at
`t₀`. -/
theorem exists_hamiltonian {U : ℝ → E →L[ℂ] E} {A : E →L[ℂ] E} {t₀ : ℝ}
    (hU : ∀ t, U t ∈ unitary (E →L[ℂ] E)) (h₀ : U t₀ = 1) (hA : HasDerivAt U A t₀) {ħ : ℝ}
    (hħ : ħ ≠ 0) : ∃ H : E →L[ℂ] E, IsSelfAdjoint H ∧ A = (Complex.I * ħ)⁻¹ • H :=
  exists_hamiltonian_of_star_eq_neg (star_eq_neg_of_hasDerivAt_of_mem_unitary hU h₀ hA) hħ

/-- **Theorem 2** (⇒): a propagator solving the Schrödinger equation
`d/dt U(t) = (iħ)⁻¹ H(t) U(t)` with `U(t₀) = 1` and self-adjoint `H(t)` is an isometry. -/
theorem star_mul_self_of_schrodinger {ħ : ℝ} {H U : ℝ → E →L[ℂ] E} {t₀ : ℝ}
    (hH : ∀ t, IsSelfAdjoint (H t))
    (hU : ∀ t, HasDerivAt U ((Complex.I * ħ)⁻¹ • (H t * U t)) t) (h₀ : U t₀ = 1) (t : ℝ) :
    star (U t) * U t = 1 := by
  have hX : ∀ t, star ((Complex.I * ħ)⁻¹ • H t) = -((Complex.I * ħ)⁻¹ • H t) := fun t => by
    rw [star_smul, (hH t).star_eq, star_inv_I_mul, neg_smul]
  have := star_mul_self_eq_of_hasDerivAt (X := fun t => (Complex.I * ħ)⁻¹ • H t) hX
    (fun t => by rw [smul_mul_assoc]; exact hU t) t₀ t
  rwa [h₀, star_one, one_mul] at this

/-- **Theorem 2** (⇒), existence: for a time-independent Hamiltonian the propagator
`U(t) = exp (t (iħ)⁻¹ H)` solves the Schrödinger equation with `U(0) = 1`. -/
theorem hasDerivAt_exp_schrodinger (ħ : ℝ) (H : E →L[ℂ] E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (Complex.I * ħ)⁻¹ • H))
      ((Complex.I * ħ)⁻¹ • (H * NormedSpace.exp (t • (Complex.I * ħ)⁻¹ • H))) t := by
  rw [← smul_mul_assoc]
  exact hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := E →L[ℂ] E) ((Complex.I * ħ)⁻¹ • H) t

variable [FiniteDimensional ℂ E]

/-- Unitary conjugation preserves eigenvalues, hence the entropy. -/
theorem vonNeumann_unitary_conj {U : E →L[ℂ] E} (hU : U ∈ unitary (E →L[ℂ] E))
    (ρ : E →L[ℂ] E) : vonNeumann (U * ρ * star U) = vonNeumann ρ := by
  refine vonNeumann_conj (Unitary.linearIsometryEquiv ⟨U, hU⟩).toLinearEquiv ?_
  ext x
  rfl

/-- **Theorem 2** (⇒), DR-INFO: along a Schrödinger evolution the future ensemble
`ρF = U ρ U†` is a density operator, the reconstructed past `U† ρF U` is the initial `ρ`, and
all three have the same entropy. The map `ρ ↦ U ρ U†` is linear, so mixtures are preserved. -/
theorem schrodinger_conserves_entropy {ħ : ℝ} {H U : ℝ → E →L[ℂ] E} {t₀ : ℝ}
    (hH : ∀ t, IsSelfAdjoint (H t))
    (hU : ∀ t, HasDerivAt U ((Complex.I * ħ)⁻¹ • (H t * U t)) t) (h₀ : U t₀ = 1)
    {ρ : E →L[ℂ] E} (hρ : IsDensity ρ) (t : ℝ) :
    IsDensity (U t * ρ * star (U t)) ∧ star (U t) * (U t * ρ * star (U t)) * U t = ρ ∧
      vonNeumann (U t * ρ * star (U t)) = vonNeumann ρ := by
  have hu := ContinuousLinearMap.mem_unitary_of_star_mul_self
    (star_mul_self_of_schrodinger hH hU h₀ t)
  refine ⟨hρ.unitary_conj hu, ?_, vonNeumann_unitary_conj hu ρ⟩
  have h1 := (Unitary.mem_iff.mp hu).1
  calc star (U t) * (U t * ρ * star (U t)) * U t
      = (star (U t) * U t) * ρ * (star (U t) * U t) := by noncomm_ring
    _ = ρ := by rw [h1, one_mul, mul_one]

/-- **Theorem 2** (⇐), DR-INFO + EVDIFF ⇒ DR-SCEQ: let `Φ t` map density operators to density
operators, preserve the entropy and equal mixtures, be the identity at `t₀`, and be differentiable
at `t₀` on each density operator. Then near `t₀`, `Φ t` acts on pure states through unitaries
`U t` with `U t₀ = 1`, and `U` solves the Schrödinger equation `U' = (iħ)⁻¹ H U` at `t₀` for a
self-adjoint `H`. -/
theorem schrodinger_of_preserves {Φ : ℝ → (E →L[ℂ] E) → E →L[ℂ] E} {t₀ ħ : ℝ}
    (hD : ∀ t ρ, IsDensity ρ → IsDensity (Φ t ρ))
    (hS : ∀ t ρ, IsDensity ρ → vonNeumann (Φ t ρ) = vonNeumann ρ)
    (hmix : ∀ t ρ σ, IsDensity ρ → IsDensity σ → Φ t (mix ρ σ) = mix (Φ t ρ) (Φ t σ))
    (h₀ : ∀ ρ, IsDensity ρ → Φ t₀ ρ = ρ)
    (hdiff : ∀ ρ, IsDensity ρ → DifferentiableAt ℝ (fun t => Φ t ρ) t₀) (hħ : ħ ≠ 0) :
    ∃ (U : ℝ → E →L[ℂ] E) (H : E →L[ℂ] E), IsSelfAdjoint H ∧
      (∀ t, U t ∈ unitary (E →L[ℂ] E)) ∧ U t₀ = 1 ∧
      (∀ᶠ t in 𝓝 t₀, ∀ ψ : E, ‖ψ‖ = 1 → Φ t (proj ψ) = proj (U t ψ)) ∧
      HasDerivAt U ((Complex.I * ħ)⁻¹ • (H * U t₀)) t₀ := by
  have hP t := pure_and_born_of_preserves (Φ t) (hD t) (hS t) (hmix t)
  have htr : ∀ t, ∀ ψ ϕ : E, ‖ψ‖ = 1 → ‖ϕ‖ = 1 →
      LinearMap.trace ℂ E ((Φ t (proj ψ) * Φ t (proj ϕ) : E →L[ℂ] E) : E →ₗ[ℂ] E) =
        LinearMap.trace ℂ E ((proj ψ * proj ϕ : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    intro t ψ ϕ hψ hϕ
    obtain ⟨ψ', hψ', h₁⟩ := (hP t).1 ψ hψ
    obtain ⟨ϕ', hϕ', h₂⟩ := (hP t).1 ϕ hϕ
    have h := (hP t).2 ψ ϕ ψ' ϕ' hψ hϕ hψ' hϕ' h₁ h₂
    rw [born_of_norm hψ' hϕ', born_of_norm hψ hϕ] at h
    rw [h₁, h₂, QuantumMechanics.Wigner.trace_rankOne_mul_rankOne,
      QuantumMechanics.Wigner.trace_rankOne_mul_rankOne, h]
  obtain ⟨U, hU, hU₀, hΦ, hUd⟩ := QuantumMechanics.Wigner.exists_unitary_differentiableAt
    (fun t => (hP t).1) htr (fun ψ hψ => h₀ _ (isDensity_proj hψ))
    (fun ψ hψ => hdiff _ (isDensity_proj hψ))
  obtain ⟨H, hH, hA⟩ := exists_hamiltonian hU hU₀ hUd.hasDerivAt hħ
  refine ⟨U, H, hH, hU, hU₀, hΦ, ?_⟩
  rw [hU₀, mul_one, ← hA]
  exact hUd.hasDerivAt

end Evolution

end UnitaryEntropy
