/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import ForMathlib.Analysis.Convex.Combination
public import ForMathlib.Analysis.InnerProductSpace.l2Space
public import ForMathlib.Geometry.Symplectic.Manifold.FubiniStudy
public import ForMathlib.MeasureTheory.Constructions.HaarToSphere
public import ForPhyslib.ProbabilisticTheory.HilbertSpace.TraceClass.CanonicalExpansion
public import ForPhyslib.QuantumMechanics.DensityOperator
public import ForPhyslib.QuantumMechanics.Qubit.HamiltonianIsotopy
public import ForPhyslib.QuantumMechanics.Qubit.Precession
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Integral
import ForPhyslib.QuantumMechanics.Kadison
import TauCeti.Geometry.Symplectic.Manifold.Descent

/-!
# Quantum pure states are not enough

## i. Overview

Formalization of the technical brief *Quantum pure states are not enough* (G. Carcassi,
Assumptions of Physics). The brief compares the classical condition CST (states form a symplectic
manifold with Liouville measure `μ`, ensembles are the probability measures absolutely continuous
with respect to `μ`) with the quantum conditions QP-RAY (states are the rays of a complex vector
space), QE-DENS (ensembles are the density operators) and BR-BORN (the Born rule).

**Theorem 3.** CST and QE-DENS are inconsistent. The ensembles of both conditions are convex
spaces, and an identification of the two must preserve mixtures. Under CST the ensemble space is
infinite-dimensional: normalizing `μ` on `N` disjoint sets of positive finite measure gives `N`
ensembles none of which is a mixture of the others. In finite dimension (which CST forces, by
Theorem 1) the density operators lie in the finite-dimensional real vector space of operators.
A map that preserves mixtures of two ensembles preserves all finite mixtures, so an injective one
would carry `dim + 2` independent ensembles to `dim + 2` independent points of a space of
dimension `dim`, which is impossible. The argument needs neither positivity nor trace of the
density operators, only the finite dimension of the space that contains them.

**Theorem 5.** Let `H` be a separable complex Hilbert space of any dimension. The pure states are
the extreme points of the density operators, as the proof of Theorem 5 starts from. A probability
measure `μ` on the pure states (with the Borel σ-algebra of the operator norm) represents the
density operator `r(μ) = ∫ |ψ⟩⟨ψ| dμ`, its barycenter. It is positive because the positive
operators form a closed convex cone, and has trace one by Parseval and monotone convergence over a
countable Hilbert basis. The map `r` is affine and onto, by the canonical expansion
`ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|`, so the density operators are the probability measures on the pure states
up to `r(μ₁) = r(μ₂)`. No Choquet theory is needed. The quotient is not trivial: in dimension at
least two, `½ δ_{e₀} + ½ δ_{e₁}` and `½ δ_{e₊} + ½ δ_{e₋}` with `e± = (e₀ ± e₁)/√2` have the same
barycenter but are told apart by the probability of the state `e₀`.

**Remark after Example 2.** CST makes distinct states mutually exclusive, the Born rule does not:
`e₀` and `e₊` are distinct rays with Born probability `½`.

**Example 2** (the classical qubit). The pure states `P(ℂ²)` form a two-sphere, through the Bloch
vector. In the coordinates `z = x₂` and `θ = θ_xy` the area is `dz dθ`, so the height of a point
is uniformly distributed (Archimedes' hat-box theorem). The quantum evolutions, the actions of
unitaries on rays, are exactly the rotations of the Bloch sphere, and every Hamiltonian
`c + ½ n · σ` makes the Bloch vector precess about `n`, `a' = n × a`. Complex conjugation of the
Riemann sphere `OnePoint ℂ ≅ P(ℂ²)` preserves the area density of the Fubini–Study form but
reverses the form, so it is area-preserving and not Hamiltonian: Hamiltonian evolution preserves
the area form, not only the area. With the area form the claim holds for evolutions: a vector field
preserves the Fubini–Study form exactly when it is Hamiltonian, and a jointly smooth time-dependent
flow preserves it at all times exactly when every velocity field is Hamiltonian. The same holds
for an evolution given as a smooth isotopy from the identity, through its generating field
`X_t = φ̇_t ∘ φ_t⁻¹`. The obstruction
would be a class in `H¹_dR`, which vanishes because the sphere is simply connected. That every
single orientation-preserving, area-preserving diffeomorphism is the end of a Hamiltonian evolution
needs Smale's theorem `Diff⁺(S²) ≃ SO(3)` and is not formalized.

**Theorem 1** (QP-RAY and CST are consistent if and only if `1 ≤ dim V < ∞`) is formalized in
part. The "if" holds for every complex inner product space `V` of finite dimension `n + 1`.
`ℂPⁿ` has exactly one symplectic form that pulls back along the Hopf map `S²ⁿ⁺¹ → ℂPⁿ` to the
restriction of the standard form `Im ⟪u, w⟫` of `ℂⁿ⁺¹`, the Fubini–Study form, obtained by
symplectic descent. An orthonormal basis of `V` identifies `P(V)` with `ℂPⁿ` as topological
spaces; a change of basis acts on `ℂPⁿ` through a unitary map, which is smooth and preserves the
Fubini–Study form, so the symplectic structure carried over to `P(V)` does not depend on the
basis. Not formalized are the Liouville measure of the form and the "only if". The edges are
checked. `P(V)` is empty for `V = 0`, a single point for `dim V = 1`, and has two points
exactly when `2 ≤ dim V`. If a point counts as a `0`-dimensional symplectic manifold, Theorem 3
fails for `dim H = 1`: the CST ensembles of a point and the density operators of `ℂ` are both a
single point. And as sets `P(ℓ²)` and `P(ℂ²)` are in bijection, so the "only if" of Theorem 1
needs the topology of `P(V)`, not only its points.

## ii. Key results

- `PureStatesNotEnough.Convex.classicalEnsembles`: the ensembles of CST form a convex set.
- `PureStatesNotEnough.not_injOn_of_map_add`: no mixture-preserving map from the ensembles of CST
  into a finite-dimensional real vector space is injective.
- `PureStatesNotEnough.hasManyDisjointSets_restrict`: a Darboux chart has enough disjoint sets.
- `PureStatesNotEnough.cst_qeDens_inconsistent`: Theorem 3.
- `PureStatesNotEnough.existsUnique_isSymplectic_projectivization`: Theorem 1, "if", for
  `V = ℂⁿ⁺¹`; `ℂPⁿ` with the Fubini–Study form is a symplectic manifold.
- `PureStatesNotEnough.basisHomeomorph`, `PureStatesNotEnough.contMDiff_basisHomeomorph_symm_trans`,
  `PureStatesNotEnough.mpullback_basisHomeomorph_symm_trans`: Theorem 1, "if", for every
  finite-dimensional `V`; the structure carried over along an orthonormal basis does not depend
  on the basis.
- `PureStatesNotEnough.subsingleton_projectivization`: for `dim V = 1`, `P(V)` is one point.
- `PureStatesNotEnough.isEmpty_projectivization`,
  `PureStatesNotEnough.nonempty_projectivization_iff`,
  `PureStatesNotEnough.nontrivial_projectivization_iff`: `P(V)` is empty for `V = 0` and has two
  points exactly when `2 ≤ dim V`.
- `PureStatesNotEnough.not_hasManyDisjointSets_dirac`,
  `PureStatesNotEnough.cst_qeDens_consistent_of_finrank_one`: with `0` degrees of freedom allowed,
  Theorem 3 fails for `dim H = 1`.
- `PureStatesNotEnough.mk_projectivization`, `PureStatesNotEnough.nonempty_projectivization_equiv`:
  `P(ℓ²)` and `P(ℂ²)` have the same cardinality `𝔠`.
- `PureStatesNotEnough.born_ne_delta`: the Remark after Example 2.
- `PureStatesNotEnough.pureStates_eq_extremePoints`: the pure states are the extreme points of
  `D(H)`.
- `PureStatesNotEnough.barycenter`, `PureStatesNotEnough.barycenter_add`: the barycenter map `r`
  and its affinity.
- `PureStatesNotEnough.posTrace_barycenter`, `PureStatesNotEnough.isDensityOperator_barycenter`:
  `r(μ)` is a density operator.
- `PureStatesNotEnough.toDensity_surjective`, `PureStatesNotEnough.densityEquiv`: Theorem 5.
- `PureStatesNotEnough.exists_barycenter_eq_and_ne`: distinct preparations of one ensemble.
- `PureStatesNotEnough.nonempty_homeomorph_sphere`: `P(ℂ²)` is a two-sphere.
- `PureStatesNotEnough.toSphere_eq_dz_dtheta`: the area of the sphere is `dz dθ`.
- `PureStatesNotEnough.conjSphere_preserves_area_reverses_form`,
  `QuantumMechanics.Qubit.globalFlow_ne_conjSphere`,
  `QuantumMechanics.Qubit.timeDependentFlowOf_ne_conjSphere`,
  `QuantumMechanics.Qubit.isotopy_ne_conjSphere`: an area-preserving map that is not
  Hamiltonian, nor the end of a time-dependent Hamiltonian evolution or isotopy.
- `PureStatesNotEnough.lieDeriv_areaForm_eq_zero_iff_hamiltonian`: the vector fields that preserve
  the area form are the Hamiltonian ones.
- `PureStatesNotEnough.preserves_areaForm_iff_hamiltonian`: the time-dependent flows that preserve
  the area form are the Hamiltonian evolutions.
- `PureStatesNotEnough.isotopy_preserves_areaForm_iff_hamiltonian`: the same for evolutions given
  as isotopies.
- `PureStatesNotEnough.exists_unitaryAction_eq_iff`: the quantum evolutions of a qubit are exactly
  the rotations of the Bloch sphere.
- `PureStatesNotEnough.exists_blochVector_precession`: every Hamiltonian makes the Bloch vector
  precess.

## iii. Table of contents

- A. The classical ensemble space
- B. Theorem 3: CST and QE-DENS are inconsistent
- C. Theorem 1 and the Remark after Example 2
- D. Theorem 5: density operators as classes of measures on pure states
- E. Example 2: the classical qubit

## iv. References

- G. Carcassi, *Quantum pure states are not enough*, Assumptions of Physics technical brief.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory ProbabilisticTheory QuantumMechanics QuantumMechanics.Wigner
open ContinuousLinearMap (posTrace posTraceBasis re_inner_apply_nonneg)
open Function
open scoped InnerProductSpace NNReal ENNReal LinearAlgebra.Projectivization

namespace PureStatesNotEnough

/-! ## A. The classical ensemble space -/

section Classical

variable {X : Type*} [MeasurableSpace X]

/-- The ensemble space of CST: the probability measures absolutely continuous with respect to the
Liouville measure `μ`. -/
def classicalEnsembles (μ : Measure X) : Set (Measure X) := {ν | IsProbabilityMeasure ν ∧ ν ≪ μ}

/-- The ensembles of CST are closed under mixtures. -/
theorem Convex.classicalEnsembles (μ : Measure X) : Convex ℝ≥0 (classicalEnsembles μ) := by
  intro ν₁ h₁ ν₂ h₂ a b _ _ hab
  have := h₁.1
  have := h₂.1
  refine ⟨⟨?_⟩, (h₁.2.smul_left a).add_left (h₂.2.smul_left b)⟩
  simp only [add_apply, smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul,
    mul_one]
  rw [← ENNReal.coe_add, hab, ENNReal.coe_one]

/-- `μ` has, for every `N`, `N` disjoint measurable sets of positive finite measure. -/
def HasManyDisjointSets (μ : Measure X) : Prop :=
  ∀ N : ℕ, ∃ s : Fin N → Set X, (∀ i, MeasurableSet (s i)) ∧ Pairwise (Disjoint on s) ∧
    ∀ i, μ (s i) ≠ 0 ∧ μ (s i) ≠ ∞

/-- The Liouville measure of a Darboux chart, the Lebesgue measure on an open subset of `ℝ²ⁿ` with
`n ≥ 1`, has enough disjoint sets: the spherical shells `k δ < ‖y - x‖ < (k + 1) δ` in a ball
around `x`. -/
theorem hasManyDisjointSets_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ] {U : Set E} (hU : IsOpen U)
    (hne : U.Nonempty) : HasManyDisjointSets (μ.restrict U) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_one
  intro N
  set δ := r / N
  set s : Fin N → Set E := fun k => {y | k * δ < dist y x ∧ dist y x < (k + 1) * δ}
  have hopen : ∀ k, IsOpen (s k) := fun k =>
    (isOpen_lt continuous_const (continuous_id.dist continuous_const)).inter
      (isOpen_lt (continuous_id.dist continuous_const) continuous_const)
  have hsub : ∀ k : Fin N, s k ⊆ Metric.ball x r := fun k y hy => by
    have hN : (0 : ℝ) < N := by exact_mod_cast k.pos
    have hk : ((k : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
    have : (k + 1) * δ ≤ r := by
      calc (k + 1) * δ ≤ N * δ := by gcongr
        _ = r := by simp only [δ]; field_simp
    exact Metric.mem_ball.2 (hy.2.trans_le this)
  refine ⟨s, fun k => (hopen k).measurableSet, fun k l hkl => ?_, fun k => ?_⟩
  · refine Set.disjoint_left.2 fun y hk hl => hkl (Fin.ext ?_)
    have hδ : 0 < δ := div_pos hr (by exact_mod_cast k.pos)
    have h1 : (k : ℝ) < l + 1 := lt_of_mul_lt_mul_right (hk.1.trans hl.2) hδ.le
    have h2 : (l : ℝ) < k + 1 := lt_of_mul_lt_mul_right (hl.1.trans hk.2) hδ.le
    have h1' : (k : ℕ) < l + 1 := by exact_mod_cast h1
    have h2' : (l : ℕ) < k + 1 := by exact_mod_cast h2
    omega
  · have hδ : 0 < δ := div_pos hr (by exact_mod_cast k.pos)
    have hne : (s k).Nonempty := by
      refine ⟨x + ((k + 2⁻¹ : ℝ) * δ) • v, ?_⟩
      have hd : dist (x + ((k + 2⁻¹ : ℝ) * δ) • v) x = (k + 2⁻¹) * δ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
      simp only [s, Set.mem_ofPred_eq, hd]
      constructor <;> nlinarith
    rw [Measure.restrict_apply (hopen k).measurableSet,
      Set.inter_eq_left.2 ((hsub k).trans hball)]
    exact ⟨((hopen k).measure_pos μ hne).ne',
      ((measure_mono (hsub k)).trans_lt measure_ball_lt_top).ne⟩

end Classical

/-! ## B. Theorem 3: CST and QE-DENS are inconsistent -/

section Theorem3

variable {X : Type*} [MeasurableSpace X]

/-- The normalized restrictions of `μ` to disjoint sets: `μ[|sᵢ](sⱼ)` is `1` for `i = j` and `0`
otherwise. -/
lemma cond_apply_of_pairwise {μ : Measure X} {N : ℕ} {s : Fin N → Set X}
    (hsm : ∀ i, MeasurableSet (s i)) (hsd : Pairwise (Disjoint on s))
    (hs : ∀ i, μ (s i) ≠ 0 ∧ μ (s i) ≠ ∞) (i j : Fin N) :
    μ[s j | s i] = if i = j then 1 else 0 := by
  rw [cond_apply (hsm i)]
  split_ifs with h
  · subst h
    rw [Set.inter_self, ENNReal.inv_mul_cancel (hs i).1 (hs i).2]
  · rw [(hsd h).inter_eq, measure_empty, mul_zero]

/-- No map from the ensembles of CST into a finite-dimensional real vector space that preserves
mixtures of two ensembles is injective. -/
theorem not_injOn_of_map_add {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    {μ : Measure X} (hμ : HasManyDisjointSets μ) {F : Measure X → W}
    (hF : ∀ ν₁ ∈ classicalEnsembles μ, ∀ ν₂ ∈ classicalEnsembles μ, ∀ a b : ℝ≥0, a + b = 1 →
      F (a • ν₁ + b • ν₂) = a • F ν₁ + b • F ν₂) :
    ¬ Set.InjOn F (classicalEnsembles μ) := by
  intro hinj
  set d := Module.finrank ℝ W
  obtain ⟨s, hsm, hsd, hs⟩ := hμ (d + 2)
  set ν : Fin (d + 2) → Measure X := fun i => μ[|s i]
  have hν : ∀ i, ν i ∈ classicalEnsembles μ := fun i =>
    ⟨cond_isProbabilityMeasure_of_finite (hs i).1 (hs i).2, cond_absolutelyContinuous⟩
  -- `d + 2` points of `W` are affinely dependent: `∑ gᵢ F(νᵢ) = 0` and `∑ gᵢ = 0`, `g ≠ 0`.
  have hdep : ¬ LinearIndependent ℝ (fun i => (F (ν i), (1 : ℝ))) := fun h => by
    have := h.fintype_card_le_finrank
    rw [Module.finrank_prod, Module.finrank_self, Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, j, hj⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hg1 : ∑ i, g i • F (ν i) = 0 := by
    simpa [Prod.fst_sum] using congrArg Prod.fst hg
  have hg2 : ∑ i, g i = 0 := by
    simpa [Prod.snd_sum] using congrArg Prod.snd hg
  -- Split `g` into its positive and negative parts, both of total weight `S > 0`.
  set S := ∑ i, max (g i) 0
  have hgpm : ∀ i, max (g i) 0 - max (-g i) 0 = g i := fun i => max_zero_sub_eq_self (g i)
  have hS' : ∑ i, max (-g i) 0 = S := by
    have := Finset.sum_sub_distrib (s := Finset.univ) (fun i => max (g i) 0)
      (fun i => max (-g i) 0)
    simp only [hgpm, hg2] at this
    linarith
  have hS : 0 < S := by
    by_contra hS
    have hS0 : S = 0 := le_antisymm (not_lt.1 hS) (Finset.sum_nonneg fun i _ => le_max_right _ _)
    have hp := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => le_max_right (g i) 0).1 hS0 j
      (Finset.mem_univ _)
    have hn := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => le_max_right (-g i) 0).1
      (hS'.trans hS0) j (Finset.mem_univ _)
    exact hj (by rw [← hgpm j, hp, hn, sub_zero])
  set a : Fin (d + 2) → ℝ≥0 := fun i => (max (g i) 0 / S).toNNReal
  set b : Fin (d + 2) → ℝ≥0 := fun i => (max (-g i) 0 / S).toNNReal
  have ha : ∀ i, (a i : ℝ) = max (g i) 0 / S := fun i =>
    Real.coe_toNNReal _ (div_nonneg (le_max_right _ _) hS.le)
  have hb : ∀ i, (b i : ℝ) = max (-g i) 0 / S := fun i =>
    Real.coe_toNNReal _ (div_nonneg (le_max_right _ _) hS.le)
  have ha1 : ∑ i, a i = 1 := NNReal.eq <| by
    rw [NNReal.coe_sum, NNReal.coe_one]
    simp only [ha, ← Finset.sum_div]
    exact div_self hS.ne'
  have hb1 : ∑ i, b i = 1 := NNReal.eq <| by
    rw [NNReal.coe_sum, NNReal.coe_one]
    simp only [hb, ← Finset.sum_div, hS']
    exact div_self hS.ne'
  have hconv := Convex.classicalEnsembles μ
  have hFa := hconv.map_sum_of_map_add (fun x hx y hy a b _ _ hab => hF x hx y hy a b hab)
    (t := Finset.univ) (w := a) (z := ν) (fun _ _ => zero_le) ha1 fun i _ => hν i
  have hFb := hconv.map_sum_of_map_add (fun x hx y hy a b _ _ hab => hF x hx y hy a b hab)
    (t := Finset.univ) (w := b) (z := ν) (fun _ _ => zero_le) hb1 fun i _ => hν i
  have hab : ∑ i, a i • F (ν i) = ∑ i, b i • F (ν i) := by
    have hsub : ∀ i, (a i : ℝ) - b i = S⁻¹ * g i := fun i => by
      rw [ha, hb, ← sub_div, hgpm, div_eq_inv_mul]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    simp only [NNReal.smul_def, ← sub_smul, hsub, mul_smul, ← Finset.smul_sum, hg1, smul_zero]
  have heq := hinj (hconv.sum_mem_of_semifield (fun _ _ => zero_le) ha1 fun i _ => hν i)
    (hconv.sum_mem_of_semifield (fun _ _ => zero_le) hb1 fun i _ => hν i)
    (by rw [hFa, hFb, hab])
  -- Evaluate both mixtures on `sⱼ`.
  have hev : ∀ w : Fin (d + 2) → ℝ≥0, (∑ i, w i • ν i) (s j) = w j := fun w => by
    simp only [sum_apply, smul_apply, ENNReal.smul_def,
      smul_eq_mul, ν, cond_apply_of_pairwise hsm hsd hs, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hj' : a j = b j := by
    have := congrArg (fun m : Measure X => m (s j)) heq
    simp only [hev] at this
    exact_mod_cast this
  have := congrArg (fun x : ℝ≥0 => (x : ℝ) * S) hj'
  simp only [ha, hb, div_mul_cancel₀ _ hS.ne'] at this
  exact hj (by rw [← hgpm j, this, sub_self])

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **Theorem 3.** CST and QE-DENS are inconsistent: when the Liouville measure has enough
disjoint sets (`hasManyDisjointSets_restrict`), no injective map from the ensembles of CST to the
density operators of a finite-dimensional Hilbert space preserves mixtures. -/
theorem cst_qeDens_inconsistent {μ : Measure X} (hμ : HasManyDisjointSets μ) :
    ¬ ∃ F : Measure X → (H →L[ℂ] H), Set.MapsTo F (classicalEnsembles μ) {ρ | IsDensity ρ} ∧
      Set.InjOn F (classicalEnsembles μ) ∧
      ∀ ν₁ ∈ classicalEnsembles μ, ∀ ν₂ ∈ classicalEnsembles μ, ∀ a b : ℝ≥0, a + b = 1 →
        F (a • ν₁ + b • ν₂) = ((a : ℝ) : ℂ) • F ν₁ + ((b : ℝ) : ℂ) • F ν₂ := by
  rintro ⟨F, -, hinj, hF⟩
  refine not_injOn_of_map_add hμ (fun ν₁ h₁ ν₂ h₂ a b hab => ?_) hinj
  rw [hF ν₁ h₁ ν₂ h₂ a b hab, Complex.coe_smul, Complex.coe_smul, NNReal.smul_def,
    NNReal.smul_def]

end Theorem3

/-! ## C. Theorem 1 and the Remark after Example 2 -/

section Theorem1

/-- For `dim V = 1` the projective space `P(V)` is a single point, a manifold of dimension `0`;
the proof of Theorem 1 needs `2 ≤ dim P(V)`. -/
theorem subsingleton_projectivization {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : Module.finrank ℂ V = 1) : Subsingleton (ℙ ℂ V) := by
  refine ⟨fun p q => ?_⟩
  induction p using Projectivization.ind with | h v hv => ?_
  induction q using Projectivization.ind with | h w hw => ?_
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_ne_zero' w hw).1 h v
  exact (Projectivization.mk_eq_mk_iff' ℂ v w hv hw).2 ⟨c, hc⟩

/-- For `V = 0` the projective space `P(V)` is empty. -/
theorem isEmpty_projectivization {V : Type*} [AddCommGroup V] [Module ℂ V] [Subsingleton V] :
    IsEmpty (ℙ ℂ V) :=
  ⟨fun p => p.rep_ne_zero (Subsingleton.elim _ _)⟩

/-- `P(V)` is nonempty if and only if `V ≠ 0`. -/
theorem nonempty_projectivization_iff {V : Type*} [AddCommGroup V] [Module ℂ V] :
    Nonempty (ℙ ℂ V) ↔ Nontrivial V := by
  refine ⟨fun ⟨p⟩ => nontrivial_of_ne _ _ p.rep_ne_zero, fun _ => ?_⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨Projectivization.mk ℂ v hv⟩

/-- In finite dimension `P(V)` has two distinct points if and only if `2 ≤ dim V`. So `P(V)` is a
manifold of positive dimension exactly when `2 ≤ dim V`. -/
theorem nontrivial_projectivization_iff {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] : Nontrivial (ℙ ℂ V) ↔ 2 ≤ Module.finrank ℂ V := by
  constructor
  · intro h
    by_contra h2
    obtain ⟨p, -⟩ := exists_pair_ne (ℙ ℂ V)
    rcases (by omega : Module.finrank ℂ V = 0 ∨ Module.finrank ℂ V = 1) with hd | hd
    · have : Subsingleton V := Module.finrank_zero_iff.mp hd
      exact isEmpty_projectivization.elim p
    · exact not_subsingleton _ (subsingleton_projectivization hd)
  · intro h
    let b := Module.finBasis ℂ V
    let i : Fin (Module.finrank ℂ V) := ⟨0, by omega⟩
    let j : Fin (Module.finrank ℂ V) := ⟨1, by omega⟩
    refine ⟨⟨Projectivization.mk ℂ (b i) (b.ne_zero i),
      Projectivization.mk ℂ (b j) (b.ne_zero j), ?_⟩⟩
    rw [Ne, Projectivization.mk_eq_mk_iff' ℂ _ _ (b.ne_zero i) (b.ne_zero j)]
    rintro ⟨a, ha⟩
    have := congrArg (fun v => b.repr v i) ha
    simp [b.repr_self, i, j] at this

/-- For `n = 0` degrees of freedom the state space is one point and its Liouville measure is `δ`,
which does not have enough disjoint sets. So the proof of Theorem 3 needs `n ≥ 1`. -/
theorem not_hasManyDisjointSets_dirac : ¬ HasManyDisjointSets (Measure.dirac ()) := by
  intro h
  obtain ⟨s, hs, hd, hpos⟩ := h 2
  have hmem : ∀ i, () ∈ s i := fun i => by
    by_contra hni
    exact (hpos i).1 (by simp [Measure.dirac_apply' _ (hs i), hni])
  exact Set.disjoint_left.mp (hd (show (0 : Fin 2) ≠ 1 by decide)) (hmem 0) (hmem 1)

/-- If `0`-dimensional symplectic manifolds count, Theorem 3 fails in dimension one. For
`dim H = 1` the state space is one point with Liouville measure `δ`; the constant map onto the
identity, the only density operator, is injective on the ensembles of CST and preserves mixtures.
-/
theorem cst_qeDens_consistent_of_finrank_one {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (hH : Module.finrank ℂ H = 1) :
    ∃ F : Measure Unit → (H →L[ℂ] H),
      Set.MapsTo F (classicalEnsembles (Measure.dirac ())) {ρ | IsDensity ρ} ∧
      Set.InjOn F (classicalEnsembles (Measure.dirac ())) ∧
      ∀ ν₁ ∈ classicalEnsembles (Measure.dirac ()), ∀ ν₂ ∈ classicalEnsembles (Measure.dirac ()),
        ∀ a b : ℝ≥0, a + b = 1 →
          F (a • ν₁ + b • ν₂) = ((a : ℝ) : ℂ) • F ν₁ + ((b : ℝ) : ℂ) • F ν₂ := by
  refine ⟨fun _ => 1, fun _ _ => ⟨?_, ?_⟩, fun ν₁ h₁ ν₂ h₂ _ => ?_, fun _ _ _ _ a b hab => ?_⟩
  · exact ContinuousLinearMap.isPositive_one.toLinearMap
  · simp [hH]
  · have := h₁.1
    have := h₂.1
    ext s -
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · simp [Subsingleton.eq_univ_of_nonempty hs]
  · rw [← add_smul, ← Complex.ofReal_add, ← NNReal.coe_add, hab]
    simp

/-- If `V` has two linearly independent vectors and at most `𝔠` elements, `P(V)` has exactly `𝔠`
points. -/
theorem mk_projectivization {V : Type} [AddCommGroup V] [Module ℂ V] {v w : V}
    (hvw : LinearIndependent ℂ ![v, w]) (hV : Cardinal.mk V ≤ Cardinal.continuum) :
    Cardinal.mk (ℙ ℂ V) = Cardinal.continuum := by
  have hpair := LinearIndependent.pair_iff.mp hvw
  have hne : ∀ z : ℂ, v + z • w ≠ 0 := fun z h => one_ne_zero (hpair 1 z (by simpa using h)).1
  refine le_antisymm ((Cardinal.mk_le_of_injective (f := Projectivization.rep) ?_).trans hV) ?_
  · intro p q h
    rw [← p.mk_rep, ← q.mk_rep]
    simp only [h]
  · rw [← Cardinal.mk_complex]
    refine Cardinal.mk_le_of_injective (f := fun z : ℂ => Projectivization.mk ℂ _ (hne z)) ?_
    intro z z' h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ (hne z) (hne z')).1 h
    have h0 : (a - 1) • v + (a * z' - z) • w = 0 := by
      rw [← sub_eq_zero.mpr ha]
      module
    obtain ⟨h1, h2⟩ := hpair _ _ h0
    rw [sub_eq_zero.mp h1, one_mul, sub_eq_zero] at h2
    exact h2.symm

lemma mk_fun_le_continuum (ι : Type) [Countable ι] :
    Cardinal.mk (ι → ℂ) ≤ Cardinal.continuum := by
  rw [← Cardinal.power_def, Cardinal.mk_complex]
  exact (Cardinal.power_le_power_left Cardinal.continuum_ne_zero
    (Cardinal.mk_le_aleph0 (α := ι))).trans_eq Cardinal.continuum_power_aleph0

/-- As sets, the projective space of `ℓ²` and the Riemann sphere `P(ℂ²)` are in bijection. If
"represented by" in CST and QP-RAY meant only a bijection, the symplectic structure of the sphere
could be carried over to `P(ℓ²)`, and the "only if" of Theorem 1 would fail. It needs the
topology of `P(V)`. -/
theorem nonempty_projectivization_equiv :
    Nonempty (ℙ ℂ (lp (fun _ : ℕ => ℂ) 2) ≃ ℙ ℂ (Fin 2 → ℂ)) := by
  let e : ℕ → lp (fun _ : ℕ => ℂ) 2 := fun i => lp.single 2 i 1
  have hl : LinearIndependent ℂ ![e 0, e 1] := by
    refine LinearIndependent.pair_iff.mpr fun s t h => ⟨?_, ?_⟩
    · have h0 : s * e 0 0 + t * e 1 0 = 0 := congrArg (fun f : lp (fun _ : ℕ => ℂ) 2 => f 0) h
      simpa [e, lp.single_apply] using h0
    · have h1 : s * e 0 1 + t * e 1 1 = 0 := congrArg (fun f : lp (fun _ : ℕ => ℂ) 2 => f 1) h
      simpa [e, lp.single_apply] using h1
  have hc : LinearIndependent ℂ ![(Pi.single 0 1 : Fin 2 → ℂ), Pi.single 1 1] := by
    refine LinearIndependent.pair_iff.mpr fun s t h => ⟨?_, ?_⟩
    · simpa using congrFun h 0
    · simpa using congrFun h 1
  have hlc : Cardinal.mk (lp (fun _ : ℕ => ℂ) 2) ≤ Cardinal.continuum :=
    (Cardinal.mk_le_of_injective (f := fun f : lp (fun _ : ℕ => ℂ) 2 => (f : ℕ → ℂ))
      fun _ _ => lp.ext).trans (mk_fun_le_continuum ℕ)
  exact Cardinal.eq.mp
    (by rw [mk_projectivization hl hlc, mk_projectivization hc (mk_fun_le_continuum (Fin 2))])

open scoped Manifold ContDiff in
/-- **Theorem 1, "if", for `V = ℂⁿ⁺¹`.** For every `n` the projective space
`P(ℂⁿ⁺¹) = ℂPⁿ`, a real manifold of dimension `2 n`, has exactly one symplectic form whose pullback
along the Hopf map `S²ⁿ⁺¹ → ℂPⁿ` is the restriction of the standard form `Im ⟪u, w⟫` of `ℂⁿ⁺¹`:
the Fubini–Study form. For `n = 0` it lives on a point. -/
theorem existsUnique_isSymplectic_projectivization (n : ℕ) :
    ∃! η : TauCeti.SmoothTwoForm 𝓘(ℝ, Fin n → ℂ) (ℙ ℂ (Fin (n + 1) → ℂ)),
      η.IsSymplectic ∧ TauCeti.SmoothForm.mpullback (Projectivization.hopfMap n)
        (Projectivization.contMDiff_hopfMap ∞) η = Projectivization.sphereForm n :=
  TauCeti.SmoothTwoForm.existsUnique_isSymplectic_mpullback_eq
    (Projectivization.isSubmersion_hopfMap (by simp)) Projectivization.hopfMap_surjective
    Projectivization.isClosed_sphereForm Projectivization.isBasic_sphereForm
    Projectivization.ker_bilinFormAt_sphereForm

section Transport

open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

/-- An orthonormal basis `b` of `V` identifies `P(V)`, with its quotient topology, with `ℂPⁿ`,
sending the line `[v]` to the line of the coordinates of `v`. -/
def basisHomeomorph (b : OrthonormalBasis (Fin (n + 1)) ℂ V) :
    ℙ ℂ V ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ) :=
  Projectivization.mapHomeomorph
    (b.repr.toContinuousLinearEquiv.trans (PiLp.continuousLinearEquiv 2 ℂ fun _ ↦ ℂ))

/-- A space of dimension `n + 1` has an orthonormal basis indexed by `Fin (n + 1)`. -/
theorem nonempty_orthonormalBasis [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = n + 1) :
    Nonempty (OrthonormalBasis (Fin (n + 1)) ℂ V) :=
  ⟨(stdOrthonormalBasis ℂ V).reindex (finCongr hV)⟩

/-- The change of orthonormal basis acts on `ℂPⁿ` through a unitary map of `ℂⁿ⁺¹`. -/
theorem basisHomeomorph_symm_trans (b₁ b₂ : OrthonormalBasis (Fin (n + 1)) ℂ V) :
    (basisHomeomorph b₁).symm.trans (basisHomeomorph b₂) =
      Projectivization.unitaryMap (b₁.repr.symm.trans b₂.repr) :=
  Homeomorph.ext <| Projectivization.ind fun v hv ↦ by
    simp [basisHomeomorph, Projectivization.unitaryMap]

/-- The change of orthonormal basis is smooth on `ℂPⁿ`, so the smooth structure that an orthonormal
basis carries over to `P(V)` does not depend on the basis. -/
theorem contMDiff_basisHomeomorph_symm_trans (b₁ b₂ : OrthonormalBasis (Fin (n + 1)) ℂ V) :
    ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ∞
      ((basisHomeomorph b₁).symm.trans (basisHomeomorph b₂)) := by
  rw [basisHomeomorph_symm_trans]
  exact Projectivization.contMDiff_unitaryMap _ ∞

/-- **Theorem 1, "if".** For a complex inner product space `V` of dimension `n + 1`, every
orthonormal basis identifies `P(V)` with `ℂPⁿ` (`basisHomeomorph`), which the Fubini–Study form
makes a symplectic manifold (`existsUnique_isSymplectic_projectivization`). The change of basis
preserves the Fubini–Study form, so the symplectic structure carried over to `P(V)` does not
depend on the basis. -/
theorem mpullback_basisHomeomorph_symm_trans (b₁ b₂ : OrthonormalBasis (Fin (n + 1)) ℂ V) :
    TauCeti.SmoothForm.mpullback _ (contMDiff_basisHomeomorph_symm_trans b₁ b₂)
      (Projectivization.fubiniStudyForm n) = Projectivization.fubiniStudyForm n := by
  have key (f : ℙ ℂ (Fin (n + 1) → ℂ) ≃ₜ ℙ ℂ (Fin (n + 1) → ℂ))
      (hf : ContMDiff 𝓘(ℝ, Fin n → ℂ) 𝓘(ℝ, Fin n → ℂ) ∞ f)
      (hfU : f = Projectivization.unitaryMap (b₁.repr.symm.trans b₂.repr)) :
      TauCeti.SmoothForm.mpullback f hf (Projectivization.fubiniStudyForm n) =
        Projectivization.fubiniStudyForm n := by
    subst hfU
    exact Projectivization.mpullback_unitaryMap_fubiniStudyForm _
  exact key _ _ (basisHomeomorph_symm_trans b₁ b₂)

end Transport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The equal superposition `(e₀ + σ e₁)/√2` of two orthonormal vectors. -/
def superpos (e : Fin 2 → H) (σ : ℂ) : H := (((√2)⁻¹ : ℝ) : ℂ) • (e 0 + σ • e 1)

section Orthonormal

variable {e : Fin 2 → H} (he : Orthonormal ℂ e)
include he

lemma inner_self_of_orthonormal (i : Fin 2) : ⟪e i, e i⟫_ℂ = 1 := by
  rw [inner_self_eq_norm_sq_to_K, he.1 i]
  simp

lemma inner_zero_superpos (σ : ℂ) : ⟪e 0, superpos e σ⟫_ℂ = (((√2)⁻¹ : ℝ) : ℂ) := by
  rw [superpos, inner_smul_right, inner_add_right, inner_smul_right,
    inner_self_of_orthonormal he, he.2 (by decide : (0 : Fin 2) ≠ 1), mul_zero, add_zero, mul_one]

lemma inner_one_superpos (σ : ℂ) : ⟪e 1, superpos e σ⟫_ℂ = (((√2)⁻¹ : ℝ) : ℂ) * σ := by
  rw [superpos, inner_smul_right, inner_add_right, inner_smul_right,
    inner_self_of_orthonormal he, he.2 (by decide : (1 : Fin 2) ≠ 0), zero_add, mul_one]

lemma norm_superpos {σ : ℂ} (hσ : ‖σ‖ = 1) : ‖superpos e σ‖ = 1 := by
  have h0 : ⟪e 0, σ • e 1⟫_ℂ = 0 := by
    rw [inner_smul_right, he.2 (by decide : (0 : Fin 2) ≠ 1), mul_zero]
  have hsq : ‖e 0 + σ • e 1‖ ^ 2 = 2 := by
    rw [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0, norm_smul, hσ, one_mul,
      he.1 0, he.1 1]
    norm_num
  have hn : ‖e 0 + σ • e 1‖ = √2 := by rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [superpos, norm_smul, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), inv_mul_cancel₀ (by positivity)]

/-- **Remark after Example 2.** Under CST distinct states are mutually exclusive,
`p(ψ | ϕ) = δ_{ψϕ}`; under the Born rule they need not be: `e₀` and `(e₀ + e₁)/√2` span distinct
rays and have Born probability `½`. -/
theorem born_ne_delta :
    (∀ c : ℂ, superpos e 1 ≠ c • e 0) ∧ ‖⟪e 0, superpos e 1⟫_ℂ‖ ^ 2 = 1 / 2 := by
  refine ⟨fun c h => ?_, ?_⟩
  · have := inner_one_superpos he 1
    rw [h, inner_smul_right, he.2 (by decide : (1 : Fin 2) ≠ 0), mul_zero, mul_one] at this
    exact (by positivity : (0 : ℝ) < (√2)⁻¹).ne' (by exact_mod_cast this.symm)
  · rw [inner_zero_superpos he, Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (by norm_num)]
    norm_num

end Orthonormal

end Theorem1

/-! ## D. Theorem 5: density operators as classes of measures on pure states -/

section Theorem5

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The pure states `|ψ⟩⟨ψ|` with `‖ψ‖ = 1`: the projective space `P(H)` inside the operators. -/
def pureStates : Set (H →L[ℂ] H) := {ρ | ∃ ψ : H, ‖ψ‖ = 1 ∧ proj ψ = ρ}

/-- The pure states carry the Borel σ-algebra of the operator norm. -/
instance : MeasurableSpace (pureStates H) := borel _

instance : BorelSpace (pureStates H) := ⟨rfl⟩

variable {H}

/-- The pure state `|ψ⟩⟨ψ|` of a unit vector. -/
def pureState {ψ : H} (hψ : ‖ψ‖ = 1) : pureStates H := ⟨proj ψ, ψ, hψ, rfl⟩

lemma norm_coe_le_one (ρ : pureStates H) : ‖(ρ : H →L[ℂ] H)‖ ≤ 1 := by
  obtain ⟨_, ψ, hψ, rfl⟩ := ρ
  simp [InnerProductSpace.norm_rankOne, hψ]

/-- Two pure states differ if some `x` is orthogonal to one but not to the other. -/
lemma pureState_ne {ψ ϕ : H} (hψ : ‖ψ‖ = 1) (hϕ : ‖ϕ‖ = 1) {x : H} (hψx : ⟪ψ, x⟫_ℂ ≠ 0)
    (hϕx : ⟪ϕ, x⟫_ℂ = 0) : pureState hψ ≠ pureState hϕ := by
  intro h
  have := congrArg (fun ρ : pureStates H => (ρ : H →L[ℂ] H) x) h
  simp only [pureState, proj_apply, hϕx, zero_smul] at this
  exact smul_ne_zero hψx (norm_ne_zero_iff.1 (by rw [hψ]; exact one_ne_zero)) this

/-- `ψ ↦ |ψ⟩⟨ψ|` is continuous: `‖|ϕ⟩⟨ϕ| - |ψ⟩⟨ψ|‖ ≤ (‖ϕ‖ + ‖ψ‖) ‖ϕ - ψ‖`. -/
lemma continuous_proj : Continuous fun ψ : H => proj ψ := by
  refine continuous_iff_continuousAt.2 fun ψ => ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ φ : H, ‖proj φ - proj ψ‖ ≤ ‖φ‖ * ‖φ - ψ‖ + ‖φ - ψ‖ * ‖ψ‖ := fun φ => by
    have : proj φ - proj ψ = InnerProductSpace.rankOne ℂ φ (φ - ψ) +
        InnerProductSpace.rankOne ℂ (φ - ψ) ψ := by
      simp only [map_sub, FunLike.coe_sub, Pi.sub_apply]
      abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
  refine squeeze_zero (fun _ => norm_nonneg _) hb ?_
  have : Continuous fun φ : H => ‖φ‖ * ‖φ - ψ‖ + ‖φ - ψ‖ * ‖ψ‖ := by fun_prop
  simpa using this.tendsto ψ

variable [TopologicalSpace.SeparableSpace H]

/-- In a separable Hilbert space the pure states are separable: they are the image of the unit
sphere under the continuous map `ψ ↦ |ψ⟩⟨ψ|`. -/
instance : TopologicalSpace.SeparableSpace (pureStates H) := by
  have hc : Continuous fun ψ : H => proj ψ := continuous_proj
  have himage : pureStates H = (fun ψ : H => proj ψ) '' Metric.sphere 0 1 := by
    ext ρ
    simp [pureStates]
  have hsep : TopologicalSpace.IsSeparable (pureStates H) := by
    rw [himage]
    exact ((TopologicalSpace.isSeparable_univ_iff.2 ‹_›).mono (Set.subset_univ _)).image hc
  exact hsep.separableSpace

lemma integrable_coe (μ : Measure (pureStates H)) [IsFiniteMeasure μ] :
    Integrable (fun ρ : pureStates H => (ρ : H →L[ℂ] H)) μ :=
  Integrable.of_bound continuous_subtype_val.aestronglyMeasurable 1 (ae_of_all _ norm_coe_le_one)

variable [CompleteSpace H]

omit [TopologicalSpace.SeparableSpace H] in
lemma isDensityOperator_coe (ρ : pureStates H) : IsDensityOperator (ρ : H →L[ℂ] H) := by
  obtain ⟨_, ψ, hψ, rfl⟩ := ρ
  exact isDensityOperator_proj hψ

omit [TopologicalSpace.SeparableSpace H] in
/-- **Proof of Theorem 5.** The pure states are the extreme points of the convex set `D(H)` of
density operators. -/
theorem pureStates_eq_extremePoints :
    pureStates H = Set.extremePoints ℝ {ρ : H →L[ℂ] H | IsDensityOperator ρ} := by
  ext ρ
  have hpure : ρ ∈ pureStates H ↔ IsPure ρ :=
    ⟨fun ⟨ψ, hψ, h⟩ => ⟨ψ, hψ, h.symm⟩, fun ⟨ψ, hψ, h⟩ => ⟨ψ, hψ, h.symm⟩⟩
  rw [hpure, isPure_iff_isExtremeDensityOperator, IsExtremeDensityOperator,
    mem_extremePoints_iff_left]
  simp only [Complex.coe_smul, Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨fun h σ hσ τ hτ ⟨a, b, ha, hb, hab, hρ⟩ => ?_,
    fun h σ τ hσ hτ t ht0 ht1 hρ => h σ hσ τ hτ ⟨t, 1 - t, ht0, by linarith, by ring, hρ.symm⟩⟩
  obtain rfl : b = 1 - a := by linarith
  exact h σ τ hσ hτ a ha (by linarith) hρ.symm

/-- The barycenter `r(μ) = ∫ ρ dμ(ρ)` of a measure on the pure states: the ensemble that `μ`
represents. -/
def barycenter (μ : Measure (pureStates H)) : H →L[ℂ] H := ∫ ρ, (ρ : H →L[ℂ] H) ∂μ

omit [CompleteSpace H] in
/-- The barycenter is affine. -/
theorem barycenter_add (μ ν : Measure (pureStates H)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (a b : ℝ≥0) : barycenter (a • μ + b • ν) = a • barycenter μ + b • barycenter ν := by
  rw [barycenter, integral_add_measure (integrable_coe _) (integrable_coe _),
    integral_smul_nnreal_measure, integral_smul_nnreal_measure, barycenter, barycenter]

omit [TopologicalSpace.SeparableSpace H] in
lemma barycenter_dirac (ρ : pureStates H) : barycenter (Measure.dirac ρ) = ρ :=
  integral_dirac _ _

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem isClosed_setOf_isPositive : IsClosed {ρ : H →L[ℂ] H | ρ.IsPositive} := by
  have happ : ∀ x : H, Continuous fun ρ : H →L[ℂ] H => ρ x := fun x =>
    continuous_id.clm_apply continuous_const
  have hsymm : IsClosed {ρ : H →L[ℂ] H | ∀ x y, ⟪ρ x, y⟫_ℂ = ⟪x, ρ y⟫_ℂ} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq ((happ x).inner continuous_const) (continuous_const.inner (happ y))
  have hpos : IsClosed {ρ : H →L[ℂ] H | ∀ x, 0 ≤ RCLike.re ⟪ρ x, x⟫_ℂ} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_le continuous_const
      (RCLike.continuous_re.comp ((happ x).inner continuous_const))
  convert hsymm.inter hpos using 1
  ext ρ
  rfl

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
theorem convex_setOf_isPositive : Convex ℝ {ρ : H →L[ℂ] H | ρ.IsPositive} := by
  intro ρ hρ σ hσ a b ha hb _
  have hc : ∀ c : ℝ, 0 ≤ c → ∀ τ : H →L[ℂ] H, τ.IsPositive → (c • τ).IsPositive :=
    fun c hc τ hτ => by
      rw [← Complex.coe_smul]
      exact hτ.smul_of_nonneg (Complex.zero_le_real.2 hc)
  exact (hc a ha ρ hρ).add (hc b hb σ hσ)

/-- The functional `ρ ↦ re ⟪x, ρ x⟫`. -/
def reInnerApply (x : H) : (H →L[ℂ] H) →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H x)).restrictScalars ℝ)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma reInnerApply_apply (x : H) (ρ : H →L[ℂ] H) : reInnerApply x ρ = (⟪x, ρ x⟫_ℂ).re := rfl

/-- The trace of the barycenter is the integral of the traces: `tr r(μ) = ∫ tr ρ dμ = 1`, by
Parseval and monotone convergence over a countable Hilbert basis. -/
theorem posTrace_barycenter (μ : Measure (pureStates H)) [IsProbabilityMeasure μ] :
    posTrace (barycenter μ) = 1 := by
  have := (posTraceBasis H).orthonormal.countable
  set b := posTraceBasis H
  have hL : ∀ x : H, (⟪x, barycenter μ x⟫_ℂ).re =
      ∫ ρ : pureStates H, reInnerApply x (ρ : H →L[ℂ] H) ∂μ := fun x =>
    ((reInnerApply x).integral_comp_comm (integrable_coe μ)).symm
  have hnn : ∀ (x : H) (ρ : pureStates H), 0 ≤ reInnerApply x (ρ : H →L[ℂ] H) := fun x ρ =>
    re_inner_apply_nonneg (isDensityOperator_coe ρ).nonneg x
  have hmeas : ∀ x : H, Measurable fun ρ : pureStates H => reInnerApply x (ρ : H →L[ℂ] H) :=
    fun x => ((reInnerApply x).continuous.comp continuous_subtype_val).measurable
  calc posTrace (barycenter μ)
      = ∑' i, ∫⁻ ρ : pureStates H, ENNReal.ofReal (reInnerApply (b i) (ρ : H →L[ℂ] H)) ∂μ := by
        refine tsum_congr fun i => ?_
        rw [hL, ofReal_integral_eq_lintegral_ofReal ((reInnerApply _).integrable_comp
          (integrable_coe μ)) (ae_of_all _ (hnn _))]
    _ = ∫⁻ ρ : pureStates H, ∑' i, ENNReal.ofReal (reInnerApply (b i) (ρ : H →L[ℂ] H)) ∂μ :=
        (lintegral_tsum fun i => (hmeas _).ennreal_ofReal.aemeasurable).symm
    _ = ∫⁻ _ : pureStates H, 1 ∂μ :=
        lintegral_congr fun ρ => (isDensityOperator_coe ρ).posTrace_eq_one
    _ = 1 := by simp

/-- The barycenter of a probability measure on the pure states is a density operator. -/
theorem isDensityOperator_barycenter (μ : Measure (pureStates H)) [IsProbabilityMeasure μ] :
    IsDensityOperator (barycenter μ) := by
  refine isDensityOperator_iff.2 ⟨ContinuousLinearMap.nonneg_iff_isPositive.2 ?_,
    posTrace_barycenter μ⟩
  exact Convex.integral_mem (s := {ρ : H →L[ℂ] H | ρ.IsPositive})
    (f := fun ρ : pureStates H => (ρ : H →L[ℂ] H)) convex_setOf_isPositive
    isClosed_setOf_isPositive
    (ae_of_all _ fun ρ =>
      ContinuousLinearMap.nonneg_iff_isPositive.1 (isDensityOperator_coe ρ).nonneg)
    (integrable_coe μ)

/-- The map `r : M¹(P(H)) → D(H)` of Theorem 5. -/
def toDensity (μ : {μ : Measure (pureStates H) // IsProbabilityMeasure μ}) :
    {ρ : H →L[ℂ] H // IsDensityOperator ρ} :=
  have := μ.2
  ⟨barycenter μ.1, isDensityOperator_barycenter μ.1⟩

/-- Every density operator is represented by a probability measure on the pure states: by the
canonical expansion `ρ = ∑ᵢ λᵢ |eᵢ⟩⟨eᵢ|`, by `∑ᵢ λᵢ δ_{eᵢ}`. -/
theorem toDensity_surjective : Surjective (toDensity (H := H)) := by
  rintro ⟨ρ, hρ⟩
  obtain ⟨w, b, lam, -, -, hlam, -, htr, hsum⟩ :=
    hρ.isTraceClass.exists_hasSum_rankOne hρ.nonneg
  have hb : ∀ i, ‖b i‖ = 1 := b.orthonormal.1
  have h1 : HasSum lam 1 := by
    rw [hρ.trace_eq_one, ← Complex.ofReal_one] at htr
    exact Complex.hasSum_ofReal.1 htr
  set ν : Measure (pureStates H) :=
    Measure.sum fun i => ENNReal.ofReal (lam i) • Measure.dirac (pureState (hb i))
  have hν : IsProbabilityMeasure ν := ⟨by
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hlam h1.summable, h1.tsum_eq, ENNReal.ofReal_one]⟩
  refine ⟨⟨ν, hν⟩, Subtype.ext ?_⟩
  change barycenter ν = ρ
  have hs : HasSum (fun i => (lam i : ℂ) • proj (b i)) ρ :=
    hsum.map (TraceClass.toOperator (H := H)) (TraceClass.toOperator (H := H)).continuous
  rw [barycenter, integral_sum_measure (integrable_coe ν), ← hs.tsum_eq]
  refine tsum_congr fun i => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hlam i), pureState,
    ← Complex.coe_smul]

/-- **Theorem 5.** The density operators are the probability measures on the pure states up to
the equivalence `μ₁ ∼ μ₂ ↔ r(μ₁) = r(μ₂)`. -/
def densityEquiv :
    Quotient (Setoid.ker (toDensity (H := H))) ≃ {ρ : H →L[ℂ] H // IsDensityOperator ρ} :=
  Setoid.quotientKerEquivOfSurjective _ toDensity_surjective

/-- The equivalence of Theorem 5 is not trivial: `½ δ_{e₀} + ½ δ_{e₁}` and `½ δ_{e₊} + ½ δ_{e₋}`
represent the same density operator, but only the first gives the state `e₀` positive
probability. -/
theorem exists_barycenter_eq_and_ne {e : Fin 2 → H} (he : Orthonormal ℂ e) :
    ∃ μ₁ μ₂ : Measure (pureStates H), IsProbabilityMeasure μ₁ ∧ IsProbabilityMeasure μ₂ ∧
      barycenter μ₁ = barycenter μ₂ ∧ μ₁ {pureState (he.1 0)} ≠ μ₂ {pureState (he.1 0)} := by
  have hp := norm_superpos he (σ := 1) (by simp)
  have hm := norm_superpos he (σ := -1) (by simp)
  have h01 : ⟪e 0, e 1⟫_ℂ = 0 := he.2 (by decide)
  have hsup : ∀ σ : ℂ, σ ≠ 0 → ⟪superpos e σ, e 1⟫_ℂ ≠ 0 := fun σ hσ => by
    rw [← inner_conj_symm, inner_one_superpos he, map_ne_zero]
    exact mul_ne_zero (by exact_mod_cast (by positivity : (0 : ℝ) < (√2)⁻¹).ne') hσ
  have hne1 : pureState (he.1 1) ≠ pureState (he.1 0) :=
    pureState_ne _ _ (by rw [inner_self_of_orthonormal he]; exact one_ne_zero) h01
  have hnep : pureState hp ≠ pureState (he.1 0) := pureState_ne _ _ (hsup 1 one_ne_zero) h01
  have hnem : pureState hm ≠ pureState (he.1 0) :=
    pureState_ne _ _ (hsup (-1) (neg_ne_zero.2 one_ne_zero)) h01
  have hhalf : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 := ENNReal.inv_two_add_inv_two
  refine ⟨(2⁻¹ : ℝ≥0) • Measure.dirac (pureState (he.1 0)) +
      (2⁻¹ : ℝ≥0) • Measure.dirac (pureState (he.1 1)),
    (2⁻¹ : ℝ≥0) • Measure.dirac (pureState hp) + (2⁻¹ : ℝ≥0) • Measure.dirac (pureState hm),
    ⟨?_⟩, ⟨?_⟩, ?_, ?_⟩
  · simpa [ENNReal.smul_def] using hhalf
  · simpa [ENNReal.smul_def] using hhalf
  · rw [barycenter_add, barycenter_add, barycenter_dirac, barycenter_dirac, barycenter_dirac,
      barycenter_dirac]
    simp only [pureState, superpos, proj_smul, one_smul, neg_one_smul, ← sub_eq_add_neg]
    have h2 : ((‖(((√2)⁻¹ : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) = 2⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
      push_cast
      ring
    rw [h2, ← smul_add, ← smul_add, ← smul_add, proj_add_add_proj_sub]
    simp only [NNReal.smul_def, ← Complex.coe_smul, smul_add, smul_smul]
    rw [inv_mul_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), mul_one]
  · simp [Set.indicator, hne1, hnep, hnem, ENNReal.smul_def]

end Theorem5

/-! ## E. Example 2: the classical qubit -/

section Example2

open Complex ComplexConjugate Matrix Qubit
open OnePoint (fubiniStudyDensity fubiniStudyForm)
open scoped Manifold ContDiff TauCeti.ComplexManifold

/-- The pure states of a qubit form a two-sphere: `P(ℂ²)` is homeomorphic to the unit sphere of
`ℝ³`, through the Bloch vector. -/
theorem nonempty_homeomorph_sphere :
    Nonempty (ℙ ℂ (Fin 2 → ℂ) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨blochSphere⟩

/-- The area of the sphere is `dz dθ` in the coordinates `z = x₂`, `θ = θ_xy`: the surface measure
is the pushforward of the area measure of `(-1, 1) × (-π, π]` under
`(z, θ) ↦ (√(1 - z²) cos θ, √(1 - z²) sin θ, z)`, and the height `z` is distributed as `2π dz`. -/
theorem toSphere_eq_dz_dtheta :
    ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere).map (↑) =
        (volume.restrict (Set.Ioo (-1) 1 ×ˢ Set.Ioc (-Real.pi) Real.pi)).map cylinderToSphere ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere).map
          (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
            (x : EuclideanSpace ℝ (Fin 3)) 2) =
        ENNReal.ofReal (2 * Real.pi) • volume.restrict (Set.Ioo (-1) 1) :=
  ⟨Measure.map_toSphere_volume_eq_map_cylinderToSphere, Measure.map_toSphere_volume_height⟩

/-- Complex conjugation of the Riemann sphere `OnePoint ℂ ≅ P(ℂ²)` preserves the area density
of the Fubini–Study form but reverses the form. So it preserves the area and is not the time-`t`
map of a Hamiltonian flow (`QuantumMechanics.Qubit.globalFlow_ne_conjSphere`), nor of a
time-dependent one (`QuantumMechanics.Qubit.timeDependentFlowOf_ne_conjSphere`), nor of a
Hamiltonian isotopy (`QuantumMechanics.Qubit.isotopy_ne_conjSphere`). -/
theorem conjSphere_preserves_area_reverses_form :
    (∀ z : ℂ, fubiniStudyDensity (conj z) = fubiniStudyDensity z) ∧
      TauCeti.SmoothForm.mpullback conjSphere contMDiff_conjSphere fubiniStudyForm =
        -fubiniStudyForm :=
  ⟨fubiniStudyDensity_conj, mpullback_conjSphere⟩

/-- **Infinitesimal Hamiltonian evolution of the classical qubit.** A smooth vector field on the
Riemann sphere preserves the Fubini–Study form, `L_X ω_FS = 0`, exactly when it is the Hamiltonian
vector field of a smooth function. -/
theorem lieDeriv_areaForm_eq_zero_iff_hamiltonian
    {X : Cₛ^∞⟮𝓘(ℝ, ℂ); ℂ, TangentSpace 𝓘(ℝ, ℂ) (M := OnePoint ℂ)⟯} :
    TauCeti.mlieDerivForm X fubiniStudyForm.1 = 0 ↔
      ∃ f : OnePoint ℂ → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ f ∧
        fubiniStudyForm.IsHamiltonianVectorField f X :=
  mlieDerivForm_fubiniStudyForm_eq_zero_iff

/-- **Hamiltonian evolution of the classical qubit preserves the area form, and only it.** The
time-dependent flow of a jointly smooth time-dependent vector field on the Riemann sphere preserves
the Fubini–Study form at all times exactly when every velocity field `X t` is the Hamiltonian
vector field of a smooth function. -/
theorem preserves_areaForm_iff_hamiltonian
    {X : ℝ → (x : OnePoint ℂ) → TangentSpace 𝓘(ℝ, ℂ) x}
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ).tangent ∞
      (fun p : ℝ × OnePoint ℂ ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)))) :
    (∀ s t, TauCeti.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (TauCeti.timeDependentFlowOf X s t)
        fubiniStudyForm.1 = fubiniStudyForm.1) ↔
      ∀ t, ∃ f : OnePoint ℂ → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ f ∧
        fubiniStudyForm.IsHamiltonianVectorField f (X t) :=
  forall_mpullback_timeDependentFlowOf_fubiniStudyForm_iff hX

/-- **Hamiltonian evolution of the classical qubit, as a family of maps.** A smooth isotopy `φ t`
of the Riemann sphere from the identity, with jointly smooth inverses `ψ t`, preserves the
Fubini–Study form at all times exactly when every generating field `X_t = φ̇_t ∘ φ_t⁻¹` is the
Hamiltonian vector field of a smooth function. The isotopy is the time-dependent flow of its
generating field (`TauCeti.timeDependentFlowOf_isotopyField`). -/
theorem isotopy_preserves_areaForm_iff_hamiltonian {φ ψ : ℝ → OnePoint ℂ → OnePoint ℂ}
    (hφ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ (fun p : ℝ × OnePoint ℂ ↦ φ p.1 p.2))
    (hψ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞ (fun p : ℝ × OnePoint ℂ ↦ ψ p.1 p.2))
    (hφψ : ∀ t y, φ t (ψ t y) = y) (hψφ : ∀ t x, ψ t (φ t x) = x) (hφ0 : ∀ x, φ 0 x = x) :
    (∀ t, TauCeti.mpullback 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (φ t) fubiniStudyForm.1 = fubiniStudyForm.1) ↔
      ∀ t, ∃ f : OnePoint ℂ → ℝ, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ f ∧
        fubiniStudyForm.IsHamiltonianVectorField f (TauCeti.isotopyField 𝓘(ℝ, ℂ) φ ψ t) :=
  forall_mpullback_isotopy_fubiniStudyForm_iff hφ hψ hφψ hψφ hφ0

/-- **The quantum evolutions of a qubit are exactly the rotations of the Bloch sphere**: a map of
rays is the action of a unitary if and only if it is a rotation on Bloch vectors. -/
theorem exists_unitaryAction_eq_iff {f : ℙ ℂ (Fin 2 → ℂ) → ℙ ℂ (Fin 2 → ℂ)} :
    (∃ U : unitaryGroup (Fin 2) ℂ, f = unitaryAction U) ↔
      ∃ R ∈ specialOrthogonalGroup (Fin 3) ℝ, ∀ p, blochPoint (f p) = R *ᵥ blochPoint p := by
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨_, TauCeti.pauliRotation_mem_specialOrthogonalGroup U, blochPoint_unitaryAction U⟩
  · rintro ⟨R, hR, hf⟩
    obtain ⟨g, hg⟩ := exists_unitaryAction_eq ⟨R, hR⟩
    exact ⟨_, funext fun p ↦ blochPoint_injective (by rw [hf, hg])⟩

/-- Every Hamiltonian of a qubit rotates the Bloch vector: for a Hermitian `H` there is `n ∈ ℝ³`,
the vector of the linear Hamiltonian `n · x`, with `a' = n × a` along every solution of
`i ψ' = H ψ`. -/
theorem exists_blochVector_precession {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H.IsHermitian) :
    ∃ n : Fin 3 → ℝ, ∀ (ψ : ℝ → EuclideanSpace ℂ (Fin 2)) (t : ℝ),
      HasDerivAt ψ (-I • WithLp.toLp 2 (H *ᵥ (ψ t).ofLp)) t →
        HasDerivAt (fun s ↦ blochVector (ψ s)) (n ⨯₃ blochVector (ψ t)) t :=
  exists_hasDerivAt_blochVector hH

end Example2

end PureStatesNotEnough
