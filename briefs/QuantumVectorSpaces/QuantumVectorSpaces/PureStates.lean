/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import QuantumVectorSpaces
public import ForMathlib.Topology.Algebra.Projectivization.SecondCountable

/-!
# Second countability from the pure states

The brief claims (Sec. 5, "Second countability vs separability") that "if the pure states are
second countable, we can always extend the topology to the vector space to preserve second
countability". Here the pure states are the rays of `V`, the projective space `ℙ ℂ V` with the
quotient topology of `topology c X`. For a definite inner product, `V` is second countable if
and only if its pure states are, so no extension of the topology is needed.

## Main results

* `separatingDual`  for a definite inner product, the functionals `w ↦ ⟨v, w⟩` are continuous
  and separate the vectors;
* `secondCountableTopology_iff_projectivization`  `V` is second countable if and only if `ℙ ℂ V`
  is;
* `IsQuantumVectorSpace.secondCountableTopology_projectivization`  the pure states of a quantum
  vector space are second countable.
-/

open scoped LinearAlgebra.Projectivization ComplexConjugate

@[expose] public noncomputable section

namespace QuantumVectorSpaces

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (c : PreInnerProductSpace.Core ℂ V)
  {ι : Type*} (X : ι → Module.End ℂ V)

/-- The linear functional `w ↦ ⟨v, w⟩`. -/
def innerRight (v : V) : V →ₗ[ℂ] ℂ where
  toFun w := c.inner v w
  map_add' w₁ w₂ := by
    rw [← c.conj_inner_symm, c.add_left, map_add, c.conj_inner_symm, c.conj_inner_symm]
  map_smul' r w := by
    rw [← c.conj_inner_symm, c.smul_left, map_mul, Complex.conj_conj, c.conj_inner_symm,
      RingHom.id_apply, smul_eq_mul]

/-- For a definite inner product, the continuous functionals `w ↦ ⟨v, w⟩` separate the
vectors. -/
theorem separatingDual (hc : ∀ v, c.inner v v = 0 → v = 0) :
    letI := topology c X; SeparatingDual ℂ V := by
  let := topology c X
  have ht := isAdmissible_topology c X
  have hcont (v : V) : Continuous (innerRight c v) :=
    ht.continuous_inner.comp (continuous_const.prodMk continuous_id)
  exact ⟨fun v hv => ⟨⟨innerRight c v, hcont v⟩, fun h => hv (hc v h)⟩⟩

/-- For a definite inner product, `V` is second countable if and only if its pure states, the
projective space `ℙ ℂ V` with the quotient topology, are. -/
theorem secondCountableTopology_iff_projectivization (hc : ∀ v, c.inner v v = 0 → v = 0) :
    letI := topology c X; SecondCountableTopology V ↔ SecondCountableTopology (ℙ ℂ V) := by
  let := topology c X
  have ht := isAdmissible_topology c X
  have := ht.isTopologicalAddGroup
  have := ht.continuousSMul
  have := separatingDual c X hc
  exact ⟨fun _ => inferInstance, fun _ => Projectivization.secondCountableTopology_of (K := ℂ)⟩

/-- The pure states of a quantum vector space are second countable. -/
theorem IsQuantumVectorSpace.secondCountableTopology_projectivization {ħ : ℝ}
    {C : ι → ι → ι →₀ ℂ} (hQ : IsQuantumVectorSpace c X ħ C) :
    letI := topology c X; SecondCountableTopology (ℙ ℂ V) := by
  let := topology c X
  have := hQ.secondCountableTopology
  have := (withSeminorms c X).continuousSMul
  infer_instance

end QuantumVectorSpaces
