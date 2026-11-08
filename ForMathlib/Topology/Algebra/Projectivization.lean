/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Projectivization

/-!
# Homeomorphisms of projective spaces induced by linear equivalences

A continuous linear equivalence `e : V ≃L[K] W` induces a homeomorphism `ℙ K V ≃ₜ ℙ K W` of
projective spaces with their quotient topologies, sending the line `[v]` to `[e v]`.

## Main definitions

* `Projectivization.mapHomeomorph`: the homeomorphism induced by a continuous linear equivalence.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K V W U : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [AddCommGroup W] [Module K W] [TopologicalSpace W] [AddCommGroup U] [Module K U]
  [TopologicalSpace U]

/-- A continuous linear equivalence `e` induces a homeomorphism of projective spaces, sending the
line `[v]` to `[e v]`. -/
@[expose] def mapHomeomorph (e : V ≃L[K] W) : ℙ K V ≃ₜ ℙ K W where
  toFun := map (e : V →ₗ[K] W) e.injective
  invFun := map (e.symm : W →ₗ[K] V) e.symm.injective
  left_inv := ind fun v hv ↦ by simp [map_mk]
  right_inv := ind fun v hv ↦ by simp [map_mk]
  continuous_toFun := continuous_map _ e.continuous
  continuous_invFun := continuous_map _ e.symm.continuous

theorem coe_mapHomeomorph (e : V ≃L[K] W) :
    ⇑(mapHomeomorph e) = map (e : V →ₗ[K] W) e.injective :=
  rfl

@[simp]
theorem mapHomeomorph_mk (e : V ≃L[K] W) (v : V) (hv : v ≠ 0) :
    mapHomeomorph e (mk K v hv) = mk K (e v) (by simpa using hv) :=
  map_mk _ e.injective _ _

@[simp]
theorem mapHomeomorph_symm (e : V ≃L[K] W) : (mapHomeomorph e).symm = mapHomeomorph e.symm :=
  rfl

@[simp]
theorem mapHomeomorph_trans (e : V ≃L[K] W) (f : W ≃L[K] U) :
    (mapHomeomorph e).trans (mapHomeomorph f) = mapHomeomorph (e.trans f) :=
  Homeomorph.ext <| ind fun v hv ↦ by simp

end Projectivization
