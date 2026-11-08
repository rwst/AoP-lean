/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import TauCeti.AlgebraicTopology.Sphere.SimplyConnected

/-!
# The one-point compactification of a real vector space is simply connected

The one-point compactification of a finite-dimensional real vector space `V` is homeomorphic to
the sphere of dimension `finrank ℝ V` (`onePointEquivSphereOfFinrankEq`), which is simply
connected for `2 ≤ finrank ℝ V`. In particular the Riemann sphere `OnePoint ℂ` is simply
connected.

## Main results

- `OnePoint.simplyConnectedSpace_of_two_le_finrank`: `OnePoint V` is simply connected for
  `2 ≤ finrank ℝ V`.
- `OnePoint.instSimplyConnectedSpaceComplex`: the Riemann sphere is simply connected.
-/

public section

open Module

namespace OnePoint

/-- The one-point compactification of a real vector space of dimension at least two is simply
connected. -/
theorem simplyConnectedSpace_of_two_le_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
    [T2Space V] (h : 2 ≤ finrank ℝ V) : SimplyConnectedSpace (OnePoint V) :=
  have := TauCeti.simplyConnectedSpace_sphere_euclideanSpace h
  (onePointEquivSphereOfFinrankEq (ι := Fin (finrank ℝ V + 1)) (by simp)).toHomotopyEquiv
    |>.simplyConnectedSpace

/-- The Riemann sphere is simply connected. -/
instance instSimplyConnectedSpaceComplex : SimplyConnectedSpace (OnePoint ℂ) :=
  simplyConnectedSpace_of_two_le_finrank Complex.finrank_real_complex.ge

end OnePoint
