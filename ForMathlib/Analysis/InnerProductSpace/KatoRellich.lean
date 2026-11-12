/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
import TauCeti.Analysis.InnerProductSpace.LinearPMap.KatoRellich

/-!
# The Kato–Rellich theorem, behind a private import

TauCeti proves the Kato–Rellich theorem (`IsSelfAdjoint.add_of_isRelativelyBounded`): if `A` is
self-adjoint, `V` symmetric, `D(A) ⊆ D(V)` and `‖V x‖ ≤ a ‖x‖ + b ‖A x‖` on `D(A)` with `b < 1`,
then `A + V` is self-adjoint. Its module cannot be imported together with Physlib's unbounded
operators (`Physlib.QuantumMechanics.Operators.Unbounded`): both declare `LinearPMap.adjoint_smul`.

This file restates the theorem with the relative bound written out, so that its statement uses
only Mathlib, and imports TauCeti privately. A module that imports this file does not load the
TauCeti modules, so it may also import Physlib. Files that load private imports, such as
non-`module` files and `lake comparator`'s exporter, still see the clash; certified statements
must therefore not depend on this file.

Delete this file once one of the two `adjoint_smul` is renamed, and import TauCeti directly.

## Main results

* `IsSelfAdjoint.add_of_relativeBound`: the Kato–Rellich theorem.
-/

@[expose] public section

namespace LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- **The Kato–Rellich theorem** (TauCeti's `IsSelfAdjoint.add_of_isRelativelyBounded`). Let `A`
be self-adjoint and `V` symmetric with `D(A) ⊆ D(V)` and `‖V x‖ ≤ a ‖x‖ + b ‖A x‖` on `D(A)`. If
`b < 1`, then `A + V`, whose domain is `D(A)`, is self-adjoint. -/
theorem _root_.IsSelfAdjoint.add_of_relativeBound {A V : E →ₗ.[𝕜] E} (hA : IsSelfAdjoint A)
    (hV : V.IsFormalAdjoint V) {a b : ℝ} (hdom : A.domain ≤ V.domain)
    (hbound : ∀ x : A.domain, ‖V ⟨x, hdom x.2⟩‖ ≤ a * ‖(x : E)‖ + b * ‖A x‖) (hb : b < 1) :
    IsSelfAdjoint (A + V) :=
  hA.add_of_isRelativelyBounded hV ⟨hdom, hbound⟩ hb

end LinearPMap
