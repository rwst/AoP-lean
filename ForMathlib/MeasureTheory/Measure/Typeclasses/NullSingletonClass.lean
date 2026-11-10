/-
(C) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).
See https://creativecommons.org/publicdomain/zero/1.0/
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Changing a function at a point

If singletons are null, changing a function at one point does not change its almost-everywhere
class. So an element of `L^p(μ)` has no well-defined value at any point.

## Main results

* `MeasureTheory.update_ae_eq`: `Function.update f a c =ᵐ[μ] f`;
* `MeasureTheory.exists_ae_eq_apply_eq`: every function has an a.e. equal one with any prescribed
  value at a given point.
-/

@[expose] public section

namespace MeasureTheory

variable {α β : Type*} {m0 : MeasurableSpace α} {μ : Measure α} [NullSingletonClass μ]

theorem update_ae_eq [DecidableEq α] (f : α → β) (a : α) (c : β) :
    Function.update f a c =ᵐ[μ] f :=
  (Measure.ae_ne μ a).mono fun _ hx => Function.update_of_ne hx _ _

theorem exists_ae_eq_apply_eq (f : α → β) (a : α) (c : β) : ∃ g : α → β, g =ᵐ[μ] f ∧ g a = c := by
  classical
  exact ⟨Function.update f a c, update_ae_eq f a c, Function.update_self a c f⟩

end MeasureTheory
