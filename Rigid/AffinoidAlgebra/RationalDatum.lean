import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.RingTheory.Ideal.Basic

set_option linter.style.header false

/-!
# Data for rational localizations

This file defines the norm-independent boundedness condition used when mapping out of a strict Tate
algebra and the unit-ideal condition on the numerator and denominator of a rational localization.
-/

universe u

namespace Rigid

/-- An element of a seminormed ring is power-bounded if the norms of all its nonnegative powers
have a common upper bound. -/
def IsPowerBounded {B : Type u} [SeminormedRing B] (x : B) : Prop :=
  BddAbove (Set.range fun m : ℕ ↦ ‖x ^ m‖)

/-- An element of norm at most one is power-bounded. -/
theorem isPowerBounded_of_norm_le_one {B : Type u} [SeminormedRing B] {x : B}
    (hx : ‖x‖ ≤ 1) : IsPowerBounded x := by
  refine ⟨max ‖(1 : B)‖ 1, ?_⟩
  rintro _ ⟨m, rfl⟩
  change ‖x ^ m‖ ≤ max ‖(1 : B)‖ 1
  induction m with
  | zero => simp
  | succ m hm =>
      rw [pow_succ]
      calc
        ‖x ^ m * x‖ ≤ ‖x ^ m‖ * ‖x‖ := norm_mul_le _ _
        _ ≤ max ‖(1 : B)‖ 1 * 1 := mul_le_mul hm hx (norm_nonneg x) (by positivity)
        _ = max ‖(1 : B)‖ 1 := mul_one _

@[simp]
theorem isPowerBounded_zero {B : Type u} [SeminormedRing B] :
    IsPowerBounded (0 : B) :=
  isPowerBounded_of_norm_le_one (norm_zero.le.trans zero_le_one)

@[simp]
theorem isPowerBounded_one {B : Type u} [SeminormedRing B] :
    IsPowerBounded (1 : B) := by
  refine ⟨‖(1 : B)‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  simp

/-- The numerator and denominator of a rational localization form a rational datum when together
they generate the unit ideal. -/
def IsRationalDatum {A : Type u} [CommRing A] {n : ℕ} (g : A) (f : Fin n → A) : Prop :=
  Ideal.span (Set.insert g (Set.range f)) = ⊤

end Rigid
