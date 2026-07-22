import Rigid.AffinoidAlgebra.RationalDatum
import Rigid.Berkovich.RelativeSpectrum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Power-bounded elements of nonarchimedean normed rings

This file develops the elementary algebra of power-bounded elements used in the affinoid maximum
modulus theorem.  The property is independent of replacing a Banach norm by an equivalent norm,
is stable under the ring operations in a commutative nonarchimedean normed ring, and forces every
Berkovich seminorm to have value at most one.
-/

open scoped BigOperators

universe u v

namespace Rigid

namespace IsPowerBounded

variable {B : Type u} [NormedCommRing B] [IsUltrametricDist B]

omit [IsUltrametricDist B] in
/-- Power-boundedness is unchanged by negation. -/
theorem neg {x : B} (hx : IsPowerBounded x) : IsPowerBounded (-x) := by
  rcases hx with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(-x) ^ n‖ ≤ C
  rw [neg_pow]
  rcases neg_one_pow_eq_or B n with hn | hn
  · rw [hn, one_mul]
    exact hC ⟨n, rfl⟩
  · rw [hn, neg_one_mul, norm_neg]
    exact hC ⟨n, rfl⟩

omit [IsUltrametricDist B] in
/-- The product of two power-bounded elements is power-bounded. -/
theorem mul {x y : B} (hx : IsPowerBounded x) (hy : IsPowerBounded y) :
    IsPowerBounded (x * y) := by
  rcases hx with ⟨Cx, hCx⟩
  rcases hy with ⟨Cy, hCy⟩
  refine ⟨max 0 Cx * max 0 Cy, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(x * y) ^ n‖ ≤ max 0 Cx * max 0 Cy
  rw [mul_pow]
  exact (norm_mul_le _ _).trans <| mul_le_mul
    ((hCx ⟨n, rfl⟩).trans (le_max_right 0 Cx))
    ((hCy ⟨n, rfl⟩).trans (le_max_right 0 Cy))
    (norm_nonneg _) (by positivity)

private theorem norm_natCast_le_norm_one (n : ℕ) : ‖(n : B)‖ ≤ ‖(1 : B)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ]
      exact (IsUltrametricDist.norm_add_le_max (n : B) 1).trans
        (max_le ih le_rfl)

/-- The sum of two power-bounded elements is power-bounded. -/
theorem add {x y : B} (hx : IsPowerBounded x) (hy : IsPowerBounded y) :
    IsPowerBounded (x + y) := by
  rcases hx with ⟨Cx, hCx⟩
  rcases hy with ⟨Cy, hCy⟩
  let C := max 0 Cx * max 0 Cy * max 1 ‖(1 : B)‖
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(x + y) ^ n‖ ≤ C
  rw [add_pow]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro i hi
  simp only [Finset.mem_range] at hi
  calc
    ‖x ^ i * y ^ (n - i) * (n.choose i : B)‖ ≤
        ‖x ^ i * y ^ (n - i)‖ * ‖(n.choose i : B)‖ := norm_mul_le _ _
    _ ≤
        ‖x ^ i * y ^ (n - i)‖ * max 1 ‖(1 : B)‖ :=
      mul_le_mul_of_nonneg_left
        ((norm_natCast_le_norm_one (B := B) _).trans (le_max_right 1 ‖(1 : B)‖))
        (norm_nonneg _)
    _ ≤ (‖x ^ i‖ * ‖y ^ (n - i)‖) * max 1 ‖(1 : B)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (by positivity)
    _ ≤ C := by
      dsimp only [C]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul
          ((hCx ⟨i, rfl⟩).trans (le_max_right 0 Cx))
          ((hCy ⟨n - i, rfl⟩).trans (le_max_right 0 Cy))
          (norm_nonneg _) (by positivity))
        (by positivity)

/-- The power-bounded elements form a subring. -/
def subring (B : Type u) [NormedCommRing B] [IsUltrametricDist B] : Subring B where
  carrier := {x | IsPowerBounded x}
  zero_mem' := isPowerBounded_zero
  one_mem' := isPowerBounded_one
  add_mem' := add
  neg_mem' := neg
  mul_mem' := mul

/-- An element integral over a uniformly bounded coefficient subring is power-bounded.  This is
the bounded-coefficient half of the affinoid maximum-modulus argument. -/
theorem of_isIntegral_over_bounded_subring (S : Subring B)
    (hS : BddAbove (Set.range fun s : S ↦ ‖(s : B)‖)) {x : B} (hx : IsIntegral S x) :
    IsPowerBounded x := by
  obtain ⟨C, hC⟩ := hS
  obtain ⟨d, v, hv⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hx.fg_adjoin_singleton
  let D : ℝ := ∑ i, ‖v i‖
  refine ⟨max 0 C * D, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hxpow : x ^ n ∈ Algebra.adjoin S {x} := by
    exact (Algebra.adjoin S {x}).pow_mem (Algebra.subset_adjoin (Set.mem_singleton x)) n
  have hxspan : x ^ n ∈ Submodule.span S (Set.range v) := by
    rw [hv]
    exact hxpow
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hxspan
  change ‖x ^ n‖ ≤ max 0 C * D
  rw [← hc]
  calc
    ‖∑ i, c i • v i‖ ≤ ∑ i, ‖c i • v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, max 0 C * ‖v i‖ := by
      apply Finset.sum_le_sum
      intro i _
      change ‖(c i : B) * v i‖ ≤ max 0 C * ‖v i‖
      exact (norm_mul_le _ _).trans <| mul_le_mul_of_nonneg_right
        ((hC ⟨c i, rfl⟩).trans (le_max_right 0 C)) (norm_nonneg _)
    _ = max 0 C * D := by rw [Finset.mul_sum]

/-- Continuous algebra homomorphisms preserve power-bounded elements. -/
theorem map_continuousAlgHom
    {K : Type v} [NontriviallyNormedField K] [NormedAlgebra K B]
    {C : Type v} [NormedCommRing C] [NormedAlgebra K C]
    (f : ContinuousAlgHom K B C) {x : B} (hx : IsPowerBounded x) :
    IsPowerBounded (f x) := by
  obtain ⟨D, hD⟩ := hx
  obtain ⟨M, hM, hf⟩ := SemilinearMapClass.bound_of_continuous f f.continuous
  refine ⟨M * max 0 D, ?_⟩
  rintro _ ⟨n, rfl⟩
  change ‖(f x) ^ n‖ ≤ M * max 0 D
  rw [← map_pow]
  exact (hf (x ^ n)).trans <| mul_le_mul_of_nonneg_left
    ((hD ⟨n, rfl⟩).trans (le_max_right 0 D)) hM.le

omit [IsUltrametricDist B] in
/-- A power-bounded element has value at most one at every relative Berkovich point. -/
theorem apply_le_one
    (K : Type v) [NormedField K] [Algebra K B]
    (x : BerkovichSpectrumOver K B) {b : B} (hb : IsPowerBounded b) : x b ≤ 1 := by
  rcases hb with ⟨C, hC⟩
  by_contra h
  have hxb : 1 < x b := lt_of_not_ge h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hxb
  apply not_le_of_gt hn
  calc
    x b ^ n = x (b ^ n) := (map_pow x.toBerkovichSpectrum.seminorm b n).symm
    _ ≤ ‖b ^ n‖ := BerkovichSpectrumOver.le_norm K B x _
    _ ≤ C := hC ⟨n, rfl⟩

end IsPowerBounded

end Rigid
