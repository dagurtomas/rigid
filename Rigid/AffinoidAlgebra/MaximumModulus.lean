import Rigid.AffinoidAlgebra.PowerBounded
import Rigid.Berkovich.RelativeNonempty
import Rigid.TateAlgebra.Multiplicative
import Rigid.TateAlgebra.NormedRing

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The affinoid maximum-modulus theorem

The Gauss point shows first that the Gauss norm on a strict Tate algebra is its spectral norm.  In
particular, the power-bounded elements of a Tate algebra are exactly its closed unit ball.  These
are the base cases for the Noether-normalization proof of the maximum-modulus theorem for general
strict affinoid algebras.
-/

universe u v

namespace Rigid

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]

namespace BerkovichSpectrumOver

variable {A : Type v} [NormedCommRing A] [NormedAlgebra K A]

/-- **Maximum-modulus theorem.** On a nonzero normed algebra, every analytic function attains its
maximum on the relative Berkovich spectrum. -/
theorem exists_maximum [Nontrivial A] (a : A) :
    ∃ x : BerkovichSpectrumOver K A, ∀ y : BerkovichSpectrumOver K A, y a ≤ x a := by
  have hne : (Set.univ : Set (BerkovichSpectrumOver K A)).Nonempty :=
    ⟨Classical.choice (nonempty_of_nontrivial K A), Set.mem_univ _⟩
  obtain ⟨x, -, hx⟩ := (isCompact_univ K A).exists_isMaxOn
    hne (continuous_eval K A a).continuousOn
  exact ⟨x, fun y ↦ hx (Set.mem_univ y)⟩

end BerkovichSpectrumOver

namespace TateAlgebra

/-- The Gauss unit ball in a strict Tate algebra. -/
def unitBallSubring (n : ℕ) : Subring (TateAlgebra K (Fin n)) where
  carrier := {f | ‖f‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {f g} hf hg :=
    (IsUltrametricDist.norm_add_le_max f g).trans (max_le hf hg)
  neg_mem' {f} hf := by simpa using hf
  mul_mem' {f g} hf hg :=
    (norm_mul_le f g).trans (by simpa using mul_le_mul hf hg (norm_nonneg g) zero_le_one)

/-- The relative Berkovich point defined by the multiplicative Gauss norm. -/
noncomputable def gaussPoint (n : ℕ) : BerkovichSpectrumOver K (TateAlgebra K (Fin n)) where
  toBerkovichSpectrum :=
    { seminorm :=
        { toFun := fun f ↦ ‖f‖
          map_zero' := norm_zero
          add_le' := norm_add_le
          neg' := norm_neg
          map_one' := by
            change ‖(1 : TateAlgebra K (Fin n))‖ = 1
            rw [show (1 : TateAlgebra K (Fin n)) = TateAlgebra.C K (Fin n) 1 by
              exact (map_one (algebraMap K (TateAlgebra K (Fin n)))).symm,
              Rigid.norm_C, norm_one]
          map_mul' := norm_mul }
      le_norm' := fun _ ↦ le_rfl }
  map_algebraMap' := fun r ↦ by
    change ‖algebraMap K (TateAlgebra K (Fin n)) r‖ = ‖r‖
    change ‖TateAlgebra.C K (Fin n) r‖ = ‖r‖
    exact Rigid.norm_C K (Fin n) r

@[simp]
theorem gaussPoint_apply (n : ℕ) (f : TateAlgebra K (Fin n)) :
    gaussPoint K n f = ‖f‖ := rfl

/-- The Gauss point realizes the maximum modulus of every function on a strict Tate algebra. -/
theorem le_gaussPoint (n : ℕ) (x : BerkovichSpectrumOver K (TateAlgebra K (Fin n)))
    (f : TateAlgebra K (Fin n)) : x f ≤ gaussPoint K n f :=
  BerkovichSpectrumOver.le_norm K _ x f

/-- In a strict Tate algebra, power-boundedness is equivalent to membership in the Gauss unit
ball. -/
theorem isPowerBounded_iff_norm_le_one {n : ℕ} {f : TateAlgebra K (Fin n)} :
    IsPowerBounded f ↔ ‖f‖ ≤ 1 := by
  constructor
  · intro hf
    simpa using IsPowerBounded.apply_le_one K (gaussPoint K n) hf
  · exact isPowerBounded_of_norm_le_one

@[simp]
theorem mem_unitBallSubring_iff {n : ℕ} {f : TateAlgebra K (Fin n)} :
    f ∈ unitBallSubring K n ↔ IsPowerBounded f := by
  rw [isPowerBounded_iff_norm_le_one]
  rfl

variable {B : Type v} [NormedCommRing B] [NormedAlgebra K B] [IsUltrametricDist B]

/-- The image of the Tate unit ball under a continuous homomorphism is uniformly bounded. -/
theorem bddAbove_image_unitBall (n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) B) :
    BddAbove (Set.range fun b : (unitBallSubring K n).map π.toRingHom ↦ ‖(b : B)‖) := by
  obtain ⟨M, hM, hπ⟩ := SemilinearMapClass.bound_of_continuous π π.continuous
  refine ⟨max 0 M, ?_⟩
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, ha, hab⟩ := b.2
  calc
    ‖(b : B)‖ = ‖π a‖ := congrArg norm hab |>.symm
    _ ≤ M * ‖a‖ := hπ a
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left ha hM.le
    _ ≤ max 0 M := by simp [le_max_right 0 M]

/-- An element integral over the image of a Tate unit ball is power-bounded. -/
theorem isPowerBounded_of_isIntegral_image_unitBall (n : ℕ)
    (π : ContinuousAlgHom K (TateAlgebra K (Fin n)) B) {b : B}
    (hb : IsIntegral ((unitBallSubring K n).map π.toRingHom) b) : IsPowerBounded b :=
  IsPowerBounded.of_isIntegral_over_bounded_subring _
    (bddAbove_image_unitBall K n π) hb

end TateAlgebra

end Rigid
