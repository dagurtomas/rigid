import Rigid.AffinoidAlgebra.CompletedLaurentTwoVariableRelation
import Rigid.AffinoidAlgebra.CompletedLaurentQuotient
import Mathlib.LinearAlgebra.Isomorphisms

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# A direct rational localization for a Laurent intersection

The locus `|f| = 1` is represented by the rational datum with denominator `f` and numerators
`f², 1`.  Its two coordinates are therefore `T = f` and `S = f⁻¹`.  The defining ideal agrees
with `(TS - 1, T - f)`, which connects this rational localization to the restricted Laurent
normal form.
-/

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- Numerators for the rational domain `|f| = 1`, ordered as `T = f` and `S = f⁻¹`. -/
def laurentIntersectionNumerator (f : A) : Fin 2 → A :=
  ![f ^ 2, 1]

/-- A direct rational localization representing the Laurent intersection `|f| = 1`. -/
abbrev LaurentIntersection (f : A) :=
  RationalLocalization K A 2 f (laurentIntersectionNumerator A f)

private noncomputable def unitGenerator : TateAlgebra A (Fin 2) :=
  tateVariable A (Fin 2) 0 * tateVariable A (Fin 2) 1 - 1

private noncomputable def firstGenerator (f : A) : TateAlgebra A (Fin 2) :=
  tateVariable A (Fin 2) 0 - TateAlgebra.C A (Fin 2) f

private theorem range_mul_eq_span_singleton_restrictScalars
    (r : TateAlgebra A (Fin 2))
    (μ : TateAlgebra A (Fin 2) →ₗ[K] TateAlgebra A (Fin 2))
    (hμ : ∀ p, μ p = r * p) :
    LinearMap.range μ =
      (Ideal.span ({r} : Set (TateAlgebra A (Fin 2)))).restrictScalars K := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change μ p ∈ Ideal.span ({r} : Set (TateAlgebra A (Fin 2)))
    rw [hμ]
    exact Ideal.mem_span_singleton.mpr ⟨p, by rw [mul_comm]⟩
  · intro hx
    change x ∈ Ideal.span ({r} : Set (TateAlgebra A (Fin 2))) at hx
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hx
    refine ⟨p, ?_⟩
    simpa [hμ] using hp.symm

private theorem range_unitRelation :
    LinearMap.range (unitRelation K A) =
      (Ideal.span ({unitGenerator A} :
        Set (TateAlgebra A (Fin 2)))).restrictScalars K :=
  range_mul_eq_span_singleton_restrictScalars K A (unitGenerator A)
    (unitRelation K A) (fun _ ↦ rfl)

private theorem range_firstVariableRelation (f : A) :
    LinearMap.range (firstVariableRelation K A f) =
      (Ideal.span ({firstGenerator A f} :
        Set (TateAlgebra A (Fin 2)))).restrictScalars K :=
  range_mul_eq_span_singleton_restrictScalars K A (firstGenerator A f)
    (firstVariableRelation K A f) (fun _ ↦ rfl)

private theorem sup_relation_ranges (f : A) :
    LinearMap.range (unitRelation K A) ⊔
        LinearMap.range (firstVariableRelation K A f) =
      (Ideal.span ({unitGenerator A, firstGenerator A f} :
        Set (TateAlgebra A (Fin 2)))).restrictScalars K := by
  rw [range_unitRelation K A, range_firstVariableRelation K A f]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    change y ∈ Ideal.span ({unitGenerator A} :
      Set (TateAlgebra A (Fin 2))) at hy
    change z ∈ Ideal.span ({firstGenerator A f} :
      Set (TateAlgebra A (Fin 2))) at hz
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hz
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by rw [ha, hb]; ring⟩
  · intro hx
    change x ∈ Ideal.span ({unitGenerator A, firstGenerator A f} :
      Set (TateAlgebra A (Fin 2))) at hx
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hx
    apply Submodule.mem_sup.mpr
    refine ⟨a * unitGenerator A, ?_, b * firstGenerator A f, ?_, hab⟩
    · change a * unitGenerator A ∈
        Ideal.span ({unitGenerator A} : Set (TateAlgebra A (Fin 2)))
      exact (Ideal.span ({unitGenerator A} :
        Set (TateAlgebra A (Fin 2)))).mul_mem_left a
        (Ideal.mem_span_singleton_self (unitGenerator A))
    · change b * firstGenerator A f ∈
        Ideal.span ({firstGenerator A f} : Set (TateAlgebra A (Fin 2)))
      exact (Ideal.span ({firstGenerator A f} :
        Set (TateAlgebra A (Fin 2)))).mul_mem_left b
        (Ideal.mem_span_singleton_self (firstGenerator A f))

private noncomputable def rationalFirstGenerator (f : A) :
    TateAlgebra A (Fin 2) :=
  TateAlgebra.C A (Fin 2) f * tateVariable A (Fin 2) 0 -
    TateAlgebra.C A (Fin 2) (f ^ 2)

private noncomputable def rationalSecondGenerator (f : A) :
    TateAlgebra A (Fin 2) :=
  TateAlgebra.C A (Fin 2) f * tateVariable A (Fin 2) 1 - 1

private theorem relationIdeal_eq_rationalIdeal (f : A) :
    Ideal.span ({unitGenerator A, firstGenerator A f} :
        Set (TateAlgebra A (Fin 2))) =
      Ideal.span ({rationalFirstGenerator A f, rationalSecondGenerator A f} :
        Set (TateAlgebra A (Fin 2))) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · apply Ideal.mem_span_pair.mpr
      refine ⟨tateVariable A (Fin 2) 1 ^ 2,
        1 - tateVariable A (Fin 2) 1 * firstGenerator A f, ?_⟩
      simp only [unitGenerator, firstGenerator, rationalFirstGenerator,
        rationalSecondGenerator, map_pow]
      ring
    · apply Ideal.mem_span_pair.mpr
      refine ⟨tateVariable A (Fin 2) 1,
        -(firstGenerator A f), ?_⟩
      simp only [firstGenerator, rationalFirstGenerator,
        rationalSecondGenerator, map_pow]
      ring
  · apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · apply Ideal.mem_span_pair.mpr
      refine ⟨0, TateAlgebra.C A (Fin 2) f, ?_⟩
      simp only [unitGenerator, firstGenerator, rationalFirstGenerator,
        map_pow, zero_mul, zero_add]
      ring
    · apply Ideal.mem_span_pair.mpr
      refine ⟨1, -tateVariable A (Fin 2) 1, ?_⟩
      simp only [unitGenerator, firstGenerator, rationalSecondGenerator,
        one_mul]
      ring

private theorem relativeTate_two_isNoetherian
    (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing (TateAlgebra A (Fin 2)) := by
  obtain ⟨m, π, hπ⟩ :=
    exists_equivalent_quotientNorm_presentation_of_presentation_topology_eq K A
      hA.presentation.n hA.presentation.ideal hA.presentation.equiv
      (topology_eq_affinoidTopology_of_presentation K A
        hA.presentation.n hA.presentation.ideal hA.presentation.equiv)
  exact isNoetherianRing_of_affinoidAlgebra K
    (isAffinoidAlgebra_relativeTateAlgebra_of_surjective K A m π hπ.surjective 2)

private theorem rational_generator_range (f : A) :
    Set.range (fun i : Fin 2 ↦
      TateAlgebra.C A (Fin 2) f * tateVariable A (Fin 2) i -
        TateAlgebra.C A (Fin 2) (laurentIntersectionNumerator A f i)) =
      {rationalFirstGenerator A f, rationalSecondGenerator A f} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Set.mem_singleton _)
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem sup_relation_ranges_eq_rationalLocalizationIdeal
    (hA : IsAffinoidAlgebra K A) (f : A) :
    LinearMap.range (unitRelation K A) ⊔
        LinearMap.range (firstVariableRelation K A f) =
      (rationalLocalizationIdeal A 2 f
        (laurentIntersectionNumerator A f)).restrictScalars K := by
  letI : IsNoetherianRing (TateAlgebra A (Fin 2)) :=
    relativeTate_two_isNoetherian K A hA
  let J : Ideal (TateAlgebra A (Fin 2)) :=
    Ideal.span ({rationalFirstGenerator A f, rationalSecondGenerator A f} :
      Set (TateAlgebra A (Fin 2)))
  have hJclosed : IsClosed (J : Set (TateAlgebra A (Fin 2))) :=
    isClosed_ideal_of_isNoetherianRing K J
  rw [sup_relation_ranges K A f, relationIdeal_eq_rationalIdeal A f]
  change J.restrictScalars K =
    (rationalLocalizationIdeal A 2 f
      (laurentIntersectionNumerator A f)).restrictScalars K
  rw [rationalLocalizationIdeal, rational_generator_range A f,
    Ideal.closure_eq_of_isClosed J hJclosed]

private theorem ker_laurentIntersectionQuotientMap
    (hA : IsAffinoidAlgebra K A) (f : A) :
    LinearMap.ker
        (RationalLocalization.quotientMap K A 2 f
          (laurentIntersectionNumerator A f)).toLinearMap =
      LinearMap.range (unitRelation K A) ⊔
        LinearMap.range (firstVariableRelation K A f) := by
  rw [sup_relation_ranges_eq_rationalLocalizationIdeal K A hA f]
  ext p
  change
    RationalLocalization.quotientMap K A 2 f
      (laurentIntersectionNumerator A f) p = 0 ↔
      p ∈ rationalLocalizationIdeal A 2 f
        (laurentIntersectionNumerator A f)
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The direct rational localization of `|f| = 1` has the restricted Laurent normal form. -/
noncomputable def twoRelationQuotientEquivLaurentIntersection
    (hA : IsAffinoidAlgebra K A) (f : A) :
    TwoRelationQuotient K A f ≃ₗ[K] LaurentIntersection K A f :=
  (Submodule.quotientQuotientEquivQuotientSup
      (LinearMap.range (unitRelation K A))
      (LinearMap.range (firstVariableRelation K A f))).trans
    ((Submodule.quotEquivOfEq
      (LinearMap.range (unitRelation K A) ⊔
        LinearMap.range (firstVariableRelation K A f))
      (LinearMap.ker
        (RationalLocalization.quotientMap K A 2 f
          (laurentIntersectionNumerator A f)).toLinearMap)
      (ker_laurentIntersectionQuotientMap K A hA f).symm).trans
        ((RationalLocalization.quotientMap K A 2 f
          (laurentIntersectionNumerator A f)).toLinearMap.quotKerEquivOfSurjective
            Ideal.Quotient.mk_surjective))

/-- The completed Laurent recurrence quotient is the direct Laurent intersection algebra. -/
noncomputable def laurentRelationQuotientEquivLaurentIntersection
    (hA : IsAffinoidAlgebra K A) (f : A) :
    LaurentRelationQuotient K A f ≃ₗ[K] LaurentIntersection K A f :=
  (twoRelationQuotientEquiv K A f).symm.trans
    (twoRelationQuotientEquivLaurentIntersection K A hA f)

@[simp]
theorem laurentRelationQuotientEquivLaurentIntersection_mk
    (hA : IsAffinoidAlgebra K A) (f : A) (c : Series K A) :
    laurentRelationQuotientEquivLaurentIntersection K A hA f
        (Submodule.Quotient.mk c) =
      RationalLocalization.quotientMap K A 2 f
        (laurentIntersectionNumerator A f) (axisSeries K A c) := by
  let x : TwoRelationQuotient K A f :=
    Submodule.Quotient.mk
      (Submodule.Quotient.mk (axisSeries K A c))
  have hx :
      twoRelationQuotientEquiv K A f x = Submodule.Quotient.mk c := by
    change Submodule.Quotient.mk
      (unitRelationQuotientEquiv K A
        (Submodule.Quotient.mk (axisSeries K A c))) =
      Submodule.Quotient.mk c
    rw [unitRelationQuotientEquiv_mk, twoVariableNormal_axisSeries]
  rw [← hx, laurentRelationQuotientEquivLaurentIntersection,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end CompletedLaurent

end Rigid
