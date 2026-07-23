import Rigid.AffinoidAlgebra.CompletedLaurentInjective
import Rigid.AffinoidAlgebra.CompletedLaurentQuotient

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Exactness for a two-member Laurent cover

This file completes the left and middle terms of the BGR completed Laurent diagram.  The
codomain is, for the moment, the canonical quotient of restricted Laurent coefficients by
`ζ - f`; identifying that quotient with the iterated rational localization is kept as a separate
normal-form step.
-/

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The diagonal map into the two Laurent rational charts is injective. -/
theorem laurentCharts_diagonal_injective
    (hA : IsAffinoidAlgebra K A) (f : A) :
    Function.Injective (LaurentCharts.diagonal K A f) := by
  apply (injective_iff_map_eq_zero (LaurentCharts.diagonal K A f)).mpr
  intro a ha
  let d : TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) :=
    diagonal K A a
  have hdker : d ∈ LinearMap.ker (chartQuotientMap K A f) := by
    apply LinearMap.mem_ker.mpr
    change LaurentCharts.diagonal K A f a = 0
    exact ha
  rw [ker_chartQuotientMap K A hA f] at hdker
  obtain ⟨pq, hpq⟩ := hdker
  change chartRelations K A f pq = diagonal K A a at hpq
  have hrelation :
      relation K A f (relationFactor K A pq) = 0 := by
    have hcomm := congrArg
      (fun L : TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) →ₗ[K] Series K A ↦ L pq)
      (difference_comp_chartRelations K A f)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at hcomm
    rw [← hcomm, hpq]
    exact (exact K A).apply_apply_eq_zero a
  have hfactor : relationFactor K A pq = 0 := by
    apply relation_injective K A hA f
    simpa using hrelation
  have hpqzero : pq = 0 := by
    apply relationFactor_injective K A
    simpa using hfactor
  have hd : diagonal K A a = 0 := by
    rw [← hpq, hpqzero, map_zero]
  have hd0 : diagonal K A a = diagonal K A 0 := by
    simpa using hd
  exact (shortExact K A).1 hd0

/-- The Laurent-cover sequence is short exact when the overlap is represented by restricted
Laurent coefficients modulo `ζ - f`. -/
theorem auxiliary_shortExact
    (hA : IsAffinoidAlgebra K A) (f : A) :
    Function.Injective (LaurentCharts.diagonal K A f) ∧
      Function.Exact (LaurentCharts.diagonal K A f)
        (auxiliaryDifference K A hA f) ∧
      Function.Surjective (auxiliaryDifference K A hA f) :=
  ⟨laurentCharts_diagonal_injective K A hA f,
    auxiliary_exact K A hA f,
    auxiliaryDifference_surjective K A hA f⟩

end CompletedLaurent

end Rigid
