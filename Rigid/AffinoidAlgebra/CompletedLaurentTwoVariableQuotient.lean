import Rigid.AffinoidAlgebra.CompletedLaurentTwoVariable
import Mathlib.LinearAlgebra.Isomorphisms

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The quotient by `TS - 1`

Diagonal summation identifies the two-variable Tate algebra modulo multiplication by `TS - 1`
with restricted Laurent coefficient families.  This is the analytic normal form underlying the
overlap in a Laurent cover.
-/

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The two-variable Tate algebra modulo the relation `TS - 1`. -/
abbrev UnitRelationQuotient :=
  TateAlgebra A (Fin 2) ⧸ LinearMap.range (unitRelation K A)

/-- Diagonal summation gives the normal form of the quotient by `TS - 1`. -/
noncomputable def unitRelationQuotientEquiv :
    UnitRelationQuotient K A ≃ₗ[K] Series K A :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (unitRelation K A))
      (LinearMap.ker (twoVariableNormal K A))
      (range_unitRelation_eq_ker_twoVariableNormal K A)).trans
    ((twoVariableNormal K A).quotKerEquivOfSurjective
      (twoVariableNormal_surjective K A))

@[simp]
theorem unitRelationQuotientEquiv_mk
    (p : TateAlgebra A (Fin 2)) :
    unitRelationQuotientEquiv K A (Submodule.Quotient.mk p) =
      twoVariableNormal K A p := by
  rw [unitRelationQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

end CompletedLaurent

end Rigid
