import Rigid.AffinoidAlgebra.BanachRealization
import Rigid.AffinoidAlgebra.CompletedLaurentRelation
import Rigid.AffinoidAlgebra.LaurentCharts
import Rigid.AffinoidAlgebra.SpectralPresentation

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Quotients in the completed Laurent diagram

This file identifies the two one-variable quotients in the completed Laurent diagram with the
positive and negative Laurent rational localizations.  The only topological point is that the
principal relation ideals are closed: the relative Tate algebras are affinoid, hence Noetherian,
and ideals in a Noetherian nonarchimedean Banach algebra are closed.
-/

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

private theorem range_mul_eq_span_singleton_restrictScalars
    (r : TateAlgebra A (Fin 1))
    (μ : TateAlgebra A (Fin 1) →ₗ[K] TateAlgebra A (Fin 1))
    (hμ : ∀ p, μ p = r * p) :
    LinearMap.range μ = (Ideal.span ({r} : Set (TateAlgebra A (Fin 1)))).restrictScalars K := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    change μ p ∈ Ideal.span ({r} : Set (TateAlgebra A (Fin 1)))
    rw [hμ]
    exact Ideal.mem_span_singleton.mpr ⟨p, by rw [mul_comm]⟩
  · intro hx
    change x ∈ Ideal.span ({r} : Set (TateAlgebra A (Fin 1))) at hx
    obtain ⟨p, hp⟩ := Ideal.mem_span_singleton.mp hx
    refine ⟨p, ?_⟩
    simpa [hμ] using hp.symm

private theorem relativeTate_isNoetherian (hA : IsAffinoidAlgebra K A) :
    IsNoetherianRing (TateAlgebra A (Fin 1)) := by
  obtain ⟨m, π, hπ⟩ :=
    exists_equivalent_quotientNorm_presentation_of_presentation_topology_eq K A
      hA.presentation.n hA.presentation.ideal hA.presentation.equiv
      (topology_eq_affinoidTopology_of_presentation K A
        hA.presentation.n hA.presentation.ideal hA.presentation.equiv)
  exact isNoetherianRing_of_affinoidAlgebra K
    (isAffinoidAlgebra_relativeTateAlgebra_of_surjective K A m π hπ.surjective 1)

private theorem plus_generator_range (f : A) :
    Set.range (fun i : Fin 1 ↦
      TateAlgebra.C A (Fin 1) (1 : A) * tateVariable A (Fin 1) i -
        TateAlgebra.C A (Fin 1) f) =
      {tateVariable A (Fin 1) 0 - TateAlgebra.C A (Fin 1) f} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rw [Fin.eq_zero i]
    simp
  · rintro (rfl : x = _)
    exact ⟨0, by simp⟩

private theorem minus_generator_range (f : A) :
    Set.range (fun i : Fin 1 ↦
      TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) i -
        TateAlgebra.C A (Fin 1) (1 : A)) =
      {-(1 - TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) 0)} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rw [Fin.eq_zero i]
    simp only [Set.mem_singleton_iff, map_one]
    ring
  · rintro (rfl : x = _)
    refine ⟨0, ?_⟩
    simp only [map_one]
    ring

theorem plus_range_eq_rationalLocalizationIdeal_restrictScalars
    (hA : IsAffinoidAlgebra K A) (f : A) :
    LinearMap.range (plusRelation K A f) =
      (rationalLocalizationIdeal A 1 1 (fun _ ↦ f)).restrictScalars K := by
  letI : IsNoetherianRing (TateAlgebra A (Fin 1)) := relativeTate_isNoetherian K A hA
  let r := tateVariable A (Fin 1) 0 - TateAlgebra.C A (Fin 1) f
  have hspanClosed :
      IsClosed ((Ideal.span ({r} : Set (TateAlgebra A (Fin 1))) :
        Ideal (TateAlgebra A (Fin 1))) : Set (TateAlgebra A (Fin 1))) :=
    isClosed_ideal_of_isNoetherianRing K _
  rw [rationalLocalizationIdeal, plus_generator_range A f,
    Ideal.closure_eq_of_isClosed _ hspanClosed]
  exact range_mul_eq_span_singleton_restrictScalars K A r
    (plusRelation K A f) (fun _ ↦ rfl)

theorem minus_range_eq_rationalLocalizationIdeal_restrictScalars
    (hA : IsAffinoidAlgebra K A) (f : A) :
    LinearMap.range (minusRelation K A f) =
      (rationalLocalizationIdeal A 1 f (fun _ ↦ 1)).restrictScalars K := by
  letI : IsNoetherianRing (TateAlgebra A (Fin 1)) := relativeTate_isNoetherian K A hA
  let r := 1 - TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) 0
  have hspanClosed :
      IsClosed ((Ideal.span ({-r} : Set (TateAlgebra A (Fin 1))) :
        Ideal (TateAlgebra A (Fin 1))) : Set (TateAlgebra A (Fin 1))) :=
    isClosed_ideal_of_isNoetherianRing K _
  rw [rationalLocalizationIdeal, minus_generator_range A f,
    Ideal.closure_eq_of_isClosed _ hspanClosed]
  have hneg :
      (Ideal.span ({-r} : Set (TateAlgebra A (Fin 1)))).restrictScalars K =
        (Ideal.span ({r} : Set (TateAlgebra A (Fin 1)))).restrictScalars K := by
    congr 1
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro x (rfl : x = -r)
      exact (Ideal.span ({r} : Set (TateAlgebra A (Fin 1)))).neg_mem
        (Ideal.mem_span_singleton_self r)
    · apply Ideal.span_le.mpr
      rintro x (rfl : x = r)
      have hnr :
          -r ∈ Ideal.span ({-r} : Set (TateAlgebra A (Fin 1))) :=
        Ideal.mem_span_singleton_self (-r)
      change r ∈ Ideal.span ({-r} : Set (TateAlgebra A (Fin 1)))
      simpa only [neg_neg] using
        (Ideal.span ({-r} : Set (TateAlgebra A (Fin 1)))).neg_mem hnr
  rw [hneg]
  exact range_mul_eq_span_singleton_restrictScalars K A r
    (minusRelation K A f) (fun _ ↦ rfl)

/-- The product of the two quotient maps defining the positive and negative Laurent charts. -/
noncomputable def chartQuotientMap (f : A) :
    TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) →ₗ[K]
      LaurentCharts.Plus K A f × LaurentCharts.Minus K A f :=
  (RationalLocalization.quotientMap K A 1 1 (fun _ ↦ f)).toLinearMap.prodMap
    (RationalLocalization.quotientMap K A 1 f (fun _ ↦ 1)).toLinearMap

@[simp]
theorem chartQuotientMap_apply (f : A)
    (p q : TateAlgebra A (Fin 1)) :
    chartQuotientMap K A f (p, q) =
      (RationalLocalization.quotientMap K A 1 1 (fun _ ↦ f) p,
        RationalLocalization.quotientMap K A 1 f (fun _ ↦ 1) q) :=
  rfl

theorem chartQuotientMap_surjective (f : A) :
    Function.Surjective (chartQuotientMap K A f) := by
  rintro ⟨p, q⟩
  obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective p
  obtain ⟨q', rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨(p', q'), rfl⟩

theorem ker_chartQuotientMap (hA : IsAffinoidAlgebra K A) (f : A) :
    LinearMap.ker (chartQuotientMap K A f) =
      LinearMap.range (chartRelations K A f) := by
  ext pq
  constructor
  · intro hpq
    have hp :
        RationalLocalization.quotientMap K A 1 1 (fun _ ↦ f) pq.1 = 0 := by
      have h := LinearMap.mem_ker.mp hpq
      exact congrArg Prod.fst h
    have hq :
        RationalLocalization.quotientMap K A 1 f (fun _ ↦ 1) pq.2 = 0 := by
      have h := LinearMap.mem_ker.mp hpq
      exact congrArg Prod.snd h
    have hp' :
        pq.1 ∈ LinearMap.range (plusRelation K A f) := by
      rw [plus_range_eq_rationalLocalizationIdeal_restrictScalars K A hA f]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hp
    have hq' :
        pq.2 ∈ LinearMap.range (minusRelation K A f) := by
      rw [minus_range_eq_rationalLocalizationIdeal_restrictScalars K A hA f]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hq
    obtain ⟨p, hp⟩ := hp'
    obtain ⟨q, hq⟩ := hq'
    refine ⟨(p, q), ?_⟩
    exact Prod.ext hp hq
  · rintro ⟨pq', rfl⟩
    apply LinearMap.mem_ker.mpr
    rcases pq' with ⟨p, q⟩
    apply Prod.ext
    · change Ideal.Quotient.mk
        (rationalLocalizationIdeal A 1 1 (fun _ ↦ f)) (plusRelation K A f p) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change plusRelation K A f p ∈
        (rationalLocalizationIdeal A 1 1 (fun _ ↦ f)).restrictScalars K
      rw [← plus_range_eq_rationalLocalizationIdeal_restrictScalars K A hA f]
      exact ⟨p, rfl⟩
    · change Ideal.Quotient.mk
        (rationalLocalizationIdeal A 1 f (fun _ ↦ 1)) (minusRelation K A f q) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change minusRelation K A f q ∈
        (rationalLocalizationIdeal A 1 f (fun _ ↦ 1)).restrictScalars K
      rw [← minus_range_eq_rationalLocalizationIdeal_restrictScalars K A hA f]
      exact ⟨q, rfl⟩

/-- The quotient of the two completed chart algebras by their relation ranges is the product of
the two Laurent rational localizations. -/
noncomputable def chartRelationQuotientEquiv
    (hA : IsAffinoidAlgebra K A) (f : A) :
    ChartRelationQuotient K A f ≃ₗ[K]
      LaurentCharts.Plus K A f × LaurentCharts.Minus K A f :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (chartRelations K A f))
      (LinearMap.ker (chartQuotientMap K A f))
      (ker_chartQuotientMap K A hA f).symm).trans
    ((chartQuotientMap K A f).quotKerEquivOfSurjective
      (chartQuotientMap_surjective K A f))

@[simp]
theorem chartRelationQuotientEquiv_mk
    (hA : IsAffinoidAlgebra K A) (f : A)
    (pq : TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1)) :
    chartRelationQuotientEquiv K A hA f (Submodule.Quotient.mk pq) =
      chartQuotientMap K A f pq :=
  rfl

/-- Remove the harmless quotient by the zero submodule in the source of the descended row. -/
noncomputable def botQuotientEquiv : (A ⧸ (⊥ : Submodule K A)) ≃ₗ[K] A :=
  Submodule.quotEquivOfEqBot (⊥ : Submodule K A) rfl

/-- The diagonal after identifying the chart-relation quotient with the two rational charts. -/
noncomputable def auxiliaryDiagonal
    (hA : IsAffinoidAlgebra K A) (f : A) :
    A →ₗ[K] LaurentCharts.Plus K A f × LaurentCharts.Minus K A f :=
  (chartRelationQuotientEquiv K A hA f).toLinearMap.comp
    ((quotientDiagonal K A f).comp (botQuotientEquiv K A).symm.toLinearMap)

/-- Laurent difference with values in the completed Laurent relation quotient. -/
noncomputable def auxiliaryDifference
    (hA : IsAffinoidAlgebra K A) (f : A) :
    LaurentCharts.Plus K A f × LaurentCharts.Minus K A f →ₗ[K]
      LaurentRelationQuotient K A f :=
  (quotientDifference K A f).comp
    (chartRelationQuotientEquiv K A hA f).symm.toLinearMap

@[simp]
theorem auxiliaryDiagonal_apply
    (hA : IsAffinoidAlgebra K A) (f a : A) :
    auxiliaryDiagonal K A hA f a = LaurentCharts.diagonal K A f a := by
  change chartQuotientMap K A f
    (TateAlgebra.C A (Fin 1) a, TateAlgebra.C A (Fin 1) a) =
      (LaurentCharts.plusMap K A f a, LaurentCharts.minusMap K A f a)
  apply Prod.ext <;> rfl

/-- Exactness at the two chart terms, with the overlap represented by completed Laurent
coefficients modulo `ζ-f`. -/
theorem auxiliary_exact
    (hA : IsAffinoidAlgebra K A) (f : A) :
    Function.Exact (LaurentCharts.diagonal K A f)
      (auxiliaryDifference K A hA f) := by
  have hmiddle :
      Function.Exact
        ((chartRelationQuotientEquiv K A hA f).toLinearMap.comp
          (quotientDiagonal K A f))
        ((quotientDifference K A f).comp
          (chartRelationQuotientEquiv K A hA f).symm.toLinearMap) :=
    (LinearEquiv.conj_exact_iff_exact
      (quotientDiagonal K A f) (quotientDifference K A f)
      (chartRelationQuotientEquiv K A hA f)).2
        (quotient_exact K A f)
  have hsource :
      Function.Exact (auxiliaryDiagonal K A hA f)
        (auxiliaryDifference K A hA f) := by
    simpa only [auxiliaryDiagonal, auxiliaryDifference, LinearMap.comp_assoc] using
      (LinearEquiv.precomp_exact_iff_exact
        (f := (chartRelationQuotientEquiv K A hA f).toLinearMap.comp
          (quotientDiagonal K A f))
        (g := (quotientDifference K A f).comp
          (chartRelationQuotientEquiv K A hA f).symm.toLinearMap)
        (e := (botQuotientEquiv K A).symm)).mpr hmiddle
  have hdiag :
      auxiliaryDiagonal K A hA f = LaurentCharts.diagonal K A f := by
    apply LinearMap.ext
    intro a
    exact auxiliaryDiagonal_apply K A hA f a
  rw [← hdiag]
  exact hsource

/-- The auxiliary Laurent difference is onto. -/
theorem auxiliaryDifference_surjective
    (hA : IsAffinoidAlgebra K A) (f : A) :
    Function.Surjective (auxiliaryDifference K A hA f) :=
  (quotientDifference_surjective K A f).comp
    (chartRelationQuotientEquiv K A hA f).symm.surjective

end CompletedLaurent

end Rigid
