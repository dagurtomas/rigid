import Rigid.AffinoidAlgebra.LaurentCoverExact
import Rigid.AffinoidAlgebra.LaurentIntersection
import Mathlib.RingTheory.MvPowerSeries.Rename

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The Laurent chart maps into the direct intersection

This file connects the completed Laurent normal form to the actual restriction maps.  The
intersection `|f| = 1` is represented directly by the rational datum `(f; f², 1)`.  Its
coordinates are the images of `f` and `f⁻¹`, so both one-variable Laurent charts map to it.
-/

open Filter

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The datum `(f; f², 1)` is rational because one of its numerators is `1`. -/
theorem laurentIntersection_isRational (f : A) :
    IsRationalDatum f (laurentIntersectionNumerator A f) := by
  rw [IsRationalDatum]
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  right
  exact ⟨1, by simp [laurentIntersectionNumerator]⟩

/-- The ambient map into the direct Laurent intersection. -/
noncomputable def laurentIntersectionMap (f : A) :
    ContinuousAlgHom K A (LaurentIntersection K A f) :=
  RationalLocalization.baseMap K A 2 f (laurentIntersectionNumerator A f)

/-- The coordinate which equals `f` on the direct Laurent intersection. -/
noncomputable def laurentIntersectionT (f : A) : LaurentIntersection K A f :=
  RationalLocalization.coordinate K A 2 f (laurentIntersectionNumerator A f) 0

/-- The coordinate which equals `f⁻¹` on the direct Laurent intersection. -/
noncomputable def laurentIntersectionS (f : A) : LaurentIntersection K A f :=
  RationalLocalization.coordinate K A 2 f (laurentIntersectionNumerator A f) 1

theorem isPowerBounded_laurentIntersectionT (f : A) :
    IsPowerBounded (laurentIntersectionT K A f) :=
  RationalLocalization.isPowerBounded_coordinate K A 2 f
    (laurentIntersectionNumerator A f) 0

theorem isPowerBounded_laurentIntersectionS (f : A) :
    IsPowerBounded (laurentIntersectionS K A f) :=
  RationalLocalization.isPowerBounded_coordinate K A 2 f
    (laurentIntersectionNumerator A f) 1

@[simp]
theorem laurentIntersectionMap_mul_S (f : A) :
    laurentIntersectionMap K A f f * laurentIntersectionS K A f = 1 := by
  exact RationalLocalization.baseMap_denominator_mul_coordinate K A 2 f
    (laurentIntersectionNumerator A f) 1

@[simp]
theorem laurentIntersectionT_eq_map (f : A) :
    laurentIntersectionT K A f = laurentIntersectionMap K A f f := by
  have hunit :
      IsUnit (laurentIntersectionMap K A f f) :=
    RationalLocalization.isUnit_baseMap_denominator K A 2 f
      (laurentIntersectionNumerator A f) (laurentIntersection_isRational A f)
  apply hunit.mul_left_cancel
  change
    RationalLocalization.baseMap K A 2 f (laurentIntersectionNumerator A f) f *
        RationalLocalization.coordinate K A 2 f
          (laurentIntersectionNumerator A f) 0 =
      RationalLocalization.baseMap K A 2 f (laurentIntersectionNumerator A f) f *
        RationalLocalization.baseMap K A 2 f
          (laurentIntersectionNumerator A f) f
  rw [RationalLocalization.baseMap_denominator_mul_coordinate]
  change
    RationalLocalization.baseMap K A 2 f (laurentIntersectionNumerator A f) (f ^ 2) =
      RationalLocalization.baseMap K A 2 f (laurentIntersectionNumerator A f) f *
        RationalLocalization.baseMap K A 2 f (laurentIntersectionNumerator A f) f
  rw [map_pow, pow_two]

/-- Restriction from the positive Laurent chart to the direct intersection. -/
noncomputable def plusToLaurentIntersection (f : A) :
    ContinuousAlgHom K (LaurentCharts.Plus K A f) (LaurentIntersection K A f) :=
  RationalLocalization.lift K A 1 1 (fun _ ↦ f)
    (laurentIntersectionMap K A f) (fun _ ↦ laurentIntersectionT K A f)
    (fun _ ↦ isPowerBounded_laurentIntersectionT K A f)
    (fun _ ↦ by simp)

/-- Restriction from the negative Laurent chart to the direct intersection. -/
noncomputable def minusToLaurentIntersection (f : A) :
    ContinuousAlgHom K (LaurentCharts.Minus K A f) (LaurentIntersection K A f) :=
  RationalLocalization.lift K A 1 f (fun _ ↦ 1)
    (laurentIntersectionMap K A f) (fun _ ↦ laurentIntersectionS K A f)
    (fun _ ↦ isPowerBounded_laurentIntersectionS K A f)
    (fun _ ↦ by simp)

@[simp]
theorem plusToLaurentIntersection_comp_plusMap (f : A) :
    (plusToLaurentIntersection K A f).comp (LaurentCharts.plusMap K A f) =
      laurentIntersectionMap K A f :=
  RationalLocalization.lift_comp_baseMap K A 1 1 (fun _ ↦ f)
    (laurentIntersectionMap K A f) (fun _ ↦ laurentIntersectionT K A f)
    (fun _ ↦ isPowerBounded_laurentIntersectionT K A f) (fun _ ↦ by simp)

@[simp]
theorem minusToLaurentIntersection_comp_minusMap (f : A) :
    (minusToLaurentIntersection K A f).comp (LaurentCharts.minusMap K A f) =
      laurentIntersectionMap K A f :=
  RationalLocalization.lift_comp_baseMap K A 1 f (fun _ ↦ 1)
    (laurentIntersectionMap K A f) (fun _ ↦ laurentIntersectionS K A f)
    (fun _ ↦ isPowerBounded_laurentIntersectionS K A f) (fun _ ↦ by simp)

/-- Difference of restriction maps with values in the direct Laurent intersection. -/
noncomputable def directDifference (f : A) :
    LaurentCharts.Plus K A f × LaurentCharts.Minus K A f →ₗ[K]
      LaurentIntersection K A f :=
  (plusToLaurentIntersection K A f).toLinearMap.comp (LinearMap.fst K _ _) -
    (minusToLaurentIntersection K A f).toLinearMap.comp (LinearMap.snd K _ _)

@[simp]
theorem directDifference_apply (f : A)
    (p : LaurentCharts.Plus K A f) (q : LaurentCharts.Minus K A f) :
    directDifference K A f (p, q) =
      plusToLaurentIntersection K A f p - minusToLaurentIntersection K A f q :=
  rfl

private noncomputable def axisEmbedding (i : Fin 2) : Fin 1 ↪ Fin 2 where
  toFun := fun _ ↦ i
  inj' x y _ := Subsingleton.elim x y

private noncomputable def algebraicAxisMap (i : Fin 2) :
    TateAlgebra A (Fin 1) →ₐ[K] TateAlgebra A (Fin 2) := by
  let e := axisEmbedding i
  refine
    { toFun := fun p ↦ ⟨MvPowerSeries.rename e p.1, ?_⟩
      map_one' := Subtype.ext (map_one (MvPowerSeries.rename e))
      map_mul' := fun p q ↦ Subtype.ext (map_mul (MvPowerSeries.rename e) p.1 q.1)
      map_zero' := Subtype.ext (map_zero (MvPowerSeries.rename e))
      map_add' := fun p q ↦ Subtype.ext (map_add (MvPowerSeries.rename e) p.1 q.1)
      commutes' := fun c ↦ Subtype.ext (by
        change MvPowerSeries.rename e (MvPowerSeries.C (algebraMap K A c)) =
          MvPowerSeries.C (algebraMap K A c)
        simp) }
  change MvPowerSeries.IsRestricted (fun _ : Fin 2 ↦ (1 : ℝ))
    (MvPowerSeries.rename e p.1)
  have hrename : Tendsto
      (fun x : Fin 2 →₀ ℕ ↦
        ‖MvPowerSeries.coeff x (MvPowerSeries.rename e p.1)‖) cofinite (nhds 0) := by
    rw [tendsto_def]
    intro s hs
    have hzero : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
    have hp : {x : Fin 1 →₀ ℕ | ‖MvPowerSeries.coeff x p.1‖ ∈ s} ∈ cofinite :=
      (tendsto_norm_coeff_zero A (Fin 1) p).eventually hs
    rw [mem_cofinite] at hp ⊢
    refine hp.image (Finsupp.embDomain e) |>.subset ?_
    intro x hx
    simp only [Set.mem_compl_iff] at hx ⊢
    by_cases hxr : x ∈ Set.range (Finsupp.embDomain e)
    · obtain ⟨y, rfl⟩ := hxr
      refine ⟨y, ?_, rfl⟩
      simpa using hx
    · exfalso
      apply hx
      change ‖MvPowerSeries.coeff x (MvPowerSeries.rename e p.1)‖ ∈ s
      rw [MvPowerSeries.coeff_rename_eq_zero]
      · simpa using hzero
      · simpa [Finsupp.embDomain_eq_mapDomain] using hxr
  simpa [MvPowerSeries.IsRestricted, Finsupp.prod] using hrename

private theorem norm_algebraicAxisMap_le (i : Fin 2) (p : TateAlgebra A (Fin 1)) :
    ‖algebraicAxisMap K A i p‖ ≤ ‖p‖ := by
  rw [norm_eq_sSup_coeff]
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨e, rfl⟩
  by_cases he : e ∈ Set.range (Finsupp.embDomain (axisEmbedding i))
  · obtain ⟨d, rfl⟩ := he
    change ‖MvPowerSeries.coeff (Finsupp.embDomain (axisEmbedding i) d)
      (MvPowerSeries.rename (axisEmbedding i) p.1)‖ ≤ ‖p‖
    rw [MvPowerSeries.coeff_embDomain_rename]
    exact norm_coeff_le_norm A (Fin 1) p d
  · change ‖MvPowerSeries.coeff e
      (MvPowerSeries.rename (axisEmbedding i) p.1)‖ ≤ ‖p‖
    rw [MvPowerSeries.coeff_rename_eq_zero]
    · simp
    · simpa [Finsupp.embDomain_eq_mapDomain] using he

/-- Embed a one-variable Tate algebra along one of the two coordinate axes. -/
noncomputable def axisMap (i : Fin 2) :
    ContinuousAlgHom K (TateAlgebra A (Fin 1)) (TateAlgebra A (Fin 2)) :=
  { algebraicAxisMap K A i with
    cont := AddMonoidHomClass.continuous_of_bound
      (algebraicAxisMap K A i) 1 (fun p ↦ by
        simpa using norm_algebraicAxisMap_le K A i p) }

@[simp]
theorem axisMap_C (i : Fin 2) (a : A) :
    axisMap K A i (TateAlgebra.C A (Fin 1) a) =
      TateAlgebra.C A (Fin 2) a := by
  apply Subtype.ext
  simp [axisMap, algebraicAxisMap]

@[simp]
theorem axisMap_tateVariable (i : Fin 2) :
    axisMap K A i (tateVariable A (Fin 1) 0) =
      tateVariable A (Fin 2) i := by
  apply Subtype.ext
  change MvPowerSeries.rename (axisEmbedding i)
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 1) A) =
    (MvPowerSeries.X i : MvPowerSeries (Fin 2) A)
  simp [axisEmbedding]

private theorem embDomain_axis_zero_oneExponent (n : ℕ) :
    Finsupp.embDomain (axisEmbedding (0 : Fin 2)) (oneExponent n) =
      twoExponent n 0 := by
  ext i
  fin_cases i <;>
    simp [axisEmbedding, oneExponent, twoExponent]

private theorem embDomain_axis_one_oneExponent (n : ℕ) :
    Finsupp.embDomain (axisEmbedding (1 : Fin 2)) (oneExponent n) =
      twoExponent 0 n := by
  ext i
  fin_cases i <;>
    simp [axisEmbedding, oneExponent, twoExponent]

private theorem coeff_axisMap_zero (p : TateAlgebra A (Fin 1)) (i j : ℕ) :
    TateAlgebra.coeff A (Fin 2) (twoExponent i j) (axisMap K A 0 p) =
      if j = 0 then TateAlgebra.coeff A (Fin 1) (oneExponent i) p else 0 := by
  by_cases hj : j = 0
  · subst j
    rw [if_pos rfl, ← embDomain_axis_zero_oneExponent i]
    exact MvPowerSeries.coeff_embDomain_rename (axisEmbedding (0 : Fin 2)) p.1
      (oneExponent i)
  · rw [if_neg hj]
    change MvPowerSeries.coeff (twoExponent i j)
      (MvPowerSeries.rename (axisEmbedding (0 : Fin 2)) p.1) = 0
    apply MvPowerSeries.coeff_rename_eq_zero
    intro hrange
    obtain ⟨d, hd⟩ := hrange
    rw [← Finsupp.embDomain_eq_mapDomain] at hd
    have h1 := congrArg (fun e : Fin 2 →₀ ℕ ↦ e 1) hd
    simp [axisEmbedding, twoExponent, Finsupp.embDomain_apply] at h1
    exact hj h1.symm

private theorem coeff_axisMap_one (p : TateAlgebra A (Fin 1)) (i j : ℕ) :
    TateAlgebra.coeff A (Fin 2) (twoExponent i j) (axisMap K A 1 p) =
      if i = 0 then TateAlgebra.coeff A (Fin 1) (oneExponent j) p else 0 := by
  by_cases hi : i = 0
  · subst i
    rw [if_pos rfl, ← embDomain_axis_one_oneExponent j]
    exact MvPowerSeries.coeff_embDomain_rename (axisEmbedding (1 : Fin 2)) p.1
      (oneExponent j)
  · rw [if_neg hi]
    change MvPowerSeries.coeff (twoExponent i j)
      (MvPowerSeries.rename (axisEmbedding (1 : Fin 2)) p.1) = 0
    apply MvPowerSeries.coeff_rename_eq_zero
    intro hrange
    obtain ⟨d, hd⟩ := hrange
    rw [← Finsupp.embDomain_eq_mapDomain] at hd
    have h0 := congrArg (fun e : Fin 2 →₀ ℕ ↦ e 0) hd
    simp [axisEmbedding, twoExponent, Finsupp.embDomain_apply] at h0
    exact hi h0.symm

theorem axisSeries_positive (p : TateAlgebra A (Fin 1)) :
    axisSeries K A (positive K A p) = axisMap K A 0 p := by
  ext e
  have he : e = twoExponent (e 0) (e 1) := by
    ext i
    fin_cases i <;> simp
  rw [he]
  rw [coeff_axisSeries_twoExponent, coeff_axisMap_zero]
  by_cases hj : e 1 = 0
  · simp [hj, positive]
  · by_cases hi : e 0 = 0
    · simp [hi, hj, positive]
    · simp [hi, hj]

theorem axisSeries_negative (p : TateAlgebra A (Fin 1)) :
    axisSeries K A (negative K A p) = axisMap K A 1 p := by
  ext e
  have he : e = twoExponent (e 0) (e 1) := by
    ext i
    fin_cases i <;> simp
  rw [he]
  rw [coeff_axisSeries_twoExponent, coeff_axisMap_one]
  by_cases hi : e 0 = 0
  · simp [hi, negative, positive]
  · by_cases hj : e 1 = 0
    · simp [hi, hj, negative, positive]
    · simp [hi, hj]

theorem axisSeries_difference
    (p q : TateAlgebra A (Fin 1)) :
    axisSeries K A (difference K A (p, q)) =
      axisMap K A 0 p - axisMap K A 1 q := by
  ext e
  have he : e = twoExponent (e 0) (e 1) := by
    ext i
    fin_cases i <;> simp
  rw [he]
  rw [coeff_axisSeries_twoExponent]
  change
    (if e 0 = 0 ∨ e 1 = 0 then
        (difference K A (p, q)).1 ((e 0 : ℤ) - (e 1 : ℤ)) else 0) =
      TateAlgebra.coeff A (Fin 2) (twoExponent (e 0) (e 1))
        (axisMap K A 0 p) -
      TateAlgebra.coeff A (Fin 2) (twoExponent (e 0) (e 1))
        (axisMap K A 1 q)
  rw [coeff_axisMap_zero, coeff_axisMap_one]
  by_cases hi : e 0 = 0
  · by_cases hj : e 1 = 0
    · simp [hi, hj, difference, positive, negative]
    · simp [hi, hj, difference, positive, negative]
  · by_cases hj : e 1 = 0
    · simp [hi, hj, difference, positive, negative]
    · simp [hi, hj]

theorem plusToLaurentIntersection_comp_quotientMap (f : A) :
    (plusToLaurentIntersection K A f).comp
        (RationalLocalization.quotientMap K A 1 1 (fun _ ↦ f)) =
      (RationalLocalization.quotientMap K A 2 f
        (laurentIntersectionNumerator A f)).comp (axisMap K A 0) := by
  apply RelativeTateAlgebra.hom_ext K A
  · intro a
    simp only [ContinuousAlgHom.comp_apply, RationalLocalization.quotientMap_C,
      axisMap_C]
    change
      plusToLaurentIntersection K A f
          (LaurentCharts.plusMap K A f a) =
        laurentIntersectionMap K A f a
    exact congrArg
      (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ a)
      (plusToLaurentIntersection_comp_plusMap K A f)
  · intro i
    rw [Fin.eq_zero i]
    simp only [ContinuousAlgHom.comp_apply,
      RationalLocalization.quotientMap_tateVariable, axisMap_tateVariable,
      plusToLaurentIntersection, RationalLocalization.lift_coordinate]
    rfl

theorem minusToLaurentIntersection_comp_quotientMap (f : A) :
    (minusToLaurentIntersection K A f).comp
        (RationalLocalization.quotientMap K A 1 f (fun _ ↦ 1)) =
      (RationalLocalization.quotientMap K A 2 f
        (laurentIntersectionNumerator A f)).comp (axisMap K A 1) := by
  apply RelativeTateAlgebra.hom_ext K A
  · intro a
    simp only [ContinuousAlgHom.comp_apply, RationalLocalization.quotientMap_C,
      axisMap_C]
    change
      minusToLaurentIntersection K A f
          (LaurentCharts.minusMap K A f a) =
        laurentIntersectionMap K A f a
    exact congrArg
      (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ a)
      (minusToLaurentIntersection_comp_minusMap K A f)
  · intro i
    rw [Fin.eq_zero i]
    simp only [ContinuousAlgHom.comp_apply,
      RationalLocalization.quotientMap_tateVariable, axisMap_tateVariable,
      minusToLaurentIntersection, RationalLocalization.lift_coordinate]
    rfl

theorem directDifference_eq_equiv_auxiliaryDifference
    (hA : IsAffinoidAlgebra K A) (f : A) :
    directDifference K A f =
      (laurentRelationQuotientEquivLaurentIntersection K A hA f).toLinearMap.comp
        (auxiliaryDifference K A hA f) := by
  apply LinearMap.ext
  intro z
  obtain ⟨pq, rfl⟩ := chartQuotientMap_surjective K A f z
  rcases pq with ⟨p, q⟩
  have hinv :
      (chartRelationQuotientEquiv K A hA f).symm
          (chartQuotientMap K A f (p, q)) =
        Submodule.Quotient.mk (p, q) := by
    apply (chartRelationQuotientEquiv K A hA f).injective
    rw [LinearEquiv.apply_symm_apply, chartRelationQuotientEquiv_mk]
  have hp := congrArg
    (fun φ : ContinuousAlgHom K (TateAlgebra A (Fin 1))
      (LaurentIntersection K A f) ↦ φ p)
    (plusToLaurentIntersection_comp_quotientMap K A f)
  have hq := congrArg
    (fun φ : ContinuousAlgHom K (TateAlgebra A (Fin 1))
      (LaurentIntersection K A f) ↦ φ q)
    (minusToLaurentIntersection_comp_quotientMap K A f)
  rw [LinearMap.comp_apply]
  change
    plusToLaurentIntersection K A f
          (RationalLocalization.quotientMap K A 1 1 (fun _ ↦ f) p) -
        minusToLaurentIntersection K A f
          (RationalLocalization.quotientMap K A 1 f (fun _ ↦ 1) q) =
      laurentRelationQuotientEquivLaurentIntersection K A hA f
        (quotientDifference K A f
          ((chartRelationQuotientEquiv K A hA f).symm
            (chartQuotientMap K A f (p, q))))
  rw [hinv]
  change
    plusToLaurentIntersection K A f
          (RationalLocalization.quotientMap K A 1 1 (fun _ ↦ f) p) -
        minusToLaurentIntersection K A f
          (RationalLocalization.quotientMap K A 1 f (fun _ ↦ 1) q) =
      laurentRelationQuotientEquivLaurentIntersection K A hA f
        (Submodule.Quotient.mk (difference K A (p, q)))
  rw [laurentRelationQuotientEquivLaurentIntersection_mk,
    axisSeries_difference, map_sub]
  have hp' :
      plusToLaurentIntersection K A f
          (RationalLocalization.quotientMap K A 1 1 (fun _ ↦ f) p) =
        RationalLocalization.quotientMap K A 2 f
          (laurentIntersectionNumerator A f) (axisMap K A 0 p) := by
    simpa only [ContinuousAlgHom.comp_apply] using hp
  have hq' :
      minusToLaurentIntersection K A f
          (RationalLocalization.quotientMap K A 1 f (fun _ ↦ 1) q) =
        RationalLocalization.quotientMap K A 2 f
          (laurentIntersectionNumerator A f) (axisMap K A 1 q) := by
    simpa only [ContinuousAlgHom.comp_apply] using hq
  exact congrArg₂ (· - ·) hp' hq'

/-- Tate's Laurent-cover sequence is short exact with the overlap represented by the direct
rational localization `(f; f², 1)`. -/
theorem direct_shortExact
    (hA : IsAffinoidAlgebra K A) (f : A) :
    Function.Injective (LaurentCharts.diagonal K A f) ∧
      Function.Exact (LaurentCharts.diagonal K A f) (directDifference K A f) ∧
      Function.Surjective (directDifference K A f) := by
  obtain ⟨hinj, hexact, hsurj⟩ := auxiliary_shortExact K A hA f
  refine ⟨hinj, ?_, ?_⟩
  · rw [directDifference_eq_equiv_auxiliaryDifference K A hA f]
    exact
      (laurentRelationQuotientEquivLaurentIntersection K A hA f
        |>.postcomp_exact_iff_exact).2 hexact
  · rw [directDifference_eq_equiv_auxiliaryDifference K A hA f]
    exact
      (laurentRelationQuotientEquivLaurentIntersection K A hA f).surjective.comp hsurj

private noncomputable def overlapT (f : A) : LaurentCharts.Overlap K A f :=
  LaurentCharts.plusToOverlap K A f
    (RationalLocalization.coordinate K A 1 1 (fun _ ↦ f) 0)

private theorem overlapT_eq_map (f : A) :
    overlapT K A f = LaurentCharts.overlapMap K A f f := by
  change
    LaurentCharts.plusToOverlap K A f
        (RationalLocalization.coordinate K A 1 1 (fun _ ↦ f) 0) =
      LaurentCharts.plusToOverlap K A f (LaurentCharts.plusMap K A f f)
  congr 1
  have h := RationalLocalization.baseMap_denominator_mul_coordinate K A 1 1
    (fun _ : Fin 1 ↦ f) 0
  change
    RationalLocalization.coordinate K A 1 1 (fun _ ↦ f) 0 =
      RationalLocalization.baseMap K A 1 1 (fun _ ↦ f) f
  simpa using h

private theorem isPowerBounded_overlapT (f : A) :
    IsPowerBounded (overlapT K A f) :=
  (RationalLocalization.isPowerBounded_coordinate K A 1 1
    (fun _ ↦ f) 0).map_continuousAlgHom (LaurentCharts.plusToOverlap K A f)

private noncomputable def overlapCoordinates (f : A) :
    Fin 2 → LaurentCharts.Overlap K A f :=
  ![overlapT K A f, LaurentCharts.overlapInverse K A f]

private theorem isPowerBounded_overlapCoordinates (f : A) (i : Fin 2) :
    IsPowerBounded (overlapCoordinates K A f i) := by
  fin_cases i
  · exact isPowerBounded_overlapT K A f
  · exact LaurentCharts.isPowerBounded_overlapInverse K A f

private theorem overlapCoordinates_relation (f : A) (i : Fin 2) :
    LaurentCharts.overlapMap K A f f * overlapCoordinates K A f i =
      LaurentCharts.overlapMap K A f (laurentIntersectionNumerator A f i) := by
  fin_cases i
  · change
      LaurentCharts.overlapMap K A f f * overlapT K A f =
        LaurentCharts.overlapMap K A f (f ^ 2)
    rw [overlapT_eq_map, map_pow, pow_two]
  · change
      LaurentCharts.overlapMap K A f f * LaurentCharts.overlapInverse K A f =
        LaurentCharts.overlapMap K A f 1
    simp

/-- Map the direct intersection `(f; f², 1)` to the iterated Laurent overlap. -/
noncomputable def laurentIntersectionToOverlap (f : A) :
    ContinuousAlgHom K (LaurentIntersection K A f) (LaurentCharts.Overlap K A f) :=
  RationalLocalization.lift K A 2 f (laurentIntersectionNumerator A f)
    (LaurentCharts.overlapMap K A f)
    (overlapCoordinates K A f)
    (isPowerBounded_overlapCoordinates K A f)
    (overlapCoordinates_relation K A f)

@[simp]
theorem laurentIntersectionToOverlap_comp_map (f : A) :
    (laurentIntersectionToOverlap K A f).comp (laurentIntersectionMap K A f) =
      LaurentCharts.overlapMap K A f :=
  RationalLocalization.lift_comp_baseMap K A 2 f
    (laurentIntersectionNumerator A f) (LaurentCharts.overlapMap K A f)
    (overlapCoordinates K A f)
    (isPowerBounded_overlapCoordinates K A f)
    (overlapCoordinates_relation K A f)

@[simp]
theorem laurentIntersectionToOverlap_T (f : A) :
    laurentIntersectionToOverlap K A f (laurentIntersectionT K A f) =
      overlapT K A f := by
  exact RationalLocalization.lift_coordinate K A 2 f
    (laurentIntersectionNumerator A f) (LaurentCharts.overlapMap K A f)
    (overlapCoordinates K A f)
    (isPowerBounded_overlapCoordinates K A f)
    (overlapCoordinates_relation K A f) 0

@[simp]
theorem laurentIntersectionToOverlap_S (f : A) :
    laurentIntersectionToOverlap K A f (laurentIntersectionS K A f) =
      LaurentCharts.overlapInverse K A f := by
  exact RationalLocalization.lift_coordinate K A 2 f
    (laurentIntersectionNumerator A f) (LaurentCharts.overlapMap K A f)
    (overlapCoordinates K A f)
    (isPowerBounded_overlapCoordinates K A f)
    (overlapCoordinates_relation K A f) 1

/-- Map the iterated Laurent overlap back to the direct rational localization. -/
noncomputable def overlapToLaurentIntersection (f : A) :
    ContinuousAlgHom K (LaurentCharts.Overlap K A f) (LaurentIntersection K A f) :=
  RationalLocalization.lift K (LaurentCharts.Plus K A f) 1
    (LaurentCharts.plusMap K A f f) (fun _ ↦ 1)
    (plusToLaurentIntersection K A f) (fun _ ↦ laurentIntersectionS K A f)
    (fun _ ↦ isPowerBounded_laurentIntersectionS K A f)
    (fun _ ↦ by
      have h := congrArg
        (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ f)
        (plusToLaurentIntersection_comp_plusMap K A f)
      change
        plusToLaurentIntersection K A f (LaurentCharts.plusMap K A f f) *
            laurentIntersectionS K A f =
          plusToLaurentIntersection K A f 1
      rw [show plusToLaurentIntersection K A f
        (LaurentCharts.plusMap K A f f) = laurentIntersectionMap K A f f by
          simpa only [ContinuousAlgHom.comp_apply] using h]
      simp)

@[simp]
theorem overlapToLaurentIntersection_comp_plusToOverlap (f : A) :
    (overlapToLaurentIntersection K A f).comp
        (LaurentCharts.plusToOverlap K A f) =
      plusToLaurentIntersection K A f := by
  exact RationalLocalization.lift_comp_baseMap K (LaurentCharts.Plus K A f) 1
    (LaurentCharts.plusMap K A f f) (fun _ ↦ 1)
    (plusToLaurentIntersection K A f) (fun _ ↦ laurentIntersectionS K A f)
    (fun _ ↦ isPowerBounded_laurentIntersectionS K A f)
    (fun _ ↦ by
      have h := congrArg
        (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ f)
        (plusToLaurentIntersection_comp_plusMap K A f)
      rw [show plusToLaurentIntersection K A f
        (LaurentCharts.plusMap K A f f) = laurentIntersectionMap K A f f by
          simpa only [ContinuousAlgHom.comp_apply] using h]
      simp)

@[simp]
theorem overlapToLaurentIntersection_inverse (f : A) :
    overlapToLaurentIntersection K A f (LaurentCharts.overlapInverse K A f) =
      laurentIntersectionS K A f := by
  exact RationalLocalization.lift_coordinate K (LaurentCharts.Plus K A f) 1
    (LaurentCharts.plusMap K A f f) (fun _ ↦ 1)
    (plusToLaurentIntersection K A f) (fun _ ↦ laurentIntersectionS K A f)
    (fun _ ↦ isPowerBounded_laurentIntersectionS K A f)
    (fun _ ↦ by
      have h := congrArg
        (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ f)
        (plusToLaurentIntersection_comp_plusMap K A f)
      rw [show plusToLaurentIntersection K A f
        (LaurentCharts.plusMap K A f f) = laurentIntersectionMap K A f f by
          simpa only [ContinuousAlgHom.comp_apply] using h]
      simp) 0

@[simp]
theorem laurentIntersectionToOverlap_comp_plusToLaurentIntersection (f : A) :
    (laurentIntersectionToOverlap K A f).comp
        (plusToLaurentIntersection K A f) =
      LaurentCharts.plusToOverlap K A f := by
  apply RationalLocalization.hom_ext K A 1 1 (fun _ ↦ f)
  · apply ContinuousAlgHom.ext
    intro a
    simp only [ContinuousAlgHom.comp_apply]
    have hplus := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ a)
      (plusToLaurentIntersection_comp_plusMap K A f)
    have hintersection := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentCharts.Overlap K A f) ↦ φ a)
      (laurentIntersectionToOverlap_comp_map K A f)
    have hoverlap := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentCharts.Overlap K A f) ↦ φ a)
      (LaurentCharts.plusToOverlap_comp_plusMap K A f)
    calc
      laurentIntersectionToOverlap K A f
          (plusToLaurentIntersection K A f (LaurentCharts.plusMap K A f a)) =
        laurentIntersectionToOverlap K A f (laurentIntersectionMap K A f a) :=
          congrArg (laurentIntersectionToOverlap K A f)
            (by simpa only [ContinuousAlgHom.comp_apply] using hplus)
      _ = LaurentCharts.overlapMap K A f a := by
        simpa only [ContinuousAlgHom.comp_apply] using hintersection
      _ = LaurentCharts.plusToOverlap K A f
          (LaurentCharts.plusMap K A f a) := by
        simpa only [ContinuousAlgHom.comp_apply] using hoverlap.symm
  · intro i
    rw [Fin.eq_zero i]
    simp only [ContinuousAlgHom.comp_apply, plusToLaurentIntersection,
      RationalLocalization.lift_coordinate, laurentIntersectionToOverlap_T]
    rfl

@[simp]
theorem laurentIntersectionToOverlap_comp_minusToLaurentIntersection (f : A) :
    (laurentIntersectionToOverlap K A f).comp
        (minusToLaurentIntersection K A f) =
      LaurentCharts.minusToOverlap K A f := by
  apply RationalLocalization.hom_ext K A 1 f (fun _ ↦ 1)
  · apply ContinuousAlgHom.ext
    intro a
    simp only [ContinuousAlgHom.comp_apply]
    have hminus := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ a)
      (minusToLaurentIntersection_comp_minusMap K A f)
    have hintersection := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentCharts.Overlap K A f) ↦ φ a)
      (laurentIntersectionToOverlap_comp_map K A f)
    have hoverlap := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentCharts.Overlap K A f) ↦ φ a)
      (LaurentCharts.minusToOverlap_comp_minusMap K A f)
    calc
      laurentIntersectionToOverlap K A f
          (minusToLaurentIntersection K A f (LaurentCharts.minusMap K A f a)) =
        laurentIntersectionToOverlap K A f (laurentIntersectionMap K A f a) :=
          congrArg (laurentIntersectionToOverlap K A f)
            (by simpa only [ContinuousAlgHom.comp_apply] using hminus)
      _ = LaurentCharts.overlapMap K A f a := by
        simpa only [ContinuousAlgHom.comp_apply] using hintersection
      _ = LaurentCharts.minusToOverlap K A f
          (LaurentCharts.minusMap K A f a) := by
        simpa only [ContinuousAlgHom.comp_apply] using hoverlap.symm
  · intro i
    rw [Fin.eq_zero i]
    simp only [ContinuousAlgHom.comp_apply, minusToLaurentIntersection,
      RationalLocalization.lift_coordinate, laurentIntersectionToOverlap_S]
    symm
    exact RationalLocalization.lift_coordinate K A 1 f (fun _ ↦ 1)
      (LaurentCharts.overlapMap K A f)
      (fun _ ↦ LaurentCharts.overlapInverse K A f)
      (fun _ ↦ LaurentCharts.isPowerBounded_overlapInverse K A f)
      (fun _ ↦ by simp) 0

private theorem overlapToLaurentIntersection_comp_intersectionToOverlap (f : A) :
    (overlapToLaurentIntersection K A f).comp
        (laurentIntersectionToOverlap K A f) =
      ContinuousAlgHom.id K (LaurentIntersection K A f) := by
  apply RationalLocalization.hom_ext K A 2 f (laurentIntersectionNumerator A f)
  · apply ContinuousAlgHom.ext
    intro a
    simp only [ContinuousAlgHom.comp_apply, ContinuousAlgHom.id_apply]
    have hforward := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentCharts.Overlap K A f) ↦ φ a)
      (laurentIntersectionToOverlap_comp_map K A f)
    rw [show laurentIntersectionToOverlap K A f
      (RationalLocalization.baseMap K A 2 f
        (laurentIntersectionNumerator A f) a) =
          LaurentCharts.overlapMap K A f a by
        simpa only [ContinuousAlgHom.comp_apply, laurentIntersectionMap] using hforward]
    change
      overlapToLaurentIntersection K A f
          (LaurentCharts.plusToOverlap K A f
            (LaurentCharts.plusMap K A f a)) =
        laurentIntersectionMap K A f a
    have hback := congrArg
      (fun φ : ContinuousAlgHom K (LaurentCharts.Plus K A f)
        (LaurentIntersection K A f) ↦ φ (LaurentCharts.plusMap K A f a))
      (overlapToLaurentIntersection_comp_plusToOverlap K A f)
    rw [show overlapToLaurentIntersection K A f
      (LaurentCharts.plusToOverlap K A f (LaurentCharts.plusMap K A f a)) =
        plusToLaurentIntersection K A f (LaurentCharts.plusMap K A f a) by
          simpa only [ContinuousAlgHom.comp_apply] using hback]
    have hplus := congrArg
      (fun φ : ContinuousAlgHom K A (LaurentIntersection K A f) ↦ φ a)
      (plusToLaurentIntersection_comp_plusMap K A f)
    simpa only [ContinuousAlgHom.comp_apply] using hplus
  · intro i
    by_cases hi : i = 0
    · subst i
      simp only [ContinuousAlgHom.comp_apply, ContinuousAlgHom.id_apply]
      rw [show laurentIntersectionToOverlap K A f
        (RationalLocalization.coordinate K A 2 f
          (laurentIntersectionNumerator A f) 0) = overlapT K A f by
            simpa only [laurentIntersectionT] using
              laurentIntersectionToOverlap_T K A f]
      change
        overlapToLaurentIntersection K A f
            (LaurentCharts.plusToOverlap K A f
              (RationalLocalization.coordinate K A 1 1 (fun _ ↦ f) 0)) =
          laurentIntersectionT K A f
      have hback := congrArg
        (fun φ : ContinuousAlgHom K (LaurentCharts.Plus K A f)
          (LaurentIntersection K A f) ↦
            φ (RationalLocalization.coordinate K A 1 1 (fun _ ↦ f) 0))
        (overlapToLaurentIntersection_comp_plusToOverlap K A f)
      rw [show overlapToLaurentIntersection K A f
        (LaurentCharts.plusToOverlap K A f
          (RationalLocalization.coordinate K A 1 1 (fun _ ↦ f) 0)) =
          plusToLaurentIntersection K A f
            (RationalLocalization.coordinate K A 1 1 (fun _ ↦ f) 0) by
            simpa only [ContinuousAlgHom.comp_apply] using hback]
      exact RationalLocalization.lift_coordinate K A 1 1 (fun _ ↦ f)
        (laurentIntersectionMap K A f) (fun _ ↦ laurentIntersectionT K A f)
        (fun _ ↦ isPowerBounded_laurentIntersectionT K A f)
        (fun _ ↦ by simp) 0
    · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
      subst i
      simp only [ContinuousAlgHom.comp_apply, ContinuousAlgHom.id_apply]
      rw [show laurentIntersectionToOverlap K A f
        (RationalLocalization.coordinate K A 2 f
          (laurentIntersectionNumerator A f) 1) =
            LaurentCharts.overlapInverse K A f by
              simpa only [laurentIntersectionS] using
                laurentIntersectionToOverlap_S K A f]
      simpa only [laurentIntersectionS] using
        overlapToLaurentIntersection_inverse K A f

private theorem intersectionToOverlap_comp_overlapToLaurentIntersection (f : A) :
    (laurentIntersectionToOverlap K A f).comp
        (overlapToLaurentIntersection K A f) =
      ContinuousAlgHom.id K (LaurentCharts.Overlap K A f) := by
  apply RationalLocalization.hom_ext K (LaurentCharts.Plus K A f) 1
    (RationalLocalization.baseMap K A 1 1 (fun _ ↦ f) f) (fun _ ↦ 1)
  · apply ContinuousAlgHom.ext
    intro p
    simp only [ContinuousAlgHom.comp_apply, ContinuousAlgHom.id_apply]
    have hback := congrArg
      (fun φ : ContinuousAlgHom K (LaurentCharts.Plus K A f)
        (LaurentIntersection K A f) ↦ φ p)
      (overlapToLaurentIntersection_comp_plusToOverlap K A f)
    rw [show overlapToLaurentIntersection K A f
      (RationalLocalization.baseMap K (LaurentCharts.Plus K A f) 1
        (RationalLocalization.baseMap K A 1 1 (fun _ ↦ f) f)
        (fun _ ↦ 1) p) =
        plusToLaurentIntersection K A f p by
          simpa only [ContinuousAlgHom.comp_apply, LaurentCharts.plusToOverlap,
            LaurentCharts.plusMap] using hback]
    have hforward := congrArg
      (fun φ : ContinuousAlgHom K (LaurentCharts.Plus K A f)
        (LaurentCharts.Overlap K A f) ↦ φ p)
      (laurentIntersectionToOverlap_comp_plusToLaurentIntersection K A f)
    simpa only [ContinuousAlgHom.comp_apply, LaurentCharts.plusToOverlap,
      LaurentCharts.plusMap] using hforward
  · intro i
    rw [Fin.eq_zero i]
    simp only [ContinuousAlgHom.comp_apply, ContinuousAlgHom.id_apply]
    rw [show overlapToLaurentIntersection K A f
      (RationalLocalization.coordinate K (LaurentCharts.Plus K A f) 1
      (RationalLocalization.baseMap K A 1 1 (fun _ ↦ f) f)
        (fun _ ↦ 1) 0) = laurentIntersectionS K A f by
          simpa only [LaurentCharts.overlapInverse, LaurentCharts.plusMap] using
            overlapToLaurentIntersection_inverse K A f]
    simpa only [laurentIntersectionS, LaurentCharts.overlapInverse,
      LaurentCharts.plusMap] using laurentIntersectionToOverlap_S K A f

/-- The direct and iterated presentations of the Laurent overlap are algebraically equivalent. -/
noncomputable def laurentIntersectionEquivOverlap (f : A) :
    LaurentIntersection K A f ≃ₐ[K] LaurentCharts.Overlap K A f :=
  AlgEquiv.ofAlgHom
    (laurentIntersectionToOverlap K A f).toAlgHom
    (overlapToLaurentIntersection K A f).toAlgHom
    (by
      exact congrArg ContinuousAlgHom.toAlgHom
        (intersectionToOverlap_comp_overlapToLaurentIntersection K A f))
    (by
      exact congrArg ContinuousAlgHom.toAlgHom
        (overlapToLaurentIntersection_comp_intersectionToOverlap K A f))

@[simp]
theorem laurentIntersectionEquivOverlap_apply (f : A)
    (x : LaurentIntersection K A f) :
    laurentIntersectionEquivOverlap K A f x =
      laurentIntersectionToOverlap K A f x :=
  rfl

theorem laurentDifference_eq_equiv_directDifference (f : A) :
    LaurentCharts.difference K A f =
      (laurentIntersectionEquivOverlap K A f).toLinearEquiv.toLinearMap.comp
        (directDifference K A f) := by
  apply LinearMap.ext
  rintro ⟨p, q⟩
  simp only [LaurentCharts.difference_apply, LinearMap.comp_apply,
    directDifference_apply, map_sub]
  have hp := congrArg
    (fun φ : ContinuousAlgHom K (LaurentCharts.Plus K A f)
      (LaurentCharts.Overlap K A f) ↦ φ p)
    (laurentIntersectionToOverlap_comp_plusToLaurentIntersection K A f)
  have hq := congrArg
    (fun φ : ContinuousAlgHom K (LaurentCharts.Minus K A f)
      (LaurentCharts.Overlap K A f) ↦ φ q)
    (laurentIntersectionToOverlap_comp_minusToLaurentIntersection K A f)
  exact congrArg₂ (· - ·)
    (by
      change LaurentCharts.plusToOverlap K A f p =
        laurentIntersectionToOverlap K A f
          (plusToLaurentIntersection K A f p)
      simpa only [ContinuousAlgHom.comp_apply] using hp.symm)
    (by
      change LaurentCharts.minusToOverlap K A f q =
        laurentIntersectionToOverlap K A f
          (minusToLaurentIntersection K A f q)
      simpa only [ContinuousAlgHom.comp_apply] using hq.symm)

/-- Tate's two-member Laurent-cover sequence with the standard iterated overlap is short exact. -/
theorem laurentCharts_shortExact
    (hA : IsAffinoidAlgebra K A) (f : A) :
    Function.Injective (LaurentCharts.diagonal K A f) ∧
      Function.Exact (LaurentCharts.diagonal K A f)
        (LaurentCharts.difference K A f) ∧
      Function.Surjective (LaurentCharts.difference K A f) := by
  obtain ⟨hinj, hexact, hsurj⟩ := direct_shortExact K A hA f
  refine ⟨hinj, ?_, ?_⟩
  · rw [laurentDifference_eq_equiv_directDifference K A f]
    exact (laurentIntersectionEquivOverlap K A f).toLinearEquiv
      |>.postcomp_exact_iff_exact |>.2 hexact
  · rw [laurentDifference_eq_equiv_directDifference K A f]
    exact
      (laurentIntersectionEquivOverlap K A f).toLinearEquiv.surjective.comp hsurj

/-- Compatible sections on the two members of a Laurent cover glue uniquely. -/
theorem laurentCharts_existsUnique_glue
    (hA : IsAffinoidAlgebra K A) (f : A)
    (p : LaurentCharts.Plus K A f) (q : LaurentCharts.Minus K A f)
    (hpq : LaurentCharts.plusToOverlap K A f p =
      LaurentCharts.minusToOverlap K A f q) :
    ∃! a : A,
      LaurentCharts.plusMap K A f a = p ∧
        LaurentCharts.minusMap K A f a = q := by
  have hzero : LaurentCharts.difference K A f (p, q) = 0 := by
    simpa [LaurentCharts.difference_apply, sub_eq_zero] using hpq
  obtain ⟨a, ha⟩ :=
    ((laurentCharts_shortExact K A hA f).2.1 (p, q)).mp hzero
  refine ⟨a, ?_, ?_⟩
  · exact Prod.ext_iff.mp ha
  · intro b hb
    apply (laurentCharts_shortExact K A hA f).1
    calc
      LaurentCharts.diagonal K A f b = (p, q) := Prod.ext hb.1 hb.2
      _ = LaurentCharts.diagonal K A f a := ha.symm

end CompletedLaurent

end Rigid
