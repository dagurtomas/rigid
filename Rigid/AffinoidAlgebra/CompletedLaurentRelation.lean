import Rigid.AffinoidAlgebra.CompletedLaurent
import Rigid.TateAlgebra.Leading

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The relation row in the completed Laurent diagram

The proof of Tate acyclicity for a two-member Laurent cover uses the diagram in BGR 8.2.3.
The middle row is the completed Laurent coefficient sequence from
`Rigid.AffinoidAlgebra.CompletedLaurent`.  This file supplies the coefficient calculation for the
row above it.

If `ζ` denotes the Laurent variable, multiplication by `ζ - f` sends a restricted Laurent
coefficient family `c` to the family

`z ↦ c (z - 1) - f * c z`.

The image of the two chart relations `(T - f)` and `(1 - fS)` under Laurent difference is exactly
the image of this operator.  Surjectivity of the factor map below is the formal version of

`(ζ - f) A⟨ζ, ζ⁻¹⟩ =
  (ζ - f) A⟨ζ⟩ + (1 - fζ⁻¹) A⟨ζ⁻¹⟩`.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

private theorem sub_one_injective : Function.Injective (fun z : ℤ ↦ z - 1) := by
  intro z w h
  have h' := congrArg (fun x : ℤ ↦ x + 1) h
  simpa only [sub_add_cancel] using h'

private theorem add_one_injective : Function.Injective (fun z : ℤ ↦ z + 1) := by
  intro z w h
  exact add_right_cancel h

/-- Shift Laurent coefficients up by one exponent. -/
noncomputable def shift : Series K A →ₗ[K] Series K A where
  toFun c :=
    ⟨fun z ↦ c.1 (z - 1), c.2.comp sub_one_injective.tendsto_cofinite⟩
  map_add' c d := by
    ext z
    rfl
  map_smul' r c := by
    ext z
    rfl

/-- Multiplication by the formal Laurent element `ζ - f`. -/
noncomputable def relation (f : A) : Series K A →ₗ[K] Series K A where
  toFun c :=
    ⟨fun z ↦ c.1 (z - 1) - f * c.1 z, by
      change Tendsto (fun z : ℤ ↦ c.1 (z - 1) - f * c.1 z) cofinite (𝓝 0)
      have hshift := c.2.comp sub_one_injective.tendsto_cofinite
      have hmul : Tendsto (fun z : ℤ ↦ f * c.1 z) cofinite (𝓝 0) := by
        simpa only [mul_zero] using (tendsto_const_nhds.mul c.2)
      simpa only [Function.comp_apply, mul_zero, sub_zero] using hshift.sub hmul⟩
  map_add' c d := by
    ext z
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' r c := by
    ext z
    change (r • c.1) (z - 1) - f * (r • c.1) z =
      r • (c.1 (z - 1) - f * c.1 z)
    simp only [Pi.smul_apply]
    rw [smul_sub, mul_smul_comm]

/-- The negative chart shifted once farther into the strictly negative Laurent exponents. -/
noncomputable def strictNegative : TateAlgebra A (Fin 1) →ₗ[K] Series K A where
  toFun q :=
    ⟨fun z ↦ -(negative K A q).1 (z + 1), by
      change Tendsto (fun z : ℤ ↦ -(negative K A q).1 (z + 1)) cofinite (𝓝 0)
      have hshift := (negative K A q).2.comp add_one_injective.tendsto_cofinite
      simpa only [Function.comp_apply, neg_zero] using hshift.neg⟩
  map_add' p q := by
    ext z
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
    abel
  map_smul' r q := by
    ext z
    simp

theorem positive_apply_of_nonneg (p : TateAlgebra A (Fin 1)) (z : ℤ) (hz : 0 ≤ z) :
    (positive K A p).1 z =
      TateAlgebra.coeff A (Fin 1) (oneExponent z.toNat) p := by
  change (if 0 ≤ z then TateAlgebra.coeff A (Fin 1) (oneExponent z.toNat) p else 0) = _
  rw [if_pos hz]

theorem positive_apply_of_neg (p : TateAlgebra A (Fin 1)) (z : ℤ) (hz : z < 0) :
    (positive K A p).1 z = 0 := by
  change (if 0 ≤ z then TateAlgebra.coeff A (Fin 1) (oneExponent z.toNat) p else 0) = 0
  rw [if_neg (not_le_of_gt hz)]

@[simp]
theorem negative_apply (q : TateAlgebra A (Fin 1)) (z : ℤ) :
    (negative K A q).1 z = (positive K A q).1 (-z) :=
  rfl

@[simp]
theorem strictNegative_apply (q : TateAlgebra A (Fin 1)) (z : ℤ) :
    (strictNegative K A q).1 z = -(negative K A q).1 (z + 1) :=
  rfl

/-- The two chart factors whose relation multiples produce an arbitrary Laurent relation
multiple.  The first component supplies the nonnegative coefficients and the second supplies the
strictly negative coefficients. -/
noncomputable def relationFactor :
    TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) →ₗ[K] Series K A :=
  (positive K A).comp (LinearMap.fst K _ _) +
    (strictNegative K A).comp (LinearMap.snd K _ _)

@[simp]
theorem relationFactor_apply (p q : TateAlgebra A (Fin 1)) :
    relationFactor K A (p, q) = positive K A p + strictNegative K A q :=
  rfl

/-- Every restricted Laurent family splits uniquely by support into a nonnegative part and a
strictly negative part.  In particular, the factor map used for the relation row is onto. -/
theorem relationFactor_surjective : Function.Surjective (relationFactor K A) := by
  intro a
  let pa : ℕ → A := fun n ↦ a.1 (n : ℤ)
  have hpa : Tendsto pa cofinite (𝓝 0) :=
    a.2.comp (show Function.Injective (fun n : ℕ ↦ (n : ℤ)) by
      intro n m h
      exact Int.ofNat.inj h).tendsto_cofinite
  let qa : ℕ → A := fun n ↦ -a.1 (-((n : ℤ) + 1))
  have hindex : Function.Injective (fun n : ℕ ↦ -((n : ℤ) + 1)) := by
    intro n m h
    have h' : (n : ℤ) + 1 = (m : ℤ) + 1 := neg_inj.mp h
    exact Int.ofNat.inj (add_right_cancel h')
  have hqa : Tendsto qa cofinite (𝓝 0) := by
    have h := a.2.comp hindex.tendsto_cofinite
    change Tendsto (fun n : ℕ ↦ -a.1 (-((n : ℤ) + 1))) cofinite (𝓝 0)
    simpa only [Function.comp_apply, neg_zero] using h.neg
  refine ⟨(ofCoefficients A pa hpa, ofCoefficients A qa hqa), ?_⟩
  ext z
  by_cases hz : 0 ≤ z
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
    rw [relationFactor_apply]
    change (positive K A (ofCoefficients A pa hpa)).1 (n : ℤ) +
      (strictNegative K A (ofCoefficients A qa hqa)).1 (n : ℤ) = a.1 (n : ℤ)
    rw [positive_apply_of_nonneg K A _ _ (Int.natCast_nonneg n), strictNegative_apply,
      negative_apply, positive_apply_of_neg]
    · rw [neg_zero, add_zero, Int.toNat_natCast, coeff_ofCoefficients]
    · omega
  · have hzneg : z < 0 := lt_of_not_ge hz
    obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hzneg
    rw [relationFactor_apply]
    change (positive K A (ofCoefficients A pa hpa)).1 (-((n : ℤ) + 1)) +
      (strictNegative K A (ofCoefficients A qa hqa)).1 (-((n : ℤ) + 1)) =
        a.1 (-((n : ℤ) + 1))
    rw [positive_apply_of_neg K A, strictNegative_apply, negative_apply]
    · have hindex : -(-((n : ℤ) + 1) + 1) = (n : ℤ) := by omega
      rw [hindex, positive_apply_of_nonneg K A _ _ (Int.natCast_nonneg n),
        Int.toNat_natCast, zero_add, coeff_ofCoefficients]
      simp [qa]
    · omega

@[simp]
theorem relation_apply (f : A) (c : Series K A) (z : ℤ) :
    (relation K A f c).1 z = c.1 (z - 1) - f * c.1 z :=
  rfl

@[simp]
theorem relationFactor_apply_ofNat (p q : TateAlgebra A (Fin 1)) (n : ℕ) :
    (relationFactor K A (p, q)).1 (n : ℤ) =
      TateAlgebra.coeff A (Fin 1) (oneExponent n) p := by
  rw [relationFactor_apply]
  change (positive K A p).1 (n : ℤ) + (strictNegative K A q).1 (n : ℤ) = _
  rw [positive_apply_of_nonneg K A _ _ (Int.natCast_nonneg n), strictNegative_apply,
    negative_apply, positive_apply_of_neg]
  · simp
  · omega

@[simp]
theorem relationFactor_apply_negSucc (p q : TateAlgebra A (Fin 1)) (n : ℕ) :
    (relationFactor K A (p, q)).1 (Int.negSucc n) =
      -TateAlgebra.coeff A (Fin 1) (oneExponent n) q := by
  rw [relationFactor_apply]
  change (positive K A p).1 (-((n : ℤ) + 1)) +
    (strictNegative K A q).1 (-((n : ℤ) + 1)) = _
  rw [positive_apply_of_neg K A, strictNegative_apply, negative_apply]
  · have hindex : -(-((n : ℤ) + 1) + 1) = (n : ℤ) := by omega
    rw [hindex, positive_apply_of_nonneg K A _ _ (Int.natCast_nonneg n),
      Int.toNat_natCast, zero_add]
  · omega

/-- Multiplication by `T - f` in the positive chart before quotienting. -/
noncomputable def plusRelation (f : A) :
    TateAlgebra A (Fin 1) →ₗ[K] TateAlgebra A (Fin 1) where
  toFun p :=
    (tateVariable A (Fin 1) 0 - TateAlgebra.C A (Fin 1) f) * p
  map_add' p q := by rw [mul_add]
  map_smul' r p := by
    rw [RingHom.id_apply, mul_smul_comm]

/-- Multiplication by `1 - fS` in the negative chart before quotienting. -/
noncomputable def minusRelation (f : A) :
    TateAlgebra A (Fin 1) →ₗ[K] TateAlgebra A (Fin 1) where
  toFun q :=
    (1 - TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) 0) * q
  map_add' p q := by rw [mul_add]
  map_smul' r p := by
    rw [RingHom.id_apply, mul_smul_comm]

/-- The pair of relation multiplications in the two one-variable Tate algebras. -/
noncomputable def chartRelations (f : A) :
    TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) →ₗ[K]
      TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) :=
  (plusRelation K A f).prodMap (minusRelation K A f)

@[simp]
theorem chartRelations_apply (f : A) (p q : TateAlgebra A (Fin 1)) :
    chartRelations K A f (p, q) = (plusRelation K A f p, minusRelation K A f q) :=
  rfl

theorem coeff_plusRelation_zero (f : A) (p : TateAlgebra A (Fin 1)) :
    TateAlgebra.coeff A (Fin 1) (oneExponent 0) (plusRelation K A f p) =
      -f * TateAlgebra.coeff A (Fin 1) (oneExponent 0) p := by
  change MvPowerSeries.coeff (oneExponent 0)
    (((tateVariable A (Fin 1) 0 - TateAlgebra.C A (Fin 1) f) * p :
      TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A) = _
  have hcoe :
      ((((tateVariable A (Fin 1) 0 - TateAlgebra.C A (Fin 1) f) * p :
        TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A)) =
        (MvPowerSeries.X 0 - MvPowerSeries.C f) * p.1 := rfl
  rw [hcoe, sub_mul, map_sub, MvPowerSeries.X_def]
  rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_C_mul]
  simp [oneExponent]

theorem coeff_plusRelation_succ (f : A) (p : TateAlgebra A (Fin 1)) (n : ℕ) :
    TateAlgebra.coeff A (Fin 1) (oneExponent (n + 1)) (plusRelation K A f p) =
      TateAlgebra.coeff A (Fin 1) (oneExponent n) p -
        f * TateAlgebra.coeff A (Fin 1) (oneExponent (n + 1)) p := by
  change MvPowerSeries.coeff (oneExponent (n + 1))
    (((tateVariable A (Fin 1) 0 - TateAlgebra.C A (Fin 1) f) * p :
      TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A) = _
  have hcoe :
      ((((tateVariable A (Fin 1) 0 - TateAlgebra.C A (Fin 1) f) * p :
        TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A)) =
        (MvPowerSeries.X 0 - MvPowerSeries.C f) * p.1 := rfl
  rw [hcoe, sub_mul, map_sub, MvPowerSeries.X_def]
  rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_C_mul]
  simp [oneExponent]

theorem coeff_minusRelation_zero (f : A) (q : TateAlgebra A (Fin 1)) :
    TateAlgebra.coeff A (Fin 1) (oneExponent 0) (minusRelation K A f q) =
      TateAlgebra.coeff A (Fin 1) (oneExponent 0) q := by
  change MvPowerSeries.coeff (oneExponent 0)
    (((1 - TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) 0) * q :
      TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A) = _
  have hcoe :
      ((((1 - TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) 0) * q :
        TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A)) =
        (1 - MvPowerSeries.C f * MvPowerSeries.X 0) * q.1 := rfl
  rw [hcoe, sub_mul, one_mul, map_sub]
  rw [show MvPowerSeries.C f * MvPowerSeries.X 0 * q.1 =
      MvPowerSeries.C f * (MvPowerSeries.X 0 * q.1) by ring]
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul]
  simp [oneExponent]

theorem coeff_minusRelation_succ (f : A) (q : TateAlgebra A (Fin 1)) (n : ℕ) :
    TateAlgebra.coeff A (Fin 1) (oneExponent (n + 1)) (minusRelation K A f q) =
      TateAlgebra.coeff A (Fin 1) (oneExponent (n + 1)) q -
        f * TateAlgebra.coeff A (Fin 1) (oneExponent n) q := by
  change MvPowerSeries.coeff (oneExponent (n + 1))
    (((1 - TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) 0) * q :
      TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A) = _
  have hcoe :
      ((((1 - TateAlgebra.C A (Fin 1) f * tateVariable A (Fin 1) 0) * q :
        TateAlgebra A (Fin 1)) : MvPowerSeries (Fin 1) A)) =
        (1 - MvPowerSeries.C f * MvPowerSeries.X 0) * q.1 := rfl
  rw [hcoe, sub_mul, one_mul, map_sub]
  rw [show MvPowerSeries.C f * MvPowerSeries.X 0 * q.1 =
      MvPowerSeries.C f * (MvPowerSeries.X 0 * q.1) by ring]
  rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.X_def,
    MvPowerSeries.coeff_monomial_mul]
  simp [oneExponent]

/-- The chart relation square in BGR 8.2.3 commutes. -/
theorem difference_comp_chartRelations (f : A) :
    (difference K A).comp (chartRelations K A f) =
      (relation K A f).comp (relationFactor K A) := by
  apply LinearMap.ext
  rintro ⟨p, q⟩
  ext z
  simp only [LinearMap.comp_apply, chartRelations_apply]
  rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hzneg
    have hdiff := difference_coeff_neg K A
      (plusRelation K A f p) (minusRelation K A f q) (n + 1) (Nat.succ_pos n)
    have hindex : -((n + 1 : ℕ) : ℤ) = Int.negSucc n := by omega
    rw [hindex] at hdiff
    rw [hdiff, coeff_minusRelation_succ]
    rw [relation_apply]
    have hsub : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
    rw [hsub, relationFactor_apply_negSucc, relationFactor_apply_negSucc]
    ring
  · rw [difference_coeff_zero, coeff_plusRelation_zero, coeff_minusRelation_zero,
      relation_apply]
    have hsub : (0 : ℤ) - 1 = Int.negSucc 0 := by omega
    rw [hsub, relationFactor_apply_negSucc]
    have hzero := relationFactor_apply_ofNat K A p q 0
    change (relationFactor K A (p, q)).1 0 =
      TateAlgebra.coeff A (Fin 1) (oneExponent 0) p at hzero
    rw [hzero]
    ring
  · obtain ⟨n, rfl⟩ := Int.eq_succ_of_zero_lt hzpos
    have hdiff := difference_coeff_pos K A
      (plusRelation K A f p) (minusRelation K A f q) (n + 1) (Nat.succ_pos n)
    have hindex : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
    rw [hindex] at hdiff
    rw [hdiff, coeff_plusRelation_succ]
    rw [relation_apply]
    have hsub : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
    rw [hsub, relationFactor_apply_ofNat, relationFactor_apply_ofNat]

/-- The two chart relation submodules map onto exactly the Laurent relation submodule.  This is
the exact relation-row statement needed before descending the completed Laurent sequence to the
three analytic chart quotients. -/
theorem map_range_chartRelations (f : A) :
    Submodule.map (difference K A) (LinearMap.range (chartRelations K A f)) =
      LinearMap.range (relation K A f) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    refine ⟨relationFactor K A z, ?_⟩
    have h := congrArg (fun L :
        TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) →ₗ[K] Series K A ↦ L z)
      (difference_comp_chartRelations K A f)
    simpa only [LinearMap.comp_apply] using h.symm
  · rintro ⟨c, rfl⟩
    obtain ⟨z, rfl⟩ := relationFactor_surjective K A c
    refine ⟨chartRelations K A f z, ⟨z, rfl⟩, ?_⟩
    have h := congrArg (fun L :
        TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1) →ₗ[K] Series K A ↦ L z)
      (difference_comp_chartRelations K A f)
    simpa only [LinearMap.comp_apply] using h

/-- The quotient of the two chart Tate algebras by the two relation submodules. -/
abbrev ChartRelationQuotient (f : A) :=
  (TateAlgebra A (Fin 1) × TateAlgebra A (Fin 1)) ⧸
    LinearMap.range (chartRelations K A f)

/-- Restricted Laurent coefficients modulo multiplication by `ζ - f`. -/
abbrev LaurentRelationQuotient (f : A) :=
  Series K A ⧸ LinearMap.range (relation K A f)

/-- The diagonal map after quotienting the two chart relation submodules.  The source is written
as the quotient by the zero submodule so that the general quotient-exactness lemma applies
directly. -/
noncomputable def quotientDiagonal (f : A) :
    (A ⧸ (⊥ : Submodule K A)) →ₗ[K] ChartRelationQuotient K A f :=
  (⊥ : Submodule K A).mapQ (LinearMap.range (chartRelations K A f))
    (diagonal K A) bot_le

private theorem chartRelations_le_comap_difference (f : A) :
    LinearMap.range (chartRelations K A f) ≤
      Submodule.comap (difference K A) (LinearMap.range (relation K A f)) := by
  rw [← Submodule.map_le_iff_le_comap, map_range_chartRelations]

/-- Laurent difference after quotienting the chart and Laurent relation submodules. -/
noncomputable def quotientDifference (f : A) :
    ChartRelationQuotient K A f →ₗ[K] LaurentRelationQuotient K A f :=
  (LinearMap.range (chartRelations K A f)).mapQ
    (LinearMap.range (relation K A f)) (difference K A)
    (chartRelations_le_comap_difference K A f)

/-- Exactness of the completed Laurent row descends through the relation submodules. -/
theorem quotient_exact (f : A) :
    Function.Exact (quotientDiagonal K A f) (quotientDifference K A f) := by
  apply (Function.Exact.exact_mapQ_iff (exact K A)
    bot_le (chartRelations_le_comap_difference K A f)).2
  rw [map_range_chartRelations]
  exact inf_le_right

/-- The descended Laurent difference remains surjective. -/
theorem quotientDifference_surjective (f : A) :
    Function.Surjective (quotientDifference K A f) := by
  intro z
  obtain ⟨c, rfl⟩ :=
    (LinearMap.range (relation K A f)).mkQ_surjective z
  obtain ⟨pq, rfl⟩ := difference_surjective K A c
  refine ⟨Submodule.Quotient.mk pq, ?_⟩
  rfl

end CompletedLaurent

end Rigid
