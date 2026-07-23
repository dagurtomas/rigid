import Rigid.AffinoidAlgebra.CompletedLaurentRelation
import Rigid.AffinoidAlgebra.CompletedLaurentTwoVariableQuotient

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The element `T - f` in the two-variable Laurent normal form

After imposing `TS = 1`, multiplication by `T - f` becomes the Laurent coefficient recurrence
`c(z - 1) - f c(z)`.  This file proves that compatibility directly from coefficients.
-/

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- Multiplication by `T - f` in the first variable of `A⟨T,S⟩`. -/
noncomputable def firstVariableRelation (f : A) :
    TateAlgebra A (Fin 2) →ₗ[K] TateAlgebra A (Fin 2) where
  toFun p :=
    (tateVariable A (Fin 2) 0 - TateAlgebra.C A (Fin 2) f) * p
  map_add' p q := by rw [mul_add]
  map_smul' c p := by rw [RingHom.id_apply, mul_smul_comm]

private theorem firstExponent_eq :
    Finsupp.single 0 1 = twoExponent 1 0 := by
  apply Finsupp.ext
  intro i
  fin_cases i <;> simp [twoExponent]

private theorem coe_firstVariable :
    ((tateVariable A (Fin 2) 0 : TateAlgebra A (Fin 2)) :
        MvPowerSeries (Fin 2) A) =
      MvPowerSeries.monomial (twoExponent 1 0) 1 := by
  change MvPowerSeries.X 0 = MvPowerSeries.monomial (twoExponent 1 0) 1
  rw [MvPowerSeries.X_def]
  rw [firstExponent_eq]

/-- Coefficients of multiplication by `T - f`. -/
theorem coeff_firstVariableRelation
    (f : A) (p : TateAlgebra A (Fin 2)) (e : Fin 2 →₀ ℕ) :
    TateAlgebra.coeff A (Fin 2) e (firstVariableRelation K A f p) =
      (if twoExponent 1 0 ≤ e then
        TateAlgebra.coeff A (Fin 2) (e - twoExponent 1 0) p else 0) -
        f * TateAlgebra.coeff A (Fin 2) e p := by
  change MvPowerSeries.coeff e
    ((((tateVariable A (Fin 2) 0 - TateAlgebra.C A (Fin 2) f) * p :
      TateAlgebra A (Fin 2))) : MvPowerSeries (Fin 2) A) = _
  have hcoe :
      ((((tateVariable A (Fin 2) 0 - TateAlgebra.C A (Fin 2) f) * p :
        TateAlgebra A (Fin 2))) : MvPowerSeries (Fin 2) A) =
        (MvPowerSeries.monomial (twoExponent 1 0) 1 - MvPowerSeries.C f) * p.1 := by
    change
      (((tateVariable A (Fin 2) 0 : TateAlgebra A (Fin 2)) :
          MvPowerSeries (Fin 2) A) - MvPowerSeries.C f) * p.1 =
        (MvPowerSeries.monomial (twoExponent 1 0) 1 - MvPowerSeries.C f) * p.1
    rw [coe_firstVariable]
  rw [hcoe, sub_mul, map_sub, MvPowerSeries.coeff_monomial_mul,
    MvPowerSeries.coeff_C_mul, one_mul]
  rfl

private theorem firstExponent_le_twoExponent_iff (i j : ℕ) :
    twoExponent 1 0 ≤ twoExponent i j ↔ 0 < i := by
  constructor
  · intro h
    have h0 := h 0
    have h0' : 1 ≤ i := by
      simpa only [twoExponent_apply_zero] using h0
    omega
  · intro hi k
    fin_cases k
    · simpa [twoExponent] using (Nat.succ_le_iff.mpr hi)
    · simp [twoExponent]

private theorem twoExponent_sub_first (i j : ℕ) (_hi : 0 < i) :
    twoExponent i j - twoExponent 1 0 = twoExponent (i - 1) j := by
  apply Finsupp.ext
  intro k
  fin_cases k <;> simp

private theorem coeff_firstVariableRelation_twoExponent
    (f : A) (p : TateAlgebra A (Fin 2)) (i j : ℕ) :
    TateAlgebra.coeff A (Fin 2) (twoExponent i j)
        (firstVariableRelation K A f p) =
      (if 0 < i then
        TateAlgebra.coeff A (Fin 2) (twoExponent (i - 1) j) p else 0) -
        f * TateAlgebra.coeff A (Fin 2) (twoExponent i j) p := by
  rw [coeff_firstVariableRelation]
  by_cases hi : 0 < i
  · rw [if_pos hi, if_pos ((firstExponent_le_twoExponent_iff i j).2 hi),
      twoExponent_sub_first i j hi]
  · rw [if_neg hi, if_neg (by
      simpa [firstExponent_le_twoExponent_iff] using hi)]

private theorem coeff_firstVariable_mul_twoExponent
    (p : TateAlgebra A (Fin 2)) (i j : ℕ) :
    TateAlgebra.coeff A (Fin 2) (twoExponent i j)
        ((tateVariable A (Fin 2) 0 : TateAlgebra A (Fin 2)) * p) =
      if 0 < i then
        TateAlgebra.coeff A (Fin 2) (twoExponent (i - 1) j) p else 0 := by
  change MvPowerSeries.coeff (twoExponent i j)
      (MvPowerSeries.X 0 * p.1) = _
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
  rw [firstExponent_eq]
  by_cases hi : 0 < i
  · rw [if_pos hi, if_pos ((firstExponent_le_twoExponent_iff i j).2 hi),
      twoExponent_sub_first i j hi]
    rfl
  · rw [if_neg hi, if_neg (by
      simpa [firstExponent_le_twoExponent_iff] using hi)]

private theorem negativeDiagonal_firstVariable
    (p : TateAlgebra A (Fin 2)) (d : ℕ) :
    (∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (twoExponent n (d + n))
        ((tateVariable A (Fin 2) 0 : TateAlgebra A (Fin 2)) * p)) =
      ∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (twoExponent n (d + 1 + n)) p := by
  let a : ℕ → A := fun n ↦
    TateAlgebra.coeff A (Fin 2) (twoExponent n (d + 1 + n)) p
  have ha : Summable a := by
    exact negativeDiagonal_summable A p (d + 1)
  calc
    (∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (twoExponent n (d + n))
        ((tateVariable A (Fin 2) 0 : TateAlgebra A (Fin 2)) * p)) =
        ∑' n : ℕ, match n with
          | 0 => 0
          | m + 1 => a m := by
            apply tsum_congr
            intro n
            cases n with
            | zero =>
                rw [coeff_firstVariable_mul_twoExponent (A := A), if_neg (by omega)]
            | succ m =>
                rw [coeff_firstVariable_mul_twoExponent (A := A), if_pos (by omega)]
                simp only [a]
                congr 2
                omega
    _ = 0 + ∑' n : ℕ, a n := by
      rw [tsum_eq_zero_add' (by simpa using ha)]
    _ = ∑' n : ℕ, TateAlgebra.coeff A (Fin 2)
        (twoExponent n (d + 1 + n)) p := by simp only [zero_add, a]

private theorem diagonalCoefficient_firstVariable
    (p : TateAlgebra A (Fin 2)) (z : ℤ) :
    diagonalCoefficient A
        ((tateVariable A (Fin 2) 0 : TateAlgebra A (Fin 2)) * p) z =
      diagonalCoefficient A p (z - 1) := by
  rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
  · rw [diagonalCoefficient_of_neg A _ z hzneg,
      diagonalCoefficient_of_neg A p (z - 1) (by omega)]
    have htoNat : (-(z - 1)).toNat = (-z).toNat + 1 := by
      calc
        (-(z - 1)).toNat = (-z + 1).toNat := by
          congr 1
          omega
        _ = (-z).toNat + (1 : ℤ).toNat :=
          Int.toNat_add (by omega) (by omega)
        _ = (-z).toNat + 1 := by simp
    rw [htoNat]
    exact negativeDiagonal_firstVariable A p (-z).toNat
  · rw [diagonalCoefficient_of_nonneg A _ 0 (by omega),
      diagonalCoefficient_of_neg A p (0 - 1) (by omega)]
    simpa using negativeDiagonal_firstVariable A p 0
  · rw [diagonalCoefficient_of_nonneg A _ z hzpos.le,
      diagonalCoefficient_of_nonneg A p (z - 1) (by omega)]
    apply tsum_congr
    intro n
    rw [coeff_firstVariable_mul_twoExponent (A := A), if_pos (by
      have hztoNat : 0 < z.toNat := by
        have hcast : (z.toNat : ℤ) = z :=
          Int.toNat_of_nonneg hzpos.le
        omega
      omega)]
    have htoNat : (z - 1).toNat = z.toNat - 1 := by
      calc
        (z - 1).toNat = ((z.toNat : ℤ) - (1 : ℕ)).toNat := by
          congr 1
          rw [Int.toNat_of_nonneg hzpos.le]
          norm_num
        _ = z.toNat - 1 := Int.toNat_sub z.toNat 1
    rw [htoNat]
    congr 2
    omega

private theorem coeff_C_mul_twoVariable
    (f : A) (p : TateAlgebra A (Fin 2)) (e : Fin 2 →₀ ℕ) :
    TateAlgebra.coeff A (Fin 2) e (TateAlgebra.C A (Fin 2) f * p) =
      f * TateAlgebra.coeff A (Fin 2) e p := by
  change MvPowerSeries.coeff e (MvPowerSeries.C f * p.1) =
    f * MvPowerSeries.coeff e p.1
  rw [MvPowerSeries.coeff_C_mul]

private theorem diagonalCoefficient_C_mul
    (f : A) (p : TateAlgebra A (Fin 2)) (z : ℤ) :
    diagonalCoefficient A (TateAlgebra.C A (Fin 2) f * p) z =
      f * diagonalCoefficient A p z := by
  by_cases hz : 0 ≤ z
  · rw [diagonalCoefficient_of_nonneg A _ z hz,
      diagonalCoefficient_of_nonneg A p z hz]
    simp_rw [coeff_C_mul_twoVariable A]
    exact Summable.tsum_mul_left f (positiveDiagonal_summable A p z.toNat)
  · have hzneg : z < 0 := lt_of_not_ge hz
    rw [diagonalCoefficient_of_neg A _ z hzneg,
      diagonalCoefficient_of_neg A p z hzneg]
    simp_rw [coeff_C_mul_twoVariable A]
    exact Summable.tsum_mul_left f (negativeDiagonal_summable A p (-z).toNat)

/-- Diagonal normal form intertwines `T - f` with multiplication by `ζ - f`. -/
theorem twoVariableNormal_firstVariableRelation
    (f : A) (p : TateAlgebra A (Fin 2)) :
    twoVariableNormal K A (firstVariableRelation K A f p) =
      relation K A f (twoVariableNormal K A p) := by
  apply Subtype.ext
  funext z
  change (twoVariableNormal K A
      ((tateVariable A (Fin 2) 0 - TateAlgebra.C A (Fin 2) f) * p)).1 z =
    diagonalCoefficient A p (z - 1) - f * diagonalCoefficient A p z
  rw [sub_mul, map_sub]
  change diagonalCoefficient A
      ((tateVariable A (Fin 2) 0 : TateAlgebra A (Fin 2)) * p) z -
        diagonalCoefficient A (TateAlgebra.C A (Fin 2) f * p) z =
    diagonalCoefficient A p (z - 1) - f * diagonalCoefficient A p z
  rw [diagonalCoefficient_firstVariable A,
    diagonalCoefficient_C_mul A]

/-- The simultaneous linear quotient by `TS - 1` and `T - f`. -/
abbrev TwoRelationQuotient (f : A) :=
  UnitRelationQuotient K A ⧸
    Submodule.map (LinearMap.range (unitRelation K A)).mkQ
      (LinearMap.range (firstVariableRelation K A f))

private theorem map_firstVariableRelationRange
    (f : A) :
    Submodule.map (unitRelationQuotientEquiv K A).toLinearMap
        (Submodule.map (LinearMap.range (unitRelation K A)).mkQ
          (LinearMap.range (firstVariableRelation K A f))) =
      LinearMap.range (relation K A f) := by
  ext c
  constructor
  · rintro ⟨q, ⟨p, ⟨r, rfl⟩, rfl⟩, rfl⟩
    refine ⟨twoVariableNormal K A r, ?_⟩
    symm
    change unitRelationQuotientEquiv K A
      (Submodule.Quotient.mk (firstVariableRelation K A f r)) =
        relation K A f (twoVariableNormal K A r)
    rw [unitRelationQuotientEquiv_mk,
      twoVariableNormal_firstVariableRelation]
  · rintro ⟨c, rfl⟩
    obtain ⟨p, rfl⟩ := twoVariableNormal_surjective K A c
    refine ⟨Submodule.Quotient.mk (firstVariableRelation K A f p), ?_, ?_⟩
    · exact ⟨firstVariableRelation K A f p, ⟨p, rfl⟩, rfl⟩
    · change unitRelationQuotientEquiv K A
        (Submodule.Quotient.mk (firstVariableRelation K A f p)) =
          relation K A f (twoVariableNormal K A p)
      rw [unitRelationQuotientEquiv_mk,
        twoVariableNormal_firstVariableRelation]

/-- The simultaneous two-variable quotient has the Laurent-recurrence normal form. -/
noncomputable def twoRelationQuotientEquiv (f : A) :
    TwoRelationQuotient K A f ≃ₗ[K] LaurentRelationQuotient K A f :=
  Submodule.Quotient.equiv
    (Submodule.map (LinearMap.range (unitRelation K A)).mkQ
      (LinearMap.range (firstVariableRelation K A f)))
    (LinearMap.range (relation K A f))
    (unitRelationQuotientEquiv K A)
    (map_firstVariableRelationRange K A f)

end CompletedLaurent

end Rigid
