import Rigid.AffinoidAlgebra.CompletedLaurent
import Rigid.TateAlgebra.GaussNorm
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Two-variable Tate series and restricted Laurent coefficients

The normal form for the quotient `A⟨T,S⟩ / (TS - 1)` is a restricted Laurent family.  This file
starts the analytic coefficient calculation by summing a two-variable Tate series along the
diagonals `i - j = z`.  The resulting Laurent coefficients again tend to zero.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The exponent `(i,j)` in a two-variable Tate algebra. -/
noncomputable def twoExponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i + Finsupp.single 1 j

@[simp]
theorem twoExponent_apply_zero (i j : ℕ) : twoExponent i j 0 = i := by
  simp [twoExponent]

@[simp]
theorem twoExponent_apply_one (i j : ℕ) : twoExponent i j 1 = j := by
  simp [twoExponent]

private theorem twoExponent_injective_left (j : ℕ) :
    Function.Injective (fun i ↦ twoExponent i j) := by
  intro i i' h
  simpa using congrArg (fun e : Fin 2 →₀ ℕ ↦ e 0) h

private theorem twoExponent_injective_right (i : ℕ) :
    Function.Injective (fun j ↦ twoExponent i j) := by
  intro j j' h
  simpa using congrArg (fun e : Fin 2 →₀ ℕ ↦ e 1) h

private theorem twoExponent_diagonal_injective (d : ℕ) :
    Function.Injective (fun n ↦ twoExponent (d + n) n) := by
  intro n n' h
  simpa using congrArg (fun e : Fin 2 →₀ ℕ ↦ e 1) h

private theorem twoExponent_antidiagonal_injective (d : ℕ) :
    Function.Injective (fun n ↦ twoExponent n (d + n)) := by
  intro n n' h
  simpa using congrArg (fun e : Fin 2 →₀ ℕ ↦ e 0) h

private theorem tendsto_twoVariable_coeff
    (p : TateAlgebra A (Fin 2)) :
    Tendsto (fun e ↦ TateAlgebra.coeff A (Fin 2) e p) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact tendsto_norm_coeff_zero A (Fin 2) p

private theorem coeff_smul_ground
    (c : K) (p : TateAlgebra A (Fin 2)) (e : Fin 2 →₀ ℕ) :
    TateAlgebra.coeff A (Fin 2) e (c • p) =
      c • TateAlgebra.coeff A (Fin 2) e p := by
  change MvPowerSeries.coeff e
      ((c • p : TateAlgebra A (Fin 2)) : MvPowerSeries (Fin 2) A) =
    c • MvPowerSeries.coeff e p.1
  have hcoe :
      ((c • p : TateAlgebra A (Fin 2)) : MvPowerSeries (Fin 2) A) =
        MvPowerSeries.C (algebraMap K A c) * p.1 := by
    rw [Algebra.smul_def]
    rfl
  rw [hcoe, MvPowerSeries.coeff_C_mul, Algebra.smul_def]

theorem positiveDiagonal_summable
    (p : TateAlgebra A (Fin 2)) (d : ℕ) :
    Summable (fun n ↦ TateAlgebra.coeff A (Fin 2) (twoExponent (d + n) n) p) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact (tendsto_twoVariable_coeff A p).comp
    (twoExponent_diagonal_injective d).tendsto_cofinite

theorem negativeDiagonal_summable
    (p : TateAlgebra A (Fin 2)) (d : ℕ) :
    Summable (fun n ↦ TateAlgebra.coeff A (Fin 2) (twoExponent n (d + n)) p) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact (tendsto_twoVariable_coeff A p).comp
    (twoExponent_antidiagonal_injective d).tendsto_cofinite

/-- Sum the coefficients of a two-variable Tate series along the diagonal `i - j = z`. -/
noncomputable def diagonalCoefficient (p : TateAlgebra A (Fin 2)) (z : ℤ) : A :=
  if _hz : 0 ≤ z then
    ∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (twoExponent (z.toNat + n) n) p
  else
    ∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (twoExponent n ((-z).toNat + n)) p

theorem diagonalCoefficient_of_nonneg
    (p : TateAlgebra A (Fin 2)) (z : ℤ) (hz : 0 ≤ z) :
    diagonalCoefficient A p z =
      ∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (twoExponent (z.toNat + n) n) p := by
  simp [diagonalCoefficient, hz]

theorem diagonalCoefficient_of_neg
    (p : TateAlgebra A (Fin 2)) (z : ℤ) (hz : z < 0) :
    diagonalCoefficient A p z =
      ∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (twoExponent n ((-z).toNat + n)) p := by
  simp [diagonalCoefficient, not_le_of_gt hz]

private def exponentDegree (e : Fin 2 →₀ ℕ) : ℤ :=
  (e 0 : ℤ) - (e 1 : ℤ)

private theorem exponentDegree_positiveDiagonal
    (z : ℤ) (hz : 0 ≤ z) (n : ℕ) :
    exponentDegree (twoExponent (z.toNat + n) n) = z := by
  simp only [exponentDegree, twoExponent_apply_zero, twoExponent_apply_one]
  push_cast
  rw [Int.toNat_of_nonneg hz]
  omega

private theorem exponentDegree_negativeDiagonal
    (z : ℤ) (hz : z < 0) (n : ℕ) :
    exponentDegree (twoExponent n ((-z).toNat + n)) = z := by
  simp only [exponentDegree, twoExponent_apply_zero, twoExponent_apply_one]
  push_cast
  rw [Int.toNat_of_nonneg (Int.neg_nonneg.mpr hz.le)]
  omega

private theorem tendsto_diagonalCoefficient
    (p : TateAlgebra A (Fin 2)) :
    Tendsto (diagonalCoefficient A p) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have heventually :
      ∀ᶠ e : Fin 2 →₀ ℕ in cofinite,
        ‖TateAlgebra.coeff A (Fin 2) e p‖ < ε / 2 := by
    have hnorm :
        Tendsto (fun e ↦ ‖TateAlgebra.coeff A (Fin 2) e p‖) cofinite (𝓝 0) :=
      tendsto_norm_coeff_zero A (Fin 2) p
    simpa [Real.dist_eq] using Metric.tendsto_nhds.mp hnorm (ε / 2) hhalf
  let bad : Set (Fin 2 →₀ ℕ) :=
    {e | ε / 2 ≤ ‖TateAlgebra.coeff A (Fin 2) e p‖}
  have hbad : bad.Finite := by
    have hcompl : badᶜ ∈ (cofinite : Filter (Fin 2 →₀ ℕ)) := by
      simpa [bad, Set.compl_setOf, not_le] using heventually
    simpa using mem_cofinite.mp hcompl
  let badDegrees : Set ℤ := exponentDegree '' bad
  have hbadDegrees : badDegrees.Finite := hbad.image exponentDegree
  filter_upwards [hbadDegrees.compl_mem_cofinite] with z hz
  rw [dist_zero_right]
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  by_cases hz0 : 0 ≤ z
  · rw [diagonalCoefficient_of_nonneg A p z hz0]
    refine (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (f := fun n : ℕ ↦ TateAlgebra.coeff A (Fin 2)
        (twoExponent (z.toNat + n) n) p) hhalf.le fun n ↦ ?_).trans_lt
      (half_lt_self hε)
    apply le_of_lt
    by_contra hn
    have hmemBad :
        twoExponent (z.toNat + n) n ∈ bad := by
      change ε / 2 ≤ ‖TateAlgebra.coeff A (Fin 2) (twoExponent (z.toNat + n) n) p‖
      exact le_of_not_gt hn
    exact hz ⟨twoExponent (z.toNat + n) n, hmemBad,
      exponentDegree_positiveDiagonal z hz0 n⟩
  · have hzneg : z < 0 := lt_of_not_ge hz0
    rw [diagonalCoefficient_of_neg A p z hzneg]
    refine (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (f := fun n : ℕ ↦ TateAlgebra.coeff A (Fin 2)
        (twoExponent n ((-z).toNat + n)) p) hhalf.le fun n ↦ ?_).trans_lt
      (half_lt_self hε)
    apply le_of_lt
    by_contra hn
    have hmemBad :
        twoExponent n ((-z).toNat + n) ∈ bad := by
      change ε / 2 ≤
        ‖TateAlgebra.coeff A (Fin 2) (twoExponent n ((-z).toNat + n)) p‖
      exact le_of_not_gt hn
    exact hz ⟨twoExponent n ((-z).toNat + n), hmemBad,
      exponentDegree_negativeDiagonal z hzneg n⟩

/-- Diagonal summation from two-variable Tate series to restricted Laurent coefficients. -/
noncomputable def twoVariableNormal :
    TateAlgebra A (Fin 2) →ₗ[K] Series K A where
  toFun p := ⟨diagonalCoefficient A p, tendsto_diagonalCoefficient A p⟩
  map_add' p q := by
    ext z
    change diagonalCoefficient A (p + q) z =
      diagonalCoefficient A p z + diagonalCoefficient A q z
    by_cases hz : 0 ≤ z
    · rw [diagonalCoefficient_of_nonneg A (p + q) z hz,
        diagonalCoefficient_of_nonneg A p z hz,
        diagonalCoefficient_of_nonneg A q z hz]
      change
        (∑' n : ℕ, (p.1 (twoExponent (z.toNat + n) n) +
          q.1 (twoExponent (z.toNat + n) n))) =
        (∑' n : ℕ, p.1 (twoExponent (z.toNat + n) n)) +
          ∑' n : ℕ, q.1 (twoExponent (z.toNat + n) n)
      exact
        (positiveDiagonal_summable A p z.toNat).tsum_add
          (positiveDiagonal_summable A q z.toNat)
    · have hzneg : z < 0 := lt_of_not_ge hz
      rw [diagonalCoefficient_of_neg A (p + q) z hzneg,
        diagonalCoefficient_of_neg A p z hzneg,
        diagonalCoefficient_of_neg A q z hzneg]
      change
        (∑' n : ℕ, (p.1 (twoExponent n ((-z).toNat + n)) +
          q.1 (twoExponent n ((-z).toNat + n)))) =
        (∑' n : ℕ, p.1 (twoExponent n ((-z).toNat + n))) +
          ∑' n : ℕ, q.1 (twoExponent n ((-z).toNat + n))
      exact
        (negativeDiagonal_summable A p (-z).toNat).tsum_add
          (negativeDiagonal_summable A q (-z).toNat)
  map_smul' c p := by
    ext z
    change diagonalCoefficient A (c • p) z = c • diagonalCoefficient A p z
    by_cases hz : 0 ≤ z
    · rw [diagonalCoefficient_of_nonneg A (c • p) z hz,
        diagonalCoefficient_of_nonneg A p z hz]
      simp_rw [coeff_smul_ground K A]
      exact
        (tsum_const_smul'' c :
          (∑' n : ℕ, c • TateAlgebra.coeff A (Fin 2)
            (twoExponent (z.toNat + n) n) p) =
          c • ∑' n : ℕ, TateAlgebra.coeff A (Fin 2)
            (twoExponent (z.toNat + n) n) p)
    · have hzneg : z < 0 := lt_of_not_ge hz
      rw [diagonalCoefficient_of_neg A (c • p) z hzneg,
        diagonalCoefficient_of_neg A p z hzneg]
      simp_rw [coeff_smul_ground K A]
      exact
        (tsum_const_smul'' c :
          (∑' n : ℕ, c • TateAlgebra.coeff A (Fin 2)
            (twoExponent n ((-z).toNat + n)) p) =
          c • ∑' n : ℕ, TateAlgebra.coeff A (Fin 2)
            (twoExponent n ((-z).toNat + n)) p)

@[simp]
theorem twoVariableNormal_apply
    (p : TateAlgebra A (Fin 2)) (z : ℤ) :
    (twoVariableNormal K A p).1 z = diagonalCoefficient A p z :=
  rfl

private def axisCoefficient (c : Series K A) (e : Fin 2 →₀ ℕ) : A :=
  if e 0 = 0 ∨ e 1 = 0 then c.1 (exponentDegree e) else 0

private theorem exponentDegree_injectiveOn_axes :
    Set.InjOn exponentDegree {e : Fin 2 →₀ ℕ | e 0 = 0 ∨ e 1 = 0} := by
  intro e he e' he' hdegree
  apply Finsupp.ext
  intro i
  fin_cases i
  · rcases he with he0 | he1 <;> rcases he' with he0' | he1'
    · simp [he0, he0']
    · have hcast :
          (e 0 : ℤ) - (e 1 : ℤ) = (e' 0 : ℤ) - (e' 1 : ℤ) := hdegree
      rw [he0, he1'] at hcast
      simp only [Nat.cast_zero, zero_sub, sub_zero] at hcast
      have he0'zero : e' 0 = 0 := by omega
      simp [he0, he0'zero]
    · have hcast :
          (e 0 : ℤ) - (e 1 : ℤ) = (e' 0 : ℤ) - (e' 1 : ℤ) := hdegree
      rw [he1, he0'] at hcast
      simp only [Nat.cast_zero, sub_zero, zero_sub] at hcast
      have he0zero : e 0 = 0 := by omega
      simp [he0zero, he0']
    · have hcast :
          (e 0 : ℤ) - (e 1 : ℤ) = (e' 0 : ℤ) - (e' 1 : ℤ) := hdegree
      rw [he1, he1'] at hcast
      simp only [Nat.cast_zero, sub_zero] at hcast
      exact_mod_cast hcast
  · rcases he with he0 | he1 <;> rcases he' with he0' | he1'
    · have hcast :
          (e 0 : ℤ) - (e 1 : ℤ) = (e' 0 : ℤ) - (e' 1 : ℤ) := hdegree
      rw [he0, he0'] at hcast
      simp only [Nat.cast_zero, zero_sub] at hcast
      exact_mod_cast neg_injective hcast
    · have hcast :
          (e 0 : ℤ) - (e 1 : ℤ) = (e' 0 : ℤ) - (e' 1 : ℤ) := hdegree
      rw [he0, he1'] at hcast
      simp only [Nat.cast_zero, zero_sub, sub_zero] at hcast
      have : e 1 = 0 := by omega
      simp [this, he1']
    · have hcast :
          (e 0 : ℤ) - (e 1 : ℤ) = (e' 0 : ℤ) - (e' 1 : ℤ) := hdegree
      rw [he1, he0'] at hcast
      simp only [Nat.cast_zero, sub_zero, zero_sub] at hcast
      have : e' 1 = 0 := by omega
      simp [he1, this]
    · simp [he1, he1']

private theorem tendsto_axisCoefficient
    (c : Series K A) :
    Tendsto (axisCoefficient K A c) cofinite (𝓝 0) := by
  rw [tendsto_def]
  intro s hs
  have hzero : (0 : A) ∈ s := mem_of_mem_nhds hs
  have hc : {z | c.1 z ∈ s} ∈ (cofinite : Filter ℤ) := c.2 hs
  rw [mem_cofinite] at hc ⊢
  have hbadDegree : Set.Finite {z : ℤ | c.1 z ∉ s} := by
    simpa only [Set.compl_setOf] using hc
  let bad : Set (Fin 2 →₀ ℕ) := {e | axisCoefficient K A c e ∉ s}
  change bad.Finite
  apply Set.Finite.of_finite_image
  · exact hbadDegree.subset fun z hz ↦ by
      obtain ⟨e, he, rfl⟩ := hz
      change axisCoefficient K A c e ∉ s at he
      by_cases haxis : e 0 = 0 ∨ e 1 = 0
      · simpa [axisCoefficient, haxis] using he
      · exact (he (by simpa [axisCoefficient, haxis] using hzero)).elim
  · intro e he e' he' hdegree
    apply exponentDegree_injectiveOn_axes
    · by_contra haxis
      change axisCoefficient K A c e ∉ s at he
      have haxis' : ¬(e 0 = 0 ∨ e 1 = 0) := by simpa using haxis
      apply he
      rw [axisCoefficient, if_neg haxis']
      exact hzero
    · by_contra haxis
      change axisCoefficient K A c e' ∉ s at he'
      have haxis' : ¬(e' 0 = 0 ∨ e' 1 = 0) := by simpa using haxis
      apply he'
      rw [axisCoefficient, if_neg haxis']
      exact hzero
    · exact hdegree

/-- Put a restricted Laurent family on the two coordinate axes in `A⟨T,S⟩`. -/
noncomputable def axisSeries (c : Series K A) : TateAlgebra A (Fin 2) :=
  ⟨axisCoefficient K A c, by
    change Tendsto (fun e : Fin 2 →₀ ℕ ↦
      ‖axisCoefficient K A c e‖ * e.prod fun _ n ↦ (1 : ℝ) ^ n) cofinite (𝓝 0)
    simp only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
    exact tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_axisCoefficient K A c)⟩

@[simp]
theorem coeff_axisSeries (c : Series K A) (e : Fin 2 →₀ ℕ) :
    TateAlgebra.coeff A (Fin 2) e (axisSeries K A c) = axisCoefficient K A c e :=
  rfl

theorem coeff_axisSeries_twoExponent (c : Series K A) (i j : ℕ) :
    TateAlgebra.coeff A (Fin 2) (twoExponent i j) (axisSeries K A c) =
      if i = 0 ∨ j = 0 then c.1 ((i : ℤ) - (j : ℤ)) else 0 := by
  change axisCoefficient K A c (twoExponent i j) =
    if i = 0 ∨ j = 0 then c.1 ((i : ℤ) - (j : ℤ)) else 0
  simp [axisCoefficient, exponentDegree]

private theorem axisCoefficient_positive_zero
    (c : Series K A) (z : ℤ) (hz : 0 ≤ z) :
    axisCoefficient K A c (twoExponent z.toNat 0) = c.1 z := by
  rw [axisCoefficient, if_pos (Or.inr (twoExponent_apply_one z.toNat 0))]
  rw [show exponentDegree (twoExponent z.toNat 0) = z by
    simpa using exponentDegree_positiveDiagonal z hz 0]

private theorem axisCoefficient_positive_succ
    (c : Series K A) (z : ℤ) (_hz : 0 ≤ z) (n : ℕ) :
    axisCoefficient K A c (twoExponent (z.toNat + (n + 1)) (n + 1)) = 0 := by
  rw [axisCoefficient, if_neg]
  simp only [twoExponent_apply_zero, twoExponent_apply_one]
  omega

private theorem axisCoefficient_negative_zero
    (c : Series K A) (z : ℤ) (hz : z < 0) :
    axisCoefficient K A c (twoExponent 0 (-z).toNat) = c.1 z := by
  rw [axisCoefficient, if_pos (Or.inl (twoExponent_apply_zero 0 (-z).toNat))]
  rw [show exponentDegree (twoExponent 0 (-z).toNat) = z by
    simpa using exponentDegree_negativeDiagonal z hz 0]

private theorem axisCoefficient_negative_succ
    (c : Series K A) (z : ℤ) (_hz : z < 0) (n : ℕ) :
    axisCoefficient K A c (twoExponent (n + 1) ((-z).toNat + (n + 1))) = 0 := by
  rw [axisCoefficient, if_neg]
  simp only [twoExponent_apply_zero, twoExponent_apply_one]
  omega

/-- Diagonal normal form sends the axis representative back to its Laurent family. -/
theorem twoVariableNormal_axisSeries (c : Series K A) :
    twoVariableNormal K A (axisSeries K A c) = c := by
  apply Subtype.ext
  funext z
  rw [twoVariableNormal_apply]
  by_cases hz : 0 ≤ z
  · rw [diagonalCoefficient_of_nonneg A _ z hz]
    rw [tsum_eq_single 0]
    · exact axisCoefficient_positive_zero K A c z hz
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact axisCoefficient_positive_succ K A c z hz m
  · have hzneg : z < 0 := lt_of_not_ge hz
    rw [diagonalCoefficient_of_neg A _ z hzneg]
    rw [tsum_eq_single 0]
    · exact axisCoefficient_negative_zero K A c z hzneg
    · intro n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      exact axisCoefficient_negative_succ K A c z hzneg m

/-- Diagonal normal form is onto. -/
theorem twoVariableNormal_surjective :
    Function.Surjective (twoVariableNormal K A) :=
  fun c ↦ ⟨axisSeries K A c, twoVariableNormal_axisSeries K A c⟩

private noncomputable def tailExponent (e : Fin 2 →₀ ℕ) (n : ℕ) : Fin 2 →₀ ℕ :=
  e + twoExponent (n + 1) (n + 1)

private theorem tailExponent_injective (e : Fin 2 →₀ ℕ) :
    Function.Injective (tailExponent e) := by
  intro n n' h
  have hzero := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
  simpa [tailExponent] using hzero

private theorem tail_summable
    (p : TateAlgebra A (Fin 2)) (e : Fin 2 →₀ ℕ) :
    Summable (fun n ↦ TateAlgebra.coeff A (Fin 2) (tailExponent e n) p) := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  exact (tendsto_twoVariable_coeff A p).comp
    (tailExponent_injective e).tendsto_cofinite

/-- The sum of the coefficients strictly farther along the diagonal through `e`. -/
noncomputable def tailCoefficient
    (p : TateAlgebra A (Fin 2)) (e : Fin 2 →₀ ℕ) : A :=
  ∑' n : ℕ, TateAlgebra.coeff A (Fin 2) (tailExponent e n) p

private theorem le_tailExponent (e : Fin 2 →₀ ℕ) (n : ℕ) :
    e ≤ tailExponent e n := by
  intro i
  simp only [tailExponent, Finsupp.add_apply]
  omega

private theorem tendsto_tailCoefficient
    (p : TateAlgebra A (Fin 2)) :
    Tendsto (tailCoefficient A p) cofinite (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have heventually :
      ∀ᶠ e : Fin 2 →₀ ℕ in cofinite,
        ‖TateAlgebra.coeff A (Fin 2) e p‖ < ε / 2 := by
    have hnorm :
        Tendsto (fun e ↦ ‖TateAlgebra.coeff A (Fin 2) e p‖) cofinite (𝓝 0) :=
      tendsto_norm_coeff_zero A (Fin 2) p
    simpa [Real.dist_eq] using Metric.tendsto_nhds.mp hnorm (ε / 2) hhalf
  let bad : Set (Fin 2 →₀ ℕ) :=
    {e | ε / 2 ≤ ‖TateAlgebra.coeff A (Fin 2) e p‖}
  have hbad : bad.Finite := by
    have hcompl : badᶜ ∈ (cofinite : Filter (Fin 2 →₀ ℕ)) := by
      simpa [bad, Set.compl_setOf, not_le] using heventually
    simpa using mem_cofinite.mp hcompl
  let badLower : Set (Fin 2 →₀ ℕ) := ⋃ b ∈ bad, Set.Iic b
  have hbadLower : badLower.Finite := by
    obtain ⟨bound, hbound⟩ :=
      Set.exists_upper_bound_image bad Finsupp.degree hbad
    apply (Finsupp.finite_of_degree_le bound.degree).subset
    intro e he
    obtain ⟨b, hb, heb⟩ := Set.mem_iUnion₂.mp he
    exact (Finsupp.degree_mono heb).trans (hbound b hb)
  filter_upwards [hbadLower.compl_mem_cofinite] with e he
  rw [dist_zero_right]
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  refine (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (f := fun n : ℕ ↦ TateAlgebra.coeff A (Fin 2) (tailExponent e n) p)
    hhalf.le fun n ↦ ?_).trans_lt (half_lt_self hε)
  apply le_of_lt
  by_contra hn
  have htailBad : tailExponent e n ∈ bad := by
    change ε / 2 ≤ ‖TateAlgebra.coeff A (Fin 2) (tailExponent e n) p‖
    exact le_of_not_gt hn
  apply he
  exact Set.mem_iUnion₂.mpr
    ⟨tailExponent e n, htailBad, le_tailExponent e n⟩

/-- The diagonal-tail series used to divide by `TS - 1`. -/
noncomputable def tailSeries (p : TateAlgebra A (Fin 2)) : TateAlgebra A (Fin 2) :=
  ⟨tailCoefficient A p, by
    change Tendsto (fun e : Fin 2 →₀ ℕ ↦
      ‖tailCoefficient A p e‖ * e.prod fun _ n ↦ (1 : ℝ) ^ n) cofinite (𝓝 0)
    simp only [one_pow, Finsupp.prod, Finset.prod_const_one, mul_one]
    exact tendsto_zero_iff_norm_tendsto_zero.mp (tendsto_tailCoefficient A p)⟩

@[simp]
theorem coeff_tailSeries (p : TateAlgebra A (Fin 2)) (e : Fin 2 →₀ ℕ) :
    TateAlgebra.coeff A (Fin 2) e (tailSeries A p) = tailCoefficient A p e :=
  rfl

private theorem coe_twoVariableProduct :
    ((tateVariable A (Fin 2) 0 * tateVariable A (Fin 2) 1 :
        TateAlgebra A (Fin 2)) : MvPowerSeries (Fin 2) A) =
      MvPowerSeries.monomial (twoExponent 1 1) 1 := by
  change MvPowerSeries.X 0 * MvPowerSeries.X 1 =
    MvPowerSeries.monomial (twoExponent 1 1) 1
  rw [MvPowerSeries.X_def, MvPowerSeries.X_def,
    MvPowerSeries.monomial_mul_monomial]
  simp [twoExponent]

/-- Multiplication by `TS - 1` in the two-variable Tate algebra. -/
noncomputable def unitRelation :
    TateAlgebra A (Fin 2) →ₗ[K] TateAlgebra A (Fin 2) where
  toFun p :=
    (tateVariable A (Fin 2) 0 * tateVariable A (Fin 2) 1 - 1) * p
  map_add' p q := by rw [mul_add]
  map_smul' c p := by rw [RingHom.id_apply, mul_smul_comm]

/-- Coefficients of multiplication by `TS - 1`. -/
theorem coeff_unitRelation (p : TateAlgebra A (Fin 2)) (e : Fin 2 →₀ ℕ) :
    TateAlgebra.coeff A (Fin 2) e (unitRelation K A p) =
      (if twoExponent 1 1 ≤ e then
        TateAlgebra.coeff A (Fin 2) (e - twoExponent 1 1) p else 0) -
        TateAlgebra.coeff A (Fin 2) e p := by
  change MvPowerSeries.coeff e
    ((((tateVariable A (Fin 2) 0 * tateVariable A (Fin 2) 1 - 1) * p :
      TateAlgebra A (Fin 2))) : MvPowerSeries (Fin 2) A) = _
  have hcoe :
      ((((tateVariable A (Fin 2) 0 * tateVariable A (Fin 2) 1 - 1) * p :
        TateAlgebra A (Fin 2))) : MvPowerSeries (Fin 2) A) =
        (MvPowerSeries.monomial (twoExponent 1 1) 1 - 1) * p.1 := by
    change
      (((tateVariable A (Fin 2) 0 * tateVariable A (Fin 2) 1 :
        TateAlgebra A (Fin 2)) : MvPowerSeries (Fin 2) A) - 1) * p.1 =
        (MvPowerSeries.monomial (twoExponent 1 1) 1 - 1) * p.1
    rw [coe_twoVariableProduct]
  rw [hcoe, sub_mul, map_sub, MvPowerSeries.coeff_monomial_mul, one_mul, one_mul]
  rfl

private theorem twoExponent_one_le_iff (i j : ℕ) :
    twoExponent 1 1 ≤ twoExponent i j ↔ 0 < i ∧ 0 < j := by
  constructor
  · intro h
    constructor
    · have h0 := h 0
      have h0' : 1 ≤ i := by
        simpa only [twoExponent_apply_zero] using h0
      omega
    · have h1 := h 1
      have h1' : 1 ≤ j := by
        simpa only [twoExponent_apply_one] using h1
      omega
  · rintro ⟨hi, hj⟩ k
    fin_cases k
    · simpa [twoExponent] using (Nat.succ_le_iff.mpr hi)
    · simpa [twoExponent] using (Nat.succ_le_iff.mpr hj)

private theorem twoExponent_sub_one (i j : ℕ) (_hi : 0 < i) (_hj : 0 < j) :
    twoExponent i j - twoExponent 1 1 = twoExponent (i - 1) (j - 1) := by
  apply Finsupp.ext
  intro k
  fin_cases k <;> simp

theorem coeff_unitRelation_twoExponent
    (p : TateAlgebra A (Fin 2)) (i j : ℕ) :
    TateAlgebra.coeff A (Fin 2) (twoExponent i j) (unitRelation K A p) =
      if 0 < i ∧ 0 < j then
        TateAlgebra.coeff A (Fin 2) (twoExponent (i - 1) (j - 1)) p -
          TateAlgebra.coeff A (Fin 2) (twoExponent i j) p
      else
        -TateAlgebra.coeff A (Fin 2) (twoExponent i j) p := by
  rw [coeff_unitRelation]
  by_cases h : 0 < i ∧ 0 < j
  · rw [if_pos h, if_pos ((twoExponent_one_le_iff i j).2 h),
      twoExponent_sub_one i j h.1 h.2]
  · rw [if_neg h, if_neg (by simpa [twoExponent_one_le_iff] using h)]
    simp

private theorem tailExponent_twoExponent (i j n : ℕ) :
    tailExponent (twoExponent i j) n = twoExponent (i + (n + 1)) (j + (n + 1)) := by
  apply Finsupp.ext
  intro k
  fin_cases k <;> simp [tailExponent, twoExponent]

private theorem tailCoefficient_twoExponent
    (p : TateAlgebra A (Fin 2)) (i j : ℕ) :
    tailCoefficient A p (twoExponent i j) =
      ∑' n : ℕ, TateAlgebra.coeff A (Fin 2)
        (twoExponent (i + (n + 1)) (j + (n + 1))) p := by
  unfold tailCoefficient
  congr 1
  funext n
  rw [tailExponent_twoExponent]

private theorem tailCoefficient_rec
    (p : TateAlgebra A (Fin 2)) (i j : ℕ) :
    tailCoefficient A p (twoExponent i j) =
      TateAlgebra.coeff A (Fin 2) (twoExponent (i + 1) (j + 1)) p +
        tailCoefficient A p (twoExponent (i + 1) (j + 1)) := by
  unfold tailCoefficient
  rw [(tail_summable A p (twoExponent i j)).tsum_eq_zero_add]
  simp_rw [tailExponent_twoExponent]
  congr 1
  apply tsum_congr
  intro n
  congr 2 <;> omega

private theorem exponentDegree_twoExponent (i j : ℕ) :
    exponentDegree (twoExponent i j) = (i : ℤ) - (j : ℤ) := by
  simp only [exponentDegree, twoExponent_apply_zero, twoExponent_apply_one]

private theorem axisCoefficient_normal_of_right_zero
    (p : TateAlgebra A (Fin 2)) (i : ℕ) :
    axisCoefficient K A (twoVariableNormal K A p) (twoExponent i 0) =
      TateAlgebra.coeff A (Fin 2) (twoExponent i 0) p +
        tailCoefficient A p (twoExponent i 0) := by
  rw [axisCoefficient, if_pos (Or.inr (twoExponent_apply_one i 0))]
  rw [twoVariableNormal_apply, exponentDegree_twoExponent]
  simp only [Nat.cast_zero, sub_zero]
  have hz : 0 ≤ (i : ℤ) - (0 : ℤ) := by omega
  rw [diagonalCoefficient_of_nonneg A p _ (by omega)]
  have htoNat : (i : ℤ).toNat = i := by simp
  rw [htoNat, (positiveDiagonal_summable A p i).tsum_eq_zero_add,
    tailCoefficient_twoExponent A p i 0]
  congr 1
  apply tsum_congr
  intro n
  simp

private theorem axisCoefficient_normal_of_left_zero
    (p : TateAlgebra A (Fin 2)) (j : ℕ) (hj : 0 < j) :
    axisCoefficient K A (twoVariableNormal K A p) (twoExponent 0 j) =
      TateAlgebra.coeff A (Fin 2) (twoExponent 0 j) p +
        tailCoefficient A p (twoExponent 0 j) := by
  rw [axisCoefficient, if_pos (Or.inl (twoExponent_apply_zero 0 j))]
  rw [twoVariableNormal_apply, exponentDegree_twoExponent]
  simp only [Nat.cast_zero, zero_sub]
  have hz : (0 : ℤ) - (j : ℤ) < 0 := by omega
  rw [diagonalCoefficient_of_neg A p _ (by omega)]
  have htoNat : (-(-(j : ℤ))).toNat = j := by
    simp
  rw [htoNat, (negativeDiagonal_summable A p j).tsum_eq_zero_add,
    tailCoefficient_twoExponent A p 0 j]
  congr 1
  apply tsum_congr
  intro n
  simp

private theorem coeff_unitRelation_tailSeries_twoExponent
    (p : TateAlgebra A (Fin 2)) (i j : ℕ) :
    TateAlgebra.coeff A (Fin 2) (twoExponent i j)
        (unitRelation K A (tailSeries A p)) =
      TateAlgebra.coeff A (Fin 2) (twoExponent i j)
        (p - axisSeries K A (twoVariableNormal K A p)) := by
  rw [coeff_unitRelation_twoExponent]
  change
    (if 0 < i ∧ 0 < j then
      tailCoefficient A p (twoExponent (i - 1) (j - 1)) -
        tailCoefficient A p (twoExponent i j)
    else -tailCoefficient A p (twoExponent i j)) =
      TateAlgebra.coeff A (Fin 2) (twoExponent i j) p -
        axisCoefficient K A (twoVariableNormal K A p) (twoExponent i j)
  by_cases hboth : 0 < i ∧ 0 < j
  · rw [if_pos hboth]
    rw [axisCoefficient, if_neg (by
      simp only [twoExponent_apply_zero, twoExponent_apply_one]
      omega)]
    simp only [sub_zero]
    have hrec := tailCoefficient_rec A p (i - 1) (j - 1)
    have hi : i - 1 + 1 = i := by omega
    have hj : j - 1 + 1 = j := by omega
    rw [hi, hj] at hrec
    rw [hrec]
    abel
  · rw [if_neg hboth]
    rcases not_and_or.mp hboth with hi | hj
    · have hi0 : i = 0 := Nat.eq_zero_of_not_pos hi
      subst i
      by_cases hj0 : j = 0
      · subst j
        rw [axisCoefficient_normal_of_right_zero K A p 0]
        abel
      · rw [axisCoefficient_normal_of_left_zero K A p j
          (Nat.pos_of_ne_zero hj0)]
        abel
    · have hj0 : j = 0 := Nat.eq_zero_of_not_pos hj
      rw [hj0, axisCoefficient_normal_of_right_zero K A p i]
      abel

/-- Division with remainder on the coordinate axes for `TS - 1`. -/
theorem unitRelation_tailSeries
    (p : TateAlgebra A (Fin 2)) :
    unitRelation K A (tailSeries A p) =
      p - axisSeries K A (twoVariableNormal K A p) := by
  apply TateAlgebra.ext
  intro e
  have he : e = twoExponent (e 0) (e 1) := by
    apply Finsupp.ext
    intro k
    fin_cases k <;> simp
  rw [he]
  exact coeff_unitRelation_tailSeries_twoExponent K A p (e 0) (e 1)

private theorem tsum_telescopingRelation
    (a : ℕ → A) (ha : Summable a) :
    (∑' n : ℕ, match n with
      | 0 => -a 0
      | m + 1 => a m - a (m + 1)) = 0 := by
  have hshift : Summable (fun n : ℕ ↦ a (n + 1)) :=
    (summable_nat_add_iff 1).2 ha
  have htail : Summable (fun n : ℕ ↦ a n - a (n + 1)) :=
    ha.sub hshift
  rw [tsum_eq_zero_add' (by simpa using htail)]
  rw [ha.tsum_sub hshift]
  rw [ha.tsum_eq_zero_add]
  simp

/-- Diagonal normal form kills the relation `TS - 1`. -/
theorem twoVariableNormal_unitRelation
    (p : TateAlgebra A (Fin 2)) :
    twoVariableNormal K A (unitRelation K A p) = 0 := by
  apply Subtype.ext
  funext z
  change diagonalCoefficient A (unitRelation K A p) z = 0
  by_cases hz : 0 ≤ z
  · rw [diagonalCoefficient_of_nonneg A _ z hz]
    let a : ℕ → A := fun n ↦ TateAlgebra.coeff A (Fin 2)
      (twoExponent (z.toNat + n) n) p
    calc
      (∑' n : ℕ, TateAlgebra.coeff A (Fin 2)
          (twoExponent (z.toNat + n) n) (unitRelation K A p)) =
          ∑' n : ℕ, match n with
            | 0 => -a 0
            | m + 1 => a m - a (m + 1) := by
              apply tsum_congr
              intro n
              cases n with
              | zero =>
                  simp only [Nat.add_zero]
                  rw [coeff_unitRelation_twoExponent K A p z.toNat 0]
                  simp [a]
              | succ m =>
                  rw [coeff_unitRelation_twoExponent, if_pos (by omega)]
                  simp only [a]
                  congr 2
      _ = 0 := tsum_telescopingRelation A a (positiveDiagonal_summable A p z.toNat)
  · have hzneg : z < 0 := lt_of_not_ge hz
    rw [diagonalCoefficient_of_neg A _ z hzneg]
    let a : ℕ → A := fun n ↦ TateAlgebra.coeff A (Fin 2)
      (twoExponent n ((-z).toNat + n)) p
    calc
      (∑' n : ℕ, TateAlgebra.coeff A (Fin 2)
          (twoExponent n ((-z).toNat + n)) (unitRelation K A p)) =
          ∑' n : ℕ, match n with
            | 0 => -a 0
            | m + 1 => a m - a (m + 1) := by
              apply tsum_congr
              intro n
              cases n with
              | zero =>
                  simp only [Nat.add_zero]
                  rw [coeff_unitRelation_twoExponent K A p 0 (-z).toNat]
                  simp [a]
              | succ m =>
                  rw [coeff_unitRelation_twoExponent, if_pos (by omega)]
                  simp only [a]
                  congr 2
      _ = 0 := tsum_telescopingRelation A a (negativeDiagonal_summable A p (-z).toNat)

@[simp]
theorem axisSeries_zero :
    axisSeries K A 0 = 0 := by
  apply TateAlgebra.ext
  intro e
  change axisCoefficient K A 0 e = 0
  simp [axisCoefficient]

/-- The kernel of diagonal normal form is exactly the range of multiplication by `TS - 1`. -/
theorem range_unitRelation_eq_ker_twoVariableNormal :
    LinearMap.range (unitRelation K A) = LinearMap.ker (twoVariableNormal K A) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact twoVariableNormal_unitRelation K A q
  · intro hp
    refine ⟨tailSeries A p, ?_⟩
    rw [unitRelation_tailSeries, LinearMap.mem_ker.mp hp, axisSeries_zero, sub_zero]

end CompletedLaurent

end Rigid
