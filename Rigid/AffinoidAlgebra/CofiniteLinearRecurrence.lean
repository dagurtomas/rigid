import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Vanishing of restricted linear recurrences

A bi-infinite sequence in a finite-dimensional nonarchimedean normed space which tends to zero
along the cofinite filter cannot be an orbit of a linear endomorphism unless it is zero.  This is
the finite-dimensional input used to prove injectivity of multiplication by `ζ - f` on restricted
Laurent coefficients.

The proof is elementary.  Cayley--Hamilton gives a scalar polynomial recurrence.  Choose the last
coefficient of largest norm and the last term of largest norm.  In the corresponding recurrence,
one summand strictly dominates all the others, contradicting the ultrametric inequality.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

namespace CofiniteLinearRecurrence

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {V : Type v} [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V]

private theorem norm_sum_lt
    {ι : Type*} (s : Finset ι) (x : ι → V) {r : ℝ} (hr : 0 < r)
    (hx : ∀ i ∈ s, ‖x i‖ < r) :
    ‖∑ i ∈ s, x i‖ < r := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
        (max_lt (hx i (Finset.mem_insert_self i s))
          (ih fun j hj ↦ hx j (Finset.mem_insert_of_mem hj)))

private theorem polynomial_recurrence_eq_zero
    (x : ℤ → V) (hx : Tendsto x cofinite (𝓝 0))
    (p : Polynomial K) (hp : p ≠ 0)
    (hrec : ∀ z : ℤ, p.sum (fun n a ↦ a • x (z - n)) = 0) :
    ∀ z, x z = 0 := by
  classical
  by_contra hzero
  push Not at hzero
  obtain ⟨z₁, hz₁⟩ := hzero
  have hr₁ : 0 < ‖x z₁‖ := norm_pos_iff.mpr hz₁
  have heventually :
      ∀ᶠ z in (cofinite : Filter ℤ), ‖x z‖ < ‖x z₁‖ := by
    have hnorm : Tendsto (fun z ↦ ‖x z‖) cofinite (𝓝 0) := by
      simpa using hx.norm
    simpa [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hnorm ‖x z₁‖ hr₁)
  let large : Set ℤ := {z | ‖x z₁‖ ≤ ‖x z‖}
  have hlarge : large.Finite := by
    have hcompl : largeᶜ ∈ (cofinite : Filter ℤ) := by
      simpa [large, Set.compl_setOf, not_le] using heventually
    simpa using mem_cofinite.mp hcompl
  have hz₁large : z₁ ∈ large := by
    change ‖x z₁‖ ≤ ‖x z₁‖
    exact le_rfl
  obtain ⟨z₂, hz₂large, hz₂max⟩ :=
    Set.exists_max_image large (fun z ↦ ‖x z‖) hlarge ⟨z₁, hz₁large⟩
  have hx_le (z : ℤ) : ‖x z‖ ≤ ‖x z₂‖ := by
    by_cases hz : z ∈ large
    · exact hz₂max z hz
    · have hzlt : ‖x z‖ < ‖x z₁‖ := by
        simpa [large, not_le] using hz
      exact hzlt.le.trans (hz₂max z₁ hz₁large)
  have hz₂ne : x z₂ ≠ 0 := by
    intro hz
    have : ‖x z₁‖ ≤ 0 := by simpa [hz] using hz₂max z₁ hz₁large
    exact (not_le_of_gt hr₁) this
  have hr₂ : 0 < ‖x z₂‖ := norm_pos_iff.mpr hz₂ne
  let peaks : Set ℤ := {z | ‖x z‖ = ‖x z₂‖}
  have hpeaks : peaks.Finite :=
    hlarge.subset fun z hz ↦ by
      change ‖x z₁‖ ≤ ‖x z‖
      rw [hz]
      exact hz₂max z₁ hz₁large
  have hz₂peak : z₂ ∈ peaks := rfl
  obtain ⟨z₀, hz₀peak, hz₀latest⟩ :=
    Set.exists_max_image peaks id hpeaks ⟨z₂, hz₂peak⟩
  have hx_peak : ‖x z₀‖ = ‖x z₂‖ := hz₀peak
  have hx_lt_of_gt {z : ℤ} (hz : z₀ < z) : ‖x z‖ < ‖x z₀‖ := by
    rw [hx_peak]
    exact lt_of_le_of_ne (hx_le z) fun heq ↦
      (not_le_of_gt hz) (hz₀latest z (by simpa [peaks] using heq))
  have hsupport : p.support.Nonempty := Polynomial.support_nonempty.mpr hp
  obtain ⟨j₁, hj₁support, hj₁max⟩ :=
    Finset.exists_max_image p.support (fun n ↦ ‖p.coeff n‖) hsupport
  let dominant := p.support.filter fun n ↦ ‖p.coeff n‖ = ‖p.coeff j₁‖
  have hj₁dominant : j₁ ∈ dominant := by simp [dominant, hj₁support]
  obtain ⟨j, hjdominant, hjlatest⟩ :=
    Finset.exists_max_image dominant id ⟨j₁, hj₁dominant⟩
  have hjsupport : j ∈ p.support := (Finset.mem_filter.mp hjdominant).1
  have hjnorm : ‖p.coeff j‖ = ‖p.coeff j₁‖ :=
    (Finset.mem_filter.mp hjdominant).2
  have hcoeff_le (i : ℕ) (hi : i ∈ p.support) :
      ‖p.coeff i‖ ≤ ‖p.coeff j‖ := by
    rw [hjnorm]
    exact hj₁max i hi
  have hcoeff_lt_of_gt {i : ℕ} (hi : i ∈ p.support) (hji : j < i) :
      ‖p.coeff i‖ < ‖p.coeff j‖ := by
    refine lt_of_le_of_ne (hcoeff_le i hi) ?_
    intro heq
    have hi' : i ∈ dominant := by
      rw [Finset.mem_filter]
      exact ⟨hi, by simpa [hjnorm] using heq⟩
    exact (not_le_of_gt hji) (hjlatest i hi')
  have hjne : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hjsupport
  have hjpos : 0 < ‖p.coeff j‖ := norm_pos_iff.mpr hjne
  have hmainpos : 0 < ‖p.coeff j‖ * ‖x z₀‖ :=
    mul_pos hjpos (by simpa [hx_peak] using hr₂)
  let z : ℤ := z₀ + j
  let term : ℕ → V := fun i ↦ p.coeff i • x (z - i)
  have hterm_lt (i : ℕ) (hi : i ∈ p.support.erase j) :
      ‖term i‖ < ‖term j‖ := by
    have hisupport : i ∈ p.support := (Finset.mem_erase.mp hi).2
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    rw [show ‖term i‖ = ‖p.coeff i‖ * ‖x (z - i)‖ by
      simp [term, norm_smul],
      show ‖term j‖ = ‖p.coeff j‖ * ‖x z₀‖ by
        simp only [term, z]
        have hindex : z₀ + (j : ℤ) - (j : ℤ) = z₀ := by omega
        rw [hindex, norm_smul]]
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · have hindex : z₀ < z - i := by
        simp only [z]
        omega
      calc
        ‖p.coeff i‖ * ‖x (z - i)‖ ≤
            ‖p.coeff j‖ * ‖x (z - i)‖ :=
          mul_le_mul_of_nonneg_right (hcoeff_le i hisupport) (norm_nonneg _)
        _ < ‖p.coeff j‖ * ‖x z₀‖ :=
          mul_lt_mul_of_pos_left (hx_lt_of_gt hindex) hjpos
    · calc
        ‖p.coeff i‖ * ‖x (z - i)‖ ≤
            ‖p.coeff i‖ * ‖x z₀‖ :=
          mul_le_mul_of_nonneg_left
            (by simpa only [hx_peak] using hx_le (z - i)) (norm_nonneg _)
        _ < ‖p.coeff j‖ * ‖x z₀‖ :=
          mul_lt_mul_of_pos_right (hcoeff_lt_of_gt hisupport hjilt)
            (by simpa [hx_peak] using hr₂)
  have hrest :
      ‖∑ i ∈ p.support.erase j, term i‖ < ‖term j‖ :=
    norm_sum_lt (p.support.erase j) term
      (by simpa [term, z, norm_smul] using hmainpos) hterm_lt
  have hsum :
      term j + ∑ i ∈ p.support.erase j, term i = 0 := by
    have hzrec := hrec z
    change (∑ i ∈ p.support, term i) = 0 at hzrec
    rw [← Finset.sum_erase_add _ _ hjsupport] at hzrec
    simpa only [add_comm] using hzrec
  have hnormeq :
      ‖term j‖ = ‖∑ i ∈ p.support.erase j, term i‖ := by
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg]
  exact (ne_of_gt hrest) hnormeq

/-- A restricted bi-infinite orbit of a linear endomorphism on a finite-dimensional
nonarchimedean normed space vanishes. -/
theorem eq_zero_of_tendsto_cofinite_zero
    [FiniteDimensional K V] (T : V →ₗ[K] V) (x : ℤ → V)
    (hx : Tendsto x cofinite (𝓝 0))
    (hT : ∀ z : ℤ, T (x z) = x (z - 1)) :
    ∀ z, x z = 0 := by
  let p := T.charpoly
  apply polynomial_recurrence_eq_zero x hx p T.charpoly_monic.ne_zero
  intro z
  have hpow (n : ℕ) : (T ^ n) (x z) = x (z - n) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ']
        change T ((T ^ n) (x z)) = _
        rw [ih, hT]
        congr 1
        omega
  have hCH := congrArg (fun L : V →ₗ[K] V ↦ L (x z)) T.aeval_self_charpoly
  rw [Polynomial.aeval_endomorphism] at hCH
  change p.sum (fun n b ↦ b • (T ^ n) (x z)) = 0 at hCH
  simpa only [hpow] using hCH

end CofiniteLinearRecurrence

end Rigid
