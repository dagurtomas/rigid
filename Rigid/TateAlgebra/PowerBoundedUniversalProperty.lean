import Rigid.AffinoidAlgebra.RationalDatum
import Rigid.TateAlgebra.UniversalProperty

set_option linter.style.header false

/-!
# The power-bounded universal property of the Tate algebra

For a finite tuple of power-bounded elements, all evaluated monomials have a common norm bound.
Consequently the usual evaluation series converges and defines a continuous algebra homomorphism,
even when the individual elements do not lie in the closed unit ball for the chosen norm.
-/

open Filter
open scoped Topology

universe u v w

namespace Rigid

namespace TateAlgebra

section PowerBoundedEval

variable {ι : Type v} [Finite ι]
variable {A : Type w} [NormedCommRing A]

/-- A finite power-bounded tuple has uniformly bounded evaluated monomials. -/
private theorem exists_bound_evalMonomial (x : ι → A) (hx : ∀ i, IsPowerBounded (x i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ι →₀ ℕ, ‖evalMonomial x n‖ ≤ C := by
  classical
  letI := Fintype.ofFinite ι
  have hx' : ∀ i, ∃ C : ℝ, ∀ m : ℕ, ‖x i ^ m‖ ≤ C := by
    intro i
    rcases hx i with ⟨C, hC⟩
    exact ⟨C, fun m ↦ hC ⟨m, rfl⟩⟩
  choose C hC using hx'
  let D : ℝ := max ‖(1 : A)‖ (∏ i, max 1 (C i))
  refine ⟨D, (norm_nonneg (1 : A)).trans (le_max_left _ _), fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [D, evalMonomial]
  · have hs : n.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
    simp only [evalMonomial, Finsupp.prod]
    calc
      ‖∏ i ∈ n.support, x i ^ n i‖ ≤ ∏ i ∈ n.support, ‖x i ^ n i‖ :=
        Finset.norm_prod_le' n.support hs _
      _ ≤ ∏ i ∈ n.support, max 1 (C i) := by
        refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg (x i ^ n i)) fun i _ ↦ ?_
        exact (hC i (n i)).trans (le_max_right _ _)
      _ ≤ ∏ i, max 1 (C i) := by
        refine Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _) ?_ ?_
        · exact fun i _ ↦ zero_le_one.trans (le_max_left _ _)
        · exact fun i _ _ ↦ le_max_left _ _
      _ ≤ D := le_max_right _ _

end PowerBoundedEval

end TateAlgebra

/-- A finite power-bounded tuple determines a unique continuous homomorphism from the Tate
algebra. The construction evaluates the convergent series directly, using the common bound on all
evaluated monomials. -/
theorem existsUnique_continuousAlgHom_of_isPowerBounded
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    {ι : Type v} [Finite ι]
    {A : Type w} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
    [IsUltrametricDist A] (x : ι → A) (hx : ∀ i, IsPowerBounded (x i)) :
    ∃! φ : ContinuousAlgHom K (TateAlgebra K ι) A,
      ∀ i, φ (tateVariable K ι i) = x i := by
  obtain ⟨C, hC0, hC⟩ := TateAlgebra.exists_bound_evalMonomial x hx
  have hsummable (f : TateAlgebra K ι) :
      Summable fun n : ι →₀ ℕ ↦
        MvPowerSeries.coeff n f.1 • TateAlgebra.evalMonomial x n := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    refine squeeze_zero_norm
      (a := fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖ * C) (fun n ↦ ?_) ?_
    · exact (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))
    · simpa using (tendsto_norm_coeff_zero K ι f).mul_const C
  let evalAdd : TateAlgebra K ι →+ A :=
    { toFun := TateAlgebra.evalFun K ι x
      map_zero' := by simp [TateAlgebra.evalFun]
      map_add' := fun f g ↦ by
        have h : ∀ n : ι →₀ ℕ,
            MvPowerSeries.coeff n ((f + g : TateAlgebra K ι) : MvPowerSeries ι K)
                • TateAlgebra.evalMonomial x n
              = MvPowerSeries.coeff n f.1 • TateAlgebra.evalMonomial x n
                + MvPowerSeries.coeff n g.1 • TateAlgebra.evalMonomial x n := by
          intro n
          rw [show ((f + g : TateAlgebra K ι) : MvPowerSeries ι K)
              = (f : MvPowerSeries ι K) + (g : MvPowerSeries ι K) from rfl,
            map_add, add_smul]
        simp only [TateAlgebra.evalFun]
        simp_rw [h]
        exact (hsummable f).tsum_add (hsummable g) }
  have hnorm (f : TateAlgebra K ι) :
      ‖TateAlgebra.evalFun K ι x f‖ ≤ C * ‖f‖ := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
      (mul_nonneg hC0 (norm_nonneg f)) fun n ↦ ?_
    calc
      ‖MvPowerSeries.coeff n f.1 • TateAlgebra.evalMonomial x n‖
          ≤ ‖MvPowerSeries.coeff n f.1‖ * C := (norm_smul_le _ _).trans
            (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))
      _ ≤ ‖f‖ * C := mul_le_mul_of_nonneg_right
        (norm_coeff_le_norm K ι f n) hC0
      _ = C * ‖f‖ := mul_comm _ _
  have hcont : Continuous (TateAlgebra.evalFun K ι x) :=
    AddMonoidHomClass.continuous_of_bound evalAdd C hnorm
  have hmul (f g : TateAlgebra K ι) :
      TateAlgebra.evalFun K ι x (f * g) =
        TateAlgebra.evalFun K ι x f * TateAlgebra.evalFun K ι x g := by
    have h1 : Continuous fun z : TateAlgebra K ι × TateAlgebra K ι ↦
        TateAlgebra.evalFun K ι x (z.1 * z.2) := hcont.comp continuous_mul
    have h2 : Continuous fun z : TateAlgebra K ι × TateAlgebra K ι ↦
        TateAlgebra.evalFun K ι x z.1 * TateAlgebra.evalFun K ι x z.2 :=
      (hcont.comp continuous_fst).mul (hcont.comp continuous_snd)
    have hd : Dense
        (Set.range (TateAlgebra.ofPolynomial K ι) ×ˢ
          Set.range (TateAlgebra.ofPolynomial K ι)) :=
      Dense.prod (denseRange_ofPolynomial K ι) (denseRange_ofPolynomial K ι)
    have key :
        (fun z : TateAlgebra K ι × TateAlgebra K ι ↦
          TateAlgebra.evalFun K ι x (z.1 * z.2)) =
        fun z ↦ TateAlgebra.evalFun K ι x z.1 * TateAlgebra.evalFun K ι x z.2 := by
      refine h1.ext_on hd h2 ?_
      rintro ⟨u, v⟩ ⟨⟨p, rfl⟩, q, rfl⟩
      change TateAlgebra.evalFun K ι x
          (TateAlgebra.ofPolynomial K ι p * TateAlgebra.ofPolynomial K ι q) =
        TateAlgebra.evalFun K ι x (TateAlgebra.ofPolynomial K ι p) *
          TateAlgebra.evalFun K ι x (TateAlgebra.ofPolynomial K ι q)
      rw [← map_mul, TateAlgebra.evalFun_ofPolynomial, TateAlgebra.evalFun_ofPolynomial,
        TateAlgebra.evalFun_ofPolynomial, map_mul]
    exact congrFun key (f, g)
  let eval : ContinuousAlgHom K (TateAlgebra K ι) A :=
    { toFun := TateAlgebra.evalFun K ι x
      map_one' := by
        have h := TateAlgebra.evalFun_ofPolynomial K ι x 1
        simpa using h
      map_mul' := hmul
      map_zero' := by simp [TateAlgebra.evalFun]
      map_add' := map_add evalAdd
      commutes' := fun c ↦ by
        have h1 := (TateAlgebra.ofPolynomial K ι).commutes c
        rw [MvPolynomial.algebraMap_eq] at h1
        change TateAlgebra.evalFun K ι x (algebraMap K (TateAlgebra K ι) c) =
          algebraMap K A c
        rw [← h1, TateAlgebra.evalFun_ofPolynomial, MvPolynomial.aeval_C]
      cont := hcont }
  have heval (i : ι) : eval (tateVariable K ι i) = x i := by
    change TateAlgebra.evalFun K ι x (tateVariable K ι i) = x i
    rw [← ofPolynomial_X K ι i, TateAlgebra.evalFun_ofPolynomial,
      MvPolynomial.aeval_X]
  refine ⟨eval, heval, ?_⟩
  intro ψ hψ
  have hpoly : ∀ p : MvPolynomial ι K,
      ψ (TateAlgebra.ofPolynomial K ι p) = MvPolynomial.aeval x p := by
    intro p
    have hcomp : ((ψ : TateAlgebra K ι →ₐ[K] A).comp (TateAlgebra.ofPolynomial K ι)) =
        MvPolynomial.aeval x := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp [hψ i]
    simpa using AlgHom.congr_fun hcomp p
  have hfun : ⇑ψ = ⇑eval := by
    refine ψ.continuous.ext_on (denseRange_ofPolynomial K ι) eval.continuous ?_
    rintro _ ⟨p, rfl⟩
    rw [hpoly p]
    exact (TateAlgebra.evalFun_ofPolynomial K ι x p).symm
  exact ContinuousAlgHom.ext fun f ↦ congrFun hfun f

end Rigid
