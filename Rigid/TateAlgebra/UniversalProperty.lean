import Rigid.TateAlgebra.NormedRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.Algebra

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# The universal property of the strict Tate algebra

A tuple `x` in the closed unit polydisc of a complete nonarchimedean normed `K`-algebra `A`
determines a unique continuous `K`-algebra homomorphism from the Tate algebra to `A` sending
the coordinates to the entries of `x`.

The evaluation map is defined directly as the sum `f ↦ ∑' n, coeff n f • x ^ n`, which converges
because the coefficients tend to zero and `A` is complete and nonarchimedean. Multiplicativity
and uniqueness both follow from density of polynomials (`Rigid.denseRange_ofPolynomial`):
the codomain is Hausdorff, so continuous maps agreeing on polynomials agree everywhere.

Note that Hausdorffness (`NormedCommRing A` rather than `SeminormedCommRing A`) is genuinely
needed for uniqueness: if the seminorm on `A` has a nontrivial null ideal, a continuous algebra
homomorphism is not determined by its values on the coordinates.
-/

open Filter
open scoped Topology

universe u v w

namespace Rigid

namespace TateAlgebra

/-! ### Evaluation of monomials -/

section EvalMonomial

variable {ι : Type v} {A : Type w} [NormedCommRing A] (x : ι → A)

/-- Evaluation of the monomial with exponents `n` at the tuple `x`. -/
noncomputable def evalMonomial (n : ι →₀ ℕ) : A :=
  n.prod fun i e ↦ x i ^ e

variable {x}

/-- On the closed unit polydisc, monomials are uniformly bounded. The bound accounts for
`‖1‖` because a general normed ring need not satisfy `‖1‖ = 1`. -/
theorem norm_evalMonomial_le (hx : ∀ i, ‖x i‖ ≤ 1) (n : ι →₀ ℕ) :
    ‖evalMonomial x n‖ ≤ max 1 ‖(1 : A)‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [evalMonomial, Finsupp.prod_zero_index]
    exact le_max_right _ _
  · refine le_trans ?_ (le_max_left _ _)
    have hs : n.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
    simp only [evalMonomial, Finsupp.prod]
    calc ‖∏ i ∈ n.support, x i ^ n i‖ ≤ ∏ i ∈ n.support, ‖x i ^ n i‖ :=
          Finset.norm_prod_le' n.support hs _
      _ ≤ ∏ i ∈ n.support, (1 : ℝ) := by
          refine Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i hi ↦ ?_
          exact (norm_pow_le' (x i)
            (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi))).trans
            (pow_le_one₀ (norm_nonneg _) (hx i))
      _ = 1 := Finset.prod_const_one

end EvalMonomial

/-! ### The evaluation homomorphism -/

section Eval

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v)
variable {A : Type w} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]
variable {x : ι → A}

/-- The terms of the evaluation series are summable. -/
theorem summable_coeff_smul_evalMonomial (hx : ∀ i, ‖x i‖ ≤ 1) (f : TateAlgebra K ι) :
    Summable fun n : ι →₀ ℕ ↦ MvPowerSeries.coeff n f.1 • evalMonomial x n := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
  refine squeeze_zero_norm
    (a := fun n : ι →₀ ℕ ↦ ‖MvPowerSeries.coeff n f.1‖ * max 1 ‖(1 : A)‖) (fun n ↦ ?_) ?_
  · exact (norm_smul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_evalMonomial_le hx n) (norm_nonneg _))
  · simpa using (tendsto_norm_coeff_zero K ι f).mul_const (max 1 ‖(1 : A)‖)

variable (x) in
/-- The underlying function of the evaluation homomorphism: `f ↦ ∑' n, coeff n f • x ^ n`. -/
noncomputable def evalFun (f : TateAlgebra K ι) : A :=
  ∑' n : ι →₀ ℕ, MvPowerSeries.coeff n f.1 • evalMonomial x n

variable (x) in
/-- On polynomials, the evaluation series reduces to polynomial evaluation. -/
theorem evalFun_ofPolynomial (p : MvPolynomial ι K) :
    evalFun K ι x (ofPolynomial K ι p) = MvPolynomial.aeval x p := by
  classical
  have hzero : ∀ n ∉ p.support,
      MvPowerSeries.coeff n ((ofPolynomial K ι p : TateAlgebra K ι) : MvPowerSeries ι K)
        • evalMonomial x n = 0 := by
    intro n hn
    rw [coe_ofPolynomial, MvPolynomial.coeff_coe, MvPolynomial.notMem_support_iff.mp hn,
      zero_smul]
  rw [evalFun, tsum_eq_sum hzero, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [coe_ofPolynomial, MvPolynomial.coeff_coe, Algebra.smul_def]
  congr 1

/-- The evaluation series is bounded by a constant multiple of the Gauss norm. -/
theorem norm_evalFun_le (hx : ∀ i, ‖x i‖ ≤ 1) (f : TateAlgebra K ι) :
    ‖evalFun K ι x f‖ ≤ max 1 ‖(1 : A)‖ * ‖f‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (norm_nonneg f)) fun n ↦ ?_
  calc ‖MvPowerSeries.coeff n f.1 • evalMonomial x n‖
      ≤ ‖MvPowerSeries.coeff n f.1‖ * max 1 ‖(1 : A)‖ := (norm_smul_le _ _).trans
        (mul_le_mul_of_nonneg_left (norm_evalMonomial_le hx n) (norm_nonneg _))
    _ ≤ ‖f‖ * max 1 ‖(1 : A)‖ := mul_le_mul_of_nonneg_right
        (norm_coeff_le_norm K ι f n) (le_trans zero_le_one (le_max_left _ _))
    _ = max 1 ‖(1 : A)‖ * ‖f‖ := mul_comm _ _

variable (x) in
/-- The evaluation map bundled as an additive monoid homomorphism. -/
noncomputable def evalAddMonoidHom (hx : ∀ i, ‖x i‖ ≤ 1) : TateAlgebra K ι →+ A where
  toFun := evalFun K ι x
  map_zero' := by simp [evalFun]
  map_add' f g := by
    have h : ∀ n : ι →₀ ℕ,
        MvPowerSeries.coeff n ((f + g : TateAlgebra K ι) : MvPowerSeries ι K)
            • evalMonomial x n
          = MvPowerSeries.coeff n f.1 • evalMonomial x n
            + MvPowerSeries.coeff n g.1 • evalMonomial x n := by
      intro n
      rw [show ((f + g : TateAlgebra K ι) : MvPowerSeries ι K)
          = (f : MvPowerSeries ι K) + (g : MvPowerSeries ι K) from rfl, map_add, add_smul]
    simp only [evalFun]
    simp_rw [h]
    exact (summable_coeff_smul_evalMonomial K ι hx f).tsum_add
      (summable_coeff_smul_evalMonomial K ι hx g)

theorem continuous_evalFun (hx : ∀ i, ‖x i‖ ≤ 1) : Continuous (evalFun K ι x) :=
  AddMonoidHomClass.continuous_of_bound (evalAddMonoidHom K ι x hx)
    (max 1 ‖(1 : A)‖) (norm_evalFun_le K ι hx)

/-- The evaluation series is multiplicative.  This follows by continuity from
multiplicativity of polynomial evaluation, using density of the polynomials. -/
theorem evalFun_mul (hx : ∀ i, ‖x i‖ ≤ 1) (f g : TateAlgebra K ι) :
    evalFun K ι x (f * g) = evalFun K ι x f * evalFun K ι x g := by
  have h1 : Continuous fun z : TateAlgebra K ι × TateAlgebra K ι ↦
      evalFun K ι x (z.1 * z.2) :=
    (continuous_evalFun K ι hx).comp continuous_mul
  have h2 : Continuous fun z : TateAlgebra K ι × TateAlgebra K ι ↦
      evalFun K ι x z.1 * evalFun K ι x z.2 :=
    ((continuous_evalFun K ι hx).comp continuous_fst).mul
      ((continuous_evalFun K ι hx).comp continuous_snd)
  have hd : Dense (Set.range (ofPolynomial K ι) ×ˢ Set.range (ofPolynomial K ι)) :=
    Dense.prod (denseRange_ofPolynomial K ι) (denseRange_ofPolynomial K ι)
  have key : (fun z : TateAlgebra K ι × TateAlgebra K ι ↦ evalFun K ι x (z.1 * z.2))
      = fun z ↦ evalFun K ι x z.1 * evalFun K ι x z.2 := by
    refine h1.ext_on hd h2 ?_
    rintro ⟨u, v⟩ ⟨⟨p, rfl⟩, q, rfl⟩
    change evalFun K ι x (ofPolynomial K ι p * ofPolynomial K ι q)
      = evalFun K ι x (ofPolynomial K ι p) * evalFun K ι x (ofPolynomial K ι q)
    rw [← map_mul, evalFun_ofPolynomial, evalFun_ofPolynomial, evalFun_ofPolynomial, map_mul]
  exact congrFun key (f, g)

variable (x) in
/-- Evaluation at a point of the closed unit polydisc, as a continuous algebra
homomorphism from the Tate algebra. -/
noncomputable def eval (hx : ∀ i, ‖x i‖ ≤ 1) : ContinuousAlgHom K (TateAlgebra K ι) A where
  toFun := evalFun K ι x
  map_one' := by
    have h := evalFun_ofPolynomial K ι x 1
    simpa using h
  map_mul' := evalFun_mul K ι hx
  map_zero' := by simp [evalFun]
  map_add' := map_add (evalAddMonoidHom K ι x hx)
  commutes' := fun c ↦ by
    have h1 := (ofPolynomial K ι).commutes c
    rw [MvPolynomial.algebraMap_eq] at h1
    change evalFun K ι x (algebraMap K (TateAlgebra K ι) c) = algebraMap K A c
    rw [← h1, evalFun_ofPolynomial, MvPolynomial.aeval_C]
  cont := continuous_evalFun K ι hx

@[simp]
theorem eval_tateVariable (hx : ∀ i, ‖x i‖ ≤ 1) (i : ι) :
    eval K ι x hx (tateVariable K ι i) = x i := by
  change evalFun K ι x (tateVariable K ι i) = x i
  rw [← ofPolynomial_X K ι i, evalFun_ofPolynomial, MvPolynomial.aeval_X]

end Eval

end TateAlgebra

section UniversalProperty

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
variable (ι : Type v)
variable {A : Type w} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- The universal property of the strict Tate algebra.

A tuple in the closed unit polydisc of a complete nonarchimedean Banach `K`-algebra determines a
unique continuous `K`-algebra homomorphism.  Note that neither completeness of `K` nor finiteness
of `ι` is needed: every individual Tate series has coefficients tending to zero, which is enough
for the evaluation series to converge. -/
theorem existsUnique_continuousAlgHom_of_norm_le_one (x : ι → A) (hx : ∀ i, ‖x i‖ ≤ 1) :
    ∃! φ : ContinuousAlgHom K (TateAlgebra K ι) A,
      ∀ i, φ (tateVariable K ι i) = x i := by
  refine ⟨TateAlgebra.eval K ι x hx, fun i ↦ TateAlgebra.eval_tateVariable K ι hx i, ?_⟩
  intro ψ hψ
  have hpoly : ∀ p : MvPolynomial ι K,
      ψ (TateAlgebra.ofPolynomial K ι p) = MvPolynomial.aeval x p := by
    intro p
    have hcomp : ((ψ : TateAlgebra K ι →ₐ[K] A).comp (TateAlgebra.ofPolynomial K ι))
        = MvPolynomial.aeval x := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      simp [hψ i]
    simpa using AlgHom.congr_fun hcomp p
  have hfun : ⇑ψ = ⇑(TateAlgebra.eval K ι x hx) := by
    refine ψ.continuous.ext_on (denseRange_ofPolynomial K ι)
      (TateAlgebra.eval K ι x hx).continuous ?_
    rintro _ ⟨p, rfl⟩
    rw [hpoly p]
    exact (TateAlgebra.evalFun_ofPolynomial K ι x p).symm
  exact ContinuousAlgHom.ext fun f ↦ congrFun hfun f

end UniversalProperty

end Rigid
