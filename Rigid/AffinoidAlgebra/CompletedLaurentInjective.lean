import Rigid.AffinoidAlgebra.ClosedIdeals
import Rigid.AffinoidAlgebra.CofiniteLinearRecurrence
import Rigid.AffinoidAlgebra.CompletedLaurentRelation
import Rigid.AffinoidAlgebra.NoetherianBanach
import Rigid.AffinoidAlgebra.SpectralPresentation

set_option linter.style.header false
set_option linter.unusedSectionVars false

/-!
# Injectivity of the completed Laurent relation

For an affinoid algebra `A`, multiplication by the formal Laurent element `ζ - f` is injective on
restricted Laurent coefficient families.  We test a relation modulo every positive power of every
maximal ideal.  These quotients are finite-dimensional over the ground field, where
Cayley--Hamilton and the nonarchimedean norm rule out a nonzero bi-infinite orbit tending to zero.
Krull intersection then gives the result in `A`.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

namespace CompletedLaurent

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (A : Type v) [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  [IsUltrametricDist A]

/-- Splitting a restricted Laurent family into its nonnegative and strictly negative parts is
unique. -/
theorem relationFactor_injective :
    Function.Injective (relationFactor K A) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  apply Prod.ext
  · apply TateAlgebra.ext
    intro e
    have he : e = oneExponent (e 0) := by
      apply Finsupp.ext
      intro i
      rw [Fin.eq_zero i]
      simp [oneExponent]
    rw [he]
    have hcoeff := congrArg
      (fun c : Series K A ↦ c.1 (e 0 : ℤ)) h
    simpa only [relationFactor_apply_ofNat] using hcoeff
  · apply TateAlgebra.ext
    intro e
    have he : e = oneExponent (e 0) := by
      apply Finsupp.ext
      intro i
      rw [Fin.eq_zero i]
      simp [oneExponent]
    rw [he]
    have hcoeff := congrArg
      (fun c : Series K A ↦ c.1 (Int.negSucc (e 0))) h
    have hneg :
        -TateAlgebra.coeff A (Fin 1) (oneExponent (e 0)) q =
          -TateAlgebra.coeff A (Fin 1) (oneExponent (e 0)) q' := by
      simpa only [relationFactor_apply_negSucc] using hcoeff
    exact neg_injective hneg

/-- A restricted Laurent family killed by `ζ - f` is zero over an affinoid algebra. -/
theorem relation_eq_zero
    (hA : IsAffinoidAlgebra K A) (f : A) (c : Series K A)
    (hc : relation K A f c = 0) :
    c = 0 := by
  letI : IsNoetherianRing A := isNoetherianRing_of_affinoidAlgebra K hA
  apply Subtype.ext
  funext z
  apply eq_zero_of_mem_all_maximal_powers_of_isAffinoidAlgebra K hA
  intro m hm l hl
  let I : Ideal A := m ^ l
  let Q := A ⧸ I
  letI : IsClosed (I : Set A) := isClosed_ideal_of_isNoetherianRing K I
  letI : IsUltrametricDist Q := idealQuotientIsUltrametricDist I
  letI : Module.Finite K Q :=
    finite_quotient_maximal_pow_of_isAffinoidAlgebra K hA m hm l hl
  let q : ContinuousAlgHom K A Q := idealQuotientMk K I
  let x : ℤ → Q := fun w ↦ q (c.1 w)
  have hx : Tendsto x cofinite (𝓝 0) := by
    have := q.continuous.continuousAt.tendsto.comp c.2
    change Tendsto (q ∘ c.1) cofinite (𝓝 0) at this
    change Tendsto (q ∘ c.1) cofinite (𝓝 0)
    exact this
  let T : Q →ₗ[K] Q := LinearMap.mulLeft K (q f)
  have hT (w : ℤ) : T (x w) = x (w - 1) := by
    have hw := congrArg (fun d : Series K A ↦ d.1 w) hc
    change c.1 (w - 1) - f * c.1 w = 0 at hw
    have hqw := congrArg q hw
    simp only [map_sub, map_mul, map_zero] at hqw
    change q f * q (c.1 w) = q (c.1 (w - 1))
    exact (sub_eq_zero.mp hqw).symm
  have hxzero :=
    CofiniteLinearRecurrence.eq_zero_of_tendsto_cofinite_zero T x hx hT z
  change c.1 z ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem.mp hxzero

/-- Multiplication by `ζ - f` on restricted Laurent coefficient families is injective over an
affinoid algebra. -/
theorem relation_injective
    (hA : IsAffinoidAlgebra K A) (f : A) :
    Function.Injective (relation K A f) := by
  apply (injective_iff_map_eq_zero (relation K A f)).mpr
  intro c hc
  exact relation_eq_zero K A hA f c hc

end CompletedLaurent

end Rigid
