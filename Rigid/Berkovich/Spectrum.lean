import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Basic

set_option linter.style.header false

/-!
# The Berkovich spectrum of a normed ring

The Berkovich spectrum of a normed ring consists of the multiplicative real-valued seminorms
bounded by the ring norm. It carries the topology of pointwise convergence. This file develops the
elementary evaluation, separation, kernel, and compactness API. Nonemptiness for nonzero complete
commutative normed rings is a deeper result and is left to a later file.
-/

open Filter
open scoped Topology

universe u v

namespace Rigid

variable (R : Type u) [NormedRing R]

/-- A point of the Berkovich spectrum of a normed ring: a multiplicative seminorm bounded by the
ring norm. The bound is normalized to be contractive. -/
structure BerkovichSpectrum where
  seminorm : MulRingSeminorm R
  le_norm' : ∀ a : R, seminorm a ≤ ‖a‖

instance berkovichSpectrumCoeFun : CoeFun (BerkovichSpectrum R) (fun _ ↦ R → ℝ) :=
  ⟨fun x ↦ x.seminorm⟩

namespace BerkovichSpectrum

/-- Two points of the Berkovich spectrum are equal when all their values are equal. -/
@[ext]
theorem ext {x y : BerkovichSpectrum R} (h : ∀ a, x a = y a) : x = y := by
  cases x with
  | mk px hx =>
    cases y with
    | mk py hy =>
      congr
      exact MulRingSeminorm.ext h

@[simp]
theorem map_zero (x : BerkovichSpectrum R) : x 0 = 0 :=
  _root_.map_zero x.seminorm

@[simp]
theorem map_one (x : BerkovichSpectrum R) : x 1 = 1 :=
  _root_.map_one x.seminorm

@[simp]
theorem map_neg (x : BerkovichSpectrum R) (a : R) : x (-a) = x a :=
  map_neg_eq_map x.seminorm a

@[simp]
theorem map_mul (x : BerkovichSpectrum R) (a b : R) : x (a * b) = x a * x b :=
  _root_.map_mul x.seminorm a b

/-- A point of the Berkovich spectrum is subadditive. -/
theorem map_add_le (x : BerkovichSpectrum R) (a b : R) : x (a + b) ≤ x a + x b :=
  map_add_le_add x.seminorm a b

/-- A point of the Berkovich spectrum takes nonnegative values. -/
theorem nonneg (x : BerkovichSpectrum R) (a : R) : 0 ≤ x a :=
  apply_nonneg x.seminorm a

/-- A point of the Berkovich spectrum is bounded by the given ring norm. -/
theorem le_norm (x : BerkovichSpectrum R) (a : R) : x a ≤ ‖a‖ :=
  x.le_norm' a

/-- The kernel of a point of the Berkovich spectrum. -/
def kernel (x : BerkovichSpectrum R) : Ideal R where
  carrier := {a | x a = 0}
  zero_mem' := x.map_zero
  add_mem' {a b} ha hb := by
    apply le_antisymm
    · exact (map_add_le R x a b).trans_eq (by rw [ha, hb, add_zero])
    · exact nonneg R x (a + b)
  smul_mem' r a ha := by
    change x (r * a) = 0
    rw [x.map_mul, ha, mul_zero]

@[simp]
theorem mem_kernel_iff (x : BerkovichSpectrum R) (a : R) : a ∈ x.kernel ↔ x a = 0 :=
  Iff.rfl

/-- The kernel of a multiplicative seminorm is a prime ideal. -/
theorem kernel_isPrime (x : BerkovichSpectrum R) : x.kernel.IsPrime := by
  refine Ideal.IsPrime.mk ?_ ?_
  · rw [Ideal.ne_top_iff_one]
    simp
  · intro a b hab
    rw [mem_kernel_iff R x, map_mul R x] at hab
    rcases mul_eq_zero.mp hab with ha | hb
    · exact Or.inl ((mem_kernel_iff R x a).mpr ha)
    · exact Or.inr ((mem_kernel_iff R x b).mpr hb)

/-- Pull back a Berkovich point along a norm-nonincreasing ring homomorphism. -/
def comap {S : Type v} [NormedRing S] (f : R →+* S) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (x : BerkovichSpectrum S) : BerkovichSpectrum R where
  seminorm :=
    { toFun := fun a ↦ x (f a)
      map_zero' := by simp
      add_le' := by intro a b; simpa using map_add_le S x (f a) (f b)
      neg' := by intro a; simp
      map_one' := by simp
      map_mul' := by intro a b; simp }
  le_norm' a := (le_norm S x (f a)).trans (hf a)

@[simp]
theorem comap_apply {S : Type v} [NormedRing S] (f : R →+* S) (hf : ∀ a, ‖f a‖ ≤ ‖a‖)
    (x : BerkovichSpectrum S) (a : R) : comap R f hf x a = x (f a) :=
  rfl

end BerkovichSpectrum

/-- The topology of pointwise convergence on the Berkovich spectrum. -/
noncomputable instance berkovichSpectrumTopologicalSpace :
    TopologicalSpace (BerkovichSpectrum R) :=
  TopologicalSpace.induced (fun x : BerkovichSpectrum R ↦ (x : R → ℝ)) inferInstance

namespace BerkovichSpectrum

/-- The map sending a point of the Berkovich spectrum to its underlying function is an embedding. -/
theorem isEmbedding_coe :
    Topology.IsEmbedding (fun x : BerkovichSpectrum R ↦ (x : R → ℝ)) := by
  refine ⟨Topology.IsInducing.induced _, ?_⟩
  intro x y h
  ext a
  exact congr_fun h a

/-- Evaluation at a ring element is continuous on the Berkovich spectrum. -/
theorem continuous_eval (a : R) : Continuous fun x : BerkovichSpectrum R ↦ x a :=
  (continuous_apply a).comp (isEmbedding_coe R).continuous

/-- A map into the Berkovich spectrum is continuous exactly when all its evaluations are
continuous. -/
theorem continuous_iff_eval {X : Type v} [TopologicalSpace X] {f : X → BerkovichSpectrum R} :
    Continuous f ↔ ∀ a : R, Continuous fun x ↦ f x a := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

/-- Pullback of Berkovich points along a norm-nonincreasing ring homomorphism is continuous. -/
theorem continuous_comap {S : Type v} [NormedRing S] (f : R →+* S) (hf : ∀ a, ‖f a‖ ≤ ‖a‖) :
    Continuous (comap R f hf) :=
  (continuous_iff_eval R).2 fun a ↦ continuous_eval S (f a)

/-- Convergence in the Berkovich spectrum is pointwise convergence of seminorms. -/
theorem tendsto_iff_eval {l : Filter (BerkovichSpectrum R)} {x : BerkovichSpectrum R} :
    Tendsto id l (𝓝 x) ↔ ∀ a : R, Tendsto (fun y ↦ y a) l (𝓝 (x a)) := by
  rw [(isEmbedding_coe R).isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

/-- The Berkovich spectrum is Hausdorff. -/
noncomputable instance berkovichSpectrumT2Space : T2Space (BerkovichSpectrum R) :=
  (isEmbedding_coe R).t2Space

private theorem isClosed_range_coe :
    IsClosed (Set.range fun x : BerkovichSpectrum R ↦ (x : R → ℝ)) := by
  let Z : Set (R → ℝ) := {f | f 0 = 0}
  let O : Set (R → ℝ) := {f | f 1 = 1}
  let A : Set (R → ℝ) := ⋂ a, ⋂ b, {f | f (a + b) ≤ f a + f b}
  let N : Set (R → ℝ) := ⋂ a, {f | f (-a) = f a}
  let M : Set (R → ℝ) := ⋂ a, ⋂ b, {f | f (a * b) = f a * f b}
  let B : Set (R → ℝ) := ⋂ a, {f | f a ≤ ‖a‖}
  have hrange : Set.range (fun x : BerkovichSpectrum R ↦ (x : R → ℝ)) =
      Z ∩ (O ∩ (A ∩ (N ∩ (M ∩ B)))) := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      simp only [Z, O, A, N, M, B, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq]
      exact ⟨x.map_zero, x.map_one, x.map_add_le, x.map_neg, x.map_mul, x.le_norm⟩
    · intro hf
      simp only [Z, O, A, N, M, B, Set.mem_inter_iff, Set.mem_iInter,
        Set.mem_setOf_eq] at hf
      rcases hf with ⟨hzero, hone, hadd, hneg, hmul, hbound⟩
      let p : MulRingSeminorm R :=
        { toFun := f
          map_zero' := hzero
          add_le' := hadd
          neg' := hneg
          map_one' := hone
          map_mul' := hmul }
      exact ⟨⟨p, hbound⟩, rfl⟩
  rw [hrange]
  have hZ : IsClosed Z := isClosed_eq (continuous_apply 0) continuous_const
  have hO : IsClosed O := isClosed_eq (continuous_apply 1) continuous_const
  have hA : IsClosed A := by
    dsimp only [A]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_le (by fun_prop) (by fun_prop)
  have hN : IsClosed N := by
    dsimp only [N]
    exact isClosed_iInter fun a ↦ isClosed_eq (by fun_prop) (by fun_prop)
  have hM : IsClosed M := by
    dsimp only [M]
    exact isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_eq (by fun_prop) (by fun_prop)
  have hB : IsClosed B := by
    dsimp only [B]
    exact isClosed_iInter fun a ↦ isClosed_le (by fun_prop) (by fun_prop)
  exact hZ.inter (hO.inter (hA.inter (hN.inter (hM.inter hB))))

/-- The Berkovich spectrum of every normed ring is compact. -/
theorem isCompact_univ : IsCompact (Set.univ : Set (BerkovichSpectrum R)) := by
  rw [(isEmbedding_coe R).isCompact_iff]
  rw [Set.image_univ]
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun a : R ↦ (isCompact_Icc : IsCompact (Set.Icc 0 ‖a‖)))
    (isClosed_range_coe R)
  rintro f ⟨x, rfl⟩ a -
  exact ⟨apply_nonneg x.seminorm a, x.le_norm' a⟩

noncomputable instance berkovichSpectrumCompactSpace : CompactSpace (BerkovichSpectrum R) :=
  isCompact_univ_iff.mp (isCompact_univ R)

end BerkovichSpectrum

end Rigid
