import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Rigid.AffinoidAlgebra.Basic
import Rigid.Berkovich.RelativeSpectrum

set_option linter.style.header false

open CategoryTheory
open scoped Topology

universe u

namespace Rigid

private abbrev PointLift (α : Type u) : Type (u + 1) := ULift.{u + 1, u} α

/-- A locally ringed topological core over `K`. This packages the data needed for morphisms and
sheaf-theoretic arguments, but it does not yet assert that the space is locally affinoid. -/
structure PreBerkovichSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] where
  point : Type u
  pointTopologicalSpace : TopologicalSpace (PointLift point)
  sections : (U : TopologicalSpace.Opens (PointLift point)) → Type u
  sectionsCommRing : ∀ U, CommRing (sections U)
  sectionsAlgebra : ∀ U, Algebra K (sections U)
  restriction : ∀ {U V : TopologicalSpace.Opens (PointLift point)}, U ≤ V →
    sections V →ₐ[K] sections U
  restriction_id : ∀ U,
    restriction (U := U) (V := U) le_rfl = AlgHom.id K (sections U)
  restriction_comp : ∀ {U V W : TopologicalSpace.Opens (PointLift point)} (hUV : U ≤ V)
      (hWU : W ≤ U),
    (restriction hWU).comp (restriction hUV) = restriction (hWU.trans hUV)
  existsUnique_glue : ∀ {ι : Type (u + 1)}
      (U : ι → TopologicalSpace.Opens (PointLift point))
      (V : TopologicalSpace.Opens (PointLift point))
      (hsub : ∀ i, U i ≤ V) (_hcover : V = ⨆ i, U i) (s : ∀ i, sections (U i)),
      (∀ i j, restriction inf_le_left (s i) = restriction inf_le_right (s j)) →
      ∃! t : sections V, ∀ i, restriction (hsub i) t = s i
  stalk : PointLift point → Type u
  stalkCommRing : ∀ x, CommRing (stalk x)
  stalkAlgebra : ∀ x, Algebra K (stalk x)
  stalkIsLocalRing : ∀ x, IsLocalRing (stalk x)
  germ : ∀ {U : TopologicalSpace.Opens (PointLift point)} {x : PointLift point}, x ∈ U →
    sections U →ₐ[K] stalk x

attribute [instance] PreBerkovichSpace.pointTopologicalSpace
attribute [instance] PreBerkovichSpace.sectionsCommRing PreBerkovichSpace.sectionsAlgebra
attribute [instance] PreBerkovichSpace.stalkCommRing PreBerkovichSpace.stalkAlgebra
attribute [instance] PreBerkovichSpace.stalkIsLocalRing

namespace PreBerkovichSpace

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The underlying type of points of a pre-Berkovich space. -/
def Point (X : PreBerkovichSpace K) : Type (u + 1) :=
  PointLift X.point

/-- The canonical topology on the points of a pre-Berkovich space. -/
instance instPointTopologicalSpace (X : PreBerkovichSpace K) : TopologicalSpace (Point X) :=
  X.pointTopologicalSpace

namespace StructureSheaf

/-- Analytic functions on an open subset of a pre-Berkovich space. -/
def Sections {X : PreBerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) : Type u :=
  X.sections U

instance sectionsCommRing {X : PreBerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) :
    CommRing (Sections U) :=
  X.sectionsCommRing U

instance sectionsAlgebra {X : PreBerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) :
    Algebra K (Sections U) :=
  X.sectionsAlgebra U

/-- Restriction of analytic functions. -/
def restriction {X : PreBerkovichSpace K}
    {U V : TopologicalSpace.Opens (Point X)} (hUV : U ≤ V) :
    Sections V →ₐ[K] Sections U :=
  X.restriction hUV

@[simp]
theorem restriction_id {X : PreBerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) :
    restriction (X := X) (U := U) (V := U) le_rfl = AlgHom.id K (Sections U) :=
  X.restriction_id U

@[simp]
theorem restriction_comp {X : PreBerkovichSpace K}
    {U V W : TopologicalSpace.Opens (Point X)} (hUV : U ≤ V) (hWU : W ≤ U) :
    (restriction (X := X) hWU).comp (restriction (X := X) hUV) =
      restriction (X := X) (hWU.trans hUV) :=
  X.restriction_comp hUV hWU

/-- Compatibility of analytic functions on an ordinary open cover. -/
def IsCompatible {X : PreBerkovichSpace K} {ι : Type (u + 1)}
    (U : ι → TopologicalSpace.Opens (Point X)) (s : ∀ i, Sections (U i)) : Prop :=
  ∀ i j,
    restriction (X := X) inf_le_left (s i) = restriction (X := X) inf_le_right (s j)

/-- The structure presheaf satisfies the sheaf condition. -/
theorem existsUnique_glue {X : PreBerkovichSpace K} {ι : Type (u + 1)}
    (U : ι → TopologicalSpace.Opens (Point X))
    (V : TopologicalSpace.Opens (Point X)) (hsub : ∀ i, U i ≤ V)
    (hcover : V = ⨆ i, U i) (s : ∀ i, Sections (U i))
    (hs : IsCompatible (X := X) U s) :
    ∃! t : Sections V, ∀ i, restriction (X := X) (hsub i) t = s i :=
  X.existsUnique_glue U V hsub hcover s hs

/-- The local ring of germs at a point. -/
def Stalk (X : PreBerkovichSpace K) (x : Point X) : Type u :=
  X.stalk x

instance stalkCommRing (X : PreBerkovichSpace K) (x : Point X) : CommRing (Stalk X x) :=
  X.stalkCommRing x

instance stalkAlgebra (X : PreBerkovichSpace K) (x : Point X) : Algebra K (Stalk X x) :=
  X.stalkAlgebra x

instance stalkIsLocalRing (X : PreBerkovichSpace K) (x : Point X) : IsLocalRing (Stalk X x) :=
  X.stalkIsLocalRing x

/-- The germ of an analytic function. -/
def germ {X : PreBerkovichSpace K}
    {U : TopologicalSpace.Opens (Point X)} {x : Point X}
    (hx : x ∈ U) : Sections U →ₐ[K] Stalk X x :=
  X.germ hx

end StructureSheaf

/-- Concrete data of a morphism of pre-Berkovich spaces. -/
structure AnalyticMorphismData (X Y : PreBerkovichSpace K) where
  base : Point X → Point Y
  continuous_base : Continuous base
  preimage : TopologicalSpace.Opens (Point Y) → TopologicalSpace.Opens (Point X)
  mem_preimage : ∀ x U, x ∈ preimage U ↔ base x ∈ U
  preimage_mono : ∀ {U V}, U ≤ V → preimage U ≤ preimage V
  pullback : ∀ U, StructureSheaf.Sections U →ₐ[K]
    StructureSheaf.Sections (preimage U)
  pullback_restriction : ∀ {U V} (hUV : U ≤ V),
    (StructureSheaf.restriction (X := X) (preimage_mono hUV)).comp (pullback V) =
      (pullback U).comp (StructureSheaf.restriction (X := Y) hUV)
  stalkMap : ∀ x, StructureSheaf.Stalk Y (base x) →ₐ[K] StructureSheaf.Stalk X x
  stalkMap_isLocal : ∀ x, IsLocalHom (stalkMap x)
  pullback_germ : ∀ (x) (U) (hx : base x ∈ U) (s : StructureSheaf.Sections U),
    stalkMap x (StructureSheaf.germ (X := Y) hx s) =
      StructureSheaf.germ (X := X) ((mem_preimage x U).2 hx) (pullback U s)

namespace AnalyticMorphismData

/-- Two analytic-morphism data are equal once their computational fields agree. -/
@[ext]
theorem ext {X Y : PreBerkovichSpace K} {f g : AnalyticMorphismData X Y}
    (hbase : f.base = g.base)
    (hpreimage : f.preimage = g.preimage)
    (hpullback : HEq f.pullback g.pullback)
    (hstalkMap : HEq f.stalkMap g.stalkMap) :
    f = g := by
  cases f
  cases g
  cases hbase
  cases hpreimage
  cases hpullback
  cases hstalkMap
  simp

/-- Identity analytic-morphism data. -/
def id (X : PreBerkovichSpace K) : AnalyticMorphismData X X where
  base x := x
  continuous_base := continuous_id
  preimage U := U
  mem_preimage _ _ := Iff.rfl
  preimage_mono h := h
  pullback U := AlgHom.id K (StructureSheaf.Sections U)
  pullback_restriction := by
    intro U V hUV
    ext s <;> rfl
  stalkMap x := AlgHom.id K (StructureSheaf.Stalk X x)
  stalkMap_isLocal _ := ⟨fun _ h => by simpa only [AlgHom.id_apply] using h⟩
  pullback_germ := by
    intro x U hx s
    rfl

/-- Composition of analytic-morphism data. -/
def comp {X Y Z : PreBerkovichSpace K}
    (f : AnalyticMorphismData X Y) (g : AnalyticMorphismData Y Z) :
    AnalyticMorphismData X Z where
  base x := g.base (f.base x)
  continuous_base := g.continuous_base.comp f.continuous_base
  preimage U := f.preimage (g.preimage U)
  mem_preimage x U := (f.mem_preimage x (g.preimage U)).trans (g.mem_preimage (f.base x) U)
  preimage_mono h := f.preimage_mono (g.preimage_mono h)
  pullback U := (f.pullback (g.preimage U)).comp (g.pullback U)
  pullback_restriction := by
    intro U V hUV
    rw [← AlgHom.comp_assoc, f.pullback_restriction (g.preimage_mono hUV),
      AlgHom.comp_assoc, g.pullback_restriction hUV, ← AlgHom.comp_assoc]
  stalkMap x := (f.stalkMap x).comp (g.stalkMap (f.base x))
  stalkMap_isLocal x := by
    refine ⟨fun a ha => ?_⟩
    exact (g.stalkMap_isLocal (f.base x)).map_nonunit a
      ((f.stalkMap_isLocal x).map_nonunit _ ha)
  pullback_germ := by
    intro x U hx s
    simp only [AlgHom.comp_apply]
    rw [g.pullback_germ, f.pullback_germ]

@[simp]
theorem id_base (X : PreBerkovichSpace K) : (id (K := K) X).base = _root_.id := rfl

@[simp]
theorem id_preimage (X : PreBerkovichSpace K)
    (U : TopologicalSpace.Opens (Point X)) : (id (K := K) X).preimage U = U := rfl

@[simp]
theorem comp_base {X Y Z : PreBerkovichSpace K}
    (f : AnalyticMorphismData X Y) (g : AnalyticMorphismData Y Z) :
    (comp (K := K) f g).base = g.base ∘ f.base := rfl

@[simp]
theorem comp_preimage {X Y Z : PreBerkovichSpace K}
    (f : AnalyticMorphismData X Y) (g : AnalyticMorphismData Y Z)
    (U : TopologicalSpace.Opens (Point Z)) :
    (comp (K := K) f g).preimage U = f.preimage (g.preimage U) := rfl

end AnalyticMorphismData

instance preBerkovichSpaceCategory : Category.{u + 1} (PreBerkovichSpace K) where
  Hom X Y := AnalyticMorphismData X Y
  id X := AnalyticMorphismData.id (K := K) X
  comp f g := AnalyticMorphismData.comp (K := K) f g
  id_comp := by
    intro X Y f
    apply AnalyticMorphismData.ext
    · rfl
    · rfl
    · exact heq_of_eq <| by
        funext U
        ext s <;> rfl
    · exact heq_of_eq <| by
        funext x
        ext s <;> rfl
  comp_id := by
    intro X Y f
    apply AnalyticMorphismData.ext
    · rfl
    · rfl
    · exact heq_of_eq <| by
        funext U
        ext s <;> rfl
    · exact heq_of_eq <| by
        funext x
        ext s <;> rfl
  assoc := by
    intro W X Y Z f g h
    apply AnalyticMorphismData.ext
    · rfl
    · rfl
    · exact heq_of_eq <| by
        funext U
        ext s <;> rfl
    · exact heq_of_eq <| by
        funext x
        ext s <;> rfl

namespace Point

/-- The map on points induced by a morphism of pre-Berkovich spaces. -/
def map {X Y : PreBerkovichSpace K} (f : X ⟶ Y) : Point X → Point Y :=
  f.base

/-- The map on points induced by an analytic morphism is continuous. -/
theorem continuous_map {X Y : PreBerkovichSpace K} (f : X ⟶ Y) : Continuous (map f) :=
  f.continuous_base

@[simp]
theorem map_id (X : PreBerkovichSpace K) : map (𝟙 X) = id := by
  funext x
  rfl

@[simp]
theorem map_comp {X Y Z : PreBerkovichSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map g ∘ map f := by
  funext x
  rfl

/-- An analytic isomorphism induces a homeomorphism on underlying point spaces. -/
def homeomorphOfIso {X Y : PreBerkovichSpace K} (e : X ≅ Y) :
    Point X ≃ₜ Point Y where
  toFun := map e.hom
  invFun := map e.inv
  left_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp e.hom e.inv).symm x
  right_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp e.inv e.hom).symm x
  continuous_toFun := continuous_map e.hom
  continuous_invFun := continuous_map e.inv

end Point

/-- The functor assigning to a pre-Berkovich space its underlying topological space. -/
def pointFunctor : PreBerkovichSpace K ⥤ TopCat.{u + 1} where
  obj X := TopCat.of (Point X)
  map f := TopCat.ofHom (ContinuousMap.mk (Point.map f) (Point.continuous_map f))
  map_id X := by
    apply TopCat.hom_ext
    ext x
    exact congr_fun (Point.map_id X) x
  map_comp f g := by
    apply TopCat.hom_ext
    ext x
    exact congr_fun (Point.map_comp f g) x

/-- Morphisms are exactly analytic-morphism data. -/
def analyticHomEquiv (X Y : PreBerkovichSpace K) :
    (X ⟶ Y) ≃ AnalyticMorphismData X Y :=
  Equiv.refl _

@[simp]
theorem analyticHomEquiv_id (X : PreBerkovichSpace K) :
    analyticHomEquiv (K := K) X X (𝟙 X) = AnalyticMorphismData.id (K := K) X := rfl

@[simp]
theorem analyticHomEquiv_comp {X Y Z : PreBerkovichSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    analyticHomEquiv (K := K) X Z (f ≫ g) =
      AnalyticMorphismData.comp (K := K) (analyticHomEquiv (K := K) X Y f)
        (analyticHomEquiv (K := K) Y Z g) := rfl

end PreBerkovichSpace

/-- A universe-bounded strict affinoid algebra used as explicit local-model data. -/
structure AffinoidAlgebraModel
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] where
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra K A]
  isAffinoid : IsAffinoidAlgebra K A

attribute [instance] AffinoidAlgebraModel.commRing AffinoidAlgebraModel.algebra

/-- An affinoid analytic core. Its points are the actual relative Berkovich spectrum of the chosen
strict affinoid algebra model, while the sheaf and stalk data remain abstract. -/
structure AffinoidBerkovichCore
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] where
  model : AffinoidAlgebraModel K
  sections :
    (U : TopologicalSpace.Opens (PointLift (BerkovichSpectrumOver K model.A))) → Type u
  sectionsCommRing : ∀ U, CommRing (sections U)
  sectionsAlgebra : ∀ U, Algebra K (sections U)
  restriction :
    ∀ {U V : TopologicalSpace.Opens (PointLift (BerkovichSpectrumOver K model.A))}, U ≤ V →
      sections V →ₐ[K] sections U
  restriction_id : ∀ U,
    restriction (U := U) (V := U) le_rfl = AlgHom.id K (sections U)
  restriction_comp :
    ∀ {U V W : TopologicalSpace.Opens (PointLift (BerkovichSpectrumOver K model.A))}
      (hUV : U ≤ V) (hWU : W ≤ U),
      (restriction hWU).comp (restriction hUV) = restriction (hWU.trans hUV)
  existsUnique_glue : ∀ {ι : Type (u + 1)}
      (U : ι → TopologicalSpace.Opens (PointLift (BerkovichSpectrumOver K model.A)))
      (V : TopologicalSpace.Opens (PointLift (BerkovichSpectrumOver K model.A)))
      (hsub : ∀ i, U i ≤ V) (_hcover : V = ⨆ i, U i) (s : ∀ i, sections (U i)),
      (∀ i j, restriction inf_le_left (s i) = restriction inf_le_right (s j)) →
      ∃! t : sections V, ∀ i, restriction (hsub i) t = s i
  stalk : PointLift (BerkovichSpectrumOver K model.A) → Type u
  stalkCommRing : ∀ x, CommRing (stalk x)
  stalkAlgebra : ∀ x, Algebra K (stalk x)
  stalkIsLocalRing : ∀ x, IsLocalRing (stalk x)
  germ :
    ∀ {U : TopologicalSpace.Opens (PointLift (BerkovichSpectrumOver K model.A))}
      {x : PointLift (BerkovichSpectrumOver K model.A)},
      x ∈ U → sections U →ₐ[K] stalk x

attribute [instance] AffinoidBerkovichCore.sectionsCommRing AffinoidBerkovichCore.sectionsAlgebra
attribute [instance] AffinoidBerkovichCore.stalkCommRing AffinoidBerkovichCore.stalkAlgebra
attribute [instance] AffinoidBerkovichCore.stalkIsLocalRing

namespace AffinoidBerkovichCore

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- Forget the affinoid local-model origin and keep only the locally ringed topological core. -/
def toPreBerkovichSpace (X : AffinoidBerkovichCore K) : PreBerkovichSpace K where
  point := BerkovichSpectrumOver K X.model.A
  pointTopologicalSpace := inferInstance
  sections := X.sections
  sectionsCommRing := X.sectionsCommRing
  sectionsAlgebra := X.sectionsAlgebra
  restriction := X.restriction
  restriction_id := X.restriction_id
  restriction_comp := X.restriction_comp
  existsUnique_glue := X.existsUnique_glue
  stalk := X.stalk
  stalkCommRing := X.stalkCommRing
  stalkAlgebra := X.stalkAlgebra
  stalkIsLocalRing := X.stalkIsLocalRing
  germ := X.germ

end AffinoidBerkovichCore

/-- An affinoid chart on a pre-Berkovich space. The source carries an actual affinoid algebra model,
its point space is identified with an open subset of the target, and the induced stalk maps are
isomorphisms. -/
structure AffinoidChart
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (X : PreBerkovichSpace K) where
  source : AffinoidBerkovichCore K
  carrier : TopologicalSpace.Opens (PreBerkovichSpace.Point X)
  toCore : source.toPreBerkovichSpace ⟶ X
  pointHomeomorph : PreBerkovichSpace.Point source.toPreBerkovichSpace ≃ₜ carrier
  pointHomeomorph_toFun : ∀ x,
    ((pointHomeomorph x : carrier) : PreBerkovichSpace.Point X) =
      PreBerkovichSpace.Point.map toCore x
  stalkMap_bijective : ∀ x, Function.Bijective (toCore.stalkMap x)

/-- A Berkovich analytic space over `K`: a locally ringed topological core equipped with an
affinoid atlas covering every point. -/
structure BerkovichSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] where
  toPreBerkovichSpace : PreBerkovichSpace K
  affinoidDomain : Type (u + 1)
  affinoidDomainData : affinoidDomain → AffinoidChart K toPreBerkovichSpace
  affinoidDomain_cover : ∀ x : PreBerkovichSpace.Point toPreBerkovichSpace,
    ∃ U : affinoidDomain, x ∈ (affinoidDomainData U).carrier

namespace BerkovichSpace

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The underlying type of points of a Berkovich space. -/
def Point (X : BerkovichSpace K) : Type (u + 1) :=
  PreBerkovichSpace.Point X.toPreBerkovichSpace

/-- The canonical topology on the points of a Berkovich space. -/
instance instPointTopologicalSpace (X : BerkovichSpace K) : TopologicalSpace (Point X) :=
  inferInstanceAs (TopologicalSpace (PreBerkovichSpace.Point X.toPreBerkovichSpace))

/-- The type of affinoid domains in a Berkovich space. -/
def AffinoidDomain (X : BerkovichSpace K) : Type (u + 1) :=
  X.affinoidDomain

namespace AffinoidDomain

/-- The underlying affinoid chart data carried by a domain. -/
def chart {X : BerkovichSpace K} (U : AffinoidDomain X) :
    AffinoidChart K X.toPreBerkovichSpace :=
  X.affinoidDomainData U

/-- The underlying open subset of points of an affinoid domain. -/
def carrier {X : BerkovichSpace K} (U : AffinoidDomain X) : TopologicalSpace.Opens (Point X) :=
  (chart U).carrier

/-- The strict affinoid algebra model carried by an affinoid domain. -/
def model {X : BerkovichSpace K} (U : AffinoidDomain X) : AffinoidAlgebraModel K :=
  (chart U).source.model

/-- The locally ringed analytic core of an affinoid domain. -/
def core {X : BerkovichSpace K} (U : AffinoidDomain X) : PreBerkovichSpace K :=
  (chart U).source.toPreBerkovichSpace

/-- The morphism identifying an affinoid domain with its image in the ambient space. -/
def inclusion {X : BerkovichSpace K} (U : AffinoidDomain X) : core U ⟶ X.toPreBerkovichSpace :=
  (chart U).toCore

/-- The point space of an affinoid domain is homeomorphic to its carrier open. -/
def pointHomeomorph {X : BerkovichSpace K} (U : AffinoidDomain X) :
    PreBerkovichSpace.Point (core U) ≃ₜ carrier U :=
  (chart U).pointHomeomorph

@[simp]
theorem pointHomeomorph_toFun {X : BerkovichSpace K} (U : AffinoidDomain X)
    (x : PreBerkovichSpace.Point (core U)) :
    ((pointHomeomorph U x : carrier U) : Point X) = PreBerkovichSpace.Point.map (inclusion U) x :=
  (chart U).pointHomeomorph_toFun x

theorem stalkMap_bijective {X : BerkovichSpace K} (U : AffinoidDomain X)
    (x : PreBerkovichSpace.Point (core U)) :
    Function.Bijective ((inclusion U).stalkMap x) :=
  (chart U).stalkMap_bijective x

end AffinoidDomain

/-- Every point of a Berkovich space lies in an affinoid domain from the chosen atlas. -/
theorem exists_affinoidDomain_containing {X : BerkovichSpace K} (x : Point X) :
    ∃ U : AffinoidDomain X, x ∈ AffinoidDomain.carrier U :=
  X.affinoidDomain_cover x

namespace StructureSheaf

/-- Analytic functions on an open subset of a Berkovich space. -/
def Sections {X : BerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) : Type u :=
  PreBerkovichSpace.StructureSheaf.Sections (X := X.toPreBerkovichSpace) U

instance sectionsCommRing {X : BerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) :
    CommRing (Sections U) :=
  PreBerkovichSpace.StructureSheaf.sectionsCommRing (X := X.toPreBerkovichSpace) U

instance sectionsAlgebra {X : BerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) :
    Algebra K (Sections U) :=
  PreBerkovichSpace.StructureSheaf.sectionsAlgebra (X := X.toPreBerkovichSpace) U

/-- Restriction of Berkovich analytic functions. -/
def restriction {X : BerkovichSpace K}
    {U V : TopologicalSpace.Opens (Point X)} (hUV : U ≤ V) :
    Sections V →ₐ[K] Sections U :=
  PreBerkovichSpace.StructureSheaf.restriction (X := X.toPreBerkovichSpace) hUV

@[simp]
theorem restriction_id {X : BerkovichSpace K} (U : TopologicalSpace.Opens (Point X)) :
    restriction (X := X) (U := U) (V := U) le_rfl = AlgHom.id K (Sections U) :=
  PreBerkovichSpace.StructureSheaf.restriction_id (X := X.toPreBerkovichSpace) U

@[simp]
theorem restriction_comp {X : BerkovichSpace K}
    {U V W : TopologicalSpace.Opens (Point X)} (hUV : U ≤ V) (hWU : W ≤ U) :
    (restriction (X := X) hWU).comp (restriction (X := X) hUV) =
      restriction (X := X) (hWU.trans hUV) :=
  PreBerkovichSpace.StructureSheaf.restriction_comp (X := X.toPreBerkovichSpace) hUV hWU

/-- Compatibility of analytic functions on an ordinary open cover. -/
def IsCompatible {X : BerkovichSpace K} {ι : Type (u + 1)}
    (U : ι → TopologicalSpace.Opens (Point X)) (s : ∀ i, Sections (U i)) : Prop :=
  PreBerkovichSpace.StructureSheaf.IsCompatible (X := X.toPreBerkovichSpace) U s

/-- The Berkovich analytic structure presheaf satisfies the sheaf condition. -/
theorem existsUnique_glue {X : BerkovichSpace K} {ι : Type (u + 1)}
    (U : ι → TopologicalSpace.Opens (Point X))
    (V : TopologicalSpace.Opens (Point X)) (hsub : ∀ i, U i ≤ V)
    (hcover : V = ⨆ i, U i) (s : ∀ i, Sections (U i))
    (hs : IsCompatible (X := X) U s) :
    ∃! t : Sections V, ∀ i, restriction (X := X) (hsub i) t = s i :=
  PreBerkovichSpace.StructureSheaf.existsUnique_glue (X := X.toPreBerkovichSpace)
    U V hsub hcover s hs

/-- The local ring of germs at a Berkovich point. -/
def Stalk (X : BerkovichSpace K) (x : Point X) : Type u :=
  PreBerkovichSpace.StructureSheaf.Stalk X.toPreBerkovichSpace x

instance stalkCommRing (X : BerkovichSpace K) (x : Point X) : CommRing (Stalk X x) :=
  PreBerkovichSpace.StructureSheaf.stalkCommRing X.toPreBerkovichSpace x

instance stalkAlgebra (X : BerkovichSpace K) (x : Point X) : Algebra K (Stalk X x) :=
  PreBerkovichSpace.StructureSheaf.stalkAlgebra X.toPreBerkovichSpace x

instance stalkIsLocalRing (X : BerkovichSpace K) (x : Point X) : IsLocalRing (Stalk X x) :=
  PreBerkovichSpace.StructureSheaf.stalkIsLocalRing X.toPreBerkovichSpace x

/-- The germ of a Berkovich analytic function. -/
def germ {X : BerkovichSpace K}
    {U : TopologicalSpace.Opens (Point X)} {x : Point X}
    (hx : x ∈ U) : Sections U →ₐ[K] Stalk X x :=
  PreBerkovichSpace.StructureSheaf.germ (X := X.toPreBerkovichSpace) hx

end StructureSheaf

/-- Concrete data of a morphism of Berkovich analytic spaces. -/
abbrev AnalyticMorphismData (X Y : BerkovichSpace K) :=
  PreBerkovichSpace.AnalyticMorphismData X.toPreBerkovichSpace Y.toPreBerkovichSpace

namespace AnalyticMorphismData

/-- Identity analytic-morphism data. -/
def id (X : BerkovichSpace K) : AnalyticMorphismData X X :=
  PreBerkovichSpace.AnalyticMorphismData.id (K := K) X.toPreBerkovichSpace

/-- Composition of analytic-morphism data. -/
def comp {X Y Z : BerkovichSpace K}
    (f : AnalyticMorphismData X Y) (g : AnalyticMorphismData Y Z) :
    AnalyticMorphismData X Z :=
  PreBerkovichSpace.AnalyticMorphismData.comp (K := K) f g

@[simp]
theorem id_base (X : BerkovichSpace K) : (id (K := K) X).base = _root_.id := rfl

@[simp]
theorem id_preimage (X : BerkovichSpace K)
    (U : TopologicalSpace.Opens (Point X)) : (id (K := K) X).preimage U = U := rfl

@[simp]
theorem comp_base {X Y Z : BerkovichSpace K}
    (f : AnalyticMorphismData X Y) (g : AnalyticMorphismData Y Z) :
    (comp (K := K) f g).base = g.base ∘ f.base := rfl

@[simp]
theorem comp_preimage {X Y Z : BerkovichSpace K}
    (f : AnalyticMorphismData X Y) (g : AnalyticMorphismData Y Z)
    (U : TopologicalSpace.Opens (Point Z)) :
    (comp (K := K) f g).preimage U = f.preimage (g.preimage U) := rfl

end AnalyticMorphismData

instance berkovichSpaceCategory : Category.{u + 1} (BerkovichSpace K) where
  Hom X Y := AnalyticMorphismData X Y
  id X := AnalyticMorphismData.id (K := K) X
  comp f g := AnalyticMorphismData.comp (K := K) f g
  id_comp := by
    intro X Y f
    apply PreBerkovichSpace.AnalyticMorphismData.ext
    · rfl
    · rfl
    · exact heq_of_eq <| by
        funext U
        ext s <;> rfl
    · exact heq_of_eq <| by
        funext x
        ext s <;> rfl
  comp_id := by
    intro X Y f
    apply PreBerkovichSpace.AnalyticMorphismData.ext
    · rfl
    · rfl
    · exact heq_of_eq <| by
        funext U
        ext s <;> rfl
    · exact heq_of_eq <| by
        funext x
        ext s <;> rfl
  assoc := by
    intro W X Y Z f g h
    apply PreBerkovichSpace.AnalyticMorphismData.ext
    · rfl
    · rfl
    · exact heq_of_eq <| by
        funext U
        ext s <;> rfl
    · exact heq_of_eq <| by
        funext x
        ext s <;> rfl

namespace Point

/-- The map on points induced by a morphism of Berkovich spaces. -/
def map {X Y : BerkovichSpace K} (f : X ⟶ Y) : Point X → Point Y :=
  PreBerkovichSpace.Point.map f

/-- The map on points induced by an analytic morphism is continuous. -/
theorem continuous_map {X Y : BerkovichSpace K} (f : X ⟶ Y) : Continuous (map f) :=
  PreBerkovichSpace.Point.continuous_map f

@[simp]
theorem map_id (X : BerkovichSpace K) : map (𝟙 X) = id := by
  funext x
  rfl

@[simp]
theorem map_comp {X Y Z : BerkovichSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map g ∘ map f := by
  funext x
  rfl

/-- An analytic isomorphism induces a homeomorphism on underlying point spaces. -/
def homeomorphOfIso {X Y : BerkovichSpace K} (e : X ≅ Y) :
    Point X ≃ₜ Point Y where
  toFun := map e.hom
  invFun := map e.inv
  left_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp e.hom e.inv).symm x
  right_inv x := by
    simpa [Function.comp_apply] using congr_fun (map_comp e.inv e.hom).symm x
  continuous_toFun := continuous_map e.hom
  continuous_invFun := continuous_map e.inv

end Point

/-- The functor assigning to a Berkovich space its underlying topological space. -/
def pointFunctor : BerkovichSpace K ⥤ TopCat.{u + 1} where
  obj X := TopCat.of (Point X)
  map f := TopCat.ofHom (ContinuousMap.mk (Point.map f) (Point.continuous_map f))
  map_id X := by
    apply TopCat.hom_ext
    ext x
    exact congr_fun (Point.map_id X) x
  map_comp f g := by
    apply TopCat.hom_ext
    ext x
    exact congr_fun (Point.map_comp f g) x

/-- Morphisms are exactly analytic-morphism data on the underlying core. -/
def analyticHomEquiv (X Y : BerkovichSpace K) :
    (X ⟶ Y) ≃ AnalyticMorphismData X Y :=
  Equiv.refl _

@[simp]
theorem analyticHomEquiv_id (X : BerkovichSpace K) :
    analyticHomEquiv (K := K) X X (𝟙 X) = AnalyticMorphismData.id (K := K) X := rfl

@[simp]
theorem analyticHomEquiv_comp {X Y Z : BerkovichSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    analyticHomEquiv (K := K) X Z (f ≫ g) =
      AnalyticMorphismData.comp (K := K) (analyticHomEquiv (K := K) X Y f)
        (analyticHomEquiv (K := K) Y Z g) := rfl

end BerkovichSpace

end Rigid
