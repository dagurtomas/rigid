import Mathlib
import Rigid.AffinoidAlgebra.Basic

set_option linter.style.header false
set_option linter.unusedVariables false

open CategoryTheory

universe u

namespace Rigid

/-- A universe-bounded strict affinoid algebra, used as explicit local-model data for global
analytic spaces. -/
structure AffinoidAlgebraModel
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] where
  A : Type u
  [commRing : CommRing A]
  [algebra : Algebra K A]
  isAffinoid : IsAffinoidAlgebra K A

attribute [instance] AffinoidAlgebraModel.commRing AffinoidAlgebraModel.algebra

/-- A small internal code for a rigid analytic space. Raw points, admissible opens, and affinoid
atlas data all live in universe `u`; the public API exposes comparator-sized wrappers via `ULift`.
The admissible-cover relation is part of the structure and is not defined in terms of finite
subcovers. -/
structure SpaceCode
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] where
  PointCode : Type u
  OpenCode : Type u
  openCarrier : OpenCode → Set PointCode
  open_ext : ∀ {U V : OpenCode}, openCarrier U = openCarrier V → U = V
  topOpen : OpenCode
  carrier_topOpen : openCarrier topOpen = Set.univ
  interOpen : OpenCode → OpenCode → OpenCode
  carrier_interOpen : ∀ U V,
    openCarrier (interOpen U V) = openCarrier U ∩ openCarrier V
  isCover : ∀ {ι : Type u}, (ι → OpenCode) → OpenCode → Prop
  isCover_singleton : ∀ V : OpenCode, isCover (fun _ : PUnit ↦ V) V
  isCover_pullback : ∀ {ι : Type u} {U : ι → OpenCode} {V : OpenCode},
    isCover U V → ∀ W : OpenCode, isCover (fun i ↦ interOpen (U i) W) (interOpen V W)
  isCover_trans : ∀ {ι : Type u} {κ : ι → Type u}
      {U : ι → OpenCode} {V : OpenCode},
    isCover U V → (W : ∀ i, κ i → OpenCode) → (∀ i, isCover (W i) (U i)) →
      isCover (fun p : Sigma κ ↦ W p.1 p.2) V
  isCover_subset : ∀ {ι : Type u} {U : ι → OpenCode} {V : OpenCode},
    isCover U V → ∀ i, openCarrier (U i) ⊆ openCarrier V
  isCover_iUnion : ∀ {ι : Type u} {U : ι → OpenCode} {V : OpenCode},
    isCover U V → openCarrier V = ⋃ i, openCarrier (U i)
  SectionsCode : OpenCode → Type u
  sectionsCommRing : ∀ U, CommRing (SectionsCode U)
  sectionsAlgebra : ∀ U, Algebra K (SectionsCode U)
  restrictSections : ∀ {U V : OpenCode}, openCarrier U ⊆ openCarrier V →
    SectionsCode V →ₐ[K] SectionsCode U
  restrictSections_id : ∀ U,
    restrictSections (U := U) (V := U) Set.Subset.rfl =
      AlgHom.id K (SectionsCode U)
  restrictSections_comp : ∀ {U V W : OpenCode}
      (hUV : openCarrier U ⊆ openCarrier V)
      (hWU : openCarrier W ⊆ openCarrier U),
    (restrictSections hWU).comp (restrictSections hUV) =
      restrictSections (hWU.trans hUV)
  glueSections : ∀ {ι : Type u} {U : ι → OpenCode} {V : OpenCode}
      (hU : isCover U V) (s : ∀ i, SectionsCode (U i)),
      (∀ i j,
        restrictSections
            (show openCarrier (interOpen (U i) (U j)) ⊆ openCarrier (U i) by
              rw [carrier_interOpen]
              exact Set.inter_subset_left)
            (s i) =
          restrictSections
            (show openCarrier (interOpen (U i) (U j)) ⊆ openCarrier (U j) by
              rw [carrier_interOpen]
              exact Set.inter_subset_right)
            (s j)) →
      ∃! t : SectionsCode V, ∀ i, restrictSections (isCover_subset hU i) t = s i
  StalkCode : PointCode → Type u
  stalkCommRing : ∀ x, CommRing (StalkCode x)
  stalkAlgebra : ∀ x, Algebra K (StalkCode x)
  stalkIsLocalRing : ∀ x, IsLocalRing (StalkCode x)
  germSections : ∀ {U : OpenCode} {x : PointCode}, x ∈ openCarrier U →
    SectionsCode U →ₐ[K] StalkCode x
  DomainCode : Type u
  domainOpen : DomainCode → OpenCode
  domainModel : DomainCode → AffinoidAlgebraModel K
  AtlasIndex : Type u
  atlasDomain : AtlasIndex → DomainCode
  atlasIsCover : isCover (fun i : AtlasIndex ↦ domainOpen (atlasDomain i)) topOpen

/-- A rigid analytic space over `K`, locally modeled on strict affinoid spectra in an admissible
Grothendieck topology. -/
def RigidSpace
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] :
    Type (u + 1) :=
  SpaceCode K

namespace RigidSpace

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The type of analytic points of a rigid space. -/
def Point (X : RigidSpace K) : Type (u + 1) := ULift.{u + 1, u} X.PointCode

/-- An admissible open of a rigid space. -/
def AdmissibleOpen (X : RigidSpace K) : Type (u + 1) := ULift.{u + 1, u} X.OpenCode

namespace AdmissibleOpen

/-- The analytic points belonging to an admissible open. -/
def carrier {X : RigidSpace K} (U : AdmissibleOpen X) : Set (Point X) :=
  {x | x.down ∈ X.openCarrier U.down}

/-- Admissible opens are determined by their point sets. -/
@[ext]
theorem ext {X : RigidSpace K} {U V : AdmissibleOpen X}
    (h : carrier U = carrier V) : U = V := by
  apply ULift.ext
  exact X.open_ext <| by
    ext x
    simpa [carrier] using (Set.ext_iff.mp h) (ULift.up x : Point X)

/-- The full admissible open. -/
def top (X : RigidSpace K) : AdmissibleOpen X := ULift.up X.topOpen

@[simp]
theorem carrier_top (X : RigidSpace K) : carrier (top X) = Set.univ := by
  ext x
  change x.down ∈ X.openCarrier X.topOpen ↔ x ∈ Set.univ
  simpa using (Set.ext_iff.mp X.carrier_topOpen x.down)

/-- The intersection of two admissible opens. -/
def inter {X : RigidSpace K} (U V : AdmissibleOpen X) : AdmissibleOpen X :=
  ULift.up (X.interOpen U.down V.down)

@[simp]
theorem carrier_inter {X : RigidSpace K} (U V : AdmissibleOpen X) :
    carrier (inter U V) = carrier U ∩ carrier V := by
  ext x
  change x.down ∈ X.openCarrier (X.interOpen U.down V.down) ↔ x ∈ carrier U ∩ carrier V
  simpa [carrier, inter] using (Set.ext_iff.mp (X.carrier_interOpen U.down V.down) x.down)

/-- The intersection is contained in its left factor. -/
theorem inter_subset_left {X : RigidSpace K} (U V : AdmissibleOpen X) :
    carrier (inter U V) ⊆ carrier U := by
  rw [carrier_inter]
  exact Set.inter_subset_left

/-- The intersection is contained in its right factor. -/
theorem inter_subset_right {X : RigidSpace K} (U V : AdmissibleOpen X) :
    carrier (inter U V) ⊆ carrier V := by
  rw [carrier_inter]
  exact Set.inter_subset_right

/-- A family is an admissible cover of an admissible open in the rigid Grothendieck topology. -/
def IsCover {X : RigidSpace K} {ι : Type u}
    (U : ι → AdmissibleOpen X) (V : AdmissibleOpen X) : Prop :=
  X.isCover (fun i ↦ (U i).down) V.down

namespace IsCover

/-- A one-member family covers its member. -/
theorem singleton {X : RigidSpace K} (V : AdmissibleOpen X) :
    IsCover (fun _ : PUnit ↦ V) V :=
  X.isCover_singleton V.down

/-- Admissible covers are stable under intersection with another admissible open. -/
theorem pullback {X : RigidSpace K} {ι : Type u}
    {U : ι → AdmissibleOpen X} {V : AdmissibleOpen X} (h : IsCover U V)
    (W : AdmissibleOpen X) :
    IsCover (fun i ↦ inter (U i) W) (inter V W) :=
  X.isCover_pullback h W.down

/-- Admissible coverings are transitive. -/
theorem trans {X : RigidSpace K} {ι : Type u} {κ : ι → Type u}
    {U : ι → AdmissibleOpen X} {V : AdmissibleOpen X} (hU : IsCover U V)
    (W : ∀ i, κ i → AdmissibleOpen X) (hW : ∀ i, IsCover (W i) (U i)) :
    IsCover (fun p : Sigma κ ↦ W p.1 p.2) V :=
  X.isCover_trans hU (fun i j ↦ (W i j).down) hW

/-- Every member of an admissible cover is contained in the covered open. -/
theorem subset {X : RigidSpace K} {ι : Type u}
    {U : ι → AdmissibleOpen X} {V : AdmissibleOpen X} (h : IsCover U V) (i : ι) :
    carrier (U i) ⊆ carrier V := by
  intro x hx
  change x.down ∈ X.openCarrier V.down
  exact X.isCover_subset h i (by simpa [carrier] using hx)

/-- An admissible cover covers the underlying point set. -/
theorem iUnion_carrier {X : RigidSpace K} {ι : Type u}
    {U : ι → AdmissibleOpen X} {V : AdmissibleOpen X} (h : IsCover U V) :
    carrier V = ⋃ i, carrier (U i) := by
  ext x
  change x.down ∈ X.openCarrier V.down ↔ x ∈ ⋃ i, carrier (U i)
  simpa [carrier] using (Set.ext_iff.mp (X.isCover_iUnion h) x.down)

end IsCover

/-- An admissible open is quasi-compact for the admissible topology. -/
def IsQuasiCompact {X : RigidSpace K} (U : AdmissibleOpen X) : Prop :=
  ∀ {ι : Type u} (V : ι → AdmissibleOpen X), IsCover V U →
    ∃ s : Set ι, s.Finite ∧ IsCover (fun i : s ↦ V i.1) U

/-- Quasi-compactness means that every admissible cover has a finite admissible subcover. -/
theorem isQuasiCompact_iff {X : RigidSpace K} (U : AdmissibleOpen X) :
    IsQuasiCompact U ↔
      ∀ {ι : Type u} (V : ι → AdmissibleOpen X), IsCover V U →
        ∃ s : Set ι, s.Finite ∧ IsCover (fun i : s ↦ V i.1) U := Iff.rfl

end AdmissibleOpen

namespace StructureSheaf

/-- Analytic functions on an admissible open of a rigid space. -/
def Sections {X : RigidSpace K} (U : AdmissibleOpen X) : Type u :=
  X.SectionsCode U.down

instance sectionsCommRing {X : RigidSpace K} (U : AdmissibleOpen X) :
    CommRing (Sections U) :=
  X.sectionsCommRing U.down

instance sectionsAlgebra {X : RigidSpace K} (U : AdmissibleOpen X) :
    Algebra K (Sections U) :=
  X.sectionsAlgebra U.down

/-- The raw subset proof corresponding to an inclusion of admissible-open carriers. -/
theorem rawSubset {X : RigidSpace K} {U V : AdmissibleOpen X}
    (hUV : AdmissibleOpen.carrier U ⊆ AdmissibleOpen.carrier V) :
    X.openCarrier U.down ⊆ X.openCarrier V.down := by
  intro x hx
  exact hUV (by simpa [AdmissibleOpen.carrier] using hx)

/-- Restriction of analytic functions. -/
def restriction {X : RigidSpace K} {U V : AdmissibleOpen X}
    (hUV : AdmissibleOpen.carrier U ⊆ AdmissibleOpen.carrier V) :
    Sections V →ₐ[K] Sections U :=
  X.restrictSections (U := U.down) (V := V.down) (rawSubset hUV)

@[simp]
theorem restriction_id {X : RigidSpace K} (U : AdmissibleOpen X) :
    restriction (U := U) (V := U) Set.Subset.rfl = AlgHom.id K (Sections U) := by
  letI := X.sectionsCommRing U.down
  letI := X.sectionsAlgebra U.down
  unfold restriction
  change X.restrictSections (rawSubset (U := U) (V := U) Set.Subset.rfl) =
    AlgHom.id K (X.SectionsCode U.down)
  simpa [Sections] using X.restrictSections_id U.down

@[simp]
theorem restriction_comp {X : RigidSpace K} {U V W : AdmissibleOpen X}
    (hUV : AdmissibleOpen.carrier U ⊆ AdmissibleOpen.carrier V)
    (hWU : AdmissibleOpen.carrier W ⊆ AdmissibleOpen.carrier U) :
    (restriction hWU).comp (restriction hUV) = restriction (hWU.trans hUV) := by
  letI := X.sectionsCommRing V.down
  letI := X.sectionsCommRing U.down
  letI := X.sectionsCommRing W.down
  letI := X.sectionsAlgebra V.down
  letI := X.sectionsAlgebra U.down
  letI := X.sectionsAlgebra W.down
  unfold restriction
  change (X.restrictSections (rawSubset hWU)).comp (X.restrictSections (rawSubset hUV)) =
    X.restrictSections (rawSubset (hWU.trans hUV))
  simpa [Sections] using X.restrictSections_comp (rawSubset hUV) (rawSubset hWU)

/-- Compatibility of local sections on an admissible cover. -/
def IsCompatible {X : RigidSpace K} {ι : Type u}
    (U : ι → AdmissibleOpen X) (s : ∀ i, Sections (U i)) : Prop :=
  ∀ i j,
    restriction (AdmissibleOpen.inter_subset_left (U i) (U j)) (s i) =
      restriction (AdmissibleOpen.inter_subset_right (U i) (U j)) (s j)

/-- The rigid analytic structure presheaf is a sheaf for admissible covers. -/
theorem existsUnique_glue {X : RigidSpace K} {ι : Type u}
    {U : ι → AdmissibleOpen X} {V : AdmissibleOpen X}
    (hU : AdmissibleOpen.IsCover U V) (s : ∀ i, Sections (U i))
    (hs : IsCompatible U s) :
    ∃! t : Sections V, ∀ i, restriction (hU.subset i) t = s i :=
  X.glueSections (V := V.down) (U := fun i ↦ (U i).down) hU s hs

/-- The local ring of germs at an analytic point. -/
def Stalk (X : RigidSpace K) (x : Point X) : Type u :=
  X.StalkCode x.down

instance stalkCommRing (X : RigidSpace K) (x : Point X) : CommRing (Stalk X x) :=
  X.stalkCommRing x.down

instance stalkAlgebra (X : RigidSpace K) (x : Point X) : Algebra K (Stalk X x) :=
  X.stalkAlgebra x.down

instance stalkIsLocalRing (X : RigidSpace K) (x : Point X) : IsLocalRing (Stalk X x) :=
  X.stalkIsLocalRing x.down

/-- The germ of a section at a point of its domain. -/
def germ {X : RigidSpace K} {U : AdmissibleOpen X} {x : Point X}
    (hx : x ∈ AdmissibleOpen.carrier U) : Sections U →ₐ[K] Stalk X x :=
  X.germSections (U := U.down) (x := x.down) hx

end StructureSheaf

/-- Concrete data of an analytic morphism of rigid spaces: a map on points, inverse images of
admissible opens, compatible pullback maps on sections, and local maps on stalks. -/
structure AnalyticMorphismData (X Y : RigidSpace K) where
  base : Point X → Point Y
  preimage : AdmissibleOpen Y → AdmissibleOpen X
  mem_preimage : ∀ x U, x ∈ AdmissibleOpen.carrier (preimage U) ↔ base x ∈ AdmissibleOpen.carrier U
  preimage_mono : ∀ {U V}, AdmissibleOpen.carrier U ⊆ AdmissibleOpen.carrier V →
    AdmissibleOpen.carrier (preimage U) ⊆ AdmissibleOpen.carrier (preimage V)
  pullback : ∀ U, StructureSheaf.Sections U →ₐ[K] StructureSheaf.Sections (preimage U)
  pullback_restriction : ∀ {U V} (hUV : AdmissibleOpen.carrier U ⊆ AdmissibleOpen.carrier V),
    (StructureSheaf.restriction (preimage_mono hUV)).comp (pullback V) =
      (pullback U).comp (StructureSheaf.restriction hUV)
  stalkMap : ∀ x, StructureSheaf.Stalk Y (base x) →ₐ[K] StructureSheaf.Stalk X x
  stalkMap_isLocal : ∀ x, IsLocalHom (stalkMap x)
  pullback_germ : ∀ (x) (U) (hx : base x ∈ AdmissibleOpen.carrier U)
      (s : StructureSheaf.Sections U),
    stalkMap x (StructureSheaf.germ hx s) =
      StructureSheaf.germ ((mem_preimage x U).2 hx) (pullback U s)

namespace AnalyticMorphismData

/-- Identity analytic-morphism data. -/
def id (X : RigidSpace K) : RigidSpace.AnalyticMorphismData X X where
  base x := x
  preimage U := U
  mem_preimage _ _ := Iff.rfl
  preimage_mono h := h
  pullback U := AlgHom.id K (StructureSheaf.Sections U)
  pullback_restriction := by
    intros
    rw [AlgHom.comp_id, AlgHom.id_comp]
  stalkMap x := AlgHom.id K (StructureSheaf.Stalk _ x)
  stalkMap_isLocal _ := ⟨fun _ h ↦ by simpa only [AlgHom.id_apply] using h⟩
  pullback_germ := by
    intro x U hx s
    rfl

/-- Composition of analytic-morphism data. -/
def comp {X Y Z : RigidSpace K} (f : RigidSpace.AnalyticMorphismData X Y)
    (g : RigidSpace.AnalyticMorphismData Y Z) : RigidSpace.AnalyticMorphismData X Z where
  base x := g.base (f.base x)
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
    refine ⟨fun a ha ↦ ?_⟩
    exact (g.stalkMap_isLocal (f.base x)).map_nonunit a
      ((f.stalkMap_isLocal x).map_nonunit _ ha)
  pullback_germ := by
    intro x U hx s
    simp only [AlgHom.comp_apply]
    rw [g.pullback_germ, f.pullback_germ]

end AnalyticMorphismData

instance rigidSpaceCategory : Category.{u + 1} (RigidSpace K) where
  Hom X Y := RigidSpace.AnalyticMorphismData X Y
  id X := RigidSpace.AnalyticMorphismData.id X
  comp f g := RigidSpace.AnalyticMorphismData.comp f g
  id_comp := by intro X Y f; cases f; rfl
  comp_id := by intro X Y f; cases f; rfl
  assoc := by intro W X Y Z f g h; cases f; cases g; cases h; rfl

namespace Point

/-- The map on analytic points induced by a rigid-space morphism. -/
def map {X Y : RigidSpace K} (f : X ⟶ Y) : Point X → Point Y :=
  f.base

@[simp]
theorem map_id (X : RigidSpace K) : map (K := K) (𝟙 X) = id := by
  rfl

@[simp]
theorem map_comp {X Y Z : RigidSpace K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (K := K) (f ≫ g) = map (K := K) g ∘ map (K := K) f := by
  rfl

end Point

/-- The functor assigning to a rigid space its type of analytic points. -/
def pointFunctor : RigidSpace K ⥤ Type (u + 1) where
  obj X := Point X
  map f := TypeCat.ofHom (Point.map (K := K) f)
  map_id X := by
    apply TypeCat.homEquiv.injective
    exact Point.map_id (K := K) X
  map_comp f g := by
    apply TypeCat.homEquiv.injective
    exact Point.map_comp (K := K) f g

/-- An affinoid domain in a rigid space. -/
def AffinoidDomain (X : RigidSpace K) : Type (u + 1) := ULift.{u + 1, u} X.DomainCode

namespace AffinoidDomain

/-- The admissible open underlying an affinoid domain. -/
def toAdmissibleOpen {X : RigidSpace K} (U : AffinoidDomain X) : AdmissibleOpen X :=
  ULift.up (X.domainOpen U.down)

/-- The points belonging to an affinoid domain. -/
def carrier {X : RigidSpace K} (U : AffinoidDomain X) : Set (Point X) :=
  AdmissibleOpen.carrier U.toAdmissibleOpen

/-- The point set of an affinoid domain agrees with that of its underlying admissible open. -/
@[simp]
theorem carrier_toAdmissibleOpen {X : RigidSpace K} (U : AffinoidDomain X) :
    AdmissibleOpen.carrier U.toAdmissibleOpen = U.carrier := rfl

/-- The coordinate algebra chosen by an affinoid domain. -/
def model {X : RigidSpace K} (U : AffinoidDomain X) : AffinoidAlgebraModel K :=
  X.domainModel U.down

/-- Two affinoid domains meet when their point sets intersect. -/
def Meets {X : RigidSpace K} (U V : AffinoidDomain X) : Prop :=
  (U.carrier ∩ V.carrier).Nonempty

end AffinoidDomain

/-- A family of affinoid domains is an admissible cover. -/
def IsAdmissibleAffinoidCover {X : RigidSpace K} {ι : Type u}
    (U : ι → AffinoidDomain X) : Prop :=
  AdmissibleOpen.IsCover (fun i ↦ (U i).toAdmissibleOpen) (AdmissibleOpen.top X)

/-- Affinoid admissible covers are precisely admissible-open covers of the full space. -/
theorem isAdmissibleAffinoidCover_iff {X : RigidSpace K} {ι : Type u}
    (U : ι → AffinoidDomain X) :
    IsAdmissibleAffinoidCover U ↔
      AdmissibleOpen.IsCover (fun i ↦ (U i).toAdmissibleOpen) (AdmissibleOpen.top X) := Iff.rfl

/-- An admissible affinoid cover of a rigid space. -/
structure AffinoidCover (X : RigidSpace K) : Type (u + 1) where
  /-- The indexing type of the cover. -/
  index : Type u
  /-- The affinoid domain at an index. -/
  domain : index → AffinoidDomain X
  /-- The domains form an admissible cover. -/
  isAdmissible : IsAdmissibleAffinoidCover domain

namespace AffinoidCover

/-- Every point lies in some member of an admissible affinoid cover. -/
theorem exists_mem_carrier {X : RigidSpace K} (𝒰 : AffinoidCover X) (x : Point X) :
    ∃ i, x ∈ (𝒰.domain i).carrier := by
  have hx : x ∈ AdmissibleOpen.carrier (AdmissibleOpen.top X) := by
    rw [AdmissibleOpen.carrier_top]
    simp
  rw [AdmissibleOpen.IsCover.iUnion_carrier 𝒰.isAdmissible] at hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
  exact ⟨i, hi⟩

/-- A cover is of finite type when every member meets only finitely many other members. -/
def IsFiniteType {X : RigidSpace K} (𝒰 : AffinoidCover X) : Prop :=
  ∀ i, Set.Finite {j : 𝒰.index | AffinoidDomain.Meets (𝒰.domain i) (𝒰.domain j)}

end AffinoidCover

/-- The stored local affinoid atlas of a rigid space. -/
def atlas (X : RigidSpace K) : AffinoidCover X where
  index := X.AtlasIndex
  domain i := ULift.up (X.atlasDomain i)
  isAdmissible := X.atlasIsCover

/-- Every point has an admissible affinoid neighborhood. -/
def IsLocallyAffinoid (X : RigidSpace K) : Prop :=
  ∀ x : Point X, ∃ U : AffinoidDomain X, x ∈ U.carrier

/-- Intersections of quasi-compact admissible opens are quasi-compact. -/
def IsQuasiSeparated (X : RigidSpace K) : Prop :=
  ∀ U V : AffinoidDomain X,
    AdmissibleOpen.IsQuasiCompact (AdmissibleOpen.inter U.toAdmissibleOpen V.toAdmissibleOpen)

/-- The rigid space has an admissible affinoid cover of finite type. -/
def HasAffinoidCoverOfFiniteType (X : RigidSpace K) : Prop :=
  ∃ 𝒰 : AffinoidCover X, 𝒰.IsFiniteType

/-- Compatibility name for the rigid-side finiteness condition in the comparison theorem. -/
abbrev IsParacompact (X : RigidSpace K) : Prop := HasAffinoidCoverOfFiniteType X

/-- The stored affinoid atlas witnesses local affinoidness. -/
theorem isLocallyAffinoid (X : RigidSpace K) : IsLocallyAffinoid X := by
  intro x
  rcases AffinoidCover.exists_mem_carrier (atlas X) x with ⟨i, hi⟩
  exact ⟨(atlas X).domain i, hi⟩

/-- Local affinoidness is characterized by affinoid domains through every point. -/
theorem isLocallyAffinoid_iff (X : RigidSpace K) :
    IsLocallyAffinoid X ↔ ∀ x : Point X, ∃ U : AffinoidDomain X, x ∈ U.carrier := Iff.rfl

/-- Quasi-separatedness is characterized by quasi-compact intersections of affinoid domains. -/
theorem isQuasiSeparated_iff (X : RigidSpace K) :
    IsQuasiSeparated X ↔ ∀ U V : AffinoidDomain X,
      AdmissibleOpen.IsQuasiCompact (AdmissibleOpen.inter U.toAdmissibleOpen V.toAdmissibleOpen) :=
  Iff.rfl

/-- The comparison finiteness condition is witnessed by an affinoid cover of finite type. -/
theorem isParacompact_iff (X : RigidSpace K) :
    IsParacompact X ↔ ∃ 𝒰 : AffinoidCover X, 𝒰.IsFiniteType := Iff.rfl

end RigidSpace

end Rigid
