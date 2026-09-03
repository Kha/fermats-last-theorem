import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isClosed_singleton_base_of_isClosed_singleton_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    {x : X} (hx : IsClosed ({x} : Set X)) (hs : IsClosed ({(f ≫ g).base x} : Set S)) :
    IsClosed ({f.base x} : Set Y) := by
  set s := (f ≫ g).base x with hsdef
  haveI : IsClosedImmersion (X.fromSpecResidueField x) := isClosed_singleton_iff_isClosedImmersion.mp hx

  have hcompat : (X.fromSpecResidueField x ≫ f) ≫ g =
      Spec.map ((f ≫ g).residueFieldMap x) ≫ S.fromSpecResidueField s := by
    rw [Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let φ : Spec (X.residueField x) ⟶ g.fiber s :=
    pullback.lift (X.fromSpecResidueField x ≫ f) (Spec.map ((f ≫ g).residueFieldMap x)) hcompat
  have hφ : φ ≫ g.fiberι s = X.fromSpecResidueField x ≫ f := pullback.lift_fst _ _ _

  haveI : LocallyOfFiniteType (φ ≫ g.fiberι s) := by rw [hφ]; infer_instance
  haveI : LocallyOfFiniteType φ := locallyOfFiniteType_of_comp φ (g.fiberι s)
  haveI : IsFinite φ := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := φ)).mpr inferInstance

  have hcl : IsClosed (Set.range φ.base) := φ.isClosedMap.isClosed_range
  have hemb : Topology.IsClosedEmbedding (g.fiberι s).base := by
    refine ⟨(g.fiberι s).isEmbedding, ?_⟩
    rw [Scheme.Hom.range_fiberι]
    exact hs.preimage g.continuous
  have himg : IsClosed ((g.fiberι s).base '' Set.range φ.base) := hemb.isClosedMap _ hcl
  have hset : (g.fiberι s).base '' Set.range φ.base = {f.base x} := by
    rw [← Set.range_comp]
    have : (g.fiberι s).base ∘ φ.base = (X.fromSpecResidueField x ≫ f).base := by
      ext z
      change (φ ≫ g.fiberι s).base z = _
      rw [hφ]
    rw [this, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.range_fromSpecResidueField,
      Set.image_singleton]
  rwa [hset] at himg
