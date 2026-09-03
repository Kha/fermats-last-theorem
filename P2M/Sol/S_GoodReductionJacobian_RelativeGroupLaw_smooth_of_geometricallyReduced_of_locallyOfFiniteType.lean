import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import P2M.Util
namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smooth_of_geometricallyReduced_of_locallyOfFiniteType

open AlgebraicGeometry CategoryTheory NeronModelInfra GoodReductionJacobian

universe u

theorem solution
    {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    [GeometricallyReduced f] [LocallyOfFiniteType f] (G : RelativeGroupLaw K f) :
    Smooth f := by
  letI := G.grpObjOverMk
  exact smooth_of_grpObj f
