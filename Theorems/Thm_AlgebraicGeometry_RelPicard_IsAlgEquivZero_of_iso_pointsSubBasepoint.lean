import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointsSubBasepoint
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))
    {L : A.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) :
    IsAlgEquivZero a L := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint.solution
