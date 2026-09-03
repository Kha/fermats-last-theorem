import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointSubBasepoint

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointSubBasepoint
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a] [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {L : A.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointSubBasepointModule (a := a) P ε) :
    IsAlgEquivZero a L := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointSubBasepoint.solution
