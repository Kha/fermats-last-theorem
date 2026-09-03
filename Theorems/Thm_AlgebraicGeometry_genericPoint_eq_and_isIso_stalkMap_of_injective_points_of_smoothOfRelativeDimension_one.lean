import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra

theorem AlgebraicGeometry.genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one
    {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    {Y X : Scheme.{0}} (gY : Y ⟶ Spec (CommRingCat.of K)) (gX : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral Y] [IsIntegral X] [IsSeparated gY] [IsSeparated gX]
    (hY : SmoothOfRelativeDimension 1 gY) (hX : SmoothOfRelativeDimension 1 gX)
    (h : Y ⟶ X) (hh : h ≫ gX = gY)
    (hinj : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
      (P P' : SchemeHomOver s gY), P.1 ≫ h = P'.1 ≫ h → P = P') :
    h.base (genericPoint Y) = genericPoint X ∧ IsIso (h.stalkMap (genericPoint Y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_genericPoint_eq_and_isIso_stalkMap_of_injective_points_of_smoothOfRelativeDimension_one.solution
