import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_ModularCurve_LevelRelabelling
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal

theorem WeierstrassCurve.DrinfeldGlobal.IsDrinfeldBasis.zlinComb_zlinComb_of_isUnit_det
    {T : Type u} [CommRing T] {W : WeierstrassCurve.Projective T}
    (G : RelativeGroupLaw T (projModelStrCR W))
    (hcomm : ∀ x y : Section W, G.mul _ x y = G.mul _ y x)
    (q : ℕ) (P Q : Section W) (h : IsDrinfeldBasis G q P Q)
    (g : Matrix (Fin 2) (Fin 2) ℤ) (hg : IsUnit ((g.det : ℤ) : ZMod q)) :
    IsDrinfeldBasis G q
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 0) (g 1 0))
      (ModularCurve.LevelRelabelling.zlinComb G P Q (g 0 1) (g 1 1)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_DrinfeldGlobal_IsDrinfeldBasis_zlinComb_zlinComb_of_isUnit_det.solution
