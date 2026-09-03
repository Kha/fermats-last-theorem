import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_projModelStrCR_smooth

theorem WeierstrassProjModel.projModelStrCR_smooth {R : Type} [CommRing R]
    (V : WeierstrassCurve.Projective R) [V.IsElliptic] :
    AlgebraicGeometry.Smooth (WeierstrassProjModel.projModelStrCR V) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_projModelStrCR_smooth.solution
