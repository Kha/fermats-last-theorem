import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_projModelStrCR_isProper

theorem WeierstrassProjModel.projModelStrCR_isProper {R : Type*} [CommRing R]
    (V : WeierstrassCurve.Projective R) :
    AlgebraicGeometry.IsProper (WeierstrassProjModel.projModelStrCR V) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_projModelStrCR_isProper.solution
