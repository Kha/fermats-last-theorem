import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_a2_sixu_cov

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.kw_a2_sixu_cov.{u} {R : Type u} [CommRing R]
    (W : WeierstrassCurve R) [W.IsElliptic] [Invertible (2 : R)] :
    KwLRSixUCoverage W := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_a2_sixu_cov.solution
