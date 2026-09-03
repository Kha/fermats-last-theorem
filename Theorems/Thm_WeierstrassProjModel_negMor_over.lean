import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_negMor_over

open CategoryTheory AlgebraicGeometry NeronModelInfra WeierstrassProjModel

theorem WeierstrassProjModel.negMor_over {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) :
    kw_lrAddNegDiag_negMor W ≫ projModelStrCR W.toProjective
      = projModelStrCR W.toProjective := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_negMor_over.solution
