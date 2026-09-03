import Definitions.Def_WeierstrassCurve_VeluQuotientMap
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isElliptic_map_veluQuotient_j

theorem WeierstrassCurve.exists_isElliptic_map_veluQuotient_j {R R' : Type*} [Field R] [Field R']
    [DecidableEq R'] (W : WeierstrassCurve R) (f : R →+* R') (S : Finset (R × R))
    (hQ : (W.veluQuotient S).IsElliptic) :
    ∃ hQ' : ((W.map f).veluQuotient (S.image (Prod.map f f))).IsElliptic,
      @WeierstrassCurve.j R' _ ((W.map f).veluQuotient (S.image (Prod.map f f))) hQ' =
        f (@WeierstrassCurve.j R _ (W.veluQuotient S) hQ) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isElliptic_map_veluQuotient_j.solution
