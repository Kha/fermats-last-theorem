import Definitions.Def_WeierstrassCurve_VeluQuotientOfSums
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_map_veluQuotientOfSums

set_option autoImplicit false
theorem WeierstrassCurve.map_veluQuotientOfSums
    {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type*} [CommRing R'] (f : R →+* R') (t w : R) :
    (W.veluQuotientOfSums t w).map f = (W.map f).veluQuotientOfSums (f t) (f w) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_map_veluQuotientOfSums.solution
