import Mathlib
import Definitions.Def_WeierstrassCurve_Velu
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_map_veluQuotient_image
open WeierstrassCurve
theorem WeierstrassCurve.map_veluQuotient_image
    {R R' : Type*} [CommRing R] [CommRing R'] [DecidableEq R'] (W : WeierstrassCurve R)
    (f : R →+* R') (S : Finset (R × R))
    (hinj : (S.image (Prod.map f f)).card = S.card) :
    (W.map f).veluQuotient (S.image (Prod.map f f)) = (W.veluQuotient S).map f := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_map_veluQuotient_image.solution
