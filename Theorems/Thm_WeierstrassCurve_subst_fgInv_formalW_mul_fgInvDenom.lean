import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_subst_fgInv_formalW_mul_fgInvDenom

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.subst_fgInv_formalW_mul_fgInvDenom
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    PowerSeries.subst W.fgInv W.formalW * W.fgInvDenom = -W.formalW := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_subst_fgInv_formalW_mul_fgInvDenom.solution
