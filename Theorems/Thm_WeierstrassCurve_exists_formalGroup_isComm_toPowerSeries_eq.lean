import Mathlib
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup

set_option autoImplicit false

universe u

theorem WeierstrassCurve.exists_formalGroup_isComm_toPowerSeries_eq
    {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    ∃ (F : FormalGroup R) (_ : F.IsComm), F.toPowerSeries = W.formalGroupLawFixed := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_formalGroup_isComm_toPowerSeries_eq.solution
