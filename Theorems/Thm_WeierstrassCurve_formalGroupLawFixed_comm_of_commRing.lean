import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup

set_option autoImplicit false

theorem WeierstrassCurve.formalGroupLawFixed_comm_of_commRing
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.formalGroupLawFixed =
      MvPowerSeries.subst ![MvPowerSeries.X 1, MvPowerSeries.X 0] W.formalGroupLawFixed := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_formalGroupLawFixed_comm_of_commRing.solution
