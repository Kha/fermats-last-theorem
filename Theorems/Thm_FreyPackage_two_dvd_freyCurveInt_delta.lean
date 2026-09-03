import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyPackage_two_dvd_freyCurveInt_delta

open WeierstrassCurve
theorem FreyPackage.two_dvd_freyCurveInt_delta (P : FreyPackage) :
    (2 : ℤ) ∣ (FreyPackage.freyCurveInt P).Δ := by p2m_exact_reverting @_root_.P2MW.S_FreyPackage_two_dvd_freyCurveInt_delta.solution
