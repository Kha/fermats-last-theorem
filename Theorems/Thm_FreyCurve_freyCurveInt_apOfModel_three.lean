import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyCurve_freyCurveInt_apOfModel_three

open WeierstrassCurve FreyPackage
namespace FreyCurve
theorem freyCurveInt_apOfModel_three (P : FreyPackage)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor 3) :
    (FreyPackage.freyCurveInt P).apOfModel 3 = 0 := by p2m_exact_reverting @_root_.P2MW.S_FreyCurve_freyCurveInt_apOfModel_three.solution
end FreyCurve
