import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import P2M.Util
import P2M.Sol.S_FreyCurve_four_dvd_card_reductionMod

open WeierstrassCurve
namespace FreyCurve
theorem four_dvd_card_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    4 ∣ ((FreyPackage.freyCurveInt P).reductionMod q).card := by p2m_exact_reverting @_root_.P2MW.S_FreyCurve_four_dvd_card_reductionMod.solution
end FreyCurve
