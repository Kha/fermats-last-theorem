import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_FreyPackage
import Mathlib.Algebra.Module.Torsion.Basic
import P2M.Util
import P2M.Sol.S_FreyCurve_card_two_torsion_reductionMod

open WeierstrassCurve
namespace FreyCurve
theorem card_two_torsion_reductionMod (P : FreyPackage) {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    (hgood : (FreyPackage.freyCurveInt P).IsGoodPrimeFor q) :
    Nat.card (Submodule.torsionBy ℤ ((FreyPackage.freyCurveInt P).reductionMod q).toAffine.Point 2) = 4 := by p2m_exact_reverting @_root_.P2MW.S_FreyCurve_card_two_torsion_reductionMod.solution
end FreyCurve
