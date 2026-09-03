import Mathlib
import Definitions.Def_WeierstrassCurve_PeuRamifiee
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyPackage_p_dvd_padicValRat_freyCurve_discr
import P2M.Util
namespace P2MW.S_FreyCurve_isPeuRamifieeAt_odd_of_integralForm

set_option autoImplicit false

open FreyPackage

theorem solution (P : FreyPackage) {q : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) : P.freyCurve.IsPeuRamifieeAt P.p q :=
  FreyPackage.p_dvd_padicValRat_freyCurve_discr P Fact.out hq2
