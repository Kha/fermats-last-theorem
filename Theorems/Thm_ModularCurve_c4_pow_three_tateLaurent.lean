import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularCurve_c4_pow_three_tateLaurent

open PowerSeries HahnSeries ModularCurve
theorem ModularCurve.c4_pow_three_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ ^ 3 = jqModC K * (tateLaurent K).Δ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_c4_pow_three_tateLaurent.solution
