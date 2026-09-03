import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_c4_tateLaurent
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve
open PowerSeries HahnSeries in

theorem ModularCurve.c4_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_c4_tateLaurent.solution
