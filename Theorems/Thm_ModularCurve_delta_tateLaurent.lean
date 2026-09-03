import Mathlib
import Definitions.Def_ModularCurve_TateFormal
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_delta_tateLaurent
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

p2m_open "ModularCurve~eisenstein4_cube_sub_mk_sq~c4_pow_three_tateLaurent"
open PowerSeries HahnSeries in

theorem ModularCurve.delta_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).Δ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_delta_tateLaurent.solution
