module

public import Mathlib
public import Definitions.Def_WeierstrassCurve_HasseInvariant
public import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem WeierstrassCurve.hasseInvariant_tatePowerSeries_map
    (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) :
    WeierstrassCurve.hasseInvariant q (ModularCurve.tatePowerSeries.map (PowerSeries.map (Int.castRingHom (ZMod q)))) = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_hasseInvariant_tatePowerSeries_map.solution
