module

public import Mathlib
public import Definitions.Def_ModularCurve_TateOrigin
public import Definitions.Def_ModularCurve_TateFormal
import P2M.Util
import P2M.Sol.S_ModularCurve_tateOrigin_equation

@[expose] public section
attribute [-instance] ModularCurve.instIsElliptic_tateBase
attribute [-simp] ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.tateOrigin_equation (K : Type*) [CommRing K] :
    tateOriginY K ^ 2 + tateOriginX K * tateOriginY K
      = tateOriginX K ^ 3 + HahnSeries.C (PowerSeries.map (Int.castRingHom K) tateA4) * tateOriginX K
        + HahnSeries.C (PowerSeries.map (Int.castRingHom K) tateA6) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_tateOrigin_equation.solution
