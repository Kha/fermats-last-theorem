module

public import Mathlib
public import Definitions.Def_ModularCurve_TateOrigin
public import P2M.Util
public import P2M.Sol.S_ModularCurve_one_add_single_mul_derivative_tateOriginX

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
open ModularCurve in

theorem ModularCurve.one_add_single_mul_derivative_tateOriginX (K : Type*) [CommRing K] :
    (1 + HahnSeries.single (1 : ℤ) (1 : PowerSeries K)) * LaurentSeries.derivative (PowerSeries K) (tateOriginX K)
      = 2 * tateOriginY K + tateOriginX K := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_one_add_single_mul_derivative_tateOriginX.solution
