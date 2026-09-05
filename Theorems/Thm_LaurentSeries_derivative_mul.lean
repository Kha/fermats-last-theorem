module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_LaurentSeries_derivative_mul

@[expose] public section
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.derivative_mul {R : Type*} [CommRing R] (f g : LaurentSeries R) :
    LaurentSeries.derivative R (f * g) =
      LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_derivative_mul.solution
