import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one

set_option autoImplicit false

theorem ModularCurve.coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one
    {K : Type} [CommRing K] (p : ℕ) (c ζ : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) :
    PowerSeries.coeff n (ModularCurve.slotSubst K p (ζ * c) j ModularCurve.tateUnivX) -
        PowerSeries.coeff n (ModularCurve.slotSubst K p c j ModularCurve.tateUnivX) ∈
      Ideal.span {((ζ : K) - 1)} := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_slotSubst_tateUnivX_mul_sub_coeff_mem_span_sub_one.solution
