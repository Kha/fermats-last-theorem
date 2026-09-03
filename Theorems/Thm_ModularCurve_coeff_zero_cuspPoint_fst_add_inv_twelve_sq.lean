import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_zero_cuspPoint_fst_add_inv_twelve_sq

set_option autoImplicit false

theorem ModularCurve.coeff_zero_cuspPoint_fst_add_inv_twelve_sq
    (L : Type) [Field L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) :
    (((ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2).coeff 0 =
      if v 1 = 0 then (((ξ ^ (v 0).val : Lˣ) : L) * ((1 - ((ξ ^ (v 0).val : Lˣ) : L))⁻¹) ^ 2 + (12 : L)⁻¹) ^ 2
      else ((12 : L)⁻¹) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_zero_cuspPoint_fst_add_inv_twelve_sq.solution
