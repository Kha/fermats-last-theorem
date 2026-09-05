module

public import Definitions.Def_ModularCurve_TateSlots
import P2M.Util
import P2M.Sol.S_ModularCurve_slotSubst_gen_injective

@[expose] public section

open ModularCurve
theorem ModularCurve.slotSubst_gen_injective : Function.Injective (slotSubst (LaurentSeries ℚ) 2
      (Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)) 1) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_slotSubst_gen_injective.solution
