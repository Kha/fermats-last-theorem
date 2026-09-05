module

public import Definitions.Def_ModularCurve_ModularUnit
import P2M.Util
import P2M.Sol.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull

@[expose] public section

theorem ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull (N : ℕ) [NeZero N] : ModularCurve.modularUnitSeries N ∈ ModularCurve.modularFunctionFieldFull N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull.solution
