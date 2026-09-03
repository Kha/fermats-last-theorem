import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.Finiteness.Defs
import P2M.Util
import P2M.Sol.S_LevelRaising_moduleFinite_parabolicHoms_int

set_option autoImplicit false
theorem LevelRaising.moduleFinite_parabolicHoms_int (M : ℕ) [NeZero M] :
    Module.Finite ℤ (ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 M) ℤ) := by p2m_exact_reverting @_root_.P2MW.S_LevelRaising_moduleFinite_parabolicHoms_int.solution
