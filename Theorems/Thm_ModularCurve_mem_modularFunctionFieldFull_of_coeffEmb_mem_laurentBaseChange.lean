import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange

theorem ModularCurve.mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange (N : ℕ) [NeZero N]
    (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb ℂ x ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.modularFunctionFieldFull N)) :
    x ∈ ModularCurve.modularFunctionFieldFull N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_modularFunctionFieldFull_of_coeffEmb_mem_laurentBaseChange.solution
