import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Complex.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange

theorem ModularCurve.mem_of_coeffEmb_mem_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (x : LaurentSeries ℚ)
    (hx : ModularCurve.coeffEmb L x ∈ ModularCurve.laurentBaseChange L F₀) : x ∈ F₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_mem_of_coeffEmb_mem_laurentBaseChange.solution
