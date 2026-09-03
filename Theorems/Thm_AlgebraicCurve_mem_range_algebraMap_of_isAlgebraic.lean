import Mathlib.FieldTheory.IsAlgClosed.Basic
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic

theorem AlgebraicCurve.mem_range_algebraMap_of_isAlgebraic {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] {x : L} (hx : IsAlgebraic K x) :
    x ∈ (algebraMap K L).range := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_mem_range_algebraMap_of_isAlgebraic.solution
