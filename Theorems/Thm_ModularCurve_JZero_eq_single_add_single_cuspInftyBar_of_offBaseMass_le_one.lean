import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import P2M.Util
import P2M.Sol.S_ModularCurve_JZero_eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v)
    (hm : offBaseMass N D ≤ 1) :
    D = Finsupp.single (cuspInftyBar N) (D (cuspInftyBar N)) ∨
      ∃ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N ∧
        D = Finsupp.single v 1 + Finsupp.single (cuspInftyBar N) (D (cuspInftyBar N)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JZero_eq_single_add_single_cuspInftyBar_of_offBaseMass_le_one.solution
