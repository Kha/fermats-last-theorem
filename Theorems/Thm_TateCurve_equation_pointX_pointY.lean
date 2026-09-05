module

public import Definitions.Def_TateCurve_Defect
import P2M.Util
import P2M.Sol.S_TateCurve_equation_pointX_pointY

@[expose] public section

open TateCurve
open scoped NNReal
theorem TateCurve.equation_pointX_pointY {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u ^ 2 + pointX q u * pointY q u = pointX q u ^ 3 + a₄ q * pointX q u + a₆ q := by p2m_exact_reverting @_root_.P2MW.S_TateCurve_equation_pointX_pointY.solution
