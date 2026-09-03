import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_pairHt_comm

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem AlgebraicCurve.pairHt_comm {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    pairHt s v w = pairHt s w v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_pairHt_comm.solution
