import Definitions.Def_ModularCurve_JZeroHeightForm
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_forall_neg_le_baseHt

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_forall_neg_le_baseHt {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    {r : ℕ} (s : Fin r → F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b v : Place (AlgebraicClosure ℚ) F, -C ≤ baseHt s b v := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_forall_neg_le_baseHt.solution
