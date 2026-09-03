import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite

set_option autoImplicit false

theorem AlgebraicCurve.card_effective_sub_isPrincipal_of_finite
    (k F : Type*) [Field k] [Finite k] [Field F] [Algebra k F]
    [AlgebraicCurve.IsCurveOver k F]
    (hC : AlgebraicCurve.ConstantsAreBase k F) (C : AlgebraicCurve.Divisor k F) :
    (Nat.card k - 1) *
        Nat.card {D : AlgebraicCurve.Divisor k F //
          0 ≤ D ∧ AlgebraicCurve.Divisor.IsPrincipal (D - C)} + 1 =
      Nat.card k ^ AlgebraicCurve.ell C := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_card_effective_sub_isPrincipal_of_finite.solution
