module

public import Mathlib
public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul

@[expose] public section

set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.restrictAlong_heckeBetaBar_frickeInvolutionBar_smul (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
      = W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul.solution
