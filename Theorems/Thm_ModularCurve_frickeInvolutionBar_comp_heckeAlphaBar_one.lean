module

public import Mathlib
public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Util
import P2M.Sol.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one

@[expose] public section

set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.frickeInvolutionBar_comp_heckeAlphaBar_one (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      = heckeBetaBar (AlgebraicClosure ℚ) 1 q := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one.solution
