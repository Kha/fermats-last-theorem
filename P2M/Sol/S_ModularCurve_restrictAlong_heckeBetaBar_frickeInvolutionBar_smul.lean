module

public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
import P2M.Sol.S_AlgebraicCurve_Place_smul_restrictAlong
import P2M.Sol.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
import P2M.Util

namespace P2MW.S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

theorem solution (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
      = W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα := by
  rw [Place.smul_restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
      (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hβ hα (frickeInvolutionBar (1 * q)) 1
      (fun x => ?_) W, one_smul]
  rw [AlgEquiv.one_apply]
  exact (DFunLike.congr_fun (frickeInvolutionBar_comp_heckeAlphaBar_one q) x).symm
end S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
end P2MW

public section
set_option autoImplicit false

open AlgebraicCurve ModularCurve
theorem ModularCurve.restrictAlong_heckeBetaBar_frickeInvolutionBar_smul (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
      = W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul.solution
end
