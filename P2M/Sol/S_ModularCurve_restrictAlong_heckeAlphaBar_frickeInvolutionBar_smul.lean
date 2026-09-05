module

public import Mathlib
public import Definitions.Def_ModularCurve_HeckeOperator
public import Definitions.Def_ModularCurve_CuspidalClass
public import Definitions.Def_ModularCurve_AtkinLehnerPartial
public import Theorems.Thm_AlgebraicCurve_Place_smul_restrictAlong
public import Theorems.Thm_ModularCurve_frickeInvolutionBar_comp_heckeBetaBar_one
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

theorem solution (q : ℕ) [NeZero q]
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (frickeInvolutionBar (1 * q) • W).restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q) hα
      = W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ := by
  rw [Place.smul_restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hα hβ (frickeInvolutionBar (1 * q)) 1
      (fun x => ?_) W, one_smul]
  rw [AlgEquiv.one_apply]
  exact (DFunLike.congr_fun (frickeInvolutionBar_comp_heckeBetaBar_one q) x).symm
