import Mathlib
import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsTwoKernel_exists_addOrderOf_eq_two_and_eq_X_sub_C

set_option autoImplicit false

universe u

open Polynomial

theorem WeierstrassCurve.IsTwoKernel.exists_addOrderOf_eq_two_and_eq_X_sub_C
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) [W.IsElliptic]
    (h2 : (2 : Ω) ≠ 0) (h : Polynomial Ω) (hh : W.IsTwoKernel h) :
    ∃ Q : W.toAffine.Point, addOrderOf Q = 2 ∧ h = X - C (Q.coordsOrZero).1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsTwoKernel_exists_addOrderOf_eq_two_and_eq_X_sub_C.solution
