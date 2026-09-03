import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_ModPFormFn
import P2M.Util
import P2M.Sol.S_ModularCurve_evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd
attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd
    {K : Type*} [Field K] [DecidableEq K] (N : ℕ) [NeZero N]
    (x : Place K ↥(modularFunctionFieldC K N)) (hx : x.IsRational) (m a : ℤ)
    (hu : 1 ≤ placeWidth N x)
    (ha : (placeWidth N x : ℤ) * a = m * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1))
    (π : ↥(modularFunctionFieldC K N)) (hπ : x.ord π = 1)
    (G : ↥(modularFunctionFieldC K N)) (hG0 : G ≠ 0) (hG : -a ≤ x.ord G) :
    x.evalAt (π ^ a * G) = 0 ↔ 1 ≤ stackOrd N m G x := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_evalAt_zpow_mul_eq_zero_iff_one_le_stackOrd.solution
