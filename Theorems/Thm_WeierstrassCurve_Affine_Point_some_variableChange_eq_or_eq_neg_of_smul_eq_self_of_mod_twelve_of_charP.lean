import Mathlib
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP
    {F : Type*} [Field F] [DecidableEq F] (p : ℕ) [Fact p.Prime] [CharP F p] (W : WeierstrassCurve F) [W.IsElliptic]
    (C : WeierstrassCurve.VariableChange F) (hC : C • W = W)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11)
    {x y : F} (h : W.toAffine.Nonsingular x y)
    (hℓP : ℓ • WeierstrassCurve.Affine.Point.some x y h = 0)
    (h' : W.toAffine.Nonsingular (((C.u⁻¹ : Fˣ) : F) ^ 2 * (x - C.r)) (((C.u⁻¹ : Fˣ) : F) ^ 3 * (y - C.s * (x - C.r) - C.t)))
    (n : ℤ) (hn : WeierstrassCurve.Affine.Point.some _ _ h' = n • WeierstrassCurve.Affine.Point.some x y h) :
    WeierstrassCurve.Affine.Point.some _ _ h' = WeierstrassCurve.Affine.Point.some x y h ∨
      WeierstrassCurve.Affine.Point.some _ _ h' = -WeierstrassCurve.Affine.Point.some x y h := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_Point_some_variableChange_eq_or_eq_neg_of_smul_eq_self_of_mod_twelve_of_charP.solution
