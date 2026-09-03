import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_npow_of_variableChange
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup
attribute [-simp] FormalGroup.LawIso.mk.sizeOf_spec FormalGroup.LawHom.mk.sizeOf_spec FormalGroup.LawHom.mk.injEq FormalGroup.LawIso.mk.injEq FormalGroup.DrinfeldLevel.mk.sizeOf_spec FormalGroup.DrinfeldLevel.mk.injEq WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

open FormalGroup

theorem WeierstrassCurve.exists_isUnit_nthSeries_eq_mul_X_npow_of_variableChange
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (q n : ℕ)
    (F F' : FormalGroup R) (hF : F.toPowerSeries = W.formalGroupLawFixed)
    (hF' : F'.toPowerSeries = (C • W).formalGroupLawFixed)
    (h : ∃ u : PowerSeries R, IsUnit u ∧ F.nthSeries q = u * PowerSeries.X ^ n) :
    ∃ u : PowerSeries R, IsUnit u ∧ F'.nthSeries q = u * PowerSeries.X ^ n := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_isUnit_nthSeries_eq_mul_X_npow_of_variableChange.solution
