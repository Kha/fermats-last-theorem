import Definitions.Def_WeierstrassCurve_VariableChangeSeries
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
attribute [-instance] WeierstrassCurve.instIsCommFormalGroup
attribute [-simp] WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero

set_option autoImplicit false

theorem WeierstrassCurve.coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed
    {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) :
    PowerSeries.coeff 1 (W.variableChangeSeries C) = (C.u : R) ∧
      PowerSeries.subst W.formalGroupLawFixed (W.variableChangeSeries C) =
        MvPowerSeries.subst
          ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) (W.variableChangeSeries C),
            PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) (W.variableChangeSeries C)]
          (C • W).formalGroupLawFixed := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_coeff_one_variableChangeSeries_and_subst_formalGroupLawFixed.solution
