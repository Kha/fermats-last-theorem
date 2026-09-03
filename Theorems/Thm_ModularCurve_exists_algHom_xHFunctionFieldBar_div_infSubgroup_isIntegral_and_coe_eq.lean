import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq

set_option autoImplicit false

p2m_open "ModularCurve~GammaH_le_GammaH_div_infSubgroup~finiteAlong_laurentBaseChange_qExpFunctionFieldC"

theorem ModularCurve.exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)] :
    ∃ (αH : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)),
      αH.toRingHom.IsIntegral ∧
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((αH u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_algHom_xHFunctionFieldBar_div_infSubgroup_isIntegral_and_coe_eq.solution
