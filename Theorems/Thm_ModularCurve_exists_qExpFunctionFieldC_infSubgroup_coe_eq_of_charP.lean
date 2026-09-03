import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP
attribute [-simp] ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]

    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (K : Type) [Field K] [CharP K p] :
    ∀ g : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H),
      ∃ g' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)),
        (g' : LaurentSeries K) = (g : LaurentSeries K) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_qExpFunctionFieldC_infSubgroup_coe_eq_of_charP.solution
