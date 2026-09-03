import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP
attribute [-simp] ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply

set_option autoImplicit false
open scoped MatrixGroups

theorem ModularCurve.qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP
    (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) =
      ModularCurve.qExpFunctionFieldC K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓
          CongruenceSubgroup.Gamma0 (M / p * ℓ)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpFunctionFieldC_gammaH_inf_gamma0_mul_eq_infSubgroup_inf_gamma0_mul_of_charP.solution
