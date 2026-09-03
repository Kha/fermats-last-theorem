import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one
    (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (A : Type*) [AddCommGroup A]
    (φ : CohCarrier.H1 N H A) (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓ1 : ℓ ≡ 1 [MOD N]) :
    CohCarrier.heckeT N H ℓ A φ - (ℓ + 1) • φ ∈
      ModularCurve.Period.parabolicHoms ℤ (CohCarrier.GammaH N H) A := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_sub_smul_mem_parabolicHoms_gammaH_of_modEq_one.solution
