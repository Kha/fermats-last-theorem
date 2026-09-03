import Mathlib
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_CohCarrier_exists_squarefree_aeval_heckeTL_mem_parabolicHoms
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

theorem CohCarrier.exists_squarefree_aeval_heckeTL_mem_parabolicHoms
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ∃ p : Polynomial ℂ, Squarefree p ∧
      ∀ φ : CohCarrier.H1 M H ℂ,
        Polynomial.aeval (CohCarrier.heckeTL M H ℂ ℓ) p φ ∈ ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_exists_squarefree_aeval_heckeTL_mem_parabolicHoms.solution
