import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero
attribute [-instance] CohCarrier.GammaHLower_finiteIndex
attribute [-simp] CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero
    (N : ℕ) (A : Type*) [AddCommGroup A] (φ : CohCarrier.H1 N ⊤ A)
    (hφ : ∃ M : ℕ, 0 < M ∧ ∀ γ : ↥(CohCarrier.GammaH N ⊤),
      (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M → φ (Additive.ofMul γ) = 0)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    CohCarrier.heckeT N ⊤ ℓ A φ = (ℓ + 1) • φ := by p2m_exact_reverting @_root_.P2MW.S_CohCarrier_heckeT_eq_smul_of_forall_mem_Gamma_apply_eq_zero.solution
