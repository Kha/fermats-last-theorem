import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_exists_mem_gamma0_redQ_inv_smul_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_mem_gamma0_redQ_inv_smul_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ ℓ' : CuspidalType.ProjLine q) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' ∧ (ModularCurve.FullLevel.redQ q γ)⁻¹ • ℓ = ℓ' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_exists_mem_gamma0_redQ_inv_smul_eq.solution
