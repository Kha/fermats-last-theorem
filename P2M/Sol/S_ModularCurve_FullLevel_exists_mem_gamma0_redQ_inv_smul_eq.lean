import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd
import P2M.Util
namespace P2MW.S_ModularCurve_FullLevel_exists_mem_gamma0_redQ_inv_smul_eq

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ ℓ' : CuspidalType.ProjLine q) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' ∧ (ModularCurve.FullLevel.redQ q γ)⁻¹ • ℓ = ℓ' := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2, ZMod q)) ℓ' ℓ
  obtain ⟨γ, hγ, hγg⟩ := (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').1 g
  refine ⟨γ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1
  · rw [inv_smul_eq_iff, ← hg, ← hγg]
    rfl
