import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_Ihara_exists_coprime_forall_mem_Gamma_apply_eq_zero
attribute [-instance] Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway
attribute [-simp] Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply

open scoped MatrixGroups

theorem Ihara.exists_coprime_forall_mem_Gamma_apply_eq_zero (N q : ℕ) (hq : q.Prime)
    (hqN : ¬ q ∣ N) (A : Type*) [AddCommGroup A]
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q),
      φ (Additive.ofMul (ι₀ N q γ)) + ψ (Additive.ofMul (ι₁ N q γ)) = 0) :
    ∃ M : ℕ, 0 < M ∧ Nat.Coprime M q ∧
      ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M →
        φ (Additive.ofMul γ) = 0 ∧ ψ (Additive.ofMul γ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_Ihara_exists_coprime_forall_mem_Gamma_apply_eq_zero.solution
