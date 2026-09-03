import Definitions.Def_IharaIota
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap
import P2M.Util
import P2M.Sol.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
attribute [-instance] Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway Ihara.instGroupIharaAmalgam
attribute [-simp] Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.gamma0UnitsHom_coe Ihara.gamma0UnitsChar_apply Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply

set_option autoImplicit false

theorem Ihara.heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
    (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hψ : ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q),
      (3 : ℤ) ∣ φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ))
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q) :
    (∃ φ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = (3 : ℤ) • φ') ∧
    (∃ ψ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ ψ - ((ℓ : ℤ) + 1) • ψ = (3 : ℤ) • ψ') := by p2m_exact_reverting @_root_.P2MW.S_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.solution
