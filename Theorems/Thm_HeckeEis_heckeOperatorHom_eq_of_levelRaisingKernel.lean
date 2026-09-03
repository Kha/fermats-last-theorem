import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel
attribute [-instance] Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway
attribute [-simp] Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply

theorem HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : Type*) [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) = 0)
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ ∧ HeckeEis.heckeOperatorHom N ℓ A ψ = (ℓ + 1) • ψ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel.solution
