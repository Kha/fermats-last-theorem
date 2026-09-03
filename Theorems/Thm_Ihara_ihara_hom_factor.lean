import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_Ihara_ihara_hom_factor
attribute [-instance] Ihara.instGroupIharaAmalgam Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway
attribute [-simp] Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.zAwayToZMod_algebraMap Ihara.gamma0AwayUnitsChar_coe Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply

theorem Ihara.ihara_hom_factor (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : Type*) [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (ι₀ N q γ) + ψ (ι₁ N q γ) = 0) :
    (∃ χ : Additive (ZMod N)ˣ →+ A, φ = χ.comp (gamma0UnitsChar N)) ∧
    (∃ χ : Additive (ZMod N)ˣ →+ A, ψ = χ.comp (gamma0UnitsChar N)) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_ihara_hom_factor.solution
