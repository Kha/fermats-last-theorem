import Definitions.Def_Gamma0AwayUnitsChar
import P2M.Util
import P2M.Sol.S_Ihara_gamma0Away_hom_factor
attribute [-instance] Ihara.instNormalSpecialLinearGroupFinOfNatNatZAwayPrincipalCongruenceAway
attribute [-simp] Ihara.mennickeA_coe Ihara.mennickeU_coe Ihara.gamma0FinUnitsChar_coe Ihara.gamma0FinMap_apply

theorem Ihara.gamma0Away_hom_factor {N q : ℕ} (hq : q.Prime) (hqN : N.Coprime q)
    {A : Type*} [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (Ψ : Gamma0Away N q →* Multiplicative A) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Ψ = χ.comp (gamma0AwayUnitsChar N q hqN) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_gamma0Away_hom_factor.solution
