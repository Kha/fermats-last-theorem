import Definitions.Def_IharaGamma0Fin
import P2M.Util
import P2M.Sol.S_Ihara_gamma0Fin_hom_factor

theorem Ihara.gamma0Fin_hom_factor {N M : ℕ} [NeZero M] (hNM : N ∣ M) {A : Type*} [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (Φ : Ihara.Gamma0Fin N M →* Multiplicative A) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Φ = χ.comp (Ihara.gamma0FinUnitsChar N M hNM) := by p2m_exact_reverting @_root_.P2MW.S_Ihara_gamma0Fin_hom_factor.solution
