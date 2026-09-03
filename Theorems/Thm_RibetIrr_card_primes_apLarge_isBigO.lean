import Definitions.Def_FLTPrelim_Modularity
import P2M.Util
import P2M.Sol.S_RibetIrr_card_primes_apLarge_isBigO

theorem RibetIrr.card_primes_apLarge_isBigO
    (M : ℕ) [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ∃ K : ℕ, ∀ X : ℕ,
      ((Finset.Ioc (X / 3) X).filter
        fun ℓ : ℕ => ℓ.Prime ∧ (ℓ : ℝ) - 1 ≤ ‖ModularFormClass.qCoeff g ℓ‖).card ≤ K := by p2m_exact_reverting @_root_.P2MW.S_RibetIrr_card_primes_apLarge_isBigO.solution
