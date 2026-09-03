import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_eq_of_factorsThroughEntry

theorem HeckeEis.heckeOperatorHom_eq_of_factorsThroughEntry (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hfac : ∀ γ δ : CongruenceSubgroup.Gamma0 N,
      CongruenceSubgroup.Gamma0Map N γ = CongruenceSubgroup.Gamma0Map N δ →
        φ (Additive.ofMul γ) = φ (Additive.ofMul δ)) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_eq_of_factorsThroughEntry.solution
