import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry

theorem HeckeEis.heckeOperatorHom_apply_of_factorsThroughEntry (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (φ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hfac : ∀ γ δ : CongruenceSubgroup.Gamma0 N,
      CongruenceSubgroup.Gamma0Map N γ = CongruenceSubgroup.Gamma0Map N δ →
        φ (Additive.ofMul γ) = φ (Additive.ofMul δ))
    (g : CongruenceSubgroup.Gamma0 N) :
    HeckeEis.heckeOperatorHom N ℓ A φ (Additive.ofMul g) = (ℓ + 1) • φ (Additive.ofMul g) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_apply_of_factorsThroughEntry.solution
