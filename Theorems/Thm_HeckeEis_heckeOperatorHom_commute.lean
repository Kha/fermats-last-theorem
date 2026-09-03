import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_commute

open CongruenceSubgroup HeckeEis
theorem HeckeEis.heckeOperatorHom_commute (N : ℕ) (A : Type*) [AddCommGroup A]
    (ℓ₁ ℓ₂ : Nat.Primes) (φ : Additive (Gamma0 N) →+ A) :
    haveI : NeZero (ℓ₁ : ℕ) := ⟨ℓ₁.2.ne_zero⟩
    haveI : NeZero (ℓ₂ : ℕ) := ⟨ℓ₂.2.ne_zero⟩
    heckeOperatorHom N ℓ₁ A (heckeOperatorHom N ℓ₂ A φ) =
      heckeOperatorHom N ℓ₂ A (heckeOperatorHom N ℓ₁ A φ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_commute.solution
