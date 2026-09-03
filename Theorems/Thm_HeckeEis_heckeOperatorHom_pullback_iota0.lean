import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_pullback_iota0

open CongruenceSubgroup HeckeEis
theorem HeckeEis.heckeOperatorHom_pullback_iota0 (N q ℓ : ℕ) [NeZero ℓ] {A : Type*} [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓq : ¬ ℓ ∣ q) (φ : Additive (Gamma0 N) →+ A) :
    pullbackHom (Ihara.ι₀ N q) (heckeOperatorHom N ℓ A φ) =
      heckeOperatorHom (N * q) ℓ A (pullbackHom (Ihara.ι₀ N q) φ) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_pullback_iota0.solution
