import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_comp_gamma0UnitsChar

theorem HeckeEis.heckeOperatorHom_comp_gamma0UnitsChar (N : ℕ) {ℓ : ℕ} [NeZero ℓ] (A : Type*) [AddCommGroup A]
    (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (χ : Additive (ZMod N)ˣ →+ A) :
    HeckeEis.heckeOperatorHom N ℓ A (χ.comp (Ihara.gamma0UnitsChar N)) =
      (ℓ + 1) • χ.comp (Ihara.gamma0UnitsChar N) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_comp_gamma0UnitsChar.solution
