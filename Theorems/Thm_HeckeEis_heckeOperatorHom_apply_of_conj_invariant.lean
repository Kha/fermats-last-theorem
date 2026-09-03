import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_HeckeEis_heckeOperatorHom_apply_of_conj_invariant

open CongruenceSubgroup Subgroup
theorem HeckeEis.heckeOperatorHom_apply_of_conj_invariant (N ℓ : ℕ) [NeZero ℓ] {A : Type*}
    [AddCommGroup A] (φ : Additive ↥(Gamma0 N) →+ A)
    (hφ : ∀ γ : ↥(HeckeEis.heckeUpper N ℓ),
      φ (Additive.ofMul ((HeckeEis.heckeConj N ℓ) γ)) = φ (Additive.ofMul ↑γ))
    (g : Additive ↥(Gamma0 N)) :
    HeckeEis.heckeOperatorHom N ℓ A φ g = (HeckeEis.heckeUpper N ℓ).index • φ g := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_heckeOperatorHom_apply_of_conj_invariant.solution
