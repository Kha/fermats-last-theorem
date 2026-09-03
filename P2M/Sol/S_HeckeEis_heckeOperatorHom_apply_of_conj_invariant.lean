import Definitions.Def_Gamma0HeckeOperatorHom
import Theorems.Thm_HeckeEis_coresHom_resHom_apply
import P2M.Util
namespace P2MW.S_HeckeEis_heckeOperatorHom_apply_of_conj_invariant

open CongruenceSubgroup Subgroup

theorem solution (N ℓ : ℕ) [NeZero ℓ] {A : Type*}
    [AddCommGroup A] (φ : Additive ↥(Gamma0 N) →+ A)
    (hφ : ∀ γ : ↥(HeckeEis.heckeUpper N ℓ),
      φ (Additive.ofMul ((HeckeEis.heckeConj N ℓ) γ)) = φ (Additive.ofMul ↑γ))
    (g : Additive ↥(Gamma0 N)) :
    HeckeEis.heckeOperatorHom N ℓ A φ g = (HeckeEis.heckeUpper N ℓ).index • φ g := by
  have hpb : HeckeEis.pullbackHom (HeckeEis.heckeConj N ℓ) φ =
      HeckeEis.resHom (HeckeEis.heckeUpper N ℓ) φ := by
    ext γ
    exact hφ γ
  show HeckeEis.coresHom (HeckeEis.heckeUpper N ℓ)
    (HeckeEis.pullbackHom (HeckeEis.heckeConj N ℓ) φ) g = _
  rw [hpb]
  exact HeckeEis.coresHom_resHom_apply (HeckeEis.heckeUpper N ℓ) φ g.toMul
