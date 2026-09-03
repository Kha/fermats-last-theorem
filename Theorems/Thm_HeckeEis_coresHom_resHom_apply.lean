import Definitions.Def_Gamma0HeckeOperatorHom
import P2M.Util
import P2M.Sol.S_HeckeEis_coresHom_resHom_apply

open Subgroup
theorem HeckeEis.coresHom_resHom_apply {G : Type*} [Group G] (H : Subgroup G) {A : Type*}
    [AddCommGroup A] [H.FiniteIndex] (φ : Additive G →+ A) (g : G) :
    HeckeEis.coresHom H (HeckeEis.resHom H φ) (Additive.ofMul g) =
      H.index • φ (Additive.ofMul g) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_coresHom_resHom_apply.solution
