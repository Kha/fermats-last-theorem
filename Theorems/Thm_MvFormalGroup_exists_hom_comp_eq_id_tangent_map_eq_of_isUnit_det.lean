import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det) :
    ∃ (Φ' : MvFormalGroup d R) (_ : Φ'.IsComm) (φ : Φ.Hom Φ') (ψ : Φ'.Hom Φ),
      φ.comp ψ = MvFormalGroup.Hom.id Φ' ∧ ψ.comp φ = MvFormalGroup.Hom.id Φ ∧
      ∀ i j, MvFormalGroup.CartierModule.tangent (MvFormalGroup.CartierModule.map φ (f i)) j =
        if i = j then 1 else 0 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det.solution
