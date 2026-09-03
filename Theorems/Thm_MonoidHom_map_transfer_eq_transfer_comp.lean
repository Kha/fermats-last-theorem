import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import P2M.Util
import P2M.Sol.S_MonoidHom_map_transfer_eq_transfer_comp

set_option autoImplicit false

theorem MonoidHom.map_transfer_eq_transfer_comp
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_map_transfer_eq_transfer_comp.solution
