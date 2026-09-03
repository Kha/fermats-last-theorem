import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import P2M.Util
namespace P2MW.S_MonoidHom_map_transfer_eq_transfer_comp

set_option autoImplicit false

theorem solution
    {G : Type*} [Group G] {H : Subgroup G} [H.FiniteIndex]
    {A B : Type*} [CommGroup A] [CommGroup B] (ϕ : ↥H →* A) (f : A →* B) (g : G) :
    f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by
  classical
  rw [MonoidHom.transfer_def ϕ (default : H.LeftTransversal) g,
    MonoidHom.transfer_def (f.comp ϕ) (default : H.LeftTransversal) g]
  unfold Subgroup.leftTransversals.diff
  simp only [map_prod, MonoidHom.comp_apply]
