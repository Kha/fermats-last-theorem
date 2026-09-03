import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.IsSpecial.of_isODHom_of_comp_eq_id
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (Y Y' : FormalODModule p B) (u v : Series B)
    (hu : FormalODModule.IsODHom Y Y' u) (hv : FormalODModule.IsODHom Y' Y v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (hY : Y.IsSpecial j) : Y'.IsSpecial j := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_IsSpecial_of_isODHom_of_comp_eq_id.solution
