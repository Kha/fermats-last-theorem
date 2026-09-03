import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_IsSpecial_map

set_option autoImplicit false

universe u v

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.IsSpecial.map
    {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']
    (j : Zp2 p →+* B) (f : B →+* B') (X : FormalODModule p B) (hX : X.IsSpecial j) :
    (X.map f).IsSpecial (f.comp j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_IsSpecial_map.solution
