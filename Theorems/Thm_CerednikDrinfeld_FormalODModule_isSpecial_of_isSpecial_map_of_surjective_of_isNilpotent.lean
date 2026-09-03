import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hp : IsNilpotent (p : R))
    (j : Zp2 p →+* R) (X : FormalODModule p R) (h : (X.map π).IsSpecial (π.comp j)) :
    X.IsSpecial j := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_isSpecial_map_of_surjective_of_isNilpotent.solution
