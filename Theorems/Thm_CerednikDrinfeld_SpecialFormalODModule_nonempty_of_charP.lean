import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.nonempty_of_charP
    (p : ℕ) [Fact p.Prime] (B : Type u) [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) :
    Nonempty (CerednikDrinfeld.SpecialFormalODModule p j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_nonempty_of_charP.solution
