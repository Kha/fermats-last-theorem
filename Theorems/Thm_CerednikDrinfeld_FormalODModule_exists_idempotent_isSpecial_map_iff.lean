import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (Y : FormalODModule p S) :
    ∃ e : S, IsIdempotentElem e ∧
      ∀ (S' : Type) [CommRing S'] (f : S →+* S'), (Y.map f).IsSpecial (f.comp j) ↔ f e = 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_idempotent_isSpecial_map_iff.solution
