import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_isSpecial_of_forall_isSpecial_map_away

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.isSpecial_of_forall_isSpecial_map_away
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (hB : IsNilpotent (p : B)) (j : Zp2 p →+* B)
    (Y : FormalODModule p B) {n : ℕ} (g : Fin n → B) (hg : Ideal.span (Set.range g) = ⊤)
    (h : ∀ i : Fin n, (Y.map (algebraMap B (Localization.Away (g i)))).IsSpecial
      ((algebraMap B (Localization.Away (g i))).comp j)) :
    Y.IsSpecial j := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_isSpecial_of_forall_isSpecial_map_away.solution
