import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent
    (p : ℕ) [Fact p.Prime] :
    ∃ X₀ : CerednikDrinfeld.FormalODModule p (CerednikDrinfeld.Zp2 p),
      ∀ (B : Type u) [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B), IsNilpotent (p : B) →
        (X₀.map j).IsSpecial j ∧ (X₀.map j).HasHeight 4 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent.solution
