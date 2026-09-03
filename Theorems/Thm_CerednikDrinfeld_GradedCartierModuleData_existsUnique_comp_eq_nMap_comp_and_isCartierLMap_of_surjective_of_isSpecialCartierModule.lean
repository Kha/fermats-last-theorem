import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B) (hφ : Function.Surjective φ)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDl : Dl.IsSpecialCartierModule)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS)) (hD : D.IsSpecialCartierModule)
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (hLl : Dl.IsCartierLMap Ll) :
    ∃! L : D.M →+ D.NMod,
      (∀ x : Dl.M, L (f x) = Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x)) ∧ D.IsCartierLMap L := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule.solution
