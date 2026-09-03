import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_nMap_apply_eq_zero_of_apply_eq_zero

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.nMap_apply_eq_zero_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    (jS : CerednikDrinfeld.Zp2 p →+* S) (φ : S →+* B)
    (Dl : CerednikDrinfeld.GradedCartierModuleData p S jS)
    (D : CerednikDrinfeld.GradedCartierModuleData p B (φ.comp jS))
    (f : Dl.M →+ D.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (hLl : Dl.IsCartierLMap Ll)
    (x : Dl.M) (hx : f x = 0) :
    Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x) = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_nMap_apply_eq_zero_of_apply_eq_zero.solution
