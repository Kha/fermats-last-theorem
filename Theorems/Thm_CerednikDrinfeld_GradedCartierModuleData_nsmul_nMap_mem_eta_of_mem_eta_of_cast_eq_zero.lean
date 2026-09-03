import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    {j : CerednikDrinfeld.Zp2 p →+* B} {j' : CerednikDrinfeld.Zp2 p →+* B'} (hp : (p : B') = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (D' : CerednikDrinfeld.GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M)
    (hF : ∀ x, f (D.frobenius x) = D'.frobenius (f x))
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCartierLMap L')
    (z : D.NMod) (hz : z ∈ D.eta L hL.map_verschiebung) :
    p • D.nMap D' f hV hPi z ∈ D'.eta L' hL'.map_verschiebung := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero.solution
