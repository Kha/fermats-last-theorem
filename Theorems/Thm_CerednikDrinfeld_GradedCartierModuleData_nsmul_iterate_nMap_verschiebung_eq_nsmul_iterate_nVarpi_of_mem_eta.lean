import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j)
    (hVF : ∀ m : D.M, D.verschiebung (D.frobenius m) = (p : ℕ) • m)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (NV : D.NMod →+ D.NMod)
    (hNV : ∀ x y : D.M, NV (D.nMk (x, y)) = D.nMk (D.verschiebung x, D.verschiebung y))
    (m : ℕ) (y : D.NMod) (hy : y ∈ D.eta L hL.map_verschiebung) :
    (p : ℕ) • ((⇑NV)^[m] y) = (p : ℕ) • ((⇑D.nVarpi)^[m] y) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_nsmul_iterate_nMap_verschiebung_eq_nsmul_iterate_nVarpi_of_mem_eta.solution
