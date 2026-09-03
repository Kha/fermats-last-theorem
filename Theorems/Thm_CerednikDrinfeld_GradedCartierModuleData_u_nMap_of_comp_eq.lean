import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.u_nMap_of_comp_eq
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B'] {j : CerednikDrinfeld.Zp2 p →+* B}
    {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (D' : CerednikDrinfeld.GradedCartierModuleData p B' j')
    (bc : D.M →+ D'.M)
    (hV : ∀ x, bc (D.verschiebung x) = D'.verschiebung (bc x)) (hPi : ∀ x, bc (D.varpi x) = D'.varpi (bc x))
    (L : D.M →+ D.NMod) (hLV : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hLV' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ x, L' (bc x) = D.nMap D' bc hV hPi (L x))
    (z : D.NMod) (hz : z ∈ D.eta L hLV) :
    D.nMap D' bc hV hPi z ∈ D'.eta L' hLV' ∧
      ∀ (m : D.M) (hz' : D.nMap D' bc hV hPi z ∈ D'.eta L' hLV'),
        D.vRange.mkQ m = D.u L hLV ⟨z, hz⟩ →
        D'.vRange.mkQ (bc m) = D'.u L' hLV' ⟨D.nMap D' bc hV hPi z, hz'⟩ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq.solution
