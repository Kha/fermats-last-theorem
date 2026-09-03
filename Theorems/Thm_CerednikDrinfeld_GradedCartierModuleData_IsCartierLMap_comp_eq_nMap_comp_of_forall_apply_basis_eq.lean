import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCartierLMap.comp_eq_nMap_comp_of_forall_apply_basis_eq
    (p : ℕ) [Fact p.Prime] {S B : Type} [CommRing S] [CommRing B]
    {jS : CerednikDrinfeld.Zp2 p →+* S} {j : CerednikDrinfeld.Zp2 p →+* B} (φ : S →+* B)
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (h : DS.M →+ D.M) (hh : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ DS D h)
    (LS : DS.M →+ DS.NMod) (hLS : DS.IsCartierLMap LS)
    (K : D.M →+ D.NMod) (hK : D.IsCartierLMap K)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ)
    (hKγ : ∀ i : Fin 2, K (h (γ i)) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS (γ i))) :
    ∀ x : DS.M, K (h x) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS x) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq.solution
