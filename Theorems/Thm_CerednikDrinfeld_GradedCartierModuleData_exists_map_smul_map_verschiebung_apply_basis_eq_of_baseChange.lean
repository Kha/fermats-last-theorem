import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange
    (p : ℕ) [Fact p.Prime] {S T B' : Type} [CommRing S] [CommRing T] [CommRing B']
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (i : S →+* T) (q : T →+* B')
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (g : DS.M →+ DT.M) (hg : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' i DS DT g)
    (k : DS.M →+ D'.M) (hk : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' (q.comp i) DS D' k)
    (γ : Fin 2 → DS.M) (hγ : DS.IsHomogeneousVBasis γ) (hgγ : DT.IsHomogeneousVBasis (fun i => g (γ i))) :
    ∃ h : DT.M →+ D'.M,
      (∀ (w : WittVector p T) (x : DT.M), h (w • x) = WittVector.map q w • h x) ∧
      (∀ x : DT.M, h (DT.verschiebung x) = D'.verschiebung (h x)) ∧
      ∀ i : Fin 2, h (g (γ i)) = k (γ i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_map_smul_map_verschiebung_apply_basis_eq_of_baseChange.solution
