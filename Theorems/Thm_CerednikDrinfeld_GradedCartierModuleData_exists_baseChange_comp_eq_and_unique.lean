import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_baseChange_comp_eq_and_unique

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_baseChange_comp_eq_and_unique
    (p : ℕ) [Fact p.Prime] {S T B' : Type} [CommRing S] [CommRing T] [CommRing B']
    {jS : CerednikDrinfeld.Zp2 p →+* S} {jT : CerednikDrinfeld.Zp2 p →+* T}
    {j' : CerednikDrinfeld.Zp2 p →+* B'}
    (i : S →+* T) (q : T →+* B')
    (DS : CerednikDrinfeld.GradedCartierModuleData p S jS) (hDS : DS.IsSpecialCartierModule)
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (g : DS.M →+ DT.M) (hg : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' i DS DT g)
    (k : DS.M →+ D'.M) (hk : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' (q.comp i) DS D' k) :
    ∃ h : DT.M →+ D'.M,
      CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DT D' h ∧
      (∀ x : DS.M, h (g x) = k x) ∧
      ∀ h' : DT.M →+ D'.M,
        (∀ (w : WittVector p T) (y : DT.M), h' (w • y) = WittVector.map q w • h' y) →
        (∀ y : DT.M, h' (DT.verschiebung y) = D'.verschiebung (h' y)) →
        (∀ x : DS.M, h' (g x) = k x) → h' = h := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_baseChange_comp_eq_and_unique.solution
