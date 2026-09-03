import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis
    (p : ℕ) [Fact p.Prime] {T B' : Type} [CommRing T] [CommRing B']
    {jT : CerednikDrinfeld.Zp2 p →+* T} {j' : CerednikDrinfeld.Zp2 p →+* B'} (q : T →+* B')
    (DT : CerednikDrinfeld.GradedCartierModuleData p T jT) (hDT : DT.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (h : DT.M →+ D'.M)
    (hsl : ∀ (w : WittVector p T) (x : DT.M), h (w • x) = WittVector.map q w • h x)
    (hV : ∀ x : DT.M, h (DT.verschiebung x) = D'.verschiebung (h x))
    (β : Fin 2 → DT.M) (hβ : DT.IsHomogeneousVBasis β) (hβ' : D'.IsHomogeneousVBasis (fun i => h (β i)))
    (hvarpi : ∀ i : Fin 2, h (DT.varpi (β i)) = D'.varpi (h (β i))) :
    CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' q DT D' h := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_baseChange_of_map_smul_of_map_verschiebung_of_isHomogeneousVBasis.solution
