import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0)
    (D D' : CerednikDrinfeld.GradedCartierModuleData p B j)
    (hD : D.IsSpecialCartierModule) (hD' : D'.IsSpecialCartierModule)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (γ' : Fin 2 → D'.M) (hγ' : D'.IsHomogeneousVBasis γ')
    (a : ℕ → Fin 2 → B) (ha : D.HasStructureConstants γ a) (ha' : D'.HasStructureConstants γ' a) :
    ∃ g : D.M →+ D'.M, (∀ i, g (γ i) = γ' i) ∧
      Function.Bijective g ∧
      (∀ (w : WittVector p B) (x : D.M), g (w • x) = w • g x) ∧
      (∀ x, g (D.frobenius x) = D'.frobenius (g x)) ∧
      (∀ x, g (D.verschiebung x) = D'.verschiebung (g x)) ∧
      (∀ x, g (D.varpi x) = D'.varpi (g x)) ∧
      (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → g x ∈ D'.piece i) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree.solution
