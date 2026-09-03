import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) :
    ∃ a : ℕ → Fin 2 → B, D.HasStructureConstants γ a ∧ a 0 0 * a 0 1 = (p : B) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis.solution
