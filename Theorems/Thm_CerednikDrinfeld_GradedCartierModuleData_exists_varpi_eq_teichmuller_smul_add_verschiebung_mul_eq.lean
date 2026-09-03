import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) :
    ∃ (a : Fin 2 → B) (x : Fin 2 → D.M),
      (∀ i : Fin 2, D.varpi (γ i) = WittVector.teichmuller p (a i) • γ (i + 1) + D.verschiebung (x i)) ∧
      (∀ i : Fin 2, x i ∈ D.piece i) ∧
      a 0 * a 1 = (p : B) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_varpi_eq_teichmuller_smul_add_verschiebung_mul_eq.solution
