import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xnext : D.M) (a : B)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (c : B) (n : D.M) :
    (∃ x ∈ D.piece (i + 1), ∃ x' : D.M,
        WittVector.teichmuller p c • γ i + D.verschiebung n = D.varpi x + D.verschiebung x') ↔ a ∣ c := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_eq_varpi_add_verschiebung_iff_dvd_of_varpi_eq_teichmuller_smul_add.solution
