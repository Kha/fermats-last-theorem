import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xi xnext : D.M) (a : B)
    (hcrit : D.varpi (γ i) = D.verschiebung xi)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (m : D.M) (hm : m ∈ D.piece i) (hinv : D.varpi m = D.verschiebung m) :
    ∃ (c d b : B) (m₂ x' : D.M),
      m = WittVector.teichmuller p c • γ i +
        D.verschiebung (WittVector.teichmuller p d • γ (i + 1) + D.verschiebung m₂) ∧
      xi = WittVector.teichmuller p b • γ i + D.verschiebung x' ∧
      c = b * c ^ p + a * d := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_digit_eq_mul_pow_add_mul_of_varpi_eq_verschiebung.solution
