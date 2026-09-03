import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_exists_digits_eq_of_varpi_eq_verschiebung_level_two

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.GradedCartierModuleData.exists_digits_eq_of_varpi_eq_verschiebung_level_two
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : Zp2 p →+* B)
    (D : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (xi xnext : D.M) (a : B)
    (hcrit : D.varpi (γ i) = D.verschiebung xi)
    (hnext : D.varpi (γ (i + 1)) = WittVector.teichmuller p a • γ i + D.verschiebung xnext)
    (m : D.M) (hm : m ∈ D.piece i) (hinv : D.varpi m = D.verschiebung m) :
    ∃ (c d e h g k : B) (m₂ x' x'' xn' fr' : D.M) (ω : WittVector p B),
      m = WittVector.teichmuller p c • γ i +
        D.verschiebung (WittVector.teichmuller p d • γ (i + 1) + D.verschiebung m₂) ∧
      xi = WittVector.teichmuller p e • γ i + D.verschiebung x' ∧
      x' = WittVector.teichmuller p h • γ (i + 1) + D.verschiebung x'' ∧
      xnext = WittVector.teichmuller p g • γ (i + 1) + D.verschiebung xn' ∧
      D.frobenius (γ i) = WittVector.teichmuller p k • γ (i + 1) + D.verschiebung fr' ∧
      ω = WittVector.teichmuller p (c ^ p * e) + WittVector.teichmuller p (d * a) - WittVector.teichmuller p c ∧
      ω.coeff 0 = 0 ∧
      c = e * c ^ p + a * d ∧
      d = g * d ^ p + h * c ^ (p * p) + ω.coeff 1 * k := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_digits_eq_of_varpi_eq_verschiebung_level_two.solution
