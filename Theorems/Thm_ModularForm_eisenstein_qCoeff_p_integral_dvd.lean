import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import P2M.Util
import P2M.Sol.S_ModularForm_eisenstein_qCoeff_p_integral_dvd
set_option autoImplicit false

theorem ModularForm.eisenstein_qCoeff_p_integral_dvd (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k)
    (hpk : p - 1 ∣ k) (m : ℕ) (hm : 0 < m) :
    ∃ (x : ℤ) (s : ℕ), ¬ p ∣ s ∧
      (x : ℂ) = s * (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 ⇑(ModularForm.E hk)) ∧
      (p : ℤ) ∣ x := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_eisenstein_qCoeff_p_integral_dvd.solution
