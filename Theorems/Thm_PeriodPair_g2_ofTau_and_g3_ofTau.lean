import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import P2M.Util
import P2M.Sol.S_PeriodPair_g2_ofTau_and_g3_ofTau

set_option autoImplicit false

theorem PeriodPair.g2_ofTau_and_g3_ofTau (τ : UpperHalfPlane) :
    (PeriodPair.ofTau τ).g₂ = 120 * riemannZeta 4 * ModularForm.E₄ τ ∧
      (PeriodPair.ofTau τ).g₃ = 280 * riemannZeta 6 * ModularForm.E₆ τ := by p2m_exact_reverting @_root_.P2MW.S_PeriodPair_g2_ofTau_and_g3_ofTau.solution
