import Mathlib.NumberTheory.ModularForms.DedekindEta
import P2M.Util
import P2M.Sol.S_ModularForm_continuous_logEta

theorem ModularForm.continuous_logEta : Continuous fun τ : UpperHalfPlane => (Real.pi * Complex.I * (τ : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (τ : ℂ))) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_continuous_logEta.solution
