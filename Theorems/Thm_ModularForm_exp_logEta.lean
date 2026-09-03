import Mathlib.NumberTheory.ModularForms.DedekindEta
import P2M.Util
import P2M.Sol.S_ModularForm_exp_logEta

theorem ModularForm.exp_logEta (z : UpperHalfPlane) : Complex.exp (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) = ModularForm.eta z := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_exp_logEta.solution
