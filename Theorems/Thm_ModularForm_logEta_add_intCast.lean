import Mathlib.NumberTheory.ModularForms.DedekindEta
import P2M.Util
import P2M.Sol.S_ModularForm_logEta_add_intCast

theorem ModularForm.logEta_add_intCast (z : ℂ) (m : ℤ) : (Real.pi * Complex.I * (z + m) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z + m))) = (Real.pi * Complex.I * z / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n z)) + Real.pi * Complex.I * m / 12 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_logEta_add_intCast.solution
