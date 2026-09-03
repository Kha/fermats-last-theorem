import Mathlib.NumberTheory.ModularForms.DedekindEta
import P2M.Util
import P2M.Sol.S_ModularForm_eta_add_intCast

theorem ModularForm.eta_add_intCast (z : ℂ) (m : ℤ) : ModularForm.eta (z + m) = Complex.exp (Real.pi * Complex.I * m / 12) * ModularForm.eta z := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_eta_add_intCast.solution
