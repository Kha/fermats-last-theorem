import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import P2M.Util
import P2M.Sol.S_ModularForm_logEta_modular_S_smul

theorem ModularForm.logEta_modular_S_smul (z : UpperHalfPlane) : (Real.pi * Complex.I * ((ModularGroup.S • z : UpperHalfPlane) : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n ((ModularGroup.S • z : UpperHalfPlane) : ℂ))) = (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) + Complex.log (-Complex.I * z) / 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_logEta_modular_S_smul.solution
