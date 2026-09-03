import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import P2M.Util
import P2M.Sol.S_ModularForm_eta_modular_S_smul

theorem ModularForm.eta_modular_S_smul (z : UpperHalfPlane) : ModularForm.eta ((ModularGroup.S • z : UpperHalfPlane) : ℂ) = Complex.sqrt (-Complex.I * z) * ModularForm.eta z := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_eta_modular_S_smul.solution
