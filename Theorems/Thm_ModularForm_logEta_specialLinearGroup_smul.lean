import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import P2M.Util
import P2M.Sol.S_ModularForm_logEta_specialLinearGroup_smul

theorem ModularForm.logEta_specialLinearGroup_smul (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hc : 0 < (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) (z : UpperHalfPlane) : (Real.pi * Complex.I * ((γ • z : UpperHalfPlane) : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n ((γ • z : UpperHalfPlane) : ℂ))) = (Real.pi * Complex.I * (z : ℂ) / 12 + ∑' n : ℕ, Complex.log (1 - ModularForm.eta_q n (z : ℂ))) + Complex.log (-Complex.I * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (z : ℂ) + ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ))) / 2 + Real.pi * Complex.I / 12 * (((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ℚ) / ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℕ) : ℚ) - 12 * dedekindSum ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0).toNat : ℚ) : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_logEta_specialLinearGroup_smul.solution
